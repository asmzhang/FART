#!/usr/bin/env python3
"""Generic missing-type stubs for FART dump (no PRE APK).

Problem class: dump DEX has class_def rows whose superclass / interfaces /
method proto / field types are only type_ids (no class_def, not a boot type).
Missing super/iface → ART DefineClass fails. Missing signature types →
getParameterTypes / invoke never enters, packer keeps the placeholder.
Ads / UMP / OAID / ArcherBridge / FormError / IdSupplier are instances.

This tool only reads packed-app dump DEX (and optional inspect_fail / ins.bin).
It emits empty class/interface stubs plus an execute list: dependents of
missing supers, and classes whose CodeItems still look packed after ins merge.

    python tools/link_stubs.py --dex-dir DIR --out fart_link_stubs.dex
    python tools/link_stubs.py --dex-dir DIR --out fart_link_stubs.dex --push
"""

from __future__ import annotations

import argparse
import base64
import os
import re
import shutil
import struct
import subprocess
import sys
import zipfile
from pathlib import Path


BOOT_PREFIXES = (
    "Ljava/",
    "Landroid/",
    "Ldalvik/",
    "Llibcore/",
    "Lsun/",
    "Lorg/xmlpull/",
    "Lorg/json/",
    "Lorg/apache/harmony/",
    "Lorg/w3c/",
    "Lorg/xml/",
)

# Android boot has a few javax.* packages. The rest (servlet, money, JAX-RS, …)
# are optional app deps and must be stubbed when dump DEX references them.
JAVAX_BOOT_PREFIXES = (
    "Ljavax/crypto/",
    "Ljavax/net/",
    "Ljavax/security/",
    "Ljavax/xml/",
    "Ljavax/sql/",
    "Ljavax/microedition/",
)

# androidx / material are app types even though they look like platform.
NOT_BOOT_PREFIXES = (
    "Landroidx/",
    "Lcom/google/android/material/",
)

FAILED_RES = re.compile(r"Failed resolution of:\s*(L[^;\s]+;)")
NOSUCH_METHOD = re.compile(
    r"No static method (?P<name>[\w$]+)\((?P<args>[^)]*)\)(?P<ret>\S*) in class (?P<cls>L[^;]+;)"
)
INS_RE = re.compile(
    rb"\{name:(?P<name>.*?),"
    rb"method_idx:(?P<mid>\d+),"
    rb"offset:(?P<off>\d+),"
    rb"code_item_len:(?P<clen>\d+),"
    rb".*?"
    rb"ins:(?P<ins>[A-Za-z0-9+/=]+)\};"
)
PRIM = {
    "V": "void",
    "Z": "boolean",
    "B": "byte",
    "S": "short",
    "C": "char",
    "I": "int",
    "J": "long",
    "F": "float",
    "D": "double",
}

SKIP_STUB_METHODS = {
    "getMessage",
    "getLocalizedMessage",
    "toString",
    "hashCode",
    "equals",
    "wait",
    "notify",
    "notifyAll",
    "getClass",
    "finalize",
    "clone",
    "getCause",
    "getStackTrace",
    "printStackTrace",
    "fillInStackTrace",
    "initCause",
    "addSuppressed",
    "getSuppressed",
}


def uleb128(data: bytes, off: int) -> tuple[int, int]:
    result = 0
    shift = 0
    while True:
        b = data[off]
        off += 1
        result |= (b & 0x7F) << shift
        if b < 0x80:
            return result, off
        shift += 7


def read_mutf8(data: bytes, off: int) -> str:
    _, payload = uleb128(data, off)
    end = data.index(0, payload)
    return bytes(data[payload:end]).decode("utf-8", "replace")


def is_boot(desc: str) -> bool:
    if not desc or desc[0] == "[":
        return True
    if desc.startswith(NOT_BOOT_PREFIXES):
        return False
    if desc.startswith("Ljavax/"):
        return desc.startswith(JAVAX_BOOT_PREFIXES)
    return desc.startswith(BOOT_PREFIXES)


def leaf_type(desc: str) -> str:
    while desc.startswith("["):
        desc = desc[1:]
    return desc


def close_signature_stubs(
    stub_kind: dict[str, str],
    stub_fields: dict[str, list[tuple[str, str]]],
    stub_methods: dict[str, list[tuple[str, str, tuple[str, ...]]]],
    defined: set[str],
) -> int:
    """Stub every L-type that appears on a stub field/method so javac can compile."""
    added = 0
    changed = True
    while changed:
        changed = False
        types: set[str] = set()
        for items in stub_fields.values():
            for _name, fty in items:
                types.add(leaf_type(fty))
        for items in stub_methods.values():
            for _name, ret, params in items:
                types.add(leaf_type(ret))
                types.update(leaf_type(p) for p in params)
        for desc in types:
            if not desc or desc[0] != "L":
                continue
            if desc in defined or is_boot(desc) or desc in stub_kind:
                continue
            stub_kind[desc] = "interface" if iface_name_hint(desc) else "class"
            added += 1
            changed = True
    return added


def dotted_to_desc(name: str) -> str:
    name = name.strip()
    if name.startswith("L") and name.endswith(";"):
        return name
    return "L" + name.replace(".", "/") + ";"


def desc_to_dotted(desc: str) -> str:
    if desc.startswith("L") and desc.endswith(";"):
        return desc[1:-1].replace("/", ".")
    return desc


def java_type(desc: str) -> str:
    if desc in PRIM:
        return PRIM[desc]
    if desc.startswith("["):
        return java_type(desc[1:]) + "[]"
    if desc.startswith("L") and desc.endswith(";"):
        return desc[1:-1].replace("/", ".").replace("$", ".")
    return desc


def java_default_stmt(desc: str) -> str:
    if desc == "V":
        return ""
    if desc == "Z":
        return "return false;"
    if desc in ("B", "S", "C", "I"):
        return "return 0;"
    if desc == "J":
        return "return 0L;"
    if desc == "F":
        return "return 0f;"
    if desc == "D":
        return "return 0d;"
    return "return null;"


def split_dalvik_params(s: str) -> list[str]:
    out: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        if s[i] == "L":
            j = s.find(";", i)
            if j < 0:
                break
            out.append(s[i : j + 1])
            i = j + 1
        elif s[i] == "[":
            k = i
            while k < n and s[k] == "[":
                k += 1
            if k < n and s[k] == "L":
                j = s.find(";", k)
                if j < 0:
                    break
                out.append(s[i : j + 1])
                i = j + 1
            else:
                out.append(s[i : k + 1])
                i = k + 1
        else:
            out.append(s[i])
            i += 1
    return out


def is_java_ident(name: str) -> bool:
    return bool(name) and name.isidentifier()


class DexLite:
    def __init__(self, raw: bytes) -> None:
        self.data = raw
        ss_sz, ss_off = struct.unpack_from("<II", raw, 0x38)
        t_sz, t_off = struct.unpack_from("<II", raw, 0x40)
        p_sz, p_off = struct.unpack_from("<II", raw, 0x48)
        m_sz, m_off = struct.unpack_from("<II", raw, 0x58)
        c_sz, c_off = struct.unpack_from("<II", raw, 0x60)
        strings = [
            read_mutf8(raw, struct.unpack_from("<I", raw, ss_off + i * 4)[0])
            for i in range(ss_sz)
        ]
        self.strings = strings
        self.types = [
            strings[struct.unpack_from("<I", raw, t_off + i * 4)[0]] for i in range(t_sz)
        ]
        self.class_defs_size = c_sz
        self.class_defs_off = c_off
        protos: list[tuple[str, list[str]]] = []
        for i in range(p_sz):
            _shorty, ret_idx, params_off = struct.unpack_from("<III", raw, p_off + i * 12)
            params: list[str] = []
            if params_off:
                n = struct.unpack_from("<I", raw, params_off)[0]
                for j in range(n):
                    ti = struct.unpack_from("<H", raw, params_off + 4 + j * 2)[0]
                    params.append(self.types[ti])
            protos.append((self.types[ret_idx], params))
        self.inits: list[tuple[str, tuple[str, ...]]] = []
        for i in range(m_sz):
            class_idx, proto_idx, name_idx = struct.unpack_from("<HHI", raw, m_off + i * 8)
            if strings[name_idx] != "<init>":
                continue
            _ret, params = protos[proto_idx]
            self.inits.append((self.types[class_idx], tuple(params)))
        self.protos = protos
        self._p_sz, self._p_off = p_sz, p_off
        self._f_sz, self._f_off = struct.unpack_from("<II", raw, 0x50)
        self._m_sz, self._m_off = m_sz, m_off

    def defined(self) -> set[str]:
        out = set()
        for ci in range(self.class_defs_size):
            ti = struct.unpack_from("<I", self.data, self.class_defs_off + ci * 32)[0]
            out.add(self.types[ti])
        return out

    def rows(self) -> list[tuple[str, str | None, list[str]]]:
        rows = []
        for ci in range(self.class_defs_size):
            base = self.class_defs_off + ci * 32
            class_idx, _a, super_idx, iface_off, _src, _ann, _cd, _sv = struct.unpack_from(
                "<IIIIIIII", self.data, base
            )
            cn = self.types[class_idx]
            sup = None if super_idx == 0xFFFFFFFF else self.types[super_idx]
            ifaces: list[str] = []
            if iface_off:
                n = struct.unpack_from("<I", self.data, iface_off)[0]
                for i in range(n):
                    ti = struct.unpack_from("<H", self.data, iface_off + 4 + i * 2)[0]
                    ifaces.append(self.types[ti])
            rows.append((cn, sup, ifaces))
        return rows

    def proto_and_field_types(self) -> tuple[set[str], set[str]]:
        protos: set[str] = set()
        for i in range(self._m_sz):
            _c, proto_idx, _n = struct.unpack_from("<HHI", self.data, self._m_off + i * 8)
            _shorty, ret_idx, params_off = struct.unpack_from(
                "<III", self.data, self._p_off + proto_idx * 12
            )
            protos.add(self.types[ret_idx])
            if params_off:
                n = struct.unpack_from("<I", self.data, params_off)[0]
                for j in range(n):
                    ti = struct.unpack_from("<H", self.data, params_off + 4 + j * 2)[0]
                    protos.add(self.types[ti])
        fields: set[str] = set()
        for i in range(self._f_sz):
            _c, t, _n = struct.unpack_from("<HHI", self.data, self._f_off + i * 8)
            fields.add(self.types[t])
        return protos, fields

    def fields_owned(self) -> dict[str, list[tuple[str, str]]]:
        out: dict[str, list[tuple[str, str]]] = {}
        for i in range(self._f_sz):
            c, t, ni = struct.unpack_from("<HHI", self.data, self._f_off + i * 8)
            owner = self.types[c]
            item = (self.strings[ni], self.types[t])
            bucket = out.setdefault(owner, [])
            if item not in bucket:
                bucket.append(item)
        return out

    def methods_owned(self) -> dict[str, list[tuple[str, str, tuple[str, ...]]]]:
        out: dict[str, list[tuple[str, str, tuple[str, ...]]]] = {}
        for i in range(self._m_sz):
            c, p, ni = struct.unpack_from("<HHI", self.data, self._m_off + i * 8)
            name = self.strings[ni]
            if name in ("<init>", "<clinit>"):
                continue
            ret, params = self.protos[p]
            item = (name, ret, tuple(params))
            bucket = out.setdefault(self.types[c], [])
            if item not in bucket:
                bucket.append(item)
        return out

    def packed_owners(self) -> set[str]:
        out: set[str] = set()
        raw = self.data
        n = len(raw)
        for ci in range(self.class_defs_size):
            base = self.class_defs_off + ci * 32
            class_idx, _a, _s, _i, _src, _ann, class_data, _sv = struct.unpack_from(
                "<IIIIIIII", raw, base
            )
            if not class_data:
                continue
            off = class_data
            try:
                sf, off = uleb128(raw, off)
                iff, off = uleb128(raw, off)
                dm, off = uleb128(raw, off)
                vm, off = uleb128(raw, off)
                for _ in range(sf + iff):
                    _, off = uleb128(raw, off)
                    _, off = uleb128(raw, off)
                packed = False
                for count in (dm, vm):
                    for _ in range(count):
                        _, off = uleb128(raw, off)
                        _, off = uleb128(raw, off)
                        code_off, off = uleb128(raw, off)
                        if looks_packed_code(raw, code_off, n):
                            packed = True
                if packed:
                    out.add(self.types[class_idx])
            except Exception:
                continue
        return out


def looks_packed_code(data: bytes | bytearray, off: int, n: int) -> bool:
    """Non-trivial Virbox-style punch: keep size, fill nops/zeros. Not 1-insn return-void."""
    if off <= 0 or off + 16 > n:
        return False
    insns = struct.unpack_from("<I", data, off + 12)[0]
    if insns < 4:
        return False
    end = off + 16 + insns * 2
    if end > n:
        return False
    code = bytes(data[off + 16 : end])
    if code[:2] == b"\x0e\x00" and code[2:].count(0) >= len(code) - 2:
        return True
    if code[:4] in (b"\x12\x00\x11\x00", b"\x12\x00\x0f\x00") and code[4:].count(0) >= len(code) - 4:
        return True
    return code.count(0) >= max(4, int(len(code) * 0.75))


def apply_ins(dex: bytearray, blob: bytes) -> int:
    wrote = 0
    for m in INS_RE.finditer(blob):
        off = int(m.group("off"))
        clen = int(m.group("clen"))
        raw = base64.b64decode(m.group("ins"))
        if len(raw) != clen or off < 0 or off + clen > len(dex):
            continue
        dex[off : off + clen] = raw
        wrote += 1
    return wrote


def packed_from_dex_dir(dex_dir: Path, dex_paths: list[Path]) -> set[str]:
    """Classes whose CodeItems still look packed after merging ins.bin (post-inspect view)."""
    out: set[str] = set()
    any_ins = False
    for p in dex_paths:
        prefix = p.name.split("_")[0]
        blobs = sorted(
            dex_dir.glob(f"{prefix}_ins_*.bin"),
            key=lambda x: x.stat().st_size,
            reverse=True,
        )
        if not blobs:
            continue
        any_ins = True
        raw = bytearray(p.read_bytes())
        for ins in blobs:
            apply_ins(raw, ins.read_bytes())
        for desc in DexLite(bytes(raw)).packed_owners():
            if not is_boot(desc):
                out.add(desc_to_dotted(desc))
    return out if any_ins else set()


def list_dump_dex(dex_dir: Path) -> list[Path]:
    files = sorted(
        p
        for p in dex_dir.glob("*_dex_file.dex")
        if "fix" not in p.name.lower()
        and "stub" not in p.name.lower()
        and p.stat().st_size >= 65536
    )
    if files:
        return files
    return [
        p
        for p in sorted(dex_dir.glob("*.dex"))
        if "fix" not in p.name.lower()
        and "stub" not in p.name.lower()
        and p.stat().st_size >= 65536
    ]


def extract_apk_dex(apk: Path, tmp: Path) -> list[Path]:
    tmp.mkdir(parents=True, exist_ok=True)
    out: list[Path] = []
    with zipfile.ZipFile(apk) as zf:
        for name in zf.namelist():
            base = name.replace("\\", "/").rsplit("/", 1)[-1]
            if not (base == "classes.dex" or re.match(r"classes\d+\.dex$", base)):
                continue
            dest = tmp / base
            dest.write_bytes(zf.read(name))
            out.append(dest)
    return sorted(out)


def pick_java_super(desc: str, kind: str) -> str:
    if kind == "interface":
        return "java.lang.Object"
    n = desc.lower()
    if n.endswith("error;"):
        return "java.lang.Error"
    if n.endswith("exception;"):
        return "java.lang.Exception"
    if "drawable" in n:
        return "android.graphics.drawable.Drawable"
    if any(s in n for s in ("view", "layout", "widget", "recycler")):
        return "android.view.ViewGroup"
    return "java.lang.Object"


def iface_name_hint(desc: str) -> bool:
    n = desc.lower()
    return any(
        s in n
        for s in (
            "listener",
            "callback",
            "monitor",
            "verifier",
            "bridge",
            "interface",
            "supplier",
        )
    )


def scan(
    dex_paths: list[Path],
) -> tuple[dict[str, str], list[str], dict[str, list[tuple[str, ...]]], set[str]]:
    defined: set[str] = set()
    rows: list[tuple[str, str | None, list[str]]] = []
    inits: dict[str, list[tuple[str, ...]]] = {}
    proto_types: set[str] = set()
    field_types: set[str] = set()
    for p in dex_paths:
        dex = DexLite(p.read_bytes())
        defined |= dex.defined()
        rows.extend(dex.rows())
        ptypes, ftypes = dex.proto_and_field_types()
        proto_types |= ptypes
        field_types |= ftypes
        for owner, params in dex.inits:
            bucket = inits.setdefault(owner, [])
            if params not in bucket:
                bucket.append(params)

    stub_kind: dict[str, str] = {}
    children: list[str] = []
    for cn, sup, ifaces in rows:
        missing = False
        if sup and sup not in defined and not is_boot(sup):
            stub_kind[sup] = "class"
            missing = True
        for iface in ifaces:
            if iface not in defined and not is_boot(iface):
                if iface not in stub_kind:
                    stub_kind[iface] = "interface"
                missing = True
        if missing:
            children.append(desc_to_dotted(cn))

    child_set = set(children)
    child_desc = {dotted_to_desc(n) for n in child_set}
    changed = True
    while changed:
        changed = False
        for cn, sup, ifaces in rows:
            dotted = desc_to_dotted(cn)
            if dotted in child_set:
                continue
            hit = (sup in stub_kind) or (sup in child_desc)
            if not hit:
                for iface in ifaces:
                    if iface in stub_kind or iface in child_desc:
                        hit = True
                        break
            if hit:
                child_set.add(dotted)
                child_desc.add(cn)
                changed = True

    for desc in proto_types | field_types:
        if not desc or desc[0] != "L" or desc in defined or is_boot(desc):
            continue
        if desc not in stub_kind:
            stub_kind[desc] = "class"
    return stub_kind, sorted(child_set), inits, defined


def merge_fail(
    fail_path: Path,
    stub_kind: dict[str, str],
    children: list[str],
    defined: set[str],
    stub_methods: dict[str, list[tuple[str, str, tuple[str, ...]]]] | None = None,
) -> None:
    child_set = set(children)
    text = fail_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        if "UnsatisfiedLinkError" in line:
            continue
        if "ExceptionInInitializerError" in line:
            continue
        if stub_methods is not None:
            for m in NOSUCH_METHOD.finditer(line):
                desc = m.group("cls")
                if desc in defined or is_boot(desc):
                    continue
                if desc not in stub_kind:
                    stub_kind[desc] = "class"
                name = m.group("name")
                ret = m.group("ret") or "V"
                params = tuple(split_dalvik_params(m.group("args") or ""))
                bucket = stub_methods.setdefault(desc, [])
                item = (name, ret, params)
                if item not in bucket:
                    bucket.append(item)
        if "NoSuchFieldError" in line:
            continue
        added_stub = False
        for m in FAILED_RES.finditer(line):
            desc = m.group(1)
            if desc in defined or is_boot(desc):
                continue
            if desc not in stub_kind:
                stub_kind[desc] = "interface" if iface_name_hint(desc) else "class"
            added_stub = True
        if not added_stub:
            continue
        parts = line.split("\t")
        if len(parts) >= 3:
            failed = parts[2].strip()
            if failed:
                child_set.add(failed)
    children[:] = sorted(child_set)


def collect_stub_members(
    dex_paths: list[Path],
    stub_kind: dict[str, str],
) -> tuple[dict[str, list[tuple[str, str]]], dict[str, list[tuple[str, str, tuple[str, ...]]]]]:
    fields: dict[str, list[tuple[str, str]]] = {}
    methods: dict[str, list[tuple[str, str, tuple[str, ...]]]] = {}
    for path in dex_paths:
        dex = DexLite(path.read_bytes())
        for owner, items in dex.fields_owned().items():
            if owner not in stub_kind:
                continue
            bucket = fields.setdefault(owner, [])
            for item in items:
                if item not in bucket:
                    bucket.append(item)
        for owner, items in dex.methods_owned().items():
            if owner not in stub_kind:
                continue
            bucket = methods.setdefault(owner, [])
            for item in items:
                if item not in bucket:
                    bucket.append(item)
    return fields, methods


def super_call(java_super: str, params: tuple[str, ...], names: list[str]) -> str:
    if java_super == "java.lang.Object" or java_super == "android.graphics.drawable.Drawable":
        return "super();"
    if java_super in ("java.lang.Exception", "java.lang.Error"):
        return "super();"
    if java_super in ("android.view.ViewGroup", "android.view.View"):
        ctx = [i for i, p in enumerate(params) if p == "Landroid/content/Context;"]
        attrs = [i for i, p in enumerate(params) if p == "Landroid/util/AttributeSet;"]
        ints = [i for i, p in enumerate(params) if p == "I"]
        if ctx and attrs and len(ints) >= 2:
            return f"super({names[ctx[0]]}, {names[attrs[0]]}, {names[ints[0]]}, {names[ints[1]]});"
        if ctx and attrs and ints:
            return f"super({names[ctx[0]]}, {names[attrs[0]]}, {names[ints[0]]});"
        if ctx and attrs:
            return f"super({names[ctx[0]]}, {names[attrs[0]]});"
        if ctx:
            return f"super({names[ctx[0]]});"
        return "super((android.content.Context) null);"
    return "super();"


def emit_ctors(cls_name: str, java_super: str, param_lists: list[tuple[str, ...]], indent: str) -> list[str]:
    lines: list[str] = []
    seen: set[tuple[str, ...]] = set()
    lists = list(param_lists)
    if java_super == "android.view.ViewGroup" and not lists:
        lists = [
            ("Landroid/content/Context;",),
            ("Landroid/content/Context;", "Landroid/util/AttributeSet;"),
        ]
    for params in lists:
        if params in seen:
            continue
        seen.add(params)
        names = [f"a{i}" for i in range(len(params))]
        args = ", ".join(f"{java_type(p)} {n}" for p, n in zip(params, names))
        body = super_call(java_super, params, names)
        lines.append(f"{indent}public {cls_name}({args}) {{ {body} }}")
    return lines


def emit_abstracts(java_super: str, indent: str) -> list[str]:
    if java_super == "android.view.ViewGroup":
        return [
            f"{indent}@Override protected void onLayout(boolean z, int a, int b, int c, int d) {{}}"
        ]
    if java_super == "android.graphics.drawable.Drawable":
        return [
            f"{indent}@Override public void draw(android.graphics.Canvas c) {{}}",
            f"{indent}@Override public void setAlpha(int a) {{}}",
            f"{indent}@Override public void setColorFilter(android.graphics.ColorFilter f) {{}}",
            f"{indent}@Override public int getOpacity() {{ return 0; }}",
        ]
    return []


class NestNode:
    def __init__(self, name: str, desc: str) -> None:
        self.name = name
        self.desc = desc
        self.kind = "class"
        self.stubbed = False
        self.children: dict[str, NestNode] = {}


def build_trees(stub_kind: dict[str, str]) -> dict[str, NestNode]:
    trees: dict[str, NestNode] = {}
    for desc, kind in stub_kind.items():
        body = desc[1:-1]
        parts = body.split("$")
        top_body = parts[0]
        top_desc = "L" + top_body + ";"
        slash = top_body.rfind("/")
        top_name = top_body[slash + 1 :]
        node = trees.get(top_desc)
        if node is None:
            node = NestNode(top_name, top_desc)
            trees[top_desc] = node
        if desc == top_desc:
            node.kind = kind
            node.stubbed = True
        cur = node
        acc = top_body
        for part in parts[1:]:
            acc = acc + "$" + part
            child_desc = "L" + acc + ";"
            nxt = cur.children.get(part)
            if nxt is None:
                nxt = NestNode(part, child_desc)
                cur.children[part] = nxt
            cur = nxt
            if child_desc == desc:
                cur.kind = kind
                cur.stubbed = True
    return trees


def emit_node(
    node: NestNode,
    stub_kind: dict[str, str],
    inits: dict[str, list[tuple[str, ...]]],
    indent: int,
    lines: list[str],
    stub_fields: dict[str, list[tuple[str, str]]] | None = None,
    stub_methods: dict[str, list[tuple[str, str, tuple[str, ...]]]] | None = None,
) -> None:
    if not is_java_ident(node.name):
        lines.append("    " * indent + f"// skip non-identifier {node.desc}")
        return
    kind = stub_kind.get(node.desc, node.kind)
    java_super = pick_java_super(node.desc, kind)
    sp = "    " * indent
    if indent == 0:
        decl = "public interface" if kind == "interface" else "public class"
    else:
        decl = "public interface" if kind == "interface" else "public static class"
    extends = ""
    if kind != "interface" and java_super != "java.lang.Object":
        extends = f" extends {java_super}"
    lines.append(f"{sp}{decl} {node.name}{extends} {{")
    inner = sp + "    "
    if kind != "interface":
        lines.extend(emit_ctors(node.name, java_super, inits.get(node.desc, []), inner))
        lines.extend(emit_abstracts(java_super, inner))
        seen_fields: set[str] = set()
        for fname, fty in (stub_fields or {}).get(node.desc, []):
            if fname in seen_fields or not is_java_ident(fname):
                continue
            seen_fields.add(fname)
            lines.append(f"{inner}public static {java_type(fty)} {fname};")
        seen_m: set[tuple[str, tuple[str, ...]]] = set()
        for mname, ret, params in (stub_methods or {}).get(node.desc, []):
            key = (mname, params)
            if key in seen_m or not is_java_ident(mname) or mname in SKIP_STUB_METHODS:
                continue
            seen_m.add(key)
            names = [f"a{i}" for i in range(len(params))]
            args = ", ".join(f"{java_type(p)} {n}" for p, n in zip(params, names))
            body = java_default_stmt(ret)
            lines.append(f"{inner}public static {java_type(ret)} {mname}({args}) {{ {body} }}")
    for child in sorted(node.children.values(), key=lambda n: n.name):
        emit_node(child, stub_kind, inits, indent + 1, lines, stub_fields, stub_methods)
    lines.append(f"{sp}}}")


def emit_java(
    stub_kind: dict[str, str],
    inits: dict[str, list[tuple[str, ...]]],
    src_dir: Path,
    stub_fields: dict[str, list[tuple[str, str]]] | None = None,
    stub_methods: dict[str, list[tuple[str, str, tuple[str, ...]]]] | None = None,
) -> None:
    trees = build_trees(stub_kind)
    for top_desc, tree in trees.items():
        body = top_desc[1:-1]
        slash = body.rfind("/")
        pkg = body[:slash].replace("/", ".") if slash >= 0 else ""
        lines: list[str] = []
        if pkg:
            lines.append(f"package {pkg};")
            lines.append("")
        lines.append("/** Auto-generated FART link stub. Empty type so packed DEX can DefineClass. */")
        emit_node(tree, stub_kind, inits, 0, lines, stub_fields, stub_methods)
        out = src_dir.joinpath(*pkg.split("."), f"{tree.name}.java") if pkg else src_dir / f"{tree.name}.java"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def unstubbed_container_descs(stub_kind: dict[str, str]) -> set[str]:
    """Outer/intermediate Java containers that javac emits but must not be loadable stubs."""
    drop: set[str] = set()

    def walk(node: NestNode) -> None:
        if not node.stubbed:
            drop.add(node.desc)
        for child in node.children.values():
            walk(child)

    for tree in build_trees(stub_kind).values():
        walk(tree)
    return drop


def _class_data_len(data: bytes | bytearray, off: int) -> int:
    start = off
    sf, off = uleb128(data, off)
    iff, off = uleb128(data, off)
    dm, off = uleb128(data, off)
    vm, off = uleb128(data, off)
    for _ in range(sf + iff):
        _, off = uleb128(data, off)
        _, off = uleb128(data, off)
    for _ in range(dm + vm):
        _, off = uleb128(data, off)
        _, off = uleb128(data, off)
        _, off = uleb128(data, off)
    return off - start


def _drop_class_defs(data: bytearray, drop_descs: set[str]) -> int:
    if not drop_descs or data[:4] != b"dex\n":
        return 0
    ss_sz, ss_off = struct.unpack_from("<II", data, 0x38)
    strings = []
    for i in range(ss_sz):
        off = struct.unpack_from("<I", data, ss_off + i * 4)[0]
        n, payload = uleb128(data, off)
        del n
        end = data.index(0, payload)
        strings.append(bytes(data[payload:end]).decode("utf-8", "replace"))
    t_sz, t_off = struct.unpack_from("<II", data, 0x40)
    types = [strings[struct.unpack_from("<I", data, t_off + i * 4)[0]] for i in range(t_sz)]
    drop_idx = {i for i, t in enumerate(types) if t in drop_descs}
    if not drop_idx:
        return 0
    c_sz, c_off = struct.unpack_from("<II", data, 0x60)
    kept_recs: list[bytearray] = []
    kept_blobs: list[bytes] = []
    data_lo: int | None = None
    data_hi: int | None = None
    for i in range(c_sz):
        rec = bytearray(data[c_off + i * 32 : c_off + (i + 1) * 32])
        class_idx = struct.unpack_from("<I", rec, 0)[0]
        cdata = struct.unpack_from("<I", rec, 24)[0]
        blob = b""
        if cdata:
            n = _class_data_len(data, cdata)
            blob = bytes(data[cdata : cdata + n])
            data_lo = cdata if data_lo is None else min(data_lo, cdata)
            data_hi = cdata + n if data_hi is None else max(data_hi, cdata + n)
        if class_idx in drop_idx:
            continue
        kept_recs.append(rec)
        kept_blobs.append(blob)
    dropped = c_sz - len(kept_recs)
    if dropped == 0:
        return 0
    map_off = struct.unpack_from("<I", data, 0x34)[0]
    nmap = struct.unpack_from("<I", data, map_off)[0]
    cd_start = data_lo
    for i in range(nmap):
        t, _u, _sz, off = struct.unpack_from("<HHII", data, map_off + 4 + i * 12)
        if t == 0x2000:
            cd_start = off
            break
    if cd_start is None:
        cd_start = 0
    cur = cd_start
    nonempty = 0
    for rec, blob in zip(kept_recs, kept_blobs):
        if blob:
            data[cur : cur + len(blob)] = blob
            struct.pack_into("<I", rec, 24, cur)
            cur += len(blob)
            nonempty += 1
        else:
            struct.pack_into("<I", rec, 24, 0)
    if data_hi is not None and cur < data_hi:
        data[cur:data_hi] = b"\x00" * (data_hi - cur)
    for i, rec in enumerate(kept_recs):
        data[c_off + i * 32 : c_off + (i + 1) * 32] = rec
    tail = c_off + len(kept_recs) * 32
    old_end = c_off + c_sz * 32
    if old_end > tail:
        data[tail:old_end] = b"\x00" * (old_end - tail)
    struct.pack_into("<I", data, 0x60, len(kept_recs))
    for i in range(nmap):
        base = map_off + 4 + i * 12
        t, u, sz, off = struct.unpack_from("<HHII", data, base)
        if t == 0x0006:
            struct.pack_into("<HHII", data, base, t, u, len(kept_recs), off)
        elif t == 0x2000:
            struct.pack_into("<HHII", data, base, t, u, nonempty, cd_start)
    import hashlib
    import zlib

    struct.pack_into("<I", data, 32, len(data))
    data[12:32] = hashlib.sha1(data[32:]).digest()
    struct.pack_into("<I", data, 8, zlib.adler32(data[12:]) & 0xFFFFFFFF)
    return dropped


def strip_unstubbed_outers(dex_path: Path, stub_kind: dict[str, str]) -> int:
    drop = unstubbed_container_descs(stub_kind)
    if not drop:
        return 0
    data = bytearray(dex_path.read_bytes())
    n = _drop_class_defs(data, drop)
    if n:
        dex_path.write_bytes(data)
    return n


def find_sdk() -> tuple[Path, Path]:
    home = os.environ.get("ANDROID_HOME") or os.environ.get("ANDROID_SDK_ROOT")
    candidates = []
    if home:
        candidates.append(Path(home))
    candidates.append(Path(r"D:/platform/Android/Sdk"))
    for root in candidates:
        platforms = sorted(root.joinpath("platforms").glob("android-*/android.jar"), reverse=True)
        d8s = list(root.joinpath("build-tools").glob("*/d8.bat")) + list(
            root.joinpath("build-tools").glob("*/d8")
        )
        if platforms and d8s:
            return platforms[0], d8s[-1]
    raise SystemExit("ANDROID_HOME / build-tools d8 / platforms android.jar not found")


def compile_dex(src_dir: Path, out_dex: Path) -> None:
    android_jar, d8 = find_sdk()
    classes = out_dex.parent / "_stub_classes"
    if classes.exists():
        shutil.rmtree(classes)
    classes.mkdir(parents=True)
    java_files = list(src_dir.rglob("*.java"))
    if not java_files:
        raise SystemExit("no stub java generated")
    javac = shutil.which("javac")
    if not javac:
        raise SystemExit("javac not on PATH")
    cmd = [
        javac,
        "-encoding",
        "UTF-8",
        "-source",
        "8",
        "-target",
        "8",
        "-bootclasspath",
        str(android_jar),
        "-d",
        str(classes),
    ] + [str(p) for p in java_files]
    subprocess.check_call(cmd)
    class_files = list(classes.rglob("*.class"))
    if not class_files:
        raise SystemExit("javac produced no class files")
    jar = shutil.which("jar")
    if not jar:
        raise SystemExit("jar not on PATH")
    stub_jar = out_dex.parent / "_stub_classes.jar"
    subprocess.check_call([jar, "cf", str(stub_jar), "-C", str(classes), "."])
    d8_out = out_dex.parent / "_stub_d8"
    if d8_out.exists():
        shutil.rmtree(d8_out)
    d8_out.mkdir(parents=True)
    d8_cmd = [
        str(d8),
        "--release",
        "--min-api",
        "24",
        "--output",
        str(d8_out),
        "--lib",
        str(android_jar),
        str(stub_jar),
    ]
    subprocess.check_call(d8_cmd)
    produced = d8_out / "classes.dex"
    if not produced.is_file():
        raise SystemExit(f"d8 did not write {produced}")
    out_dex.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(produced, out_dex)


def adb_push(local: Path, remote: str, serial: str | None) -> None:
    cmd = ["adb"]
    if serial:
        cmd += ["-s", serial]
    cmd += ["push", str(local), remote]
    subprocess.check_call(cmd)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dex-dir", type=Path, default=None, help="cyrus dump directory")
    ap.add_argument("--apk", type=Path, default=None, help="optional APK whose classes*.dex to scan")
    ap.add_argument("--fail", type=Path, default=None, help="inspect_fail.txt (auto if present in --dex-dir)")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--src-out", type=Path, default=None)
    ap.add_argument("--execute-out", type=Path, default=None)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--push", action="store_true", help="adb push to /data/local/tmp/")
    ap.add_argument("--serial", default=None)
    args = ap.parse_args()

    dex_paths: list[Path] = []
    tmp_apk = None
    if args.dex_dir:
        dex_paths.extend(list_dump_dex(args.dex_dir))
    if args.apk:
        tmp_apk = args.out.parent / "_apk_dex"
        if tmp_apk.exists():
            shutil.rmtree(tmp_apk)
        dex_paths.extend(extract_apk_dex(args.apk, tmp_apk))
    if not dex_paths:
        raise SystemExit("no dex: pass --dex-dir and/or --apk")

    stub_kind, children, inits, defined = scan(dex_paths)
    stub_methods: dict[str, list[tuple[str, str, tuple[str, ...]]]] = {}
    fail_path = args.fail
    if fail_path is None and args.dex_dir:
        cand = args.dex_dir / "inspect_fail.txt"
        if cand.is_file():
            fail_path = cand
    if fail_path and fail_path.is_file():
        merge_fail(fail_path, stub_kind, children, defined, stub_methods)
    stub_fields, dex_methods = collect_stub_members(dex_paths, stub_kind)
    for owner, items in dex_methods.items():
        bucket = stub_methods.setdefault(owner, [])
        for item in items:
            if item not in bucket:
                bucket.append(item)
    closed = close_signature_stubs(stub_kind, stub_fields, stub_methods, defined)
    if closed:
        extra_fields, extra_methods = collect_stub_members(dex_paths, stub_kind)
        for owner, items in extra_fields.items():
            bucket = stub_fields.setdefault(owner, [])
            for item in items:
                if item not in bucket:
                    bucket.append(item)
        for owner, items in extra_methods.items():
            bucket = stub_methods.setdefault(owner, [])
            for item in items:
                if item not in bucket:
                    bucket.append(item)
        close_signature_stubs(stub_kind, stub_fields, stub_methods, defined)

    packed: set[str] = set()
    if args.dex_dir:
        packed = packed_from_dex_dir(args.dex_dir, dex_paths)
    execute = set(children) | packed
    exe = args.execute_out or args.out.with_suffix(".execute.txt")
    if exe.is_file():
        execute |= {ln.strip() for ln in exe.read_text(encoding="utf-8").splitlines() if ln.strip()}
    execute_list = sorted(execute)

    print(
        "stubs",
        len(stub_kind),
        "execute_classes",
        len(execute),
        "from_missing_super",
        len(children),
        "from_packed",
        len(packed),
        "stub_fields",
        sum(len(v) for v in stub_fields.values()),
        "stub_methods",
        sum(len(v) for v in stub_methods.values()),
    )
    for desc, kind in sorted(stub_kind.items()):
        print(f"  {kind:9} {desc}")
    if not stub_kind:
        print("no missing super/iface/signature class_def; nothing to compile")
        exe = args.execute_out or args.out.with_suffix(".execute.txt")
        exe.write_text("\n".join(execute_list) + ("\n" if execute_list else ""), encoding="utf-8")
        return 0
    if args.dry_run:
        return 0

    src = args.src_out or (args.out.parent / "_stub_src")
    if src.exists():
        shutil.rmtree(src)
    src.mkdir(parents=True)
    emit_java(stub_kind, inits, src, stub_fields, stub_methods)
    compile_dex(src, args.out)
    stripped = strip_unstubbed_outers(args.out, stub_kind)
    if stripped:
        print("stripped_unstubbed_outers", stripped)
    exe.write_text("\n".join(execute_list) + ("\n" if execute_list else ""), encoding="utf-8")
    print("wrote", args.out, "execute", exe)
    if args.push:
        adb_push(args.out, "/data/local/tmp/fart_link_stubs.dex", args.serial)
        adb_push(exe, "/data/local/tmp/fart_link_stubs.execute.txt", args.serial)
    return 0


if __name__ == "__main__":
    sys.exit(main())

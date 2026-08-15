#!/usr/bin/env python3
"""Generic missing-type stubs for FART dump (no PRE APK).

Problem class: dump DEX has class_def rows whose superclass / interfaces are
only type_ids (no class_def, not a boot type). ART DefineClass fails, so the
packer never decrypts those CodeItems. Ads / UMP / OAID / ArcherBridge are
instances of this class, not special cases.

This tool only reads packed-app dump DEX (and optional inspect_fail). It emits
empty class/interface stubs plus an execute list of children that needed them.

    python tools/link_stubs.py --dex-dir DIR --out fart_link_stubs.dex
    python tools/link_stubs.py --dex-dir DIR --out fart_link_stubs.dex --push
"""

from __future__ import annotations

import argparse
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
    "Ljavax/",
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

# androidx / material are app types even though they look like platform.
NOT_BOOT_PREFIXES = (
    "Landroidx/",
    "Lcom/google/android/material/",
)

FAILED_RES = re.compile(r"Failed resolution of:\s*(L[^;\s]+;)")
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
    return desc.startswith(BOOT_PREFIXES)


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


def list_dump_dex(dex_dir: Path) -> list[Path]:
    files = sorted(
        p
        for p in dex_dir.glob("*_dex_file.dex")
        if "fix" not in p.name.lower() and "stub" not in p.name.lower()
    )
    if files:
        return files
    return [
        p
        for p in sorted(dex_dir.glob("*.dex"))
        if "fix" not in p.name.lower() and "stub" not in p.name.lower()
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
        )
    )


def scan(
    dex_paths: list[Path],
) -> tuple[dict[str, str], list[str], dict[str, list[tuple[str, ...]]], set[str]]:
    defined: set[str] = set()
    rows: list[tuple[str, str | None, list[str]]] = []
    inits: dict[str, list[tuple[str, ...]]] = {}
    for p in dex_paths:
        dex = DexLite(p.read_bytes())
        defined |= dex.defined()
        rows.extend(dex.rows())
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
    return stub_kind, sorted(child_set), inits, defined


def merge_fail(
    fail_path: Path,
    stub_kind: dict[str, str],
    children: list[str],
    defined: set[str],
) -> None:
    child_set = set(children)
    text = fail_path.read_text(encoding="utf-8", errors="replace")
    for line in text.splitlines():
        if "UnsatisfiedLinkError" in line or "NoSuchFieldError" in line:
            continue
        if "ExceptionInInitializerError" in line:
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


def super_call(java_super: str, params: tuple[str, ...], names: list[str]) -> str:
    if java_super == "java.lang.Object" or java_super == "android.graphics.drawable.Drawable":
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
    for child in sorted(node.children.values(), key=lambda n: n.name):
        emit_node(child, stub_kind, inits, indent + 1, lines)
    lines.append(f"{sp}}}")


def emit_java(
    stub_kind: dict[str, str],
    inits: dict[str, list[tuple[str, ...]]],
    src_dir: Path,
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
        emit_node(tree, stub_kind, inits, 0, lines)
        out = src_dir.joinpath(*pkg.split("."), f"{tree.name}.java") if pkg else src_dir / f"{tree.name}.java"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text("\n".join(lines) + "\n", encoding="utf-8")


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
    d8_cmd = [str(d8), "--release", "--min-api", "24", "--output", str(out_dex.parent), "--lib", str(android_jar)]
    d8_cmd += [str(p) for p in class_files]
    subprocess.check_call(d8_cmd)
    produced = out_dex.parent / "classes.dex"
    if produced.resolve() != out_dex.resolve():
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
    fail_path = args.fail
    if fail_path is None and args.dex_dir:
        cand = args.dex_dir / "inspect_fail.txt"
        if cand.is_file():
            fail_path = cand
    if fail_path and fail_path.is_file():
        merge_fail(fail_path, stub_kind, children, defined)

    print("stubs", len(stub_kind), "execute_classes", len(children))
    for desc, kind in sorted(stub_kind.items()):
        print(f"  {kind:9} {desc}")
    if not stub_kind:
        print("no missing super/iface class_def; nothing to compile")
        exe = args.execute_out or args.out.with_suffix(".execute.txt")
        exe.write_text("", encoding="utf-8")
        return 0
    if args.dry_run:
        return 0

    src = args.src_out or (args.out.parent / "_stub_src")
    if src.exists():
        shutil.rmtree(src)
    src.mkdir(parents=True)
    emit_java(stub_kind, inits, src)
    compile_dex(src, args.out)
    exe = args.execute_out or args.out.with_suffix(".execute.txt")
    exe.write_text("\n".join(children) + ("\n" if children else ""), encoding="utf-8")
    print("wrote", args.out, "execute", exe)
    if args.push:
        adb_push(args.out, "/data/local/tmp/fart_link_stubs.dex", args.serial)
        adb_push(exe, "/data/local/tmp/fart_link_stubs.execute.txt", args.serial)
    return 0


if __name__ == "__main__":
    sys.exit(main())

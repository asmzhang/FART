/*
 * Copyright (C) 2011 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "art_method.h"

#include <algorithm>
#include <cstddef>

#include "android-base/stringprintf.h"

#include "arch/context.h"
#include "art_method-inl.h"
#include "base/enums.h"
#include "base/stl_util.h"
#include "class_linker-inl.h"
#include "class_root-inl.h"
#include "debugger.h"
#include "dex/class_accessor-inl.h"
#include "dex/descriptors_names.h"
#include "dex/dex_file-inl.h"
#include "dex/dex_file_exception_helpers.h"
#include "dex/dex_instruction.h"
#include "dex/signature-inl.h"
#include "entrypoints/runtime_asm_entrypoints.h"
#include "gc/accounting/card_table-inl.h"
#include "hidden_api.h"
#include "interpreter/interpreter.h"
#include "jit/jit.h"
#include "jit/jit_code_cache.h"
#include "jit/profiling_info.h"
#include "jni/jni_internal.h"
#include "mirror/class-inl.h"
#include "mirror/class_ext-inl.h"
#include "mirror/executable.h"
#include "mirror/object-inl.h"
#include "mirror/object_array-inl.h"
#include "mirror/string.h"
#include "oat_file-inl.h"
#include "quicken_info.h"
#include "runtime_callbacks.h"
#include "scoped_thread_state_change-inl.h"
#include "vdex_file.h"

//add
#include <algorithm>
#include <atomic>
#include <map>
#include <mutex>
#include <set>
#include <sstream>
#include <utility>
#include <vector>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "runtime.h"
#include <android/log.h>
#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

#define gettidv1() syscall(__NR_gettid)
#define LOG_TAG "ActivityThread"
#define ALOGI(...) __android_log_print(ANDROID_LOG_INFO, LOG_TAG, __VA_ARGS__)
// add end

namespace art {

    //add
    uint8_t* getDexCodeItemEnd(const uint8_t **pData){
        uint32_t num_of_list = DecodeUnsignedLeb128(pData);
        for (;num_of_list>0;num_of_list--) {
            int32_t num_of_handlers=DecodeSignedLeb128(pData);
            int num=num_of_handlers;
            if (num_of_handlers<=0) {
                num=-num_of_handlers;
            }
            for (; num > 0; num--) {
                DecodeUnsignedLeb128(pData);
                DecodeUnsignedLeb128(pData);
            }
            if (num_of_handlers<=0) {
                DecodeUnsignedLeb128(pData);
            }
        }
        return (uint8_t*)(*pData);
    }

    extern "C" char *encodeBase64Buffer(char *str,long str_len,long* outlen){
        long len;
        char *res;
        int i,j;
        const char *base64_table="ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

        if(str_len % 3 == 0)
            len=str_len/3*4;
        else
            len=(str_len/3+1)*4;

        res=(char*)malloc(sizeof(char)*(len+1));
        res[len]='\0';
        *outlen=len;

        for(i=0,j=0;i<len-2;j+=3,i+=4){
            res[i]=base64_table[str[j]>>2];
            res[i+1]=base64_table[(str[j]&0x3)<<4 | (str[j+1]>>4)];
            res[i+2]=base64_table[(str[j+1]&0xf)<<2 | (str[j+2]>>6)];
            res[i+3]=base64_table[str[j+2]&0x3f];
        }

        switch(str_len % 3){
            case 1:
                res[i-2]='=';
                res[i-1]='=';
                break;
            case 2:
                res[i-1]='=';
                break;
        }
        return res;
    }

    //创建目录
    bool ensure_dir_exists(const std::string& path) {
        int res = mkdir(path.c_str(), 0777);
        if (res == 0 || errno == EEXIST) {
            return true;
        } else {
            LOG(ERROR) << "mkdir failed: " << path << ", errno=" << errno << ", " << errno;
            return false;
        }
    }

    //跳过 Android 编译构建阶段的 dex2oatd 工具执行时的调用
    bool isValidAndroidApp(const char* procName) {
        return procName != nullptr &&
               strstr(procName, "/") == nullptr &&
               strstr(procName, "dex2oat") == nullptr &&
               strstr(procName, "soong") == nullptr;
    }

    static std::string packageFromProcName(const char* procName) {
        std::string pkg = procName != nullptr ? procName : "";
        size_t colon = pkg.find(':');
        if (colon != std::string::npos) {
            pkg.resize(colon);
        }
        return pkg;
    }

    static bool isInMemoryDexLocation(const std::string& loc) {
        if (loc.empty()) {
            return true;
        }
        if (loc.find("Anonymous") != std::string::npos ||
            loc.find("anonymous") != std::string::npos ||
            loc.find("memfd") != std::string::npos ||
            loc.find("InMemory") != std::string::npos ||
            loc.find("in-memory") != std::string::npos) {
            return true;
        }
        return false;
    }

    static bool isSystemDexLocation(const std::string& loc) {
        if (isInMemoryDexLocation(loc)) {
            return false;
        }
        auto starts = [&](const char* prefix) {
            return loc.rfind(prefix, 0) == 0;
        };
        if (starts("/system/") || starts("/system_ext/") || starts("/apex/") ||
            starts("/vendor/") || starts("/product/") || starts("/framework/") ||
            starts("/data/dalvik-cache/") || starts("/data/misc/")) {
            return true;
        }
        if (loc.find("/apex/") != std::string::npos) {
            return true;
        }
        if (loc.find("/system/framework/") != std::string::npos) {
            return true;
        }
        if (loc.find("boot.oat") != std::string::npos ||
            loc.find("boot.vdex") != std::string::npos ||
            loc.find("boot-framework") != std::string::npos) {
            return true;
        }
        return false;
    }

    static bool pathContainsPackage(const std::string& loc, const std::string& pkg) {
        if (pkg.empty() || loc.empty()) {
            return false;
        }
        if (loc.find("/" + pkg + "-") != std::string::npos) {
            return true;
        }
        if (loc.find("/" + pkg + "/") != std::string::npos) {
            return true;
        }
        if (loc.find("/" + pkg + "!") != std::string::npos) {
            return true;
        }
        if (loc.size() >= pkg.size() &&
            loc.compare(loc.size() - pkg.size(), pkg.size(), pkg) == 0) {
            if (loc.size() == pkg.size() || loc[loc.size() - pkg.size() - 1] == '/') {
                return true;
            }
        }
        return false;
    }

    static bool locationBelongsToApp(const std::string& loc, const std::string& pkg) {
        (void)pkg;
        // 本进程内：只丢掉系统 DEX。壳/原包/加密体/内存/自定义/动态全部保留，分类给人看。
        if (isSystemDexLocation(loc)) {
            return false;
        }
        return true;
    }

    static bool isCompactDexMagic(const DexFile* dex) {
        if (dex == nullptr || dex->Begin() == nullptr || dex->Size() < 4) {
            return false;
        }
        return memcmp(dex->Begin(), "cdex", 4) == 0;
    }

    static void jsonEscapeAppend(std::string* out, const std::string& s) {
        for (unsigned char c : s) {
            switch (c) {
                case '"': *out += "\\\""; break;
                case '\\': *out += "\\\\"; break;
                case '\n': *out += "\\n"; break;
                case '\r': *out += "\\r"; break;
                case '\t': *out += "\\t"; break;
                default:
                    if (c < 0x20) {
                        char buf[8];
                        snprintf(buf, sizeof(buf), "\\u%04x", c);
                        *out += buf;
                    } else {
                        *out += static_cast<char>(c);
                    }
            }
        }
    }

    struct OwnedDexInfo {
        int index = -1;
        size_t size = 0;
        uint32_t checksum = 0;
        std::string location;
        std::string source;
        std::string begin_hex;
        std::string kind;
        bool compact = false;
        bool java_assigned = false;
    };

    static std::mutex g_fart_mutex;
    static std::map<const uint8_t*, OwnedDexInfo> g_owned_dex_map;
    static std::atomic<bool> g_owned_java_ready{false};
    static std::map<const uint8_t*, int> g_dex_counter_map;
    static std::set<const uint8_t*> g_dumped_dex_set;

    static std::string inferKind(const std::string& source, const std::string& loc) {
        if (isInMemoryDexLocation(loc)) {
            return "inmemory";
        }
        if (source.find("custom") != std::string::npos) {
            return "custom";
        }
        if (source.find("primary") != std::string::npos) {
            return "primary";
        }
        if (source.find("extra") != std::string::npos) {
            return "extra";
        }
        if (loc.find("split_") != std::string::npos) {
            return "extra";
        }
        if (loc.find(".apk") != std::string::npos || loc.find("!classes") != std::string::npos) {
            return "primary";
        }
        if (source.find("auto") != std::string::npos || source == "pre-register") {
            return "auto";
        }
        return "extra";
    }

    static std::string sanitizeKind(const std::string& kind) {
        if (kind == "primary" || kind == "extra" || kind == "custom" ||
            kind == "inmemory" || kind == "auto") {
            return kind;
        }
        return "extra";
    }

    static bool writeAllBytes(const std::string& path, const void* data, size_t n) {
        int fp = open(path.c_str(), O_CREAT | O_WRONLY | O_TRUNC, 0666);
        if (fp < 0) {
            return false;
        }
        ssize_t w = write(fp, data, n);
        fsync(fp);
        close(fp);
        return w >= 0;
    }

    static bool looksLikeDexMagic(const uint8_t* begin, size_t size) {
        if (begin == nullptr || size < 8) {
            return false;
        }
        return memcmp(begin, "dex\n", 4) == 0 || memcmp(begin, "cdex", 4) == 0;
    }

    static bool fileNonEmpty(const std::string& path) {
        struct stat st;
        return stat(path.c_str(), &st) == 0 && S_ISREG(st.st_mode) && st.st_size > 0;
    }

    static std::mutex g_cyrus_dir_mu;
    static std::string g_cached_cyrus_dir;
    static pid_t g_cached_cyrus_pid = -1;
    static std::string g_cached_cyrus_pkg;

    static bool getCyrusDir(std::string* out_dir, std::string* out_pkg = nullptr) {
        pid_t pid = getpid();
        {
            std::lock_guard<std::mutex> lock(g_cyrus_dir_mu);
            if (pid == g_cached_cyrus_pid && !g_cached_cyrus_dir.empty()) {
                if (out_dir != nullptr) {
                    *out_dir = g_cached_cyrus_dir;
                }
                if (out_pkg != nullptr) {
                    *out_pkg = g_cached_cyrus_pkg;
                }
                return true;
            }
        }
        char szProcName[256] = {0};
        char szCmdline[64] = {0};
        snprintf(szCmdline, sizeof(szCmdline), "/proc/%d/cmdline", pid);
        int fcmdline = open(szCmdline, O_RDONLY);
        if (fcmdline >= 0) {
            ssize_t n = read(fcmdline, szProcName, sizeof(szProcName) - 1);
            (void)n;
            close(fcmdline);
        }
        if (szProcName[0] == '\0' || !isValidAndroidApp(szProcName)) {
            return false;
        }
        std::string pkg = packageFromProcName(szProcName);
        std::string app_dir = std::string("/data/data/") + pkg;
        std::string cyrus_dir = app_dir + "/cyrus_" + pkg;
        ensure_dir_exists(app_dir);
        ensure_dir_exists(cyrus_dir);
        {
            std::lock_guard<std::mutex> lock(g_cyrus_dir_mu);
            g_cached_cyrus_dir = cyrus_dir;
            g_cached_cyrus_pkg = pkg;
            g_cached_cyrus_pid = pid;
        }
        if (out_dir != nullptr) {
            *out_dir = cyrus_dir;
        }
        if (out_pkg != nullptr) {
            *out_pkg = pkg;
        }
        return true;
    }

    // JNI / flush 路径写 DEX（禁止在 Execute/mutator 热路径调用）。
    static void dumpDexToCyrus(const uint8_t* begin, size_t size, int index,
                               const std::string& kind, const DexFile* dex_for_list) {
        if (!looksLikeDexMagic(begin, size) || index < 0) {
            return;
        }
        std::string cyrus_dir;
        if (!getCyrusDir(&cyrus_dir)) {
            return;
        }
        std::string k = sanitizeKind(kind);
        std::string kind_dir = cyrus_dir + "/" + k;
        ensure_dir_exists(kind_dir);
        int size_int = static_cast<int>(size);
        char kind_name[128];
        snprintf(kind_name, sizeof(kind_name), "%03d_%d_dex_file.dex", index, size_int);
        std::string legacy = cyrus_dir + "/" + std::to_string(size_int) + "_" +
                             std::to_string(index) + "_dex_file.dex";
        std::string kind_path = kind_dir + "/" + kind_name;
        if (fileNonEmpty(legacy) && fileNonEmpty(kind_path)) {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            g_dumped_dex_set.insert(begin);
            g_dex_counter_map[begin] = index;
            return;
        }
        writeAllBytes(legacy, begin, size);
        writeAllBytes(kind_path, begin, size);
        if (dex_for_list != nullptr) {
            std::string class_list;
            for (size_t i = 0; i < dex_for_list->NumClassDefs(); ++i) {
                const dex::ClassDef& class_def = dex_for_list->GetClassDef(i);
                const char* descriptor = dex_for_list->GetClassDescriptor(class_def);
                if (descriptor != nullptr) {
                    class_list.append(descriptor);
                    class_list.push_back('\n');
                }
            }
            writeAllBytes(cyrus_dir + "/" + std::to_string(size_int) + "_" +
                              std::to_string(index) + "_class_list.txt",
                          class_list.data(), class_list.size());
            writeAllBytes(kind_dir + "/" + std::to_string(index) + "_" +
                              std::to_string(size_int) + "_class_list.txt",
                          class_list.data(), class_list.size());
        }
        {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            g_dumped_dex_set.insert(begin);
            g_dex_counter_map[begin] = index;
        }
    }

    static std::string pointerToHex(const void* p) {
        char buf[32];
        snprintf(buf, sizeof(buf), "0x%llx", static_cast<unsigned long long>(reinterpret_cast<uintptr_t>(p)));
        return std::string(buf);
    }

    static int maxOwnedIndexLocked() {
        int m = -1;
        for (const auto& kv : g_owned_dex_map) {
            if (kv.second.index > m) {
                m = kv.second.index;
            }
        }
        return m;
    }

    static void relocateConflictingIndexLocked(const uint8_t* keep_begin, int index) {
        int spill = maxOwnedIndexLocked() + 1;
        if (spill <= index) {
            spill = index + 1;
        }
        for (auto& kv : g_owned_dex_map) {
            if (kv.first == keep_begin) {
                continue;
            }
            if (kv.second.index != index) {
                continue;
            }
            if (kv.second.java_assigned) {
                continue;
            }
            kv.second.index = spill++;
            kv.second.source = kv.second.source.empty()
                ? "relocated" : (kv.second.source + "|relocated");
            g_dex_counter_map[kv.first] = kv.second.index;
        }
    }

    static bool prepareOwnedDex(const DexFile* dex_file, const std::string& pkg, int* out_slot)
        REQUIRES_SHARED(Locks::mutator_lock_) {
        if (dex_file == nullptr || out_slot == nullptr) {
            return false;
        }
        const uint8_t* begin = dex_file->Begin();
        const std::string& loc = dex_file->GetLocation();
        if (isSystemDexLocation(loc)) {
            return false;
        }

        std::lock_guard<std::mutex> lock(g_fart_mutex);
        auto it = g_owned_dex_map.find(begin);
        if (it != g_owned_dex_map.end()) {
            *out_slot = it->second.index;
            g_dex_counter_map[begin] = it->second.index;
            return true;
        }

        if (!locationBelongsToApp(loc, pkg)) {
            return false;
        }

        int idx = maxOwnedIndexLocked() + 1;
        OwnedDexInfo info;
        info.index = idx;
        info.size = dex_file->Size();
        info.checksum = dex_file->GetLocationChecksum();
        info.location = loc;
        info.source = g_owned_java_ready.load() ? "auto-discovered" : "pre-register";
        info.kind = inferKind(info.source, loc);
        info.begin_hex = pointerToHex(begin);
        info.compact = isCompactDexMagic(dex_file);
        info.java_assigned = false;
        g_owned_dex_map[begin] = info;
        g_dex_counter_map[begin] = idx;
        *out_slot = idx;
        return true;
    }

    // FART: 线程局部标志位，替代 self==nullptr 作为主动触发信号，避免误触发
    thread_local bool g_fart_trace_active = false;
    // FART: CodeItem 方法级去重（dex_begin + method_idx），避免 Execute/<clinit> 重复写 ins.bin
    static std::set<std::pair<const uint8_t*, uint32_t>> g_dumped_method_set;
    // FART: dump=true 才开 Invoke/Execute 热路径写盘，避免无配置应用落 ins
    static std::atomic<bool> g_fart_dump_enabled{false};
    static std::atomic<uint64_t> g_fart_codeitem_written{0};
    static std::atomic<uint64_t> g_fart_clinit_written{0};
    static std::atomic<uint64_t> g_fart_clinit_placeholder{0};
    // FART fix: 是否启用内存修复DEX功能（将CodeItem回写生成修复后的DEX）
    static std::atomic<bool> g_fart_fix_enabled{false};
    // FART fix: DEX起始地址 → 可写缓冲区（受 g_fart_mutex 保护）
    static std::map<const uint8_t*, std::vector<uint8_t>> g_dex_fix_buffers;

    extern "C" bool fartDumpEnabled() {
        return g_fart_dump_enabled.load(std::memory_order_relaxed);
    }

    extern "C" void setFartDumpEnabled(bool enabled) {
        g_fart_dump_enabled.store(enabled, std::memory_order_relaxed);
        LOG(INFO) << "[setFartDumpEnabled] dump " << (enabled ? "enabled" : "disabled");
    }

    static bool looksClinitPlaceholder(const uint8_t* item, uint32_t insns_units, int code_item_len) {
        if (insns_units <= 1u || (code_item_len > 0 && code_item_len <= 18)) {
            return true;
        }
        const uint16_t* insns = reinterpret_cast<const uint16_t*>(item + 16);
        if ((insns[0] & 0xffu) == 0x0eu) {
            return true;
        }
        if (insns_units >= 2u && insns[0] == 0x0012u &&
            (insns[1] == 0x0011u || insns[1] == 0x000fu)) {
            return true;
        }
        const uint32_t cap = insns_units < 16u ? insns_units : 16u;
        uint32_t zeros = 0;
        for (uint32_t i = 0; i < cap; ++i) {
            if (insns[i] == 0) {
                ++zeros;
            }
        }
        return cap >= 4u && zeros * 4u >= cap * 3u;
    }

    extern "C" void traceDexExecution(ArtMethod* artmethod) REQUIRES_SHARED(Locks::mutator_lock_) {
            char szCmdline[64] = {0};
            char szProcName[256] = {0};
            int procid = getpid();
            snprintf(szCmdline, sizeof(szCmdline), "/proc/%d/cmdline", procid);

            int fcmdline = open(szCmdline, O_RDONLY);
            if (fcmdline >= 0) {
                ssize_t result = read(fcmdline, szProcName, sizeof(szProcName) - 1);
                if (result < 0) {
                    LOG(ERROR) << "traceDexExecution: Failed to read cmdline";
                }
                close(fcmdline);
            } else {
                LOG(ERROR) << "[traceDexExecution] " << szCmdline << " open failed ";
            }

            if (szProcName[0] == '\0') {
                LOG(WARNING) << "[traceDexExecution] 获取进程名失败：" << artmethod->PrettyMethod();
                return;
            }

            if (!isValidAndroidApp(szProcName)) {
                LOG(WARNING) << "[traceDexExecution] 当前进程 " << szProcName << " 非法，跳过 dex dump";
                return;
            }

            const DexFile* dex_file = artmethod->GetDexFile();
            int slot = 0;
            if (!prepareOwnedDex(dex_file, packageFromProcName(szProcName), &slot)) {
                return;
            }
            const uint8_t* begin_ = dex_file->Begin();
            size_t size_ = dex_file->Size();
            int size_int = static_cast<int>(size_);

            std::string pkg = packageFromProcName(szProcName);
            std::string base_dir = "/data/data/";
            std::string app_dir = base_dir + pkg;
            std::string cyrus_dir = app_dir + "/cyrus_" + pkg;

            ensure_dir_exists(app_dir);
            ensure_dir_exists(cyrus_dir);

            // 去重：跳过已 dump 过的 DEX（基于内存起始地址）；同时分配计数器并初始化 fix 缓冲区
            int counter = slot;
            {
                std::lock_guard<std::mutex> lock(g_fart_mutex);
                if (g_dumped_dex_set.count(begin_) > 0) {
                    return;
                }
                g_dumped_dex_set.insert(begin_);
                g_dex_counter_map[begin_] = slot;
                if (g_fart_fix_enabled.load()) {
                    auto& buf = g_dex_fix_buffers[begin_];
                    if (buf.empty()) {
                        buf.assign(begin_, begin_ + size_);
                    }
                }
            }
            // 保存 dex 文件
            std::string dex_path = cyrus_dir + "/" + std::to_string(size_int) + "_" +
                                   std::to_string(counter) + "_dex_file_execute.dex";
            // 保存 class 列表
            std::string classlist_path = cyrus_dir + "/" + std::to_string(size_int) + "_" +
                                         std::to_string(counter) + "_class_list_execute.txt";

            LOG(INFO) << "[traceDexExecution] " << artmethod->PrettyMethod() << " dump dex to " << dex_path;

            int fp = open(dex_path.c_str(), O_CREAT | O_WRONLY | O_TRUNC, 0666);
            if (fp >= 0) {
                ssize_t w1 = write(fp, begin_, size_);
                if (w1 < 0) {
                    LOG(ERROR) << "traceDexExecution: Failed to write dex file, errno=" << errno;
                }
                fsync(fp);
                close(fp);

                int class_list_file = open(classlist_path.c_str(), O_CREAT | O_WRONLY | O_TRUNC, 0666);
                if (class_list_file >= 0) {
                    for (size_t ii = 0; ii < dex_file->NumClassDefs(); ++ii) {
                        const dex::ClassDef& class_def = dex_file->GetClassDef(ii);
                        const char* descriptor = dex_file->GetClassDescriptor(class_def);

                        ssize_t w2 = write(class_list_file, descriptor, strlen(descriptor));
                        if (w2 < 0) {
                            LOG(ERROR) << "traceDexExecution: Failed to write class descriptor";
                        }

                        ssize_t w3 = write(class_list_file, "\n", 1);
                        if (w3 < 0) {
                            LOG(ERROR) << "traceDexExecution: Failed to write newline";
                        }
                    }
                    fsync(class_list_file);
                    close(class_list_file);
                } else {
                    LOG(ERROR) << "[traceDexExecution] open class list failed: " << classlist_path
                               << ", errno=" << errno;
                }
            } else {
                LOG(ERROR) << "[traceDexExecution] open dex failed: " << dex_path
                           << ", errno=" << errno;
            }
    }

    extern "C" void traceMethodCode(ArtMethod* artmethod) REQUIRES_SHARED(Locks::mutator_lock_) {
            if (artmethod == nullptr) {
                return;
            }
            if (!g_fart_dump_enabled.load(std::memory_order_relaxed)) {
                return;
            }
            const DexFile* dex_file = artmethod->GetDexFile();
            if (dex_file == nullptr || dex_file->Begin() == nullptr) {
                return;
            }
            std::string cyrus_dir;
            std::string pkg;
            if (!getCyrusDir(&cyrus_dir, &pkg)) {
                return;
            }
            int slot = 0;
            if (!prepareOwnedDex(dex_file, pkg, &slot)) {
                return;
            }
            const uint8_t* begin_ = dex_file->Begin();
            size_t size_ = dex_file->Size();
            int size_int = static_cast<int>(size_);
            std::string kind = "auto";
            {
                std::lock_guard<std::mutex> lock(g_fart_mutex);
                auto kit = g_owned_dex_map.find(begin_);
                if (kit != g_owned_dex_map.end()) {
                    kind = sanitizeKind(kit->second.kind.empty()
                        ? inferKind(kit->second.source, kit->second.location)
                        : kit->second.kind);
                }
            }
            std::string kind_dir = cyrus_dir + "/" + kind;

            // Execute 热路径只写 CodeItem；整包 DEX 由 JNI 登记 / flush 写出，避免 mutator 下大 I/O。
            const dex::CodeItem* code_item = artmethod->GetCodeItem();
            if (LIKELY(code_item != nullptr)) {
                uint8_t* item = (uint8_t*)code_item;
                int code_item_len = 0;
                CodeItemDataAccessor accessor(*dex_file, code_item);
                if (accessor.TriesSize() > 0) {
                    const uint8_t* handler_data = accessor.GetCatchHandlerData();
                    uint8_t* tail = getDexCodeItemEnd(&handler_data);
                    code_item_len = static_cast<int>(tail - item);
                } else {
                    code_item_len = 16 + accessor.InsnsSizeInCodeUnits() * 2;
                }

                uint32_t method_idx = artmethod->GetDexMethodIndex();
                int offset = static_cast<int>(item - begin_);
                if (code_item_len <= 0 || offset < 0 ||
                    static_cast<size_t>(offset) >= size_ ||
                    static_cast<size_t>(offset) + static_cast<size_t>(code_item_len) > size_) {
                    return;
                }

                const bool is_clinit = artmethod->IsClassInitializer();
                // 仅 <clinit>：占位/打孔体不写、不进集，解密后的真体才能进。
                if (is_clinit) {
                    if (looksClinitPlaceholder(item, accessor.InsnsSizeInCodeUnits(), code_item_len)) {
                        g_fart_clinit_placeholder.fetch_add(1, std::memory_order_relaxed);
                        return;
                    }
                }

                {
                    std::lock_guard<std::mutex> lock(g_fart_mutex);
                    auto key = std::make_pair(begin_, method_idx);
                    if (g_dumped_method_set.count(key) > 0) {
                        return;
                    }
                    g_dumped_method_set.insert(key);
                }

                pid_t tid = gettidv1();
                ensure_dir_exists(cyrus_dir);
                ensure_dir_exists(kind_dir);
                std::string ins_path = cyrus_dir + "/" + std::to_string(size_int) + "_ins_" + std::to_string(tid) + ".bin";
                std::string kind_ins_path = kind_dir + "/" + std::to_string(size_int) + "_ins_" + std::to_string(tid) + ".bin";

                int fp2 = open(ins_path.c_str(), O_CREAT | O_APPEND | O_RDWR, 0666);
                int fp3 = open(kind_ins_path.c_str(), O_CREAT | O_APPEND | O_RDWR, 0666);
                if (fp2 >= 0) {
                    (void)lseek(fp2, 0, SEEK_END);
                    if (fp3 >= 0) {
                        (void)lseek(fp3, 0, SEEK_END);
                    }
                    std::string header = "{name:" + artmethod->PrettyMethod() +
                                         ",method_idx:" + std::to_string(method_idx) +
                                         ",offset:" + std::to_string(offset) +
                                         ",code_item_len:" + std::to_string(code_item_len) +
                                         ",dex_index:" + std::to_string(slot) +
                                         ",kind:" + kind +
                                         ",ins:";

                    ssize_t w3 = write(fp2, header.c_str(), header.length());
                    if (w3 < 0) {
                        LOG(ERROR) << "ArtMethod::traceMethodCode: write header failed";
                    }
                    if (fp3 >= 0) {
                        ssize_t wk = write(fp3, header.c_str(), header.length());
                        (void)wk;
                    }

                    long outlen = 0;
                    char* base64result = encodeBase64Buffer((char*)item, (long)code_item_len, &outlen);
                    if (base64result != nullptr) {
                        ssize_t w4 = write(fp2, base64result, outlen);
                        if (w4 < 0) {
                            LOG(ERROR) << "ArtMethod::traceMethodCode: write base64 ins failed";
                        }
                        if (fp3 >= 0) {
                            ssize_t wk = write(fp3, base64result, outlen);
                            (void)wk;
                        }
                        free(base64result);
                    }

                    ssize_t w5 = write(fp2, "};", 2);
                    if (w5 < 0) {
                        LOG(ERROR) << "ArtMethod::traceMethodCode: write tail failed";
                    }
                    if (fp3 >= 0) {
                        ssize_t wk = write(fp3, "};", 2);
                        (void)wk;
                        close(fp3);
                    }

                    // clinit 热路径：不做 fsync，降低 mutator 下卡顿/ANR 风险
                    close(fp2);
                    g_fart_codeitem_written.fetch_add(1, std::memory_order_relaxed);
                    if (is_clinit) {
                        g_fart_clinit_written.fetch_add(1, std::memory_order_relaxed);
                    }

                    // Fix DEX: 将真实 CodeItem 指令回写到内存缓冲区
                    if (g_fart_fix_enabled.load()) {
                      std::lock_guard<std::mutex> lock(g_fart_mutex);
                      auto it = g_dex_fix_buffers.find(begin_);
                      if (it != g_dex_fix_buffers.end() && !it->second.empty()) {
                          if (offset >= 0 && (size_t)(offset + code_item_len) <= it->second.size()) {
                              memcpy(it->second.data() + offset, item, code_item_len);
                          }
                      }
                    }
                } else {
                    std::lock_guard<std::mutex> lock(g_fart_mutex);
                    g_dumped_method_set.erase(std::make_pair(begin_, method_idx));
                    LOG(ERROR) << "[traceMethodCode] " << ins_path << " open failed, fp2=" << fp2;
                }
            }
    }

    extern "C" void setFartFixEnabled(bool enabled) {
        g_fart_fix_enabled.store(enabled);
        if (enabled) {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            for (const auto& kv : g_owned_dex_map) {
                const uint8_t* begin = kv.first;
                size_t n = kv.second.size;
                if (begin == nullptr || n == 0 || !looksLikeDexMagic(begin, n)) {
                    continue;
                }
                auto& buf = g_dex_fix_buffers[begin];
                if (buf.empty()) {
                    buf.assign(begin, begin + n);
                }
            }
        }
        LOG(INFO) << "[setFartFixEnabled] fix mode " << (enabled ? "enabled" : "disabled");
    }

    extern "C" int fartRegisterOwnedDex(const void* dex_file_ptr, int force_index, const char* source) {
        const DexFile* dex = reinterpret_cast<const DexFile*>(dex_file_ptr);
        if (dex == nullptr || force_index < 0) {
            return force_index;
        }
        const uint8_t* begin = dex->Begin();
        size_t size = dex->Size();
        if (!looksLikeDexMagic(begin, size)) {
            return force_index;
        }
        const std::string& loc = dex->GetLocation();
        if (isSystemDexLocation(loc)) {
            return force_index;
        }
        std::string out_kind;
        int out_index = force_index;
        int ret_next = force_index + 1;
        {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            auto it = g_owned_dex_map.find(begin);
            if (it != g_owned_dex_map.end() && it->second.java_assigned) {
                int next = it->second.index + 1;
                if (next < force_index) {
                    next = force_index;
                }
                out_kind = it->second.kind;
                out_index = it->second.index;
                ret_next = next;
            } else {
                relocateConflictingIndexLocked(begin, force_index);
                it = g_owned_dex_map.find(begin);
                if (it != g_owned_dex_map.end()) {
                    it->second.index = force_index;
                    it->second.java_assigned = true;
                    if (source != nullptr && source[0] != '\0') {
                        it->second.source = source;
                    }
                    it->second.size = dex->Size();
                    it->second.checksum = dex->GetLocationChecksum();
                    it->second.location = loc;
                    it->second.begin_hex = pointerToHex(begin);
                    it->second.compact = isCompactDexMagic(dex);
                    it->second.kind = inferKind(it->second.source, loc);
                    g_dex_counter_map[begin] = force_index;
                    out_kind = it->second.kind;
                } else {
                    OwnedDexInfo info;
                    info.index = force_index;
                    info.size = dex->Size();
                    info.checksum = dex->GetLocationChecksum();
                    info.location = loc;
                    info.source = source != nullptr ? source : "java";
                    info.begin_hex = pointerToHex(begin);
                    info.compact = isCompactDexMagic(dex);
                    info.java_assigned = true;
                    info.kind = inferKind(info.source, loc);
                    g_owned_dex_map[begin] = info;
                    g_dex_counter_map[begin] = force_index;
                    out_kind = info.kind;
                }
                g_owned_java_ready.store(true);
                out_index = force_index;
                ret_next = force_index + 1;
                LOG(INFO) << "[registerOwnedDex] index=" << force_index
                          << " size=" << dex->Size()
                          << " loc=" << loc
                          << " source=" << (source != nullptr ? source : "");
            }
        }
        dumpDexToCyrus(begin, size, out_index, out_kind, dex);
        return ret_next;
    }

    extern "C" void fartFlushOwnedDexManifest() {
        char szProcName[256] = {0};
        int procid = getpid();
        char szCmdline[64] = {0};
        snprintf(szCmdline, sizeof(szCmdline), "/proc/%d/cmdline", procid);
        int fcmdline = open(szCmdline, O_RDONLY);
        if (fcmdline >= 0) {
            ssize_t result = read(fcmdline, szProcName, sizeof(szProcName) - 1);
            if (result < 0) {
                LOG(ERROR) << "[owned-manifest] read cmdline failed";
            }
            close(fcmdline);
        }
        if (szProcName[0] == '\0' || !isValidAndroidApp(szProcName)) {
            LOG(WARNING) << "[owned-manifest] skip, proc=" << szProcName;
            return;
        }

        std::string pkg = packageFromProcName(szProcName);
        std::string cyrus_dir = std::string("/data/data/") + pkg + "/cyrus_" + pkg;
        ensure_dir_exists(std::string("/data/data/") + pkg);
        ensure_dir_exists(cyrus_dir);

        std::vector<OwnedDexInfo> slots;
        {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            slots.reserve(g_owned_dex_map.size());
            for (const auto& kv : g_owned_dex_map) {
                slots.push_back(kv.second);
            }
        }
        std::sort(slots.begin(), slots.end(),
                  [](const OwnedDexInfo& a, const OwnedDexInfo& b) { return a.index < b.index; });

        std::string json = "{\n  \"package\":\"";
        jsonEscapeAppend(&json, pkg);
        json += "\",\n  \"filter\":\"owned-dex\",\n  \"slots\":[\n";
        for (size_t i = 0; i < slots.size(); ++i) {
            const OwnedDexInfo& s = slots[i];
            json += "    {\"index\":";
            json += std::to_string(s.index);
            json += ",\"size\":";
            json += std::to_string(static_cast<unsigned long long>(s.size));
            json += ",\"checksum\":";
            json += std::to_string(s.checksum);
            json += ",\"compact\":";
            json += s.compact ? "true" : "false";
            json += ",\"java_assigned\":";
            json += s.java_assigned ? "true" : "false";
            json += ",\"pkg_match\":";
            json += pathContainsPackage(s.location, pkg) ? "true" : "false";
            json += ",\"inmemory\":";
            json += isInMemoryDexLocation(s.location) ? "true" : "false";
            json += ",\"kind\":\"";
            jsonEscapeAppend(&json, sanitizeKind(s.kind.empty()
                ? inferKind(s.source, s.location) : s.kind));
            json += "\",\"begin\":\"";
            jsonEscapeAppend(&json, s.begin_hex);
            json += "\",\"location\":\"";
            jsonEscapeAppend(&json, s.location);
            json += "\",\"source\":\"";
            jsonEscapeAppend(&json, s.source);
            json += "\"}";
            if (i + 1 < slots.size()) {
                json += ",";
            }
            json += "\n";
        }
        json += "  ]\n}\n";

        std::string path = cyrus_dir + "/dex_manifest.json";
        int fp = open(path.c_str(), O_CREAT | O_WRONLY | O_TRUNC, 0666);
        if (fp >= 0) {
            ssize_t w = write(fp, json.data(), json.size());
            (void)w;
            fsync(fp);
            close(fp);
            LOG(INFO) << "[owned-manifest] wrote " << path << " slots=" << slots.size();
        } else {
            LOG(ERROR) << "[owned-manifest] open failed " << path << " errno=" << errno;
        }
        {
            std::string stats = "{\n  \"codeitem_written\":";
            stats += std::to_string(g_fart_codeitem_written.load());
            stats += ",\n  \"clinit_written\":";
            stats += std::to_string(g_fart_clinit_written.load());
            stats += ",\n  \"clinit_placeholder_skipped\":";
            stats += std::to_string(g_fart_clinit_placeholder.load());
            stats += "\n}\n";
            writeAllBytes(cyrus_dir + "/dump_stats.json", stats.data(), stats.size());
        }

        std::vector<std::pair<const uint8_t*, OwnedDexInfo>> pending;
        {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            pending.reserve(g_owned_dex_map.size());
            for (const auto& kv : g_owned_dex_map) {
                pending.push_back(kv);
            }
        }
        for (const auto& p : pending) {
            dumpDexToCyrus(p.first, p.second.size, p.second.index, p.second.kind, nullptr);
        }
    }

    // 将所有已收集的修复缓冲区写入 *_dex_file_fix.dex 文件
    extern "C" void flushFixedDex() {
        char szProcName[256] = {0};
        int procid = getpid();

        // 获取进程名
        char szCmdline[64] = {0};
        snprintf(szCmdline, sizeof(szCmdline), "/proc/%d/cmdline", procid);
        int fcmdline = open(szCmdline, O_RDONLY);
        if (fcmdline >= 0) {
            ssize_t result = read(fcmdline, szProcName, sizeof(szProcName) - 1);
            if (result < 0) {
                LOG(ERROR) << "[flushFixedDex]: read cmdline failed.";
            }
            close(fcmdline);
        } else {
            LOG(ERROR) << "[flushFixedDex] " << szCmdline << " open failed ";
        }

        if (szProcName[0] == '\0') {
            LOG(WARNING) << "[flushFixedDex] 获取进程名失败";
            return;
        }

        if (!isValidAndroidApp(szProcName)) {
            LOG(WARNING) << "[flushFixedDex] 当前进程 " << szProcName << " 非法，跳过 dex dump";
            return;
        }



        std::string pkg = packageFromProcName(szProcName);
        std::string cyrus_dir = std::string("/data/data/") + pkg + "/cyrus_" + pkg;
        std::string fix_dir = cyrus_dir + "/fix";

        // 在锁内拷贝需要写出的数据，避免持锁期间做文件 I/O
        struct FixEntry { int size_int; int counter; std::string kind; std::vector<uint8_t> buf; };
        std::vector<FixEntry> entries;
        {
            std::lock_guard<std::mutex> lock(g_fart_mutex);
            for (auto& kv : g_dex_fix_buffers) {
                auto it = g_dex_counter_map.find(kv.first);
                if (it == g_dex_counter_map.end() || kv.second.empty()) continue;
                std::string kind = "auto";
                auto oit = g_owned_dex_map.find(kv.first);
                if (oit != g_owned_dex_map.end()) {
                    kind = sanitizeKind(oit->second.kind.empty()
                        ? inferKind(oit->second.source, oit->second.location)
                        : oit->second.kind);
                }
                entries.push_back({static_cast<int>(kv.second.size()), it->second, kind, kv.second});
            }
        }

        for (auto& e : entries) {
            std::string fix_path = fix_dir + "/" + std::to_string(e.size_int) + "_" +
                                   std::to_string(e.counter) + "_dex_file_fix.dex";
            std::string kind_fix_dir = fix_dir + "/" + e.kind;
            ensure_dir_exists(fix_dir);
            ensure_dir_exists(kind_fix_dir);
            char kind_name[128];
            snprintf(kind_name, sizeof(kind_name), "%03d_%d_dex_file_fix.dex", e.counter, e.size_int);
            std::string kind_fix_path = kind_fix_dir + "/" + kind_name;
            int fp = open(fix_path.c_str(), O_CREAT | O_WRONLY | O_TRUNC, 0666);
            if (fp >= 0) {
              ssize_t w = write(fp, e.buf.data(), e.buf.size());
              if (w < 0) {
                LOG(ERROR) << "[flushFixedDex]: write dexfile failed, errno=" << errno;
              }
              fsync(fp);
              close(fp);
              writeAllBytes(kind_fix_path, e.buf.data(), e.buf.size());
              LOG(INFO) << "[flushFixedDex] written: " << kind_fix_path;
            } else {
                LOG(ERROR) << "[flushFixedDex] open failed: " << fix_path << ", errno=" << errno;
            }
        }
    }

    extern "C" void callNativeMethodInspector(ArtMethod* artmethod) REQUIRES_SHARED(Locks::mutator_lock_) {
            JValue *result=nullptr;
            Thread *self=nullptr;
            uint32_t temp=6;
            uint32_t* args=&temp;
            uint32_t args_size=6;
            // 通过线程局部标志位通知 Invoke，此次调用是 FART 主动触发，而非真实执行路径
            g_fart_trace_active = true;
            artmethod->Invoke(self, args, args_size, result, "startCodeInspection");
            g_fart_trace_active = false;
    }
    // add end

using android::base::StringPrintf;

extern "C" void art_quick_invoke_stub(ArtMethod*, uint32_t*, uint32_t, Thread*, JValue*,
                                      const char*);
extern "C" void art_quick_invoke_static_stub(ArtMethod*, uint32_t*, uint32_t, Thread*, JValue*,
                                             const char*);

// Enforce that we have the right index for runtime methods.
static_assert(ArtMethod::kRuntimeMethodDexMethodIndex == dex::kDexNoIndex,
              "Wrong runtime-method dex method index");

ArtMethod* ArtMethod::GetCanonicalMethod(PointerSize pointer_size) {
  if (LIKELY(!IsCopied())) {
    return this;
  } else {
    ObjPtr<mirror::Class> declaring_class = GetDeclaringClass();
    DCHECK(declaring_class->IsInterface());
    ArtMethod* ret = declaring_class->FindInterfaceMethod(GetDexCache(),
                                                          GetDexMethodIndex(),
                                                          pointer_size);
    DCHECK(ret != nullptr);
    return ret;
  }
}

ArtMethod* ArtMethod::GetNonObsoleteMethod() {
  if (LIKELY(!IsObsolete())) {
    return this;
  }
  DCHECK_EQ(kRuntimePointerSize, Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  if (IsDirect()) {
    return &GetDeclaringClass()->GetDirectMethodsSlice(kRuntimePointerSize)[GetMethodIndex()];
  } else {
    return GetDeclaringClass()->GetVTableEntry(GetMethodIndex(), kRuntimePointerSize);
  }
}

ArtMethod* ArtMethod::GetSingleImplementation(PointerSize pointer_size) {
  if (IsInvokable()) {
    // An invokable method single implementation is itself.
    return this;
  }
  DCHECK(!IsDefaultConflicting());
  ArtMethod* m = reinterpret_cast<ArtMethod*>(GetDataPtrSize(pointer_size));
  CHECK(m == nullptr || !m->IsDefaultConflicting());
  return m;
}

ArtMethod* ArtMethod::FromReflectedMethod(const ScopedObjectAccessAlreadyRunnable& soa,
                                          jobject jlr_method) {
  ObjPtr<mirror::Executable> executable = soa.Decode<mirror::Executable>(jlr_method);
  DCHECK(executable != nullptr);
  return executable->GetArtMethod();
}

ObjPtr<mirror::DexCache> ArtMethod::GetObsoleteDexCache() {
  PointerSize pointer_size = kRuntimePointerSize;
  DCHECK(!Runtime::Current()->IsAotCompiler()) << PrettyMethod();
  DCHECK(IsObsolete());
  ObjPtr<mirror::ClassExt> ext(GetDeclaringClass()->GetExtData());
  ObjPtr<mirror::PointerArray> obsolete_methods(ext.IsNull() ? nullptr : ext->GetObsoleteMethods());
  int32_t len = (obsolete_methods.IsNull() ? 0 : obsolete_methods->GetLength());
  DCHECK(len == 0 || len == ext->GetObsoleteDexCaches()->GetLength())
      << "len=" << len << " ext->GetObsoleteDexCaches()=" << ext->GetObsoleteDexCaches();
  // Using kRuntimePointerSize (instead of using the image's pointer size) is fine since images
  // should never have obsolete methods in them so they should always be the same.
  DCHECK_EQ(pointer_size, Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  for (int32_t i = 0; i < len; i++) {
    if (this == obsolete_methods->GetElementPtrSize<ArtMethod*>(i, pointer_size)) {
      return ext->GetObsoleteDexCaches()->Get(i);
    }
  }
  CHECK(GetDeclaringClass()->IsObsoleteObject())
      << "This non-structurally obsolete method does not appear in the obsolete map of its class: "
      << GetDeclaringClass()->PrettyClass() << " Searched " << len << " caches.";
  CHECK_EQ(this,
           std::clamp(this,
                      &(*GetDeclaringClass()->GetMethods(pointer_size).begin()),
                      &(*GetDeclaringClass()->GetMethods(pointer_size).end())))
      << "class is marked as structurally obsolete method but not found in normal obsolete-map "
      << "despite not being the original method pointer for " << GetDeclaringClass()->PrettyClass();
  return GetDeclaringClass()->GetDexCache();
}

uint16_t ArtMethod::FindObsoleteDexClassDefIndex() {
  DCHECK(!Runtime::Current()->IsAotCompiler()) << PrettyMethod();
  DCHECK(IsObsolete());
  const DexFile* dex_file = GetDexFile();
  const dex::TypeIndex declaring_class_type = dex_file->GetMethodId(GetDexMethodIndex()).class_idx_;
  const dex::ClassDef* class_def = dex_file->FindClassDef(declaring_class_type);
  CHECK(class_def != nullptr);
  return dex_file->GetIndexForClassDef(*class_def);
}

void ArtMethod::ThrowInvocationTimeError() {
  DCHECK(!IsInvokable());
  if (IsDefaultConflicting()) {
    ThrowIncompatibleClassChangeErrorForMethodConflict(this);
  } else {
    DCHECK(IsAbstract());
    ThrowAbstractMethodError(this);
  }
}

InvokeType ArtMethod::GetInvokeType() {
  // TODO: kSuper?
  if (IsStatic()) {
    return kStatic;
  } else if (GetDeclaringClass()->IsInterface()) {
    return kInterface;
  } else if (IsDirect()) {
    return kDirect;
  } else if (IsSignaturePolymorphic()) {
    return kPolymorphic;
  } else {
    return kVirtual;
  }
}

size_t ArtMethod::NumArgRegisters(const char* shorty) {
  CHECK_NE(shorty[0], '\0');
  uint32_t num_registers = 0;
  for (const char* s = shorty + 1; *s != '\0'; ++s) {
    if (*s == 'D' || *s == 'J') {
      num_registers += 2;
    } else {
      num_registers += 1;
    }
  }
  return num_registers;
}

bool ArtMethod::HasSameNameAndSignature(ArtMethod* other) {
  ScopedAssertNoThreadSuspension ants("HasSameNameAndSignature");
  const DexFile* dex_file = GetDexFile();
  const dex::MethodId& mid = dex_file->GetMethodId(GetDexMethodIndex());
  if (GetDexCache() == other->GetDexCache()) {
    const dex::MethodId& mid2 = dex_file->GetMethodId(other->GetDexMethodIndex());
    return mid.name_idx_ == mid2.name_idx_ && mid.proto_idx_ == mid2.proto_idx_;
  }
  const DexFile* dex_file2 = other->GetDexFile();
  const dex::MethodId& mid2 = dex_file2->GetMethodId(other->GetDexMethodIndex());
  if (!DexFile::StringEquals(dex_file, mid.name_idx_, dex_file2, mid2.name_idx_)) {
    return false;  // Name mismatch.
  }
  return dex_file->GetMethodSignature(mid) == dex_file2->GetMethodSignature(mid2);
}

ArtMethod* ArtMethod::FindOverriddenMethod(PointerSize pointer_size) {
  if (IsStatic()) {
    return nullptr;
  }
  ObjPtr<mirror::Class> declaring_class = GetDeclaringClass();
  ObjPtr<mirror::Class> super_class = declaring_class->GetSuperClass();
  uint16_t method_index = GetMethodIndex();
  ArtMethod* result = nullptr;
  // Did this method override a super class method? If so load the result from the super class'
  // vtable
  if (super_class->HasVTable() && method_index < super_class->GetVTableLength()) {
    result = super_class->GetVTableEntry(method_index, pointer_size);
  } else {
    // Method didn't override superclass method so search interfaces
    if (IsProxyMethod()) {
      result = GetInterfaceMethodIfProxy(pointer_size);
      DCHECK(result != nullptr);
    } else {
      ObjPtr<mirror::IfTable> iftable = GetDeclaringClass()->GetIfTable();
      for (size_t i = 0; i < iftable->Count() && result == nullptr; i++) {
        ObjPtr<mirror::Class> interface = iftable->GetInterface(i);
        for (ArtMethod& interface_method : interface->GetVirtualMethods(pointer_size)) {
          if (HasSameNameAndSignature(interface_method.GetInterfaceMethodIfProxy(pointer_size))) {
            result = &interface_method;
            break;
          }
        }
      }
    }
  }
  DCHECK(result == nullptr ||
         GetInterfaceMethodIfProxy(pointer_size)->HasSameNameAndSignature(
             result->GetInterfaceMethodIfProxy(pointer_size)));
  return result;
}

uint32_t ArtMethod::FindDexMethodIndexInOtherDexFile(const DexFile& other_dexfile,
                                                     uint32_t name_and_signature_idx) {
  const DexFile* dexfile = GetDexFile();
  const uint32_t dex_method_idx = GetDexMethodIndex();
  const dex::MethodId& mid = dexfile->GetMethodId(dex_method_idx);
  const dex::MethodId& name_and_sig_mid = other_dexfile.GetMethodId(name_and_signature_idx);
  DCHECK_STREQ(dexfile->GetMethodName(mid), other_dexfile.GetMethodName(name_and_sig_mid));
  DCHECK_EQ(dexfile->GetMethodSignature(mid), other_dexfile.GetMethodSignature(name_and_sig_mid));
  if (dexfile == &other_dexfile) {
    return dex_method_idx;
  }
  const char* mid_declaring_class_descriptor = dexfile->StringByTypeIdx(mid.class_idx_);
  const dex::TypeId* other_type_id = other_dexfile.FindTypeId(mid_declaring_class_descriptor);
  if (other_type_id != nullptr) {
    const dex::MethodId* other_mid = other_dexfile.FindMethodId(
        *other_type_id, other_dexfile.GetStringId(name_and_sig_mid.name_idx_),
        other_dexfile.GetProtoId(name_and_sig_mid.proto_idx_));
    if (other_mid != nullptr) {
      return other_dexfile.GetIndexForMethodId(*other_mid);
    }
  }
  return dex::kDexNoIndex;
}

uint32_t ArtMethod::FindCatchBlock(Handle<mirror::Class> exception_type,
                                   uint32_t dex_pc, bool* has_no_move_exception) {
  // Set aside the exception while we resolve its type.
  Thread* self = Thread::Current();
  StackHandleScope<1> hs(self);
  Handle<mirror::Throwable> exception(hs.NewHandle(self->GetException()));
  self->ClearException();
  // Default to handler not found.
  uint32_t found_dex_pc = dex::kDexNoIndex;
  // Iterate over the catch handlers associated with dex_pc.
  CodeItemDataAccessor accessor(DexInstructionData());
  for (CatchHandlerIterator it(accessor, dex_pc); it.HasNext(); it.Next()) {
    dex::TypeIndex iter_type_idx = it.GetHandlerTypeIndex();
    // Catch all case
    if (!iter_type_idx.IsValid()) {
      found_dex_pc = it.GetHandlerAddress();
      break;
    }
    // Does this catch exception type apply?
    ObjPtr<mirror::Class> iter_exception_type = ResolveClassFromTypeIndex(iter_type_idx);
    if (UNLIKELY(iter_exception_type == nullptr)) {
      // Now have a NoClassDefFoundError as exception. Ignore in case the exception class was
      // removed by a pro-guard like tool.
      // Note: this is not RI behavior. RI would have failed when loading the class.
      self->ClearException();
      // Delete any long jump context as this routine is called during a stack walk which will
      // release its in use context at the end.
      delete self->GetLongJumpContext();
      LOG(WARNING) << "Unresolved exception class when finding catch block: "
        << DescriptorToDot(GetTypeDescriptorFromTypeIdx(iter_type_idx));
    } else if (iter_exception_type->IsAssignableFrom(exception_type.Get())) {
      found_dex_pc = it.GetHandlerAddress();
      break;
    }
  }
  if (found_dex_pc != dex::kDexNoIndex) {
    const Instruction& first_catch_instr = accessor.InstructionAt(found_dex_pc);
    *has_no_move_exception = (first_catch_instr.Opcode() != Instruction::MOVE_EXCEPTION);
  }
  // Put the exception back.
  if (exception != nullptr) {
    self->SetException(exception.Get());
  }
  return found_dex_pc;
}

void ArtMethod::Invoke(Thread* self, uint32_t* args, uint32_t args_size, JValue* result,
                       const char* shorty) {
  //add
  // 使用线程局部标志位替代 self==nullptr 判断：避免因其他代码路径传入 nullptr 导致误触发
  if (g_fart_trace_active) {
    traceMethodCode(this);
    return;
  }
  // AOSP 13 默认 nterp / quick stub，C++ Execute 经常进不去。
  // <clinit> 必须在 Invoke 返回后 dump（与 Frida leave 同窗口）。
  // dump=false 时只读 atomic，不碰 IsClassInitializer。
  struct FartClinitInvokeDump {
    ArtMethod* method_;
    explicit FartClinitInvokeDump(ArtMethod* m) : method_(m) {}
    ~FartClinitInvokeDump() {
      if (UNLIKELY(method_ != nullptr)) {
        traceMethodCode(method_);
      }
    }
  };
  FartClinitInvokeDump fart_clinit_invoke(
      (fartDumpEnabled() && IsClassInitializer()) ? this : nullptr);
  // add end

  if (UNLIKELY(__builtin_frame_address(0) < self->GetStackEnd())) {
    ThrowStackOverflowError(self);
    return;
  }

  if (kIsDebugBuild) {
    self->AssertThreadSuspensionIsAllowable();
    CHECK_EQ(ThreadState::kRunnable, self->GetState());
    CHECK_STREQ(GetInterfaceMethodIfProxy(kRuntimePointerSize)->GetShorty(), shorty);
  }

  // Push a transition back into managed code onto the linked list in thread.
  ManagedStack fragment;
  self->PushManagedStackFragment(&fragment);

  Runtime* runtime = Runtime::Current();
  // Call the invoke stub, passing everything as arguments.
  // If the runtime is not yet started or it is required by the debugger, then perform the
  // Invocation by the interpreter, explicitly forcing interpretation over JIT to prevent
  // cycling around the various JIT/Interpreter methods that handle method invocation.
  if (UNLIKELY(!runtime->IsStarted() ||
               (self->IsForceInterpreter() && !IsNative() && !IsProxyMethod() && IsInvokable()))) {
    if (IsStatic()) {
      art::interpreter::EnterInterpreterFromInvoke(
          self, this, nullptr, args, result, /*stay_in_interpreter=*/ true);
    } else {
      mirror::Object* receiver =
          reinterpret_cast<StackReference<mirror::Object>*>(&args[0])->AsMirrorPtr();
      art::interpreter::EnterInterpreterFromInvoke(
          self, this, receiver, args + 1, result, /*stay_in_interpreter=*/ true);
    }
  } else {
    DCHECK_EQ(runtime->GetClassLinker()->GetImagePointerSize(), kRuntimePointerSize);

    constexpr bool kLogInvocationStartAndReturn = false;
    bool have_quick_code = GetEntryPointFromQuickCompiledCode() != nullptr;
    if (LIKELY(have_quick_code)) {
      if (kLogInvocationStartAndReturn) {
        LOG(INFO) << StringPrintf(
            "Invoking '%s' quick code=%p static=%d", PrettyMethod().c_str(),
            GetEntryPointFromQuickCompiledCode(), static_cast<int>(IsStatic() ? 1 : 0));
      }

      // Ensure that we won't be accidentally calling quick compiled code when -Xint.
      if (kIsDebugBuild && runtime->GetInstrumentation()->IsForcedInterpretOnly()) {
        CHECK(!runtime->UseJitCompilation());
        const void* oat_quick_code =
            (IsNative() || !IsInvokable() || IsProxyMethod() || IsObsolete())
            ? nullptr
            : GetOatMethodQuickCode(runtime->GetClassLinker()->GetImagePointerSize());
        CHECK(oat_quick_code == nullptr || oat_quick_code != GetEntryPointFromQuickCompiledCode())
            << "Don't call compiled code when -Xint " << PrettyMethod();
      }

      if (!IsStatic()) {
        (*art_quick_invoke_stub)(this, args, args_size, self, result, shorty);
      } else {
        (*art_quick_invoke_static_stub)(this, args, args_size, self, result, shorty);
      }
      if (UNLIKELY(self->GetException() == Thread::GetDeoptimizationException())) {
        // Unusual case where we were running generated code and an
        // exception was thrown to force the activations to be removed from the
        // stack. Continue execution in the interpreter.
        self->DeoptimizeWithDeoptimizationException(result);
      }
      if (kLogInvocationStartAndReturn) {
        LOG(INFO) << StringPrintf("Returned '%s' quick code=%p", PrettyMethod().c_str(),
                                  GetEntryPointFromQuickCompiledCode());
      }
    } else {
      LOG(INFO) << "Not invoking '" << PrettyMethod() << "' code=null";
      if (result != nullptr) {
        result->SetJ(0);
      }
    }
  }

  // Pop transition.
  self->PopManagedStackFragment(fragment);
}

bool ArtMethod::IsSignaturePolymorphic() {
  // Methods with a polymorphic signature have constraints that they
  // are native and varargs and belong to either MethodHandle or VarHandle.
  if (!IsNative() || !IsVarargs()) {
    return false;
  }
  ObjPtr<mirror::ObjectArray<mirror::Class>> class_roots =
      Runtime::Current()->GetClassLinker()->GetClassRoots();
  ObjPtr<mirror::Class> cls = GetDeclaringClass();
  return (cls == GetClassRoot<mirror::MethodHandle>(class_roots) ||
          cls == GetClassRoot<mirror::VarHandle>(class_roots));
}

static uint32_t GetOatMethodIndexFromMethodIndex(const DexFile& dex_file,
                                                 uint16_t class_def_idx,
                                                 uint32_t method_idx) {
  ClassAccessor accessor(dex_file, class_def_idx);
  uint32_t class_def_method_index = 0u;
  for (const ClassAccessor::Method& method : accessor.GetMethods()) {
    if (method.GetIndex() == method_idx) {
      return class_def_method_index;
    }
    class_def_method_index++;
  }
  LOG(FATAL) << "Failed to find method index " << method_idx << " in " << dex_file.GetLocation();
  UNREACHABLE();
}

// We use the method's DexFile and declaring class name to find the OatMethod for an obsolete
// method.  This is extremely slow but we need it if we want to be able to have obsolete native
// methods since we need this to find the size of its stack frames.
//
// NB We could (potentially) do this differently and rely on the way the transformation is applied
// in order to use the entrypoint to find this information. However, for debugging reasons (most
// notably making sure that new invokes of obsolete methods fail) we choose to instead get the data
// directly from the dex file.
static const OatFile::OatMethod FindOatMethodFromDexFileFor(ArtMethod* method, bool* found)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  DCHECK(method->IsObsolete() && method->IsNative());
  const DexFile* dex_file = method->GetDexFile();

  // recreate the class_def_index from the descriptor.
  std::string descriptor_storage;
  const dex::TypeId* declaring_class_type_id =
      dex_file->FindTypeId(method->GetDeclaringClass()->GetDescriptor(&descriptor_storage));
  CHECK(declaring_class_type_id != nullptr);
  dex::TypeIndex declaring_class_type_index = dex_file->GetIndexForTypeId(*declaring_class_type_id);
  const dex::ClassDef* declaring_class_type_def =
      dex_file->FindClassDef(declaring_class_type_index);
  CHECK(declaring_class_type_def != nullptr);
  uint16_t declaring_class_def_index = dex_file->GetIndexForClassDef(*declaring_class_type_def);

  size_t oat_method_index = GetOatMethodIndexFromMethodIndex(*dex_file,
                                                             declaring_class_def_index,
                                                             method->GetDexMethodIndex());

  OatFile::OatClass oat_class = OatFile::FindOatClass(*dex_file,
                                                      declaring_class_def_index,
                                                      found);
  if (!(*found)) {
    return OatFile::OatMethod::Invalid();
  }
  return oat_class.GetOatMethod(oat_method_index);
}

static const OatFile::OatMethod FindOatMethodFor(ArtMethod* method,
                                                 PointerSize pointer_size,
                                                 bool* found)
    REQUIRES_SHARED(Locks::mutator_lock_) {
  if (UNLIKELY(method->IsObsolete())) {
    // We shouldn't be calling this with obsolete methods except for native obsolete methods for
    // which we need to use the oat method to figure out how large the quick frame is.
    DCHECK(method->IsNative()) << "We should only be finding the OatMethod of obsolete methods in "
                               << "order to allow stack walking. Other obsolete methods should "
                               << "never need to access this information.";
    DCHECK_EQ(pointer_size, kRuntimePointerSize) << "Obsolete method in compiler!";
    return FindOatMethodFromDexFileFor(method, found);
  }
  // Although we overwrite the trampoline of non-static methods, we may get here via the resolution
  // method for direct methods (or virtual methods made direct).
  ObjPtr<mirror::Class> declaring_class = method->GetDeclaringClass();
  size_t oat_method_index;
  if (method->IsStatic() || method->IsDirect()) {
    // Simple case where the oat method index was stashed at load time.
    oat_method_index = method->GetMethodIndex();
  } else {
    // Compute the oat_method_index by search for its position in the declared virtual methods.
    oat_method_index = declaring_class->NumDirectMethods();
    bool found_virtual = false;
    for (ArtMethod& art_method : declaring_class->GetVirtualMethods(pointer_size)) {
      // Check method index instead of identity in case of duplicate method definitions.
      if (method->GetDexMethodIndex() == art_method.GetDexMethodIndex()) {
        found_virtual = true;
        break;
      }
      oat_method_index++;
    }
    CHECK(found_virtual) << "Didn't find oat method index for virtual method: "
                         << method->PrettyMethod();
  }
  DCHECK_EQ(oat_method_index,
            GetOatMethodIndexFromMethodIndex(declaring_class->GetDexFile(),
                                             method->GetDeclaringClass()->GetDexClassDefIndex(),
                                             method->GetDexMethodIndex()));
  OatFile::OatClass oat_class = OatFile::FindOatClass(declaring_class->GetDexFile(),
                                                      declaring_class->GetDexClassDefIndex(),
                                                      found);
  if (!(*found)) {
    return OatFile::OatMethod::Invalid();
  }
  return oat_class.GetOatMethod(oat_method_index);
}

bool ArtMethod::EqualParameters(Handle<mirror::ObjectArray<mirror::Class>> params) {
  const DexFile* dex_file = GetDexFile();
  const auto& method_id = dex_file->GetMethodId(GetDexMethodIndex());
  const auto& proto_id = dex_file->GetMethodPrototype(method_id);
  const dex::TypeList* proto_params = dex_file->GetProtoParameters(proto_id);
  auto count = proto_params != nullptr ? proto_params->Size() : 0u;
  auto param_len = params != nullptr ? params->GetLength() : 0u;
  if (param_len != count) {
    return false;
  }
  auto* cl = Runtime::Current()->GetClassLinker();
  for (size_t i = 0; i < count; ++i) {
    dex::TypeIndex type_idx = proto_params->GetTypeItem(i).type_idx_;
    ObjPtr<mirror::Class> type = cl->ResolveType(type_idx, this);
    if (type == nullptr) {
      Thread::Current()->AssertPendingException();
      return false;
    }
    if (type != params->GetWithoutChecks(i)) {
      return false;
    }
  }
  return true;
}

const OatQuickMethodHeader* ArtMethod::GetOatQuickMethodHeader(uintptr_t pc) {
  // Our callers should make sure they don't pass the instrumentation exit pc,
  // as this method does not look at the side instrumentation stack.
  DCHECK_NE(pc, reinterpret_cast<uintptr_t>(GetQuickInstrumentationExitPc()));

  if (IsRuntimeMethod()) {
    return nullptr;
  }

  Runtime* runtime = Runtime::Current();
  const void* existing_entry_point = GetEntryPointFromQuickCompiledCode();
  CHECK(existing_entry_point != nullptr) << PrettyMethod() << "@" << this;
  ClassLinker* class_linker = runtime->GetClassLinker();

  if (existing_entry_point == GetQuickProxyInvokeHandler()) {
    DCHECK(IsProxyMethod() && !IsConstructor());
    // The proxy entry point does not have any method header.
    return nullptr;
  }

  // Check whether the current entry point contains this pc.
  if (!class_linker->IsQuickGenericJniStub(existing_entry_point) &&
      !class_linker->IsQuickResolutionStub(existing_entry_point) &&
      !class_linker->IsQuickToInterpreterBridge(existing_entry_point) &&
      existing_entry_point != GetQuickInstrumentationEntryPoint() &&
      existing_entry_point != GetInvokeObsoleteMethodStub()) {
    OatQuickMethodHeader* method_header =
        OatQuickMethodHeader::FromEntryPoint(existing_entry_point);

    if (method_header->Contains(pc)) {
      return method_header;
    }
  }

  if (OatQuickMethodHeader::IsNterpPc(pc)) {
    return OatQuickMethodHeader::NterpMethodHeader;
  }

  // Check whether the pc is in the JIT code cache.
  jit::Jit* jit = runtime->GetJit();
  if (jit != nullptr) {
    jit::JitCodeCache* code_cache = jit->GetCodeCache();
    OatQuickMethodHeader* method_header = code_cache->LookupMethodHeader(pc, this);
    if (method_header != nullptr) {
      DCHECK(method_header->Contains(pc));
      return method_header;
    } else {
      DCHECK(!code_cache->ContainsPc(reinterpret_cast<const void*>(pc)))
          << PrettyMethod()
          << ", pc=" << std::hex << pc
          << ", entry_point=" << std::hex << reinterpret_cast<uintptr_t>(existing_entry_point)
          << ", copy=" << std::boolalpha << IsCopied()
          << ", proxy=" << std::boolalpha << IsProxyMethod();
    }
  }

  // The code has to be in an oat file.
  bool found;
  OatFile::OatMethod oat_method =
      FindOatMethodFor(this, class_linker->GetImagePointerSize(), &found);
  if (!found) {
    if (IsNative()) {
      // We are running the GenericJNI stub. The entrypoint may point
      // to different entrypoints or to a JIT-compiled JNI stub.
      DCHECK(class_linker->IsQuickGenericJniStub(existing_entry_point) ||
             class_linker->IsQuickResolutionStub(existing_entry_point) ||
             existing_entry_point == GetQuickInstrumentationEntryPoint() ||
             (jit != nullptr && jit->GetCodeCache()->ContainsPc(existing_entry_point)))
          << " entrypoint: " << existing_entry_point
          << " size: " << OatQuickMethodHeader::FromEntryPoint(existing_entry_point)->GetCodeSize()
          << " pc: " << reinterpret_cast<const void*>(pc);
      return nullptr;
    }
    // Only for unit tests.
    // TODO(ngeoffray): Update these tests to pass the right pc?
    return OatQuickMethodHeader::FromEntryPoint(existing_entry_point);
  }
  const void* oat_entry_point = oat_method.GetQuickCode();
  if (oat_entry_point == nullptr || class_linker->IsQuickGenericJniStub(oat_entry_point)) {
    DCHECK(IsNative()) << PrettyMethod();
    return nullptr;
  }

  OatQuickMethodHeader* method_header = OatQuickMethodHeader::FromEntryPoint(oat_entry_point);
  if (pc == 0) {
    // This is a downcall, it can only happen for a native method.
    DCHECK(IsNative());
    return method_header;
  }

  DCHECK(method_header->Contains(pc))
      << PrettyMethod()
      << " " << std::hex << pc << " " << oat_entry_point
      << " " << (uintptr_t)(method_header->GetCode() + method_header->GetCodeSize());
  return method_header;
}

const void* ArtMethod::GetOatMethodQuickCode(PointerSize pointer_size) {
  bool found;
  OatFile::OatMethod oat_method = FindOatMethodFor(this, pointer_size, &found);
  if (found) {
    return oat_method.GetQuickCode();
  }
  return nullptr;
}

bool ArtMethod::HasAnyCompiledCode() {
  if (IsNative() || !IsInvokable() || IsProxyMethod()) {
    return false;
  }

  // Check whether the JIT has compiled it.
  Runtime* runtime = Runtime::Current();
  jit::Jit* jit = runtime->GetJit();
  if (jit != nullptr && jit->GetCodeCache()->ContainsMethod(this)) {
    return true;
  }

  // Check whether we have AOT code.
  return GetOatMethodQuickCode(runtime->GetClassLinker()->GetImagePointerSize()) != nullptr;
}

void ArtMethod::SetIntrinsic(uint32_t intrinsic) {
  // Currently we only do intrinsics for static/final methods or methods of final
  // classes. We don't set kHasSingleImplementation for those methods.
  DCHECK(IsStatic() || IsFinal() || GetDeclaringClass()->IsFinal()) <<
      "Potential conflict with kAccSingleImplementation";
  static const int kAccFlagsShift = CTZ(kAccIntrinsicBits);
  DCHECK_LE(intrinsic, kAccIntrinsicBits >> kAccFlagsShift);
  uint32_t intrinsic_bits = intrinsic << kAccFlagsShift;
  uint32_t new_value = (GetAccessFlags() & ~kAccIntrinsicBits) | kAccIntrinsic | intrinsic_bits;
  if (kIsDebugBuild) {
    uint32_t java_flags = (GetAccessFlags() & kAccJavaFlagsMask);
    bool is_constructor = IsConstructor();
    bool is_synchronized = IsSynchronized();
    bool skip_access_checks = SkipAccessChecks();
    bool is_fast_native = IsFastNative();
    bool is_critical_native = IsCriticalNative();
    bool is_copied = IsCopied();
    bool is_miranda = IsMiranda();
    bool is_default = IsDefault();
    bool is_default_conflict = IsDefaultConflicting();
    bool is_compilable = IsCompilable();
    bool must_count_locks = MustCountLocks();
    // Recompute flags instead of getting them from the current access flags because
    // access flags may have been changed to deduplicate warning messages (b/129063331).
    uint32_t hiddenapi_flags = hiddenapi::CreateRuntimeFlags(this);
    SetAccessFlags(new_value);
    DCHECK_EQ(java_flags, (GetAccessFlags() & kAccJavaFlagsMask));
    DCHECK_EQ(is_constructor, IsConstructor());
    DCHECK_EQ(is_synchronized, IsSynchronized());
    DCHECK_EQ(skip_access_checks, SkipAccessChecks());
    DCHECK_EQ(is_fast_native, IsFastNative());
    DCHECK_EQ(is_critical_native, IsCriticalNative());
    DCHECK_EQ(is_copied, IsCopied());
    DCHECK_EQ(is_miranda, IsMiranda());
    DCHECK_EQ(is_default, IsDefault());
    DCHECK_EQ(is_default_conflict, IsDefaultConflicting());
    DCHECK_EQ(is_compilable, IsCompilable());
    DCHECK_EQ(must_count_locks, MustCountLocks());
    // Only DCHECK that we have preserved the hidden API access flags if the
    // original method was not in the SDK list. This is because the core image
    // does not have the access flags set (b/77733081).
    if ((hiddenapi_flags & kAccHiddenapiBits) != kAccPublicApi) {
      DCHECK_EQ(hiddenapi_flags, hiddenapi::GetRuntimeFlags(this)) << PrettyMethod();
    }
  } else {
    SetAccessFlags(new_value);
  }
}

void ArtMethod::SetNotIntrinsic() {
  if (!IsIntrinsic()) {
    return;
  }

  // Read the existing hiddenapi flags.
  uint32_t hiddenapi_runtime_flags = hiddenapi::GetRuntimeFlags(this);

  // Clear intrinsic-related access flags.
  ClearAccessFlags(kAccIntrinsic | kAccIntrinsicBits);

  // Re-apply hidden API access flags now that the method is not an intrinsic.
  SetAccessFlags(GetAccessFlags() | hiddenapi_runtime_flags);
  DCHECK_EQ(hiddenapi_runtime_flags, hiddenapi::GetRuntimeFlags(this));
}

void ArtMethod::CopyFrom(ArtMethod* src, PointerSize image_pointer_size) {
  memcpy(reinterpret_cast<void*>(this), reinterpret_cast<const void*>(src),
         Size(image_pointer_size));
  declaring_class_ = GcRoot<mirror::Class>(const_cast<ArtMethod*>(src)->GetDeclaringClass());

  // If the entry point of the method we are copying from is from JIT code, we just
  // put the entry point of the new method to interpreter or GenericJNI. We could set
  // the entry point to the JIT code, but this would require taking the JIT code cache
  // lock to notify it, which we do not want at this level.
  Runtime* runtime = Runtime::Current();
  if (runtime->UseJitCompilation()) {
    if (runtime->GetJit()->GetCodeCache()->ContainsPc(GetEntryPointFromQuickCompiledCode())) {
      SetEntryPointFromQuickCompiledCodePtrSize(
          src->IsNative() ? GetQuickGenericJniStub() : GetQuickToInterpreterBridge(),
          image_pointer_size);
    }
  }
  if (interpreter::IsNterpSupported() &&
      (GetEntryPointFromQuickCompiledCodePtrSize(image_pointer_size) ==
          interpreter::GetNterpEntryPoint())) {
    // If the entrypoint is nterp, it's too early to check if the new method
    // will support it. So for simplicity, use the interpreter bridge.
    SetEntryPointFromQuickCompiledCodePtrSize(GetQuickToInterpreterBridge(), image_pointer_size);
  }

  // Clear the data pointer, it will be set if needed by the caller.
  if (!src->HasCodeItem() && !src->IsNative()) {
    SetDataPtrSize(nullptr, image_pointer_size);
  }
  // Clear hotness to let the JIT properly decide when to compile this method.
  ResetCounter(runtime->GetJITOptions()->GetWarmupThreshold());
}

bool ArtMethod::IsImagePointerSize(PointerSize pointer_size) {
  // Hijack this function to get access to PtrSizedFieldsOffset.
  //
  // Ensure that PrtSizedFieldsOffset is correct. We rely here on usually having both 32-bit and
  // 64-bit builds.
  static_assert(std::is_standard_layout<ArtMethod>::value, "ArtMethod is not standard layout.");
  static_assert(
      (sizeof(void*) != 4) ||
          (offsetof(ArtMethod, ptr_sized_fields_) == PtrSizedFieldsOffset(PointerSize::k32)),
      "Unexpected 32-bit class layout.");
  static_assert(
      (sizeof(void*) != 8) ||
          (offsetof(ArtMethod, ptr_sized_fields_) == PtrSizedFieldsOffset(PointerSize::k64)),
      "Unexpected 64-bit class layout.");

  Runtime* runtime = Runtime::Current();
  if (runtime == nullptr) {
    return true;
  }
  return runtime->GetClassLinker()->GetImagePointerSize() == pointer_size;
}

std::string ArtMethod::PrettyMethod(ArtMethod* m, bool with_signature) {
  if (m == nullptr) {
    return "null";
  }
  return m->PrettyMethod(with_signature);
}

std::string ArtMethod::PrettyMethod(bool with_signature) {
  if (UNLIKELY(IsRuntimeMethod())) {
    std::string result = GetDeclaringClassDescriptor();
    result += '.';
    result += GetName();
    // Do not add "<no signature>" even if `with_signature` is true.
    return result;
  }
  ArtMethod* m =
      GetInterfaceMethodIfProxy(Runtime::Current()->GetClassLinker()->GetImagePointerSize());
  std::string res(m->GetDexFile()->PrettyMethod(m->GetDexMethodIndex(), with_signature));
  if (with_signature && m->IsObsolete()) {
    return "<OBSOLETE> " + res;
  } else {
    return res;
  }
}

std::string ArtMethod::JniShortName() {
  return GetJniShortName(GetDeclaringClassDescriptor(), GetName());
}

std::string ArtMethod::JniLongName() {
  std::string long_name;
  long_name += JniShortName();
  long_name += "__";

  std::string signature(GetSignature().ToString());
  signature.erase(0, 1);
  signature.erase(signature.begin() + signature.find(')'), signature.end());

  long_name += MangleForJni(signature);

  return long_name;
}

const char* ArtMethod::GetRuntimeMethodName() {
  Runtime* const runtime = Runtime::Current();
  if (this == runtime->GetResolutionMethod()) {
    return "<runtime internal resolution method>";
  } else if (this == runtime->GetImtConflictMethod()) {
    return "<runtime internal imt conflict method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveAllCalleeSaves)) {
    return "<runtime internal callee-save all registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveRefsOnly)) {
    return "<runtime internal callee-save reference registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveRefsAndArgs)) {
    return "<runtime internal callee-save reference and argument registers method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverything)) {
    return "<runtime internal save-every-register method>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverythingForClinit)) {
    return "<runtime internal save-every-register method for clinit>";
  } else if (this == runtime->GetCalleeSaveMethod(CalleeSaveType::kSaveEverythingForSuspendCheck)) {
    return "<runtime internal save-every-register method for suspend check>";
  } else {
    return "<unknown runtime internal method>";
  }
}

void ArtMethod::SetCodeItem(const dex::CodeItem* code_item, bool is_compact_dex_code_item) {
  DCHECK(HasCodeItem());
  // We mark the lowest bit for the interpreter to know whether it's executing a
  // method in a compact or standard dex file.
  uintptr_t data =
      reinterpret_cast<uintptr_t>(code_item) | (is_compact_dex_code_item ? 1 : 0);
  SetDataPtrSize(reinterpret_cast<void*>(data), kRuntimePointerSize);
}

// AssertSharedHeld doesn't work in GetAccessFlags, so use a NO_THREAD_SAFETY_ANALYSIS helper.
// TODO: Figure out why ASSERT_SHARED_CAPABILITY doesn't work.
template <ReadBarrierOption kReadBarrierOption>
ALWAYS_INLINE static inline void DoGetAccessFlagsHelper(ArtMethod* method)
    NO_THREAD_SAFETY_ANALYSIS {
  CHECK(method->IsRuntimeMethod() ||
        method->GetDeclaringClass<kReadBarrierOption>()->IsIdxLoaded() ||
        method->GetDeclaringClass<kReadBarrierOption>()->IsErroneous());
}

}  // namespace art

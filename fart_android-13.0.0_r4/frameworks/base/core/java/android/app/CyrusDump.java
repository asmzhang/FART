//add
package android.app;

import android.annotation.NonNull;
import android.util.Log;

import java.io.File;
import java.io.FileWriter;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import dalvik.system.PathClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * @hide FART dump 模块（与 ActivityThread 解耦，非 SDK API）。
 * 负责：ClassLoader 发现（含自定义）、owned DEX 登记、主动调用巡检、loaders 清单。
 */
final class CyrusDump {

    private CyrusDump() {}

    private static final String TAG = "CyrusDump";
    private static final int HARVEST_MAX_DEPTH = 6;

    static final String KIND_PRIMARY = "primary";
    static final String KIND_EXTRA = "extra";
    static final String KIND_CUSTOM = "custom";
    static final String KIND_INMEMORY = "inmemory";

    private static final IdentityHashMap<ClassLoader, Boolean> sLinkStubInstalled =
            new IdentityHashMap<ClassLoader, Boolean>();

    /** 一次完整登记：主 CL cookie 序优先，自定义加载器追加且不打乱已有槽位。 */
    static void registerAll(@NonNull String phase) {
        try {
            List<ClassLoader> loaders = discoverAppClassLoaders(!"pre-sleep".equals(phase));
            writeLoaderList(loaders, phase);
            int next = 0;
            for (int i = 0; i < loaders.size(); i++) {
                ClassLoader cl = loaders.get(i);
                String kind = classifyLoaderKind(cl, i == 0);
                next = registerFromClassLoader(cl, next, kind + "/" + phase);
            }
            invokeDexNative("nativeFlushOwnedDexManifest", new Class[]{});
            Log.e(TAG, "registerAll phase=" + phase + " loaders=" + loaders.size()
                    + " nextSlot=" + next);
            // After owned slots are recorded so fart_link_stubs.dex is not dumped.
            for (int i = 0; i < loaders.size(); i++) {
                installLinkStubs(loaders.get(i));
            }
        } catch (Throwable t) {
            Log.e(TAG, "registerAll failed phase=" + phase + " : " + t);
        }
    }

    /** 对已发现的每个 ClassLoader 做主动调用；自定义 CL 走字段收获，避免 pathList NPE。 */
    static void inspectAll() {
        beginFailLog();
        try {
            List<ClassLoader> loaders = discoverAppClassLoaders(true);
            for (int i = 0; i < loaders.size(); i++) {
                installLinkStubs(loaders.get(i));
            }
            for (ClassLoader cl : loaders) {
                inspectOneLoader(cl);
            }
            retryPendingFails();
        } catch (Throwable t) {
            Log.e(TAG, "inspectAll failed: " + t);
        } finally {
            endFailLog();
        }
    }

    static void setDumpEnabled(boolean enabled) {
        invokeDexNative("nativeSetDumpEnabled", new Class[]{boolean.class}, enabled);
    }

    static void setFixEnabled(boolean enabled) {
        invokeDexNative("nativeSetFixEnabled", new Class[]{boolean.class}, enabled);
    }

    static void flushFixedDex() {
        invokeDexNative("nativeFlushFixedDex", new Class[]{});
    }

    static void flushManifest() {
        invokeDexNative("nativeFlushOwnedDexManifest", new Class[]{});
    }

    static void inspectClassLoader(ClassLoader cl) {
        beginFailLog();
        try {
            installLinkStubs(cl);
            inspectOneLoader(cl);
            retryPendingFails();
        } finally {
            endFailLog();
        }
    }

    private static void inspectOneLoader(ClassLoader cl) {
        if (isBootClassLoader(cl)) {
            return;
        }
        Object pathList = getFieldByClassName("dalvik.system.BaseDexClassLoader", cl, "pathList");
        if (pathList != null) {
            inspectPathList(cl, pathList);
            return;
        }
        Log.i(TAG, "[custom] no pathList, harvest: " + safeName(cl));
        inspectHarvested(cl);
    }

    static List<ClassLoader> discoverAppClassLoaders(boolean includeThreadCcl) {
        LinkedHashSet<ClassLoader> out = new LinkedHashSet<ClassLoader>();
        try {
            addClassLoader(ActivityThread.obtainAppClassLoader(), out);
        } catch (Throwable t) {
            Log.w(TAG, "obtainAppClassLoader failed: " + t);
        }

        if (Cyrus.shouldIncludeExtraLoaders()) {
            try {
                ActivityThread at = ActivityThread.currentActivityThread();
                if (at != null) {
                    if (at.mInitialApplication != null) {
                        addClassLoader(at.mInitialApplication.getClassLoader(), out);
                    }
                    if (at.mAllApplications != null) {
                        for (int i = 0; i < at.mAllApplications.size(); i++) {
                            Application app = at.mAllApplications.get(i);
                            if (app != null) {
                                addClassLoader(app.getClassLoader(), out);
                            }
                        }
                    }
                    if (at.mBoundApplication != null && at.mBoundApplication.info != null) {
                        collectClassLoaderFields(at.mBoundApplication.info, out);
                    }
                }
            } catch (Throwable t) {
                Log.w(TAG, "ActivityThread walk failed: " + t);
            }

            try {
                Class<?> al = Class.forName("android.app.ApplicationLoaders");
                Object inst = al.getDeclaredMethod("getDefault").invoke(null);
                collectClassLoaderFields(inst, out);
            } catch (Throwable t) {
                Log.w(TAG, "ApplicationLoaders walk failed: " + t);
            }

            if (includeThreadCcl) {
                try {
                    for (Thread th : Thread.getAllStackTraces().keySet()) {
                        if (th != null) {
                            addClassLoader(th.getContextClassLoader(), out);
                        }
                    }
                } catch (Throwable t) {
                    Log.w(TAG, "thread CCL walk failed: " + t);
                }
            }
        }

        // 自定义 ClassLoader 内部常挂 delegate / pathClassLoader 字段（两跳，避免 Outer→Mid→Inner 漏掉）
        LinkedHashSet<ClassLoader> nested = new LinkedHashSet<ClassLoader>();
        for (ClassLoader cl : out) {
            collectClassLoaderFields(cl, nested);
        }
        LinkedHashSet<ClassLoader> nested2 = new LinkedHashSet<ClassLoader>();
        for (ClassLoader cl : nested) {
            collectClassLoaderFields(cl, nested2);
        }
        out.addAll(nested);
        out.addAll(nested2);

        if (Cyrus.shouldScanParents()) {
            LinkedHashSet<ClassLoader> parents = new LinkedHashSet<ClassLoader>();
            for (ClassLoader cl : out) {
                ClassLoader p = cl.getParent();
                while (p != null && !isBootClassLoader(p)) {
                    parents.add(p);
                    p = p.getParent();
                }
            }
            out.addAll(parents);
        }

        Log.e(TAG, "discovered ClassLoaders=" + out.size());
        return new ArrayList<ClassLoader>(out);
    }

    static String classifyLoaderKind(ClassLoader cl, boolean primary) {
        if (cl != null) {
            String cn = cl.getClass().getName();
            if (cn.indexOf("InMemory") >= 0) {
                return KIND_INMEMORY;
            }
        }
        if (primary) {
            return KIND_PRIMARY;
        }
        if (isBaseDexClassLoader(cl)) {
            return KIND_EXTRA;
        }
        return KIND_CUSTOM;
    }

    private static boolean isBootClassLoader(ClassLoader cl) {
        return cl == null || String.valueOf(cl).indexOf("java.lang.BootClassLoader") != -1;
    }

    private static boolean isBaseDexClassLoader(ClassLoader cl) {
        if (cl == null) {
            return false;
        }
        try {
            return Class.forName("dalvik.system.BaseDexClassLoader").isInstance(cl);
        } catch (Throwable t) {
            return false;
        }
    }

    private static void addClassLoader(Object maybeLoader, LinkedHashSet<ClassLoader> out) {
        if (maybeLoader instanceof ClassLoader) {
            ClassLoader cl = (ClassLoader) maybeLoader;
            if (!isBootClassLoader(cl)) {
                out.add(cl);
            }
            return;
        }
        if (maybeLoader instanceof Map) {
            for (Object v : ((Map<?, ?>) maybeLoader).values()) {
                addClassLoader(v, out);
            }
            return;
        }
        if (maybeLoader instanceof Iterable) {
            for (Object v : (Iterable<?>) maybeLoader) {
                addClassLoader(v, out);
            }
            return;
        }
        if (maybeLoader instanceof Object[]) {
            for (Object v : (Object[]) maybeLoader) {
                addClassLoader(v, out);
            }
        }
    }

    private static void collectClassLoaderFields(Object obj, LinkedHashSet<ClassLoader> out) {
        if (obj == null) {
            return;
        }
        Class<?> clazz = obj.getClass();
        while (clazz != null && clazz != Object.class) {
            Field[] fields;
            try {
                fields = clazz.getDeclaredFields();
            } catch (Throwable t) {
                break;
            }
            for (Field f : fields) {
                try {
                    Class<?> ft = f.getType();
                    if (ft != ClassLoader.class && !ClassLoader.class.isAssignableFrom(ft)
                            && !Map.class.isAssignableFrom(ft)
                            && !Iterable.class.isAssignableFrom(ft)
                            && !ft.isArray()) {
                        continue;
                    }
                    f.setAccessible(true);
                    addClassLoader(f.get(obj), out);
                } catch (Throwable ignored) {
                }
            }
            clazz = clazz.getSuperclass();
        }
    }

    private static int registerFromClassLoader(ClassLoader cl, int startIndex, String source) {
        if (isBootClassLoader(cl)) {
            return startIndex;
        }
        int next = startIndex;
        Object pathList = getFieldByClassName("dalvik.system.BaseDexClassLoader", cl, "pathList");
        if (pathList != null) {
            return registerFromPathList(cl, pathList, startIndex, source);
        }
        Harvest harvest = harvestFrom(cl);
        for (Object dex : harvest.dexFiles) {
            next = registerDexFile(cl, dex, next, source);
        }
        for (Object cookie : harvest.cookies) {
            next = registerCookie(cookie, next, source);
        }
        return next;
    }

    private static int registerFromPathList(ClassLoader cl, Object pathList, int startIndex,
                                            String source) {
        int next = startIndex;
        Object elements = getFieldByClassName("dalvik.system.DexPathList", pathList, "dexElements");
        if (!(elements instanceof Object[])) {
            return next;
        }
        Object[] arr = (Object[]) elements;
        Field dexFileField = declaredField("dalvik.system.DexPathList$Element", "dexFile");
        for (int j = 0; j < arr.length; j++) {
            Object dexfile = null;
            try {
                if (dexFileField != null) {
                    dexfile = dexFileField.get(arr[j]);
                }
            } catch (Throwable ignored) {
            }
            next = registerDexFile(cl, dexfile, next, source + "#e" + j);
        }
        return next;
    }

    private static int registerDexFile(ClassLoader cl, Object dexfile, int startIndex, String source) {
        if (dexfile == null || !isUserDex(dexfile)) {
            return startIndex;
        }
        Object cookie = readDexCookie(cl, dexfile);
        return registerCookie(cookie, startIndex, source);
    }

    private static int registerCookie(Object cookie, int startIndex, String source) {
        if (cookie == null) {
            return startIndex;
        }
        Object ret = invokeDexNative("nativeRegisterOwnedDex",
                new Class[]{Object.class, int.class, String.class},
                cookie, startIndex, source);
        if (ret instanceof Integer) {
            return ((Integer) ret).intValue();
        }
        return startIndex;
    }

    private static Object readDexCookie(ClassLoader cl, Object dexfile) {
        Object cookie = getInstanceField(dexfile, "mCookie");
        if (cookie == null) {
            cookie = getInstanceField(dexfile, "mInternalCookie");
        }
        if (cookie == null && cl != null) {
            cookie = extractField(cl, "dalvik.system.DexFile", dexfile, "mCookie");
            if (cookie == null) {
                cookie = extractField(cl, "dalvik.system.DexFile", dexfile, "mInternalCookie");
            }
        }
        return cookie;
    }

    private static final class Harvest {
        final List<Object> dexFiles = new ArrayList<Object>();
        final List<Object> cookies = new ArrayList<Object>();
    }

    /**
     * 自定义 ClassLoader：不假设 pathList，递归扫 DexFile / DexPathList / cookie / 嵌套 CL。
     */
    private static Harvest harvestFrom(Object root) {
        Harvest h = new Harvest();
        IdentityHashMap<Object, Boolean> visited = new IdentityHashMap<Object, Boolean>();
        harvest(root, visited, h, 0, "");
        return h;
    }

    private static boolean isCookieFieldName(String fieldHint) {
        return "mCookie".equals(fieldHint) || "mInternalCookie".equals(fieldHint);
    }

    private static void harvest(Object obj, IdentityHashMap<Object, Boolean> visited,
                                Harvest h, int depth, String fieldHint) {
        if (obj == null || depth > HARVEST_MAX_DEPTH) {
            return;
        }
        if (obj instanceof ClassLoader && isBootClassLoader((ClassLoader) obj) && depth > 0) {
            return;
        }
        if (obj instanceof Class || obj instanceof Thread || obj instanceof Throwable
                || obj instanceof android.content.Context) {
            return;
        }
        if (visited.containsKey(obj)) {
            return;
        }
        Class<?> cls = obj.getClass();
        if (cls.isPrimitive() || obj instanceof String || obj instanceof Number
                || obj instanceof Boolean) {
            return;
        }
        visited.put(obj, Boolean.TRUE);

        String cn = cls.getName();
        try {
            if (Class.forName("dalvik.system.DexFile").isInstance(obj)) {
                h.dexFiles.add(obj);
                return;
            }
        } catch (Throwable ignored) {
            if ("dalvik.system.DexFile".equals(cn)) {
                h.dexFiles.add(obj);
                return;
            }
        }
        if ("dalvik.system.DexPathList".equals(cn)) {
            Object elements = getFieldByClassName("dalvik.system.DexPathList", obj, "dexElements");
            harvest(elements, visited, h, depth + 1, "dexElements");
            return;
        }
        if (obj instanceof long[]) {
            // 只收 mCookie / mInternalCookie，避免把任意 long[] 当 DexFile* 解引用
            if (isCookieFieldName(fieldHint) && ((long[]) obj).length >= 2) {
                h.cookies.add(obj);
            }
            return;
        }

        if (cls.isArray()) {
            int n = Array.getLength(obj);
            int cap = Math.min(n, 256);
            for (int i = 0; i < cap; i++) {
                harvest(Array.get(obj, i), visited, h, depth + 1, fieldHint);
            }
            return;
        }
        if (obj instanceof Map) {
            int n = 0;
            for (Object v : ((Map<?, ?>) obj).values()) {
                harvest(v, visited, h, depth + 1, fieldHint);
                if (++n > 256) {
                    break;
                }
            }
            return;
        }
        if (obj instanceof Iterable && !(obj instanceof CharSequence)) {
            int n = 0;
            for (Object v : (Iterable<?>) obj) {
                harvest(v, visited, h, depth + 1, fieldHint);
                if (++n > 256) {
                    break;
                }
            }
            return;
        }

        Class<?> cur = cls;
        int fields = 0;
        while (cur != null && cur != Object.class && fields < 80) {
            Field[] declared;
            try {
                declared = cur.getDeclaredFields();
            } catch (Throwable t) {
                break;
            }
            for (Field f : declared) {
                if (++fields > 80) {
                    break;
                }
                try {
                    Class<?> ft = f.getType();
                    if (ft.isPrimitive()) {
                        continue;
                    }
                    f.setAccessible(true);
                    harvest(f.get(obj), visited, h, depth + 1, f.getName());
                } catch (Throwable ignored) {
                }
            }
            cur = cur.getSuperclass();
        }
    }

    private static void inspectPathList(ClassLoader cl, Object pathList) {
        Object elements = getFieldByClassName("dalvik.system.DexPathList", pathList, "dexElements");
        if (!(elements instanceof Object[])) {
            inspectHarvested(cl);
            return;
        }
        Method dumpMethod = findNativeDumpCode(cl);
        Method getClassNameList = findDexMethod(cl, "getClassNameList");
        if (dumpMethod == null || getClassNameList == null) {
            writeFail("inspect", safeName(cl), "", "dumpMethod/getClassNameList null");
            return;
        }
        Field dexFileField = declaredField("dalvik.system.DexPathList$Element", "dexFile");
        Object[] arr = (Object[]) elements;
        Log.v(TAG, "inspect pathList elements=" + arr.length + " loader=" + safeName(cl));
        for (int j = 0; j < arr.length; j++) {
            Object dexfile = null;
            try {
                if (dexFileField != null) {
                    dexfile = dexFileField.get(arr[j]);
                }
            } catch (Throwable ignored) {
            }
            inspectDexFile(cl, dexfile, dumpMethod, getClassNameList);
        }
    }

    private static void inspectHarvested(ClassLoader cl) {
        Method dumpMethod = findNativeDumpCode(cl);
        Method getClassNameList = findDexMethod(cl, "getClassNameList");
        if (dumpMethod == null || getClassNameList == null) {
            writeFail("inspect", safeName(cl), "", "dumpMethod/getClassNameList null");
            return;
        }
        Harvest h = harvestFrom(cl);
        if (h.dexFiles.isEmpty() && h.cookies.isEmpty()) {
            writeFail("harvest", safeName(cl), "", "no DexFile/cookie");
        }
        for (Object dex : h.dexFiles) {
            inspectDexFile(cl, dex, dumpMethod, getClassNameList);
        }
        for (Object cookie : h.cookies) {
            inspectCookie(cl, cookie, null, dumpMethod, getClassNameList);
        }
    }

    private static void inspectDexFile(ClassLoader cl, Object dexfile, Method dumpMethod,
                                       Method getClassNameList) {
        if (dexfile == null || !isUserDex(dexfile)) {
            return;
        }
        inspectCookie(cl, readDexCookie(cl, dexfile), dexfile, dumpMethod, getClassNameList);
    }

    private static void inspectCookie(ClassLoader cl, Object cookie, Object dexfile,
                                      Method dumpMethod, Method getClassNameList) {
        if (cookie == null) {
            return;
        }
        if (getClassNameList == null || dumpMethod == null) {
            writeFail("inspectCookie", safeName(cl), "", "dumpMethod/getClassNameList null");
            return;
        }
        String[] classnames;
        try {
            getClassNameList.setAccessible(true);
            classnames = (String[]) getClassNameList.invoke(null, cookie);
        } catch (Throwable t) {
            writeFail("getClassNameList", safeName(cl), "", t);
            return;
        }
        if (classnames == null) {
            writeFail("getClassNameList", safeName(cl), "", "null class list");
            return;
        }
        // 外部类先于内部类，defineClass 才找得到 $1 / $1$1。
        Arrays.sort(classnames, new Comparator<String>() {
            @Override
            public int compare(String a, String b) {
                int da = dollarCount(a);
                int db = dollarCount(b);
                if (da != db) {
                    return da - db;
                }
                return a.compareTo(b);
            }
        });
        ArrayList<String> failed = new ArrayList<String>();
        for (int i = 0; i < classnames.length; i++) {
            if (!dispatchClassTask(cl, classnames[i], dumpMethod, dexfile, cookie)) {
                failed.add(classnames[i]);
            }
        }
        for (int pass = 0; pass < 2 && !failed.isEmpty(); pass++) {
            ArrayList<String> still = new ArrayList<String>();
            for (int i = 0; i < failed.size(); i++) {
                String name = failed.get(i);
                if (dispatchClassTask(cl, name, dumpMethod, dexfile, cookie)) {
                    sInspectRetryOk++;
                } else {
                    still.add(name);
                }
            }
            failed = still;
        }
        for (int i = 0; i < failed.size(); i++) {
            sPendingFail.add(new InspectFail(cl, failed.get(i), dumpMethod, dexfile, cookie));
        }
    }

    private static void retryPendingFails() {
        for (int pass = 0; pass < 2 && !sPendingFail.isEmpty(); pass++) {
            ArrayList<InspectFail> still = new ArrayList<InspectFail>();
            for (int i = 0; i < sPendingFail.size(); i++) {
                InspectFail p = sPendingFail.get(i);
                if (dispatchClassTask(p.cl, p.name, p.dumpMethod, p.dexfile, p.cookie)) {
                    sInspectRetryOk++;
                } else {
                    still.add(p);
                }
            }
            sPendingFail.clear();
            sPendingFail.addAll(still);
        }
        for (int i = 0; i < sPendingFail.size(); i++) {
            InspectFail p = sPendingFail.get(i);
            sInspectFail++;
            try {
                loadInspectClass(p.cl, p.name, p.dexfile, p.cookie);
                writeFail("loadClass", safeName(p.cl), p.name,
                        "null class after DexFile.defineClass+retry");
            } catch (Throwable t) {
                writeFail("loadClass", safeName(p.cl), p.name, t);
            }
        }
        sPendingFail.clear();
    }

    private static int dollarCount(String name) {
        int n = 0;
        for (int i = 0; i < name.length(); i++) {
            if (name.charAt(i) == '$') {
                n++;
            }
        }
        return n;
    }

    //add
    /**
     * 优先对该 DEX 调 DexFile.loadClass / defineClassNative（与
     * PathClassLoader.findClass → DexPathList → loadClassBinaryName 同一条
     * defineClassNative）。AOSP 对 PathClassLoader 的 Class.forName 也会先走
     * ClassLinker::FindClass → 同一 DefineClass。
     * 单独再调一次只对「不在 pathList 上的 harvested cookie」有意义；
     * 父类/接口缺失时两边一样失败。init_classes 时再 forName 跑 clinit。
     */
    static Class<?> loadInspectClass(ClassLoader cl, String name) throws ClassNotFoundException {
        return loadInspectClass(cl, name, null, null);
    }

    static Class<?> loadInspectClass(ClassLoader cl, String name, Object dexfile, Object cookie)
            throws ClassNotFoundException {
        if (name != null) {
            name = name.replace('/', '.');
        }
        Class<?> defined = defineFromDex(cl, name, dexfile, cookie);
        if (defined != null) {
            sInspectDefined++;
            if (Cyrus.shouldInitClasses()) {
                try {
                    Class.forName(defined.getName(), true, cl);
                } catch (Throwable ignored) {
                }
            }
            return defined;
        }
        if (Cyrus.shouldInitClasses()) {
            return Class.forName(name, true, cl);
        }
        return cl.loadClass(name);
    }

    private static Class<?> defineFromDex(ClassLoader cl, String name, Object dexfile,
                                          Object cookie) {
        if (dexfile != null) {
            try {
                Method load = dexfile.getClass().getMethod(
                        "loadClass", String.class, ClassLoader.class);
                Object ret = load.invoke(dexfile, name, cl);
                if (ret instanceof Class) {
                    return (Class<?>) ret;
                }
            } catch (Throwable ignored) {
            }
        }
        if (cookie != null) {
            try {
                Class<?> dexClz = Class.forName("dalvik.system.DexFile");
                Method def = dexClz.getDeclaredMethod(
                        "defineClassNative",
                        String.class, ClassLoader.class, Object.class, dexClz);
                def.setAccessible(true);
                Object ret = def.invoke(null, name.replace('.', '/'), cl, cookie, dexfile);
                if (ret instanceof Class) {
                    return (Class<?>) ret;
                }
            } catch (Throwable ignored) {
            }
        }
        return null;
    }
    //add end

    //add
    /**
     * Append (not prepend) a stub DEX so missing super/iface type_ids can
     * resolve. App class_defs stay first; stub types are only the ones dump
     * DEX never defined. Not PRE bytecode.
     */
    static void installLinkStubsOn(ClassLoader cl) {
        installLinkStubs(cl);
    }

    private static void installLinkStubs(ClassLoader cl) {
        if (cl == null || !Cyrus.isDumpEnabled() || isBootClassLoader(cl)
                || sLinkStubInstalled.containsKey(cl)) {
            return;
        }
        String path = Cyrus.getLinkStubsPath();
        File f = new File(path);
        if (!f.isFile()) {
            return;
        }
        try {
            PathClassLoader stub = new PathClassLoader(path, cl.getParent());
            Object appList = getFieldByClassName("dalvik.system.BaseDexClassLoader", cl, "pathList");
            Object stubList = getFieldByClassName("dalvik.system.BaseDexClassLoader", stub, "pathList");
            if (appList == null || stubList == null) {
                Log.w(TAG, "link_stubs pathList missing loader=" + safeName(cl));
                return;
            }
            Object appEls = getFieldByClassName("dalvik.system.DexPathList", appList, "dexElements");
            Object stubEls = getFieldByClassName("dalvik.system.DexPathList", stubList, "dexElements");
            if (!(appEls instanceof Object[]) || !(stubEls instanceof Object[])) {
                return;
            }
            Object[] a = (Object[]) appEls;
            Object[] s = (Object[]) stubEls;
            if (s.length == 0) {
                return;
            }
            if (alreadyHasStubPath(a, path)) {
                sLinkStubInstalled.put(cl, Boolean.TRUE);
                return;
            }
            Object[] merged = (Object[]) Array.newInstance(a.getClass().getComponentType(), a.length + s.length);
            System.arraycopy(a, 0, merged, 0, a.length);
            System.arraycopy(s, 0, merged, a.length, s.length);
            Field els = declaredField("dalvik.system.DexPathList", "dexElements");
            if (els == null) {
                return;
            }
            els.set(appList, merged);
            sLinkStubInstalled.put(cl, Boolean.TRUE);
            Log.e(TAG, "link_stubs appended " + path + " elements=" + s.length
                    + " loader=" + safeName(cl));
        } catch (Throwable t) {
            Log.e(TAG, "link_stubs failed: " + t);
        }
    }

    private static boolean alreadyHasStubPath(Object[] elements, String stubPath) {
        Field dexFileField = declaredField("dalvik.system.DexPathList$Element", "dexFile");
        if (dexFileField == null || stubPath == null) {
            return false;
        }
        for (int i = 0; i < elements.length; i++) {
            try {
                Object df = dexFileField.get(elements[i]);
                if (df == null) {
                    continue;
                }
                Field nf = df.getClass().getDeclaredField("mFileName");
                nf.setAccessible(true);
                String n = (String) nf.get(df);
                if (stubPath.equals(n)) {
                    return true;
                }
            } catch (Throwable ignored) {
            }
        }
        return false;
    }

    private static void executeThenDump(Class<?> cls, Method dumpMethod) {
        Object inst = tryAllocInstance(cls);
        try {
            Constructor<?>[] cons = cls.getDeclaredConstructors();
            for (int i = 0; i < cons.length; i++) {
                try {
                    dumpMethod.invoke(null, cons[i]);
                } catch (Throwable ignored) {
                }
            }
        } catch (Throwable ignored) {
        }
        try {
            Method[] methods = cls.getDeclaredMethods();
            if (methods == null) {
                return;
            }
            for (int i = 0; i < methods.length; i++) {
                Method m = methods[i];
                try {
                    m.setAccessible(true);
                    Object[] args = defaultArgs(m.getParameterTypes());
                    if ((m.getModifiers() & Modifier.STATIC) != 0) {
                        m.invoke(null, args);
                    } else if (inst != null) {
                        m.invoke(inst, args);
                    }
                } catch (Throwable ignored) {
                }
                try {
                    dumpMethod.invoke(null, m);
                } catch (Throwable ignored) {
                }
            }
        } catch (Throwable ignored) {
        }
        if (sDumpClinit != null) {
            try {
                sDumpClinit.invoke(null, cls);
            } catch (Throwable ignored) {
            }
        }
    }

    /**
     * Inner/anonymous classes need an outer instance; dummy ctor often fails.
     * Allocate without &lt;init&gt; so instance methods can still be invoked
     * (packer decrypts on Invoke, even if the call then NPEs).
     */
    private static Object tryAllocInstance(Class<?> cls) {
        int mods = cls.getModifiers();
        if ((mods & Modifier.INTERFACE) != 0 || (mods & Modifier.ABSTRACT) != 0) {
            return null;
        }
        try {
            Constructor<?>[] cons = cls.getDeclaredConstructors();
            for (int i = 0; i < cons.length; i++) {
                Constructor<?> c = cons[i];
                try {
                    c.setAccessible(true);
                    Object inst = c.newInstance(defaultArgs(c.getParameterTypes()));
                    if (inst != null) {
                        return inst;
                    }
                } catch (Throwable ignored) {
                }
            }
        } catch (Throwable ignored) {
        }
        try {
            Class<?> u = Class.forName("sun.misc.Unsafe");
            Object unsafe = null;
            String[] fields = new String[] {"THE_ONE", "theUnsafe"};
            for (int i = 0; i < fields.length && unsafe == null; i++) {
                try {
                    Field f = u.getDeclaredField(fields[i]);
                    f.setAccessible(true);
                    unsafe = f.get(null);
                } catch (Throwable ignored) {
                }
            }
            if (unsafe == null) {
                return null;
            }
            Method alloc = u.getMethod("allocateInstance", Class.class);
            return alloc.invoke(unsafe, cls);
        } catch (Throwable ignored) {
            return null;
        }
    }

    private static Object[] defaultArgs(Class<?>[] types) {
        Object[] args = new Object[types.length];
        for (int i = 0; i < types.length; i++) {
            Class<?> t = types[i];
            if (t == boolean.class) {
                args[i] = Boolean.FALSE;
            } else if (t == byte.class) {
                args[i] = Byte.valueOf((byte) 0);
            } else if (t == short.class) {
                args[i] = Short.valueOf((short) 0);
            } else if (t == int.class) {
                args[i] = Integer.valueOf(0);
            } else if (t == long.class) {
                args[i] = Long.valueOf(0L);
            } else if (t == float.class) {
                args[i] = Float.valueOf(0f);
            } else if (t == double.class) {
                args[i] = Double.valueOf(0d);
            } else if (t == char.class) {
                args[i] = Character.valueOf((char) 0);
            } else if (t == android.content.Context.class) {
                try {
                    args[i] = ActivityThread.currentApplication();
                } catch (Throwable ignored) {
                    args[i] = null;
                }
            } else {
                args[i] = null;
            }
        }
        return args;
    }
    //add end

    private static boolean dispatchClassTask(ClassLoader cl, String eachclassname, Method dumpMethod,
                                             Object dexfile, Object cookie) {
        if (!Cyrus.shouldForceCall(eachclassname)) {
            return true;
        }
        Class<?> resultclass;
        try {
            resultclass = loadInspectClass(cl, eachclassname, dexfile, cookie);
        } catch (Throwable t) {
            return false;
        }
        if (resultclass == null) {
            return false;
        }
        sInspectOk++;
        try {
            Constructor<?>[] cons = resultclass.getDeclaredConstructors();
            for (Constructor<?> c : cons) {
                try {
                    dumpMethod.invoke(null, c);
                } catch (Throwable ignored) {
                }
            }
        } catch (Throwable ignored) {
        }
        try {
            Method[] methods = resultclass.getDeclaredMethods();
            if (methods != null) {
                for (Method m : methods) {
                    try {
                        dumpMethod.invoke(null, m);
                    } catch (Throwable ignored) {
                    }
                }
            }
        } catch (Throwable ignored) {
        }
        // getDeclaredMethods 没有 <clinit>；AOSP 用 FindClassInitializer。
        if (sDumpClinit != null) {
            try {
                sDumpClinit.invoke(null, resultclass);
            } catch (Throwable ignored) {
            }
        }
        if (Cyrus.shouldExecute(eachclassname)) {
            executeThenDump(resultclass, dumpMethod);
        }
        return true;
    }

    static boolean isUserDex(Object dexFile) {
        if (dexFile == null) {
            return false;
        }
        try {
            Field nameField = dexFile.getClass().getDeclaredField("mFileName");
            nameField.setAccessible(true);
            String fileName = (String) nameField.get(dexFile);
            if (fileName == null || fileName.length() == 0) {
                return true;
            }
            // 只丢掉系统 DEX。壳/原包/加密/内存/自定义/动态全部保留。
            if (fileName.startsWith("/system/") ||
                    fileName.startsWith("/system_ext/") ||
                    fileName.startsWith("/apex/") ||
                    fileName.startsWith("/vendor/") ||
                    fileName.startsWith("/product/") ||
                    fileName.startsWith("/framework/") ||
                    fileName.startsWith("/data/dalvik-cache/") ||
                    fileName.startsWith("/data/misc/")) {
                return false;
            }
            if (fileName.indexOf("/apex/") >= 0 ||
                    fileName.indexOf("/system/framework/") >= 0 ||
                    fileName.indexOf("boot.oat") >= 0) {
                return false;
            }
            String stubPath = Cyrus.getLinkStubsPath();
            if (stubPath.length() > 0 && stubPath.equals(fileName)) {
                return false;
            }
            if (fileName.indexOf("fart_link_stubs") >= 0) {
                return false;
            }
            return true;
        } catch (Exception e) {
            Log.w(TAG, "isUserDex failed", e);
            return true;
        }
    }

    private static Method findNativeDumpCode(ClassLoader cl) {
        Method m = findDexMethod(cl, "nativeDumpCode");
        if (m == null) {
            m = findDexMethod(cl, "dumpMethodCode");
        }
        return m;
    }

    private static Method findDexMethod(ClassLoader cl, String name) {
        Class<?> dex = null;
        try {
            dex = Class.forName("dalvik.system.DexFile");
        } catch (Throwable ignored) {
        }
        if (dex == null && cl != null) {
            try {
                dex = cl.loadClass("dalvik.system.DexFile");
            } catch (Throwable ignored) {
            }
        }
        if (dex == null) {
            writeFail("findDexMethod", safeName(cl), name, "DexFile class missing");
            return null;
        }
        try {
            for (Method m : dex.getDeclaredMethods()) {
                if (name.equals(m.getName())) {
                    m.setAccessible(true);
                    return m;
                }
            }
        } catch (Throwable t) {
            writeFail("findDexMethod", safeName(cl), name, t);
        }
        return null;
    }

    private static Object invokeDexNative(String methodName, Class<?>[] types, Object... args) {
        try {
            Class<?> dexFileClazz = Class.forName("dalvik.system.DexFile");
            Method m = dexFileClazz.getDeclaredMethod(methodName, types);
            m.setAccessible(true);
            return m.invoke(null, args);
        } catch (Throwable t) {
            Log.e(TAG, "DexFile." + methodName + " failed: " + t);
            return null;
        }
    }

    private static Object getFieldByClassName(String className, Object obj, String fieldName) {
        if (obj == null) {
            return null;
        }
        try {
            Field f = Class.forName(className).getDeclaredField(fieldName);
            f.setAccessible(true);
            return f.get(obj);
        } catch (Throwable t) {
            return null;
        }
    }

    private static Object getInstanceField(Object obj, String fieldName) {
        if (obj == null) {
            return null;
        }
        Class<?> c = obj.getClass();
        while (c != null && c != Object.class) {
            try {
                Field f = c.getDeclaredField(fieldName);
                f.setAccessible(true);
                return f.get(obj);
            } catch (NoSuchFieldException e) {
                c = c.getSuperclass();
            } catch (Throwable t) {
                return null;
            }
        }
        return null;
    }

    private static Object extractField(ClassLoader cl, String className, Object obj, String field) {
        try {
            Class<?> c = cl.loadClass(className);
            Field f = c.getDeclaredField(field);
            f.setAccessible(true);
            return f.get(obj);
        } catch (Throwable t) {
            return null;
        }
    }

    private static Field declaredField(String className, String fieldName) {
        try {
            Field f = Class.forName(className).getDeclaredField(fieldName);
            f.setAccessible(true);
            return f;
        } catch (Throwable t) {
            return null;
        }
    }

    private static String safeName(ClassLoader cl) {
        try {
            return String.valueOf(cl);
        } catch (Throwable t) {
            return "ClassLoader";
        }
    }

    private static final class InspectFail {
        final ClassLoader cl;
        final String name;
        final Method dumpMethod;
        final Object dexfile;
        final Object cookie;

        InspectFail(ClassLoader cl, String name, Method dumpMethod, Object dexfile, Object cookie) {
            this.cl = cl;
            this.name = name;
            this.dumpMethod = dumpMethod;
            this.dexfile = dexfile;
            this.cookie = cookie;
        }
    }

    private static FileWriter sFailLog;
    private static int sInspectOk;
    private static int sInspectFail;
    private static int sInspectDefined;
    private static int sInspectRetryOk;
    private static Method sDumpClinit;
    private static final ArrayList<InspectFail> sPendingFail = new ArrayList<InspectFail>();

    private static void beginFailLog() {
        sFailLog = null;
        sInspectOk = 0;
        sInspectFail = 0;
        sInspectDefined = 0;
        sInspectRetryOk = 0;
        sDumpClinit = findDexMethod(null, "nativeDumpClassInitializer");
        sPendingFail.clear();
        try {
            String pkg = Cyrus.getPackageName();
            if (pkg == null || pkg.length() == 0) {
                return;
            }
            File dir = new File("/data/data/" + pkg + "/cyrus_" + pkg);
            if (!dir.exists() && !dir.mkdirs()) {
                return;
            }
            sFailLog = new FileWriter(new File(dir, "inspect_fail.txt"), false);
        } catch (Throwable t) {
            sFailLog = null;
        }
    }

    private static void endFailLog() {
        try {
            String pkg = Cyrus.getPackageName();
            if (pkg != null && pkg.length() > 0) {
                File dir = new File("/data/data/" + pkg + "/cyrus_" + pkg);
                if (dir.exists() || dir.mkdirs()) {
                    FileWriter sw = new FileWriter(new File(dir, "inspect_stats.txt"), false);
                    try {
                        sw.write("loaded=" + sInspectOk + "\n");
                        sw.write("failed=" + sInspectFail + "\n");
                        sw.write("defined=" + sInspectDefined + "\n");
                        sw.write("retry_ok=" + sInspectRetryOk + "\n");
                        sw.write("init_classes=" + Cyrus.shouldInitClasses() + "\n");
                    } finally {
                        sw.close();
                    }
                }
            }
        } catch (Throwable ignored) {
        }
        if (sFailLog != null) {
            try {
                sFailLog.close();
            } catch (Throwable ignored) {
            }
            sFailLog = null;
        }
    }

    private static void writeFail(String op, String loader, String cls, Throwable t) {
        writeFail(op, loader, cls, formatThrowable(t));
    }

    /**
     * AOSP DexFile.defineClass 会吞掉 NCDFE/CNFE；BaseDexClassLoader.findClass
     * 再抛「Didn't find class on path」，真因在 cause / suppressed / CNFE.ex。
     * Class.forName 的 native 包装用 CNFE(name, cause)，getMessage 只有类名。
     */
    private static String formatThrowable(Throwable t) {
        if (t == null) {
            return "";
        }
        StringBuilder sb = new StringBuilder();
        Throwable cur = t;
        int depth = 0;
        while (cur != null && depth < 6) {
            if (depth > 0) {
                sb.append(" <= ");
            }
            sb.append(cur.getClass().getName()).append(": ").append(cur.getMessage());
            Throwable[] supp = cur.getSuppressed();
            if (supp != null) {
                int n = supp.length < 4 ? supp.length : 4;
                for (int i = 0; i < n; i++) {
                    if (supp[i] != null) {
                        sb.append(" |suppressed ").append(supp[i].getClass().getName())
                                .append(": ").append(supp[i].getMessage());
                    }
                }
            }
            if (cur instanceof ClassNotFoundException) {
                Throwable legacy = ((ClassNotFoundException) cur).getException();
                Throwable cause = cur.getCause();
                if (legacy != null && legacy != cause) {
                    sb.append(" |legacy ").append(legacy.getClass().getName())
                            .append(": ").append(legacy.getMessage());
                }
            }
            cur = cur.getCause();
            depth++;
        }
        return sb.toString();
    }

    private static void writeFail(String op, String loader, String cls, String msg) {
        Log.w(TAG, op + " " + cls + " -> " + msg);
        if (sFailLog == null) {
            return;
        }
        try {
            sFailLog.write(op + "\t" + loader + "\t" + cls + "\t" + msg + "\n");
            sFailLog.flush();
        } catch (Throwable ignored) {
        }
    }

    private static void writeLoaderList(List<ClassLoader> loaders, String phase) {
        try {
            String pkg = Cyrus.getPackageName();
            if (pkg == null || pkg.length() == 0) {
                return;
            }
            File dir = new File("/data/data/" + pkg + "/cyrus_" + pkg);
            if (!dir.exists() && !dir.mkdirs()) {
                return;
            }
            File out = new File(dir, "loaders_" + phase + ".txt");
            FileWriter fw = new FileWriter(out, false);
            try {
                for (int i = 0; i < loaders.size(); i++) {
                    ClassLoader cl = loaders.get(i);
                    fw.write(i + "\t" + classifyLoaderKind(cl, i == 0) + "\t"
                            + (isBaseDexClassLoader(cl) ? "base-dex" : "custom") + "\t"
                            + safeName(cl) + "\n");
                }
            } finally {
                fw.close();
            }
        } catch (Throwable t) {
            Log.w(TAG, "writeLoaderList failed: " + t);
        }
    }
}
//add end

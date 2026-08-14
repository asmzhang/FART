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
import java.util.ArrayList;
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
        } catch (Throwable t) {
            Log.e(TAG, "registerAll failed phase=" + phase + " : " + t);
        }
    }

    /** 对已发现的每个 ClassLoader 做主动调用；自定义 CL 走字段收获，避免 pathList NPE。 */
    static void inspectAll() {
        beginFailLog();
        try {
            List<ClassLoader> loaders = discoverAppClassLoaders(true);
            for (ClassLoader cl : loaders) {
                inspectClassLoader(cl);
            }
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
            inspectCookie(cl, cookie, dumpMethod, getClassNameList);
        }
    }

    private static void inspectDexFile(ClassLoader cl, Object dexfile, Method dumpMethod,
                                       Method getClassNameList) {
        if (dexfile == null || !isUserDex(dexfile)) {
            return;
        }
        inspectCookie(cl, readDexCookie(cl, dexfile), dumpMethod, getClassNameList);
    }

    private static void inspectCookie(ClassLoader cl, Object cookie, Method dumpMethod,
                                      Method getClassNameList) {
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
        for (String name : classnames) {
            dispatchClassTask(cl, name, dumpMethod);
        }
    }

    //add
    /**
     * loadClass 只链接；forName(..., true) 才会跑 clinit，Invoke 退出才能抓到解密体。
     */
    static Class<?> loadInspectClass(ClassLoader cl, String name) throws ClassNotFoundException {
        if (Cyrus.shouldInitClasses()) {
            return Class.forName(name, true, cl);
        }
        return cl.loadClass(name);
    }
    //add end

    private static void dispatchClassTask(ClassLoader cl, String eachclassname, Method dumpMethod) {
        if (!Cyrus.shouldForceCall(eachclassname)) {
            return;
        }
        Class<?> resultclass;
        try {
            resultclass = loadInspectClass(cl, eachclassname);
            sInspectOk++;
        } catch (Throwable t) {
            sInspectFail++;
            writeFail("loadClass", safeName(cl), eachclassname, t);
            return;
        }
        if (resultclass == null) {
            return;
        }
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

    private static FileWriter sFailLog;
    private static int sInspectOk;
    private static int sInspectFail;

    private static void beginFailLog() {
        sFailLog = null;
        sInspectOk = 0;
        sInspectFail = 0;
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
        String msg = t == null ? "" : (t.getClass().getName() + ": " + t.getMessage());
        writeFail(op, loader, cls, msg);
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

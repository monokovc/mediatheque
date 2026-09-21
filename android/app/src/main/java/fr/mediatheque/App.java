package fr.mediatheque;

import android.app.Application;
import android.util.Log;

import com.chaquo.python.PyObject;
import com.chaquo.python.Python;
import com.chaquo.python.android.AndroidPlatform;

public class App extends Application {
    public static volatile boolean serverStarted = false;
    public static volatile int serverPort = 0;
    public static volatile String serverError = null;

    @Override
    public void onCreate() {
        super.onCreate();
        new Thread(() -> {
            try {
                if (!Python.isStarted()) Python.start(new AndroidPlatform(this));
                Python py = Python.getInstance();
                PyObject os = py.getModule("os");
                PyObject environ = os.get("environ");
                environ.callAttr("__setitem__", "MEDIATHEQUE_EMBEDDED", "1");
                environ.callAttr("__setitem__", "MEDIATHEQUE_DATA",
                        getExternalFilesDir(null) != null
                                ? getExternalFilesDir(null).getAbsolutePath()
                                : getFilesDir().getAbsolutePath());
                PyObject port = py.getModule("mediatheque").callAttr("start_embedded");
                serverPort = port.toInt();
                serverStarted = true;
            } catch (Throwable t) {
                Log.e("Mediatheque", "Erreur serveur", t);
                serverError = t.toString();
            }
        }, "mediatheque-server").start();
    }
}

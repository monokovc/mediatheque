package fr.mediatheque;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.AlertDialog;
import android.content.ActivityNotFoundException;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.net.Uri;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.provider.Settings;
import android.view.View;
import android.webkit.JavascriptInterface;
import android.webkit.WebChromeClient;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.TextView;
import android.widget.Toast;

import androidx.appcompat.app.AppCompatActivity;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.core.content.FileProvider;

import java.io.File;
import java.net.Socket;

public class MainActivity extends AppCompatActivity {
    private static final String URL = "http://127.0.0.1:8765/";
    private WebView web;
    private TextView loading;
    private final Handler handler = new Handler(Looper.getMainLooper());
    private boolean loaded = false;

    @SuppressLint("SetJavaScriptEnabled")
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.activity_main);
        web = findViewById(R.id.web);
        loading = findViewById(R.id.loading);

        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setAllowFileAccess(true);
        s.setMixedContentMode(WebSettings.MIXED_CONTENT_ALWAYS_ALLOW);
        s.setCacheMode(WebSettings.LOAD_DEFAULT);
        web.setBackgroundColor(0xFF0F1115);
        web.setWebViewClient(new WebViewClient());
        web.setWebChromeClient(new WebChromeClient());
        web.addJavascriptInterface(new Bridge(), "Android");

        askStoragePermission();
        waitForServer();
    }

    private void waitForServer() {
        handler.postDelayed(() -> {
            if (App.serverError != null) {
                loading.setText("Erreur : " + App.serverError);
                return;
            }
            boolean up = false;
            try (Socket sock = new Socket("127.0.0.1", 8765)) { up = true; } catch (Exception ignored) {}
            if (up) {
                loading.setVisibility(View.GONE);
                if (!loaded) { loaded = true; web.loadUrl(URL); }
            } else {
                waitForServer();
            }
        }, 400);
    }

    private void askStoragePermission() {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            if (!Environment.isExternalStorageManager()) {
                new AlertDialog.Builder(this)
                        .setTitle(R.string.perm_title)
                        .setMessage(R.string.perm_text)
                        .setPositiveButton(R.string.ok, (d, w) -> {
                            try {
                                Intent i = new Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION,
                                        Uri.parse("package:" + getPackageName()));
                                startActivity(i);
                            } catch (Exception e) {
                                startActivity(new Intent(Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION));
                            }
                        })
                        .setCancelable(false)
                        .show();
            }
        } else if (ContextCompat.checkSelfPermission(this, Manifest.permission.READ_EXTERNAL_STORAGE)
                != PackageManager.PERMISSION_GRANTED) {
            ActivityCompat.requestPermissions(this,
                    new String[]{Manifest.permission.READ_EXTERNAL_STORAGE}, 1);
        }
    }

    @Override
    protected void onResume() {
        super.onResume();
        // apres avoir donne l'acces au stockage : rescanner
        if (loaded) web.evaluateJavascript("fetch('/api/rescan').then(()=>setTimeout(()=>location.reload(),1500))", null);
    }

    @Override
    public void onBackPressed() {
        if (web != null && web.canGoBack()) web.goBack(); else super.onBackPressed();
    }

    class Bridge {
        @JavascriptInterface
        public void play(String path, String name) {
            runOnUiThread(() -> openWithPlayer(path));
        }

        @JavascriptInterface
        public String platform() { return "android-apk"; }
    }

    private void openWithPlayer(String path) {
        try {
            File f = new File(path);
            Uri uri = FileProvider.getUriForFile(this, getPackageName() + ".files", f);
            Intent i = new Intent(Intent.ACTION_VIEW);
            i.setDataAndType(uri, "video/*");
            i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
            // VLC en priorite s'il est installe
            Intent vlc = new Intent(i);
            vlc.setPackage("org.videolan.vlc");
            if (vlc.resolveActivity(getPackageManager()) != null) {
                startActivity(vlc);
            } else {
                startActivity(Intent.createChooser(i, "Lire avec"));
            }
        } catch (ActivityNotFoundException e) {
            Toast.makeText(this, "Aucun lecteur vidéo trouvé : installe VLC", Toast.LENGTH_LONG).show();
        } catch (Exception e) {
            Toast.makeText(this, "Impossible d'ouvrir : " + e.getMessage(), Toast.LENGTH_LONG).show();
        }
    }
}

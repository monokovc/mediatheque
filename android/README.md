# Mediatheque — appli Android

Ce dossier contient tout ce qu'il faut pour fabriquer l'APK Android de la Médiathèque.
Le fichier `.github/workflows/build.yml` construit l'APK automatiquement sur GitHub.

Étapes (une seule fois) :
1. Crée un compte sur github.com (gratuit).
2. Crée un nouveau dépôt (New repository), nom : `mediatheque`, laisse "Public", clique Create.
3. Sur la page du dépôt : "uploading an existing file" → glisse TOUT le contenu de ce dossier
   (y compris le dossier caché `.github`) → "Commit changes".
4. Onglet "Actions" : la construction démarre (≈ 5-10 min).
5. Quand c'est vert, onglet "Releases" (ou "Code" → Releases à droite) : télécharge `Mediatheque.apk`
   depuis le téléphone et installe-le (autorise "sources inconnues" si demandé).

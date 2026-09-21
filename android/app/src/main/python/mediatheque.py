# -*- coding: utf-8 -*-
"""
Mediatheque - serveur de bibliotheque video pour disque externe.

  Double-clique sur Mediatheque.pyw : l'application s'ouvre dans sa propre
  fenetre. Elle surveille les disques, scanne les videos, les classe en
  Animes / Films / Series / Autres, regroupe saisons et episodes et fabrique
  des miniatures. Depuis un telephone, une tablette ou une tele du meme
  Wi-Fi, ouvre l'adresse affichee dans l'appli : aucune installation.

Aucune bibliotheque Python a installer. ffmpeg est optionnel.
"""

import os
import re
import sys
import json
import time
import string
import socket
import hashlib
import threading
import subprocess
import mimetypes
import webbrowser
import zipfile
import traceback
import urllib.request
from urllib.parse import urlparse, parse_qs, quote, unquote
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

PORT = 8765
ANDROID = os.path.isdir("/data/data/com.termux") or "ANDROID_ROOT" in os.environ
EMBEDDED = bool(os.environ.get("MEDIATHEQUE_EMBEDDED"))     # lance depuis l'appli Android (APK)
IOS = sys.platform == "darwin" and os.path.isdir(os.path.expanduser("~/Documents")) and "a-Shell" in os.path.expanduser("~")
APP_DIR = os.path.dirname(os.path.abspath(sys.argv[0])) if sys.argv and sys.argv[0] else os.getcwd()
DATA_DIR = os.environ.get("MEDIATHEQUE_DATA") or os.path.join(APP_DIR, "mediatheque-data")
THUMB_DIR = os.path.join(DATA_DIR, "miniatures")
LIB_FILE = os.path.join(DATA_DIR, "bibliotheque.json")

VIDEO_EXT = {".mkv", ".mp4", ".avi", ".m4v", ".mov", ".wmv", ".flv", ".webm",
             ".mpg", ".mpeg", ".m2ts", ".ts", ".ogv", ".rmvb", ".divx", ".vob"}

IGNORED_DIRS = {"$recycle.bin", "system volume information", "windows",
                "program files", "program files (x86)", "programdata",
                "appdata", "recovery", "msocache", "node_modules", "mediatheque-data"}

MIN_MEDIA_SIZE = 150 * 1024 * 1024     # en dessous -> "Autres" (sauf si episode)
MIN_KEEP_SIZE = 5 * 1024 * 1024        # en dessous -> ignore
THUMB_W, THUMB_H = 320, 180
CATEGORIES = ["Animes", "Films", "Series", "Autres"]

# --------------------------------------------------------------------------
# Analyse des noms
# --------------------------------------------------------------------------

RE_SEASON_EP = [
    re.compile(r"[sS](\d{1,2})[\s._\-]*[eE](\d{1,3})(?!\d)"),
    re.compile(r"(?<!\d)(\d{1,2})[xX](\d{2,3})(?!\d)"),
    re.compile(r"(?:saison|season)[\s._\-]*(\d{1,2})[\s._\-]*(?:episode|ep|e)[\s._\-]*(\d{1,3})", re.I),
]
RE_EP_ONLY = [
    re.compile(r"(?:^|[\s._\-])(?:episode|episodes|ep|e|#)[\s._\-]?(\d{1,4})(?!\d)", re.I),
    re.compile(r"\s-\s(\d{1,4})(?:v\d)?(?!\d)"),
    re.compile(r"(?:^|[\s._\-])(\d{2,4})(?:v\d)?[\s._\-]*(?:vostfr|vf|final|end|\[|\(|multi|french|$)", re.I),
]
NOT_EPISODE = {1080, 720, 480, 2160, 264, 265, 1440, 4320, 360, 576}
RE_SEASON_FOLDER = re.compile(r"^(?:saison|season|s|staffel|temporada)[\s._\-]*(\d{1,2})\b", re.I)
RE_SEASON_ANY = re.compile(r"(?:saison|season)[\s._\-]*(\d{1,2})(?!\d)", re.I)
RE_YEAR = re.compile(r"[\(\[\s._\-](19\d{2}|20\d{2})[\)\]\s._\-]")

ANIME_WORDS = ["vostfr", "vost fr", "vostf", "sub fr", "subfr", "raws", "raw",
               "ova", "oav", "ona", "wakanim", "crunchyroll", "adn", "anime",
               "animes", "anim\u00e9", "fansub", "subsplease", "erai-raws",
               "horriblesubs", "nyaa", "judas", "ember", "dual audio",
               "vf japonais", "manga", "mangas", "shonen", "seinen"]
SERIE_WORDS = ["saison", "season", "serie", "series", "s\u00e9rie", "integrale",
               "int\u00e9grale", "episode", "staffel"]
FILM_WORDS = ["film", "films", "movie", "movies", "cinema", "cin\u00e9ma", "bluray",
              "truefrench"]
JUNK_TOKENS = ["1080p", "720p", "2160p", "480p", "4k", "uhd", "hdr", "hdr10", "sdr",
               "x264", "x265", "h264", "h265", "hevc", "avc", "xvid", "divx", "av1",
               "bluray", "blu ray", "brrip", "bdrip", "bdremux", "remux", "webrip",
               "web dl", "webdl", "web", "hdlight", "hdrip", "dvdrip", "dvd", "hdtv",
               "aac", "ac3", "dts", "truehd", "atmos", "eac3", "flac", "10bit",
               "8bit", "repack", "proper", "extended", "unrated", "remastered",
               "imax", "vff", "vfq", "vfi", "vf2", "truefrench", "french", "multi",
               "vostfr", "vost", "vf", "vo", "subfrench", "complete", "integrale",
               "custom", "fastsub", "final", "mkv", "mp4", "avi", "anime sama",
               "streaming", "integral", "intégral", "integrale", "intégrale", "v2", "v3"]
RE_BRACKETS = re.compile(r"[\[\(\{][^\]\)\}]*[\]\)\}]")
BONUS_WORDS = {"bonus", "sp", "sps", "special", "specials", "spécial", "spécials", "ova", "ovas",
               "oav", "oavs", "oad", "oads", "pv", "web pv", "nc", "nced", "ncop", "oped", "op ed",
               "opening", "ending", "opening + ending", "opening & ending", "extras", "extra",
               "menu", "autre", "autres", "after talk", "film", "films", "movie", "movies",
               "recap", "récap", "recaps", "revival", "cm", "trailer", "trailers", "clips"}
RE_ROMAN = re.compile(r"^(.*?)[\s\-]+(II|III|IV|V|VI)$", re.I)
ROMAN = {"ii": 2, "iii": 3, "iv": 4, "v": 5, "vi": 6}


def folder_kind(name):
    """Renvoie ('season', n), ('bonus', None), ('part', n) ou None si c'est un vrai titre."""
    n = name.strip().lower()
    n2 = RE_SPACES.sub(" ", RE_BRACKETS.sub(" ", n)).strip()
    if n2 in ("vostfr", "vf", "vo", "multi", "vostfr-vf", "vf-vostfr", "french", "vostfr vf", "sub", "dub"):
        return ("skip", None)
    m = re.fullmatch(r"\d{1,2}\s*[-_.:]+\s*(.+)", n2)      # "01 - Season 1", "02 - OADs"
    if m:
        inner = folder_kind(m.group(1))
        if inner is not None:
            return inner
    first = n2.split(" ")[0]
    if first in BONUS_WORDS and first not in ("cm",) and len(n2.split(" ")) <= 4:
        return ("bonus", None)
    if re.fullmatch(r"\d{1,2}(?:\s*bis)?", n2):
        return ("season", int(re.match(r"\d+", n2).group()))
    m = re.fullmatch(r"(?:s|saison|season|staffel|temporada)\s*0?(\d{1,2})(?:\s*v\d)?", n2)
    if m:
        return ("season", int(m.group(1)))
    m = re.fullmatch(r"(?:part|partie|cour)\s*(\d{1,2})", n2)
    if m:
        return ("part", int(m.group(1)))
    if n2 in BONUS_WORDS or re.fullmatch(r"\d{1,2}\s*(?:oads?|ovas?|sps?|bonus)", n2):
        return ("bonus", None)
    if n2 in ("anime", "animes", "series", "serie", "films", "film", "videos", "video", "tv", ""):
        return ("root", None)
    return None


def folder_title(folder):
    """Remonte les dossiers generiques (S02, Bonus, 3...) jusqu'au vrai titre.
    Renvoie (titre, saison ou None, bonus:bool)."""
    season, bonus = None, False
    cur = folder
    for depth in range(4):
        name = os.path.basename(cur)
        kind = folder_kind(name)
        if kind is None:
            t = clean_title(name)
            m = RE_ROMAN.match(t)
            if m and season is None:
                t, season = m.group(1).strip(), ROMAN[m.group(2).lower()]
            m = RE_SEASON_ANY.search(name)
            if m and season is None:
                season = int(m.group(1))
            m = re.search(r"\s(?:s|saison|season)\s*0?(\d{1,2})(?:\s*v\d)?$", RE_BRACKETS.sub(" ", name).strip(), re.I)
            if m and season is None:
                season = int(m.group(1))
            low = RE_BRACKETS.sub(" ", name).lower()
            if depth == 0:
                for w in ("film", "ova", "oav", "oad", "opening", "ending", "revival", "special", "bonus", "movie"):
                    if re.search(r"\b%s" % w, low) and not re.search(r"\b%s" % w, t.lower()):
                        bonus = True
            return (t if len(t) >= 2 else name, season, bonus)
        if kind[0] == "season" and season is None:
            season = kind[1]
        elif kind[0] == "bonus":
            bonus = True
        elif kind[0] == "skip":
            pass
        elif kind[0] == "root":
            return (clean_title(name), season, bonus)
        cur = os.path.dirname(cur)
    return (clean_title(os.path.basename(folder)), season, bonus)
RE_SPACES = re.compile(r"\s+")


def clean_title(raw):
    name = RE_BRACKETS.sub(" ", raw)
    name = name.replace("_", " ")
    name = re.sub(r"^\s*@\w+\s*", "", name).replace(".", " ").replace("-", " ")
    name = RE_SPACES.sub(" ", name).strip()
    low = " " + name.lower() + " "
    cut = len(name)
    for token in JUNK_TOKENS:
        pos = low.find(" " + token + " ")
        if pos != -1:
            cut = min(cut, pos)
    name = name[:cut].strip()
    m = re.search(r"\b(19\d{2}|20\d{2})\b", name)
    if m and m.start() > 3:
        name = name[:m.start()].strip()
    for rx in RE_SEASON_EP + [RE_SEASON_ANY]:
        m = rx.search(name)
        if m and m.start() > 2:
            name = name[:m.start()].strip()
            break
    m = re.search(r"\s(?:episode|ep|e)\s?\d{1,4}\b", name, re.I)
    if m and m.start() > 2:
        name = name[:m.start()].strip()
    m = re.search(r"\s\d{2,4}$", name)          # "Naruto 045"
    if m and m.start() > 2:
        name = name[:m.start()].strip()
    name = re.sub(r"\s+(?:s|saison|season)\s*\d{1,2}(?:\s*v\d)?$", "", name, flags=re.I)
    name = re.sub(r"\s+(?:s|saison|season)\s*\d{1,2}\s*[+&-].*$", "", name, flags=re.I)
    name = re.sub(r"\s+(?:film|movie|the movie|le film)$", "", name, flags=re.I)
    name = name.strip(" -_,;:+&")
    return (name or raw)[:90]


def analyse(path, size):
    folder, filename = os.path.split(path)
    base = os.path.splitext(filename)[0]
    parent = os.path.basename(folder)
    grand = os.path.basename(os.path.dirname(folder))
    haystack = path.lower().replace("\\", "/")

    season = episode = None
    for rx in RE_SEASON_EP:
        m = rx.search(base)
        if m:
            season, episode = int(m.group(1)), int(m.group(2))
            break
    if episode is None:
        m = re.search(r"\((\d{1,4})\)\s*$", base)
        if m:
            episode = int(m.group(1))
    if episode is None:
        stripped = RE_BRACKETS.sub(" ", base)
        for rx in RE_EP_ONLY:
            m = rx.search(stripped)
            if m and int(m.group(1)) not in NOT_EPISODE and not (1900 <= int(m.group(1)) <= 2099):
                episode = int(m.group(1))
                break

    # saison depuis le dossier "Saison 2" / "S02" / "Season 2"
    season_folder = RE_SEASON_FOLDER.match(parent.strip())
    if season is None:
        if season_folder:
            season = int(season_folder.group(1))
        else:
            m = RE_SEASON_ANY.search(parent) or RE_SEASON_ANY.search(base)
            if m:
                season = int(m.group(1))

    year = None
    m = RE_YEAR.search(" " + base + " ")
    if m:
        year = int(m.group(1))
    if year is None:
        for seg in (parent, grand):
            m = RE_YEAR.search(" " + seg + " ")
            if m:
                year = int(m.group(1))
                break
    hay = " " + re.sub(r"[\[\]\(\)_.\-]", " ", haystack) + " "
    if " multi " in hay or "vf-vostfr" in haystack or "vostfr-vf" in haystack or " vff " in hay or " vfi " in hay:
        lang = "MULTI"
    elif "vostfr" in haystack or " vost " in hay or " sub " in hay or "subfrench" in haystack or " vo " in hay or "eng" in hay and "jpn" in hay:
        lang = "VOSTFR"
    elif " vf " in hay or " french " in hay or "truefrench" in haystack or " vf2 " in hay or " fr " in hay:
        lang = "VF"
    else:
        lang = ""
    if "2160" in haystack or " 4k " in hay or " uhd " in hay:
        quality = "4K"
    elif "1080" in haystack or " fhd " in hay:
        quality = "1080p"
    elif "720" in haystack or " hd " in hay:
        quality = "720p"
    elif "480" in haystack or " sd " in hay or "dvdrip" in haystack:
        quality = "480p"
    else:
        quality = ""

    anime_score = 0
    segments = [x.lower() for x in haystack.split("/")[:-1]]
    for w in ANIME_WORDS:
        if w in haystack:
            anime_score += 2 if any(w in seg for seg in segments) else 1
    if any(seg in ("series", "serie", "séries", "série", "tv") for seg in segments):
        anime_score = 0 if anime_score < 2 else anime_score
    if re.match(r"^\s*\[[^\]]{2,25}\]", base):
        anime_score += 2
    serie_hint = any(w in haystack for w in SERIE_WORDS) or season_folder is not None
    film_hint = any(w in haystack for w in FILM_WORDS)

    forced = None
    forced_idx = -1
    raw_segments = path.replace("\\", "/").split("/")[:-1]
    for idx, seg in enumerate(segments):
        w = seg.strip()
        if w in ("anime", "animes", "animé", "animés", "manga", "mangas", "animation japonaise"):
            forced, forced_idx = "Animes", idx
        elif w in ("film", "films", "movie", "movies", "cinema", "cinéma"):
            if not forced:
                forced, forced_idx = "Films", idx
        elif w in ("serie", "series", "série", "séries", "tv", "tv shows"):
            if not forced:
                forced, forced_idx = "Series", idx
    if forced == "Animes":
        category = "Animes"
    elif forced:
        category = forced if (forced == "Films" and episode is None) else ("Series" if episode is not None else forced)
    elif anime_score >= 2 or (anime_score >= 1 and episode is not None):
        category = "Animes"
    elif episode is not None or serie_hint:
        category = "Series"
    elif size < MIN_MEDIA_SIZE:
        category = "Autres"
    elif year is not None or size >= 700 * 1024 * 1024 or film_hint:
        category = "Films"
    else:
        category = "Autres"

    title = clean_title(base)
    bonus = False
    if category in ("Animes", "Series"):
        ft, fs, fb = folder_title(folder)
        if folder_kind(os.path.basename(folder)) == ("root", None) or ft.lower() in ("anime", "animes", "series", "films"):
            # fichier pose directement a la racine : le nom du fichier fait foi
            m = re.search(r"\bfilm\b", base, re.I)
            bonus = bool(m)
        else:
            title = ft
            bonus = fb
            if season is None:
                season = fs
        rest = RE_BRACKETS.sub(" ", base).replace("_", " ")
        rest = re.sub(re.escape(title), " ", rest, flags=re.I) if len(title) >= 3 else rest
        if bonus or re.search(r"(?:^|[\s\-.])(?:film|movie|ova|oav|oad|special|specials|sp|nced|ncop|pv|menu|bdmenu|recap|r\u00e9cap)(?:\s?\d{1,2})?(?:[\s\-.\[\(]|$)", rest, re.I):
            bonus = True
        if bonus:
            season = 0
        if episode is None:
            episode = 0

    collection = ""
    if forced_idx >= 0 and forced_idx + 1 < len(raw_segments):
        top = raw_segments[forced_idx + 1]
        kind = folder_kind(top)
        if kind is None:
            ct = clean_title(top)
            collection = ct if len(ct) >= 2 else top
    if not collection:
        collection = title
    return {"path": path, "file": filename, "title": title, "category": category,
            "collection": collection,
            "season": season, "episode": episode, "year": year, "size": size,
            "bonus": bonus, "lang": lang, "quality": quality}


# --------------------------------------------------------------------------
# Disques et scan
# --------------------------------------------------------------------------

def drive_info(root):
    """(nom du volume, identifiant stable) pour un lecteur."""
    label, serial = "", ""
    if os.name == "nt":
        try:
            import ctypes
            buf = ctypes.create_unicode_buffer(261)
            fs = ctypes.create_unicode_buffer(261)
            ser = ctypes.c_uint(0)
            if ctypes.windll.kernel32.GetVolumeInformationW(ctypes.c_wchar_p(root), buf, 261,
                                                            ctypes.byref(ser), None, None, fs, 261):
                label, serial = buf.value, "%08X" % ser.value
        except Exception:
            pass
    if not label:
        label = os.path.basename(root.rstrip("/\\")) or root.rstrip("\\")
    if not serial:
        serial = hashlib.md5(root.encode("utf-8")).hexdigest()[:8]
    return label, serial


EXTRA_ROOTS_FILE = os.path.join(DATA_DIR, "dossiers.json")


def extra_roots():
    try:
        with open(EXTRA_ROOTS_FILE, "r", encoding="utf-8") as f:
            return [r for r in json.load(f) if isinstance(r, str)]
    except Exception:
        return []


def list_drives():
    found = [r for r in extra_roots() if os.path.isdir(r)]
    if os.name == "nt":
        try:
            import ctypes
            mask = ctypes.windll.kernel32.GetLogicalDrives()
            system = (os.environ.get("SystemDrive", "C:") + "\\").upper()
            for i, letter in enumerate(string.ascii_uppercase):
                if (mask >> i) & 1:
                    root = letter + ":\\"
                    dtype = ctypes.windll.kernel32.GetDriveTypeW(ctypes.c_wchar_p(root))
                    if dtype in (2, 3) and root.upper() != system:
                        found.append(root)
        except Exception:
            pass
    elif ANDROID:
        for base in ("/storage",):
            if os.path.isdir(base):
                for entry in os.listdir(base):
                    if entry in ("emulated", "self"):
                        continue
                    p = os.path.join(base, entry)
                    if os.path.isdir(p) and os.access(p, os.R_OK):
                        found.append(p)          # disque USB / carte SD
        for p in ("/storage/emulated/0/Movies", "/storage/emulated/0/Download", "/storage/emulated/0/DCIM"):
            if os.path.isdir(p):
                found.append(p)
    else:
        for base in ("/media", "/run/media", "/Volumes", "/mnt"):
            if os.path.isdir(base):
                for entry in os.listdir(base):
                    p = os.path.join(base, entry)
                    if os.path.isdir(p):
                        found.append(p)
                        if base == "/run/media":       # /run/media/<user>/<disk>
                            for sub in os.listdir(p):
                                sp = os.path.join(p, sub)
                                if os.path.isdir(sp):
                                    found.append(sp)
    return found


def walk_videos(root, stop_flag, progress=None):
    results = []
    label, serial = drive_info(root)
    for dirpath, dirnames, filenames in os.walk(root, topdown=True):
        if stop_flag.is_set():
            break
        dirnames[:] = [d for d in dirnames if d.lower() not in IGNORED_DIRS
                       and not d.startswith("$") and not d.startswith(".")]
        for fn in filenames:
            if os.path.splitext(fn)[1].lower() not in VIDEO_EXT:
                continue
            full = os.path.join(dirpath, fn)
            try:
                st = os.stat(full)
            except OSError:
                continue
            if st.st_size < MIN_KEEP_SIZE:
                continue
            item = analyse(full, st.st_size)
            item["mtime"] = int(st.st_mtime)
            item["drive"] = label
            item["drive_id"] = serial
            item["id"] = hashlib.md5((serial + "|" + full[len(root):]).encode("utf-8", "replace")).hexdigest()[:16]
            results.append(item)
            if progress and len(results) % 20 == 0:
                progress(len(results))
    group_folders(results)
    return results


def group_folders(items):
    """Un dossier qui contient plusieurs videos = une serie ; numerote les episodes manquants,
    puis fusionne les titres ('Overlord', 'Overlord II', 'Overlord Film'...)."""
    folders = {}
    for it in items:
        folders.setdefault(os.path.dirname(it["path"]), []).append(it)
    for folder, its in folders.items():
        if len(its) < 3:
            continue
        with_ep = [i for i in its if i["episode"]]
        if len(with_ep) < max(2, len(its) * 0.5):
            # pas de numeros : on numerote dans l'ordre alphabetique
            its.sort(key=lambda i: i["file"].lower())
            for n, it in enumerate(its, 1):
                if not it["episode"]:
                    it["episode"] = n
        if all(i["category"] not in ("Animes", "Series") for i in its):
            cat = "Animes" if any(w in folder.lower() for w in ("anime", "vostfr", "manga")) else "Series"
            ft, fs, fb = folder_title(folder)
            for it in its:
                it["category"] = cat
                it["title"] = ft
                it["season"] = 0 if fb else (it["season"] or fs)
        seasons = [i["season"] for i in its if i["season"]]
        common = max(set(seasons), key=seasons.count) if seasons else None
        for it in its:
            if it["season"] is None:
                it["season"] = common
    for it in items:
        if it["season"] is None:
            it["season"] = 1 if it["category"] in ("Animes", "Series") else None
    merge_titles(items)


def merge_titles(items):
    """'Overlord II' -> Overlord saison 2 ; 'Evangelion Film 1 & 2' -> Evangelion bonus."""
    series = [i for i in items if i["category"] in ("Animes", "Series")]
    by_title = {}
    for i in series:
        by_title.setdefault(i["title"].lower(), []).append(i)
    titles = sorted(by_title, key=len)
    for t in titles:
        for longer in titles:
            if longer == t or not longer.startswith(t + " ") or len(t) < 6:
                continue
            suffix = longer[len(t):].strip(" -:")
            season = None
            bonus = False
            m = re.fullmatch(r"(?:s|saison|season)?\s*0?(\d{1,2})", suffix)
            if m:
                season = int(m.group(1))
            elif suffix in ROMAN:
                season = ROMAN[suffix]
            elif any(re.search(r"\b%s" % w, suffix) for w in
                     ("film", "movie", "ova", "oav", "oad", "sp", "special", "opening", "ending",
                      "revival", "bonus", "recap", "récap")):
                bonus = True
            else:
                continue
            src = by_title.get(longer, [])
            if not src:
                continue
            target = by_title[t]
            if season is not None:
                if any(x["season"] == season for x in target):
                    continue          # collision : on laisse separe
                for x in src:
                    x["season"] = season
            if bonus:
                for x in src:
                    x["season"] = 0
            for x in src:
                x["title"] = target[0]["title"]
            target.extend(src)
            by_title[longer] = []


def find_ffmpeg():
    import shutil
    for name in ("ffmpeg", "ffmpeg.exe"):
        p = shutil.which(name)
        if p:
            return p
    local = os.path.join(APP_DIR, "ffmpeg.exe")
    return local if os.path.isfile(local) else None


FFMPEG = find_ffmpeg()
FFMPEG_URL = "https://github.com/BtbN/FFmpeg-Builds/releases/download/latest/ffmpeg-master-latest-win64-gpl.zip"
INSTALLING = {"on": False, "msg": ""}


def install_ffmpeg():
    """Telecharge ffmpeg.exe dans le dossier de l'appli (Windows)."""
    global FFMPEG
    if INSTALLING["on"] or FFMPEG:
        return
    INSTALLING["on"] = True
    zpath = os.path.join(DATA_DIR, "ffmpeg.zip")
    try:
        os.makedirs(DATA_DIR, exist_ok=True)
        def hook(n, bs, total):
            if total > 0:
                INSTALLING["msg"] = "Telechargement des miniatures (ffmpeg) : %d %%" % min(100, n * bs * 100 // total)
        INSTALLING["msg"] = "Telechargement de ffmpeg..."
        urllib.request.urlretrieve(FFMPEG_URL, zpath, hook)
        INSTALLING["msg"] = "Installation..."
        with zipfile.ZipFile(zpath) as z:
            for name in z.namelist():
                low = name.lower()
                for exe in ("ffmpeg.exe", "ffprobe.exe"):
                    if low.endswith("/" + exe):
                        with z.open(name) as src, open(os.path.join(APP_DIR, exe), "wb") as dst:
                            dst.write(src.read())
        os.remove(zpath)
        FFMPEG = find_ffmpeg()
        INSTALLING["msg"] = "Miniatures installees" if FFMPEG else "Echec de l'installation"
    except Exception as exc:
        INSTALLING["msg"] = "Echec du telechargement : %s" % exc
    finally:
        INSTALLING["on"] = False


THUMB_JOB = {"on": False, "cancel": False}


def make_all_thumbs():
    """Genere les miniatures manquantes (une par titre d'abord, puis le reste)."""
    if THUMB_JOB["on"]:
        return
    THUMB_JOB["on"] = True
    THUMB_JOB["cancel"] = False
    try:
        with LIB.lock:
            items = list(LIB.items)
        seen = set()
        first, rest = [], []
        for i in items:
            if os.path.isfile(thumb_path(i)) or not os.path.isfile(i["path"]):
                continue
            key = (i["category"], i["title"].lower())
            (rest if key in seen else first).append(i)
            seen.add(key)
        todo = first + rest
        for k, item in enumerate(todo, 1):
            if STOP.is_set() or THUMB_JOB["cancel"]:
                LIB.status = "Miniatures annulees"
                return
            make_thumb(item)
            LIB.status = "Miniatures %d/%d" % (k, len(todo))
        LIB.status = "Miniatures terminees"
    finally:
        THUMB_JOB["on"] = False


def find_ffprobe():
    import shutil
    if FFMPEG:
        cand = os.path.join(os.path.dirname(FFMPEG), "ffprobe.exe" if os.name == "nt" else "ffprobe")
        if os.path.isfile(cand):
            return cand
    return shutil.which("ffprobe")


NVENC = {"checked": False, "ok": False}
PROBE_CACHE = {}
NOWIN = 0x08000000 if os.name == "nt" else 0


def nvenc_available():
    if not NVENC["checked"] and FFMPEG:
        NVENC["checked"] = True
        try:
            r = subprocess.run([FFMPEG, "-v", "error", "-f", "lavfi", "-i", "nullsrc=s=256x256:d=1",
                                "-c:v", "h264_nvenc", "-f", "null", "-"],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               timeout=20, creationflags=NOWIN)
            NVENC["ok"] = r.returncode == 0
        except Exception:
            NVENC["ok"] = False
    return NVENC["ok"]


def probe(item):
    """Pistes audio/sous-titres + duree (via ffprobe), mis en cache."""
    if item["id"] in PROBE_CACHE:
        return PROBE_CACHE[item["id"]]
    info = {"duration": 0, "audio": [], "subs": [], "vcodec": ""}
    fp = find_ffprobe()
    if not fp and FFMPEG and os.path.isfile(item["path"]):
        try:   # sans ffprobe : on lit la sortie de "ffmpeg -i"
            r = subprocess.run([FFMPEG, "-hide_banner", "-i", item["path"]], capture_output=True,
                               timeout=30, creationflags=NOWIN)
            txt = r.stderr.decode("utf-8", "replace")
            m = re.search(r"Duration: (\d+):(\d+):(\d+\.?\d*)", txt)
            if m:
                info["duration"] = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
            ai = si = 0
            for m in re.finditer(r"Stream #0:\d+(?:\[[^\]]*\])?(?:\((\w+)\))?: (Video|Audio|Subtitle): (\w+)([^\n]*)(?:\n\s+Metadata:\n(?:\s+[^\n]*\n)*?\s+title\s*:\s*([^\n]*))?", txt):
                lang = (m.group(1) or "").lower()
                kind, codec, title = m.group(2), m.group(3), (m.group(5) or "").strip()
                if kind == "Video" and not info["vcodec"]:
                    info["vcodec"] = codec
                elif kind == "Audio":
                    info["audio"].append({"i": ai, "lang": lang, "title": title, "label": title or lang or "Piste %d" % (ai + 1)})
                    ai += 1
                elif kind == "Subtitle":
                    info["subs"].append({"i": si, "lang": lang, "title": title, "codec": codec, "label": title or lang or "Sous-titres %d" % (si + 1)})
                    si += 1
        except Exception:
            pass
    if fp and os.path.isfile(item["path"]):
        try:
            r = subprocess.run([fp, "-v", "error", "-print_format", "json", "-show_format",
                                "-show_streams", item["path"]],
                               capture_output=True, timeout=30, creationflags=NOWIN)
            j = json.loads(r.stdout.decode("utf-8", "replace") or "{}")
            info["duration"] = float(j.get("format", {}).get("duration") or 0)
            ai = si = 0
            for st in j.get("streams", []):
                tags = st.get("tags", {}) or {}
                lang = (tags.get("language") or "").lower()
                title = tags.get("title") or ""
                if st.get("codec_type") == "video" and not info["vcodec"]:
                    info["vcodec"] = st.get("codec_name", "")
                elif st.get("codec_type") == "audio":
                    info["audio"].append({"i": ai, "lang": lang, "title": title,
                                          "label": (title or lang or "Piste %d" % (ai + 1))})
                    ai += 1
                elif st.get("codec_type") == "subtitle":
                    info["subs"].append({"i": si, "lang": lang, "title": title,
                                         "codec": st.get("codec_name", ""),
                                         "label": (title or lang or "Sous-titres %d" % (si + 1))})
                    si += 1
        except Exception:
            pass
    # choix par defaut : audio francais si present, sinon VO + sous-titres francais
    fr = ("fre", "fra", "fr", "french", "francais", "français", "vf")
    def is_fr(t):
        return t["lang"] in fr or any(w in t["title"].lower() for w in ("fr", "vf", "fran"))
    info["audio_default"] = next((a["i"] for a in info["audio"] if is_fr(a)), 0)
    if info["audio"] and is_fr(info["audio"][info["audio_default"]]):
        info["sub_default"] = -1
    else:
        info["sub_default"] = next((x["i"] for x in info["subs"] if is_fr(x)),
                                   info["subs"][0]["i"] if info["subs"] else -1)
    PROBE_CACHE[item["id"]] = info
    return info


SUBS_DIR = os.path.join(DATA_DIR, "sous-titres")


def extract_subs(item, sub):
    """Extrait la piste de sous-titres en .ass dans un dossier au nom simple
    (evite tout probleme de caracteres speciaux dans le filtre ffmpeg)."""
    os.makedirs(SUBS_DIR, exist_ok=True)
    name = "%s_%d.ass" % (item["id"], sub)
    out = os.path.join(SUBS_DIR, name)
    fonts = "fonts_" + item["id"]
    fdir = os.path.join(SUBS_DIR, fonts)
    if not (os.path.isfile(out) and os.path.getsize(out) > 0):
        try:
            subprocess.run([FFMPEG, "-v", "error", "-y", "-i", item["path"], "-map", "0:s:%d" % sub,
                            "-c:s", "ass", out], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=120, creationflags=NOWIN)
        except Exception:
            return None, None
        if not (os.path.isfile(out) and os.path.getsize(out) > 0):
            return None, None
        os.makedirs(fdir, exist_ok=True)
        try:   # polices embarquees dans le mkv (pour les sous-titres stylises)
            subprocess.run([FFMPEG, "-v", "error", "-y", "-dump_attachment:t", "", "-i", item["path"],
                            "-t", "0", "-f", "null", "-"], cwd=fdir, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=120, creationflags=NOWIN)
        except Exception:
            pass
    return name, (fonts if os.path.isdir(fdir) else None)


def transcode_cmd(item, start, audio, sub, height):
    info = probe(item)
    cmd = [FFMPEG, "-v", "error", "-nostdin", "-hide_banner"]
    if start > 0:
        cmd += ["-ss", "%.3f" % start, "-copyts"]
    cmd += ["-i", item["path"]]
    vf = []
    if height and height > 0:
        vf.append("scale=-2:'min(%d,ih)'" % height)
    subdef = next((x for x in info["subs"] if x["i"] == sub), None)
    filter_complex = None
    if subdef and subdef["codec"] in ("hdmv_pgs_subtitle", "dvd_subtitle", "dvb_subtitle"):
        filter_complex = "[0:v:0]%s[v];[v][0:s:%d]overlay[out]" % (
            (",".join(vf) if vf else "null"), sub)
    elif subdef:
        name, fonts = extract_subs(item, sub)
        if name:
            vf.append("subtitles=%s%s" % (name, (":fontsdir=" + fonts) if fonts else ""))
    vf.append("format=yuv420p")
    if filter_complex:
        cmd += ["-filter_complex", filter_complex + ";[out]format=yuv420p[o]", "-map", "[o]"]
    else:
        cmd += ["-map", "0:v:0", "-vf", ",".join(vf)]
    if info["audio"]:
        cmd += ["-map", "0:a:%d" % (audio if 0 <= audio < len(info["audio"]) else 0)]
    if start > 0:
        cmd += ["-output_ts_offset", "-%.3f" % start]
    if not ANDROID and nvenc_available():
        cmd += ["-c:v", "h264_nvenc", "-preset", "p4", "-rc", "vbr", "-cq", "23", "-b:v", "0"]
    else:
        cmd += ["-c:v", "libx264", "-preset", "ultrafast" if ANDROID else "veryfast",
                "-crf", "26" if ANDROID else "23", "-tune", "zerolatency"]
    cmd += ["-g", "50", "-c:a", "aac", "-ac", "2", "-b:a", "160k", "-sn",
            "-movflags", "frag_keyframe+empty_moov+default_base_moof", "-f", "mp4", "pipe:1"]
    return cmd


def thumb_path(item):
    new = os.path.join(THUMB_DIR, item["id"] + ".jpg")
    if not os.path.isfile(new):
        key = "%s|%s|%s" % (item["path"], item["size"], item.get("mtime", 0))
        old = os.path.join(THUMB_DIR, hashlib.md5(key.encode("utf-8")).hexdigest() + ".png")
        if os.path.isfile(old):
            try:
                os.replace(old, new)
            except OSError:
                return old
    return new


def make_thumb(item):
    out = thumb_path(item)
    if os.path.isfile(out) and os.path.getsize(out) > 500:
        return True
    if not FFMPEG or not os.path.isfile(item["path"]):
        return False
    flags = 0x08000000 if os.name == "nt" else 0
    for seek in ("00:05:00", "00:01:00", "00:00:05"):
        cmd = [FFMPEG, "-y", "-loglevel", "error", "-ss", seek, "-i", item["path"],
               "-frames:v", "1",
               "-vf", "scale=%d:%d:force_original_aspect_ratio=increase,crop=%d:%d"
               % (THUMB_W, THUMB_H, THUMB_W, THUMB_H), "-q:v", "4", out]
        try:
            subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=60, creationflags=flags)
        except Exception:
            return False
        if os.path.isfile(out) and os.path.getsize(out) > 500:
            return True
    return False


# --------------------------------------------------------------------------
# Bibliotheque
# --------------------------------------------------------------------------

class Library:
    def __init__(self):
        self.lock = threading.Lock()
        self.items = []
        self.sources = {}
        self.overrides = {}
        self.progress = {}     # id -> {t, dur, done, at}
        self.status = "Demarrage"
        self._fixups = set()
        self.scanning = False
        self.load()

    def load(self):
        try:
            with open(LIB_FILE, "r", encoding="utf-8") as f:
                d = json.load(f)
            self.items = d.get("items", [])
            self.sources = d.get("sources", {})
            self.overrides = d.get("overrides", {})
            self.progress = d.get("progress", {})
            self._fixups = set(d.get("fixups", []))
            if "absolute-duo-2026-09" not in self._fixups:
                ids = {i["id"] for i in self.items if "absolute duo" in i["path"].lower()}
                for k in list(self.overrides):
                    if k in ids:
                        del self.overrides[k]
                self._fixups.add("absolute-duo-2026-09")
        except Exception:
            pass

    def save(self):
        os.makedirs(DATA_DIR, exist_ok=True)
        payload = json.dumps({"items": self.items, "sources": self.sources,
                              "overrides": self.overrides, "progress": self.progress,
                              "fixups": sorted(self._fixups)}, ensure_ascii=False)
        tmp = LIB_FILE + ".%d.tmp" % os.getpid()
        for attempt in range(5):
            try:
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(payload)
                os.replace(tmp, LIB_FILE)
                return
            except OSError:
                time.sleep(0.3 * (attempt + 1))
        try:                       # dernier recours : ecriture directe
            with open(LIB_FILE, "w", encoding="utf-8") as f:
                f.write(payload)
        except OSError:
            dbg("sauvegarde impossible : " + traceback.format_exc().splitlines()[-1])
        try:
            os.remove(tmp)
        except OSError:
            pass

    def replace_source(self, root, items):
        label, serial = drive_info(root)
        with self.lock:
            rl = root.lower()
            self.items = [i for i in self.items
                          if not i["path"].lower().startswith(rl) and i.get("drive_id") != serial]
            self.items.extend(items)
            # anciennes entrees indexees par lettre -> on les remplace par l'identifiant
            for k in [k for k in self.sources if k.lower() == rl]:
                del self.sources[k]
            self.sources[serial] = {"root": root, "label": label, "count": len(items),
                                    "last_scan": int(time.time())}
            self.save()

    def roots(self):
        return [v["root"] for v in self.sources.values() if isinstance(v, dict) and v.get("root")]

    def by_id(self, iid):
        with self.lock:
            for i in self.items:
                if i["id"] == iid:
                    return i
        return None

    def export(self):
        with self.lock:
            out = []
            online_roots = {}
            for i in self.items:
                d = dict(i)
                d["category"] = self.overrides.get(i["id"], i["category"])
                d["thumb"] = os.path.isfile(thumb_path(i))
                did = i.get("drive_id", "")
                if did not in online_roots:
                    src = self.sources.get(did) or {}
                    online_roots[did] = os.path.isdir(src.get("root", "")) if src else True
                d["online"] = online_roots[did] and os.path.isfile(i["path"])
                d.pop("path", None)
                out.append(d)
            drives = []
            for did, src in self.sources.items():
                if not isinstance(src, dict) or not src.get("root"):
                    continue
                drives.append({"id": did, "label": src.get("label") or src["root"], "root": src["root"],
                               "count": src.get("count", 0), "online": os.path.isdir(src["root"]),
                               "last_scan": src.get("last_scan", 0)})
            return {"items": out, "status": self.status, "scanning": self.scanning,
                    "ffmpeg": bool(FFMPEG), "sources": self.sources, "disks": drives,
                    "progress": self.progress,
                    "url": "http://%s:%d" % (local_ip(), PORT),
                    "drives": list_drives(), "installing": INSTALLING["on"],
                    "install_msg": INSTALLING["msg"], "windows": os.name == "nt",
                    "thumb_job": THUMB_JOB["on"], "firewall": FIREWALL["ok"], "embedded": EMBEDDED,
                    "missing_thumbs": sum(1 for i in out if not i["thumb"])}


LIB = Library()
STOP = threading.Event()


def scan(roots):
    if LIB.scanning:
        return
    LIB.scanning = True
    try:
        for root in roots:
            if not os.path.isdir(root):
                continue
            LIB.status = "Analyse de %s ..." % root
            found = walk_videos(root, STOP,
                                lambda n: setattr(LIB, "status", "Analyse de %s : %d videos" % (root, n)))
            if STOP.is_set():
                return
            LIB.replace_source(root, found)
            LIB.status = "%d videos sur %s" % (len(found), root)
        LIB.status = "Scan termine"
    finally:
        LIB.scanning = False


def autosave():
    while not STOP.is_set():
        time.sleep(30)
        try:
            with LIB.lock:
                LIB.save()
        except Exception:
            pass


def watch_drives():
    known = set(list_drives())
    if known:
        scan(sorted(known))
    else:
        LIB.status = "Aucun disque branche"
    while not STOP.is_set():
        time.sleep(3)
        try:
            current = set(list_drives())
        except Exception:
            continue
        new = current - known
        known = current
        if new:
            threading.Thread(target=scan, args=(sorted(new),), daemon=True).start()


def local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


# --------------------------------------------------------------------------
# Page web (responsive : telephone, tablette, PC, tele)
# --------------------------------------------------------------------------

HTML = r"""<!DOCTYPE html>
<html lang="fr"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="theme-color" content="#0f1115">
<link rel="manifest" href="/manifest.webmanifest">
<link rel="apple-touch-icon" href="/icon.png">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="Mediatheque">
<title>Mediatheque</title>
<style>
:root{--bg:#0f1115;--panel:#171a21;--card:#1e222b;--hi:#2a2f3a;--txt:#e8ebf1;--dim:#8b93a5;--acc:#7aa2f7}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
body{margin:0;background:var(--bg);color:var(--txt);font:15px/1.4 -apple-system,Segoe UI,Roboto,sans-serif}
header{position:sticky;top:0;z-index:5;background:var(--panel);padding:10px 14px;display:flex;flex-wrap:wrap;gap:8px;align-items:center;box-shadow:0 2px 10px #0006}
header h1{font-size:18px;margin:0 10px 0 0;font-weight:600}
#sort,#filters select{background:var(--card);color:var(--txt);border:none;padding:7px 10px;border-radius:8px;font-size:13px}
#filters select.on{background:var(--acc);color:#0b0d10}
.dk{display:flex;align-items:center;gap:6px;background:var(--card);padding:5px 10px;border-radius:14px}.dk.off{opacity:.5}.dk .dot{width:8px;height:8px;border-radius:50%;background:#9be29b}.dk.off .dot{background:#f7768e}
.dk button{background:none;border:none;color:var(--dim);cursor:pointer;font-size:12px;padding:0 0 0 4px}
.card.off{opacity:.45}
.bar{height:4px;background:#ffffff14}.bar div{height:100%;background:var(--acc)}
.ep .pb{height:3px;background:#ffffff14;margin-top:4px;border-radius:2px;overflow:hidden}.ep .pb div{height:100%;background:var(--acc)}
.ep .st{font-size:11px;color:var(--dim);white-space:nowrap}.ep .chk{background:none;border:1px solid #ffffff33;color:var(--dim);border-radius:6px;width:26px;height:26px;cursor:pointer;flex-shrink:0}.ep.done .chk{background:#2b4a2b;color:#9be29b;border-color:#2b4a2b}
.lt{font-size:12px;color:var(--dim);padding:4px 6px;border-radius:6px;cursor:pointer;border:none;background:none}.lt.on{background:var(--acc);color:#0b0d10}
.rs{flex:0 0 auto;width:220px;background:var(--card);border-radius:10px;padding:8px 10px;cursor:pointer;display:flex;gap:10px;align-items:center}
.rs img,.rs .ph{width:64px;height:36px;border-radius:6px;object-fit:cover;background:var(--hi);flex-shrink:0}
.rsx{position:absolute;top:4px;right:6px;background:none;border:none;color:var(--dim);cursor:pointer;font-size:14px;padding:2px 4px}.rsx:hover{color:#f7768e}
.rs .t{font-size:13px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.rs .e{font-size:11px;color:var(--dim)}
.card .meta{display:flex;gap:6px;flex-wrap:wrap;padding:0 10px 10px}.chip{font-size:11px;background:var(--hi);color:var(--dim);padding:2px 7px;border-radius:9px}
.ep .name{font-size:14px}.ep .fn{font-size:11px;color:var(--dim);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.ep .f{display:flex;flex-direction:column;min-width:0}
.ep.done .n{background:#2b4a2b;color:#9be29b}.ep.cur .n{background:var(--acc);color:#0b0d10}
.tabs{display:flex;gap:4px;flex-wrap:wrap}
.tab{padding:7px 13px;border-radius:20px;color:var(--dim);cursor:pointer;font-size:14px;border:none;background:none}
.tab.on{background:var(--card);color:var(--acc)}
#q{margin-left:auto;background:var(--card);border:none;color:var(--txt);padding:8px 12px;border-radius:8px;font-size:15px;min-width:150px;flex:1;max-width:320px}
#st{font-size:12px;color:var(--dim);padding:6px 14px;background:var(--panel)}
main{padding:12px;display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:12px}
@media(min-width:700px){main{grid-template-columns:repeat(auto-fill,minmax(200px,1fr));gap:16px;padding:16px}}
@media(min-width:1600px){main{grid-template-columns:repeat(auto-fill,minmax(260px,1fr))}}
.card{background:var(--card);border-radius:12px;overflow:hidden;cursor:pointer;transition:transform .12s}
.card:hover,.card:focus{transform:scale(1.03);outline:2px solid var(--acc)}
.th{aspect-ratio:16/9;background-size:cover;background-position:center;display:flex;align-items:center;justify-content:center;font-size:34px;font-weight:700;color:#fff8;position:relative}
.badge{position:absolute;right:6px;top:6px;background:#000a;font-size:11px;padding:2px 7px;border-radius:10px;color:#fff}
.ti{padding:8px 10px 2px;font-weight:600;font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.su{padding:0 10px 10px;font-size:12px;color:var(--dim)}
.empty{grid-column:1/-1;text-align:center;color:var(--dim);padding:60px 20px}
#dlg{position:fixed;inset:0;background:#000b;display:none;z-index:10;overflow:auto}
#dlg.on{display:block}
.box{max-width:900px;margin:20px auto;background:var(--panel);border-radius:14px;overflow:hidden}
.box .hd{display:flex;align-items:center;gap:12px;padding:14px 16px;background:var(--card)}
.box .hd h2{margin:0;font-size:18px;flex:1}
.x{background:none;border:none;color:var(--txt);font-size:26px;cursor:pointer}
.seasons{display:flex;gap:6px;flex-wrap:wrap;padding:12px 16px 0}
.ep{display:flex;align-items:center;gap:12px;padding:10px 16px;border-bottom:1px solid #ffffff0d;cursor:pointer}
.ep:hover{background:var(--hi)}.ep.sel{background:#243252;outline:1px solid var(--acc)}
.ep .pl,.ep .vl{padding:5px 9px;font-size:12px;flex-shrink:0}
.ep .n{width:34px;height:34px;border-radius:8px;background:var(--card);display:flex;align-items:center;justify-content:center;font-weight:600;flex-shrink:0}
.ep .f{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:14px}
.ep .s{color:var(--dim);font-size:12px}
.off{opacity:.45}
video{width:100%;max-height:70vh;background:#000;display:block}
.vwrap{background:#000}.ctl{display:flex;align-items:center;gap:10px;padding:8px 12px;background:#0b0d10;color:var(--txt);font-size:13px}
.ctl button{background:none;border:none;color:var(--txt);font-size:20px;cursor:pointer}.ctl input[type=range]{flex:1;accent-color:var(--acc)}
select{background:var(--card);color:var(--txt);border:none;padding:7px 10px;border-radius:8px;font-size:13px}
.menu{display:flex;gap:8px;padding:10px 16px;flex-wrap:wrap}
.menu button,.seasons button{background:var(--card);border:none;color:var(--txt);padding:8px 12px;border-radius:8px;cursor:pointer;font-size:14px}
.seasons button.on{background:var(--acc);color:#0b0d10}
.note{padding:8px 16px 14px;color:var(--dim);font-size:13px}
</style></head><body>
<header><h1>Mediatheque</h1>
<div class="tabs" id="tabs"></div>
<select id="sort" title="Tri"><option value="az">A → Z</option><option value="recent">Ajoutés récemment</option><option value="eps">Nb d'épisodes</option><option value="size">Taille</option></select>
<input id="q" placeholder="Rechercher..." autocomplete="off">
</header>
<div id="disks" style="display:none;gap:8px;flex-wrap:wrap;align-items:center;padding:8px 14px;background:var(--panel);border-top:1px solid #ffffff0a;font-size:13px"></div>
<div id="filters" style="display:flex;gap:8px;flex-wrap:wrap;align-items:center;padding:8px 14px;background:var(--panel);border-top:1px solid #ffffff0a">
  <select data-f="disk" style="display:none"><option value="">Disque : tous</option></select>
  <select data-f="added"><option value="">Ajouté : tout</option><option value="7">7 derniers jours</option><option value="30">30 derniers jours</option><option value="365">Cette année</option></select>
  <select data-f="year"><option value="">Année : toutes</option></select>
  <select data-f="lang"><option value="">Langue : toutes</option><option>VOSTFR</option><option>VF</option><option>MULTI</option></select>
  <select data-f="quality"><option value="">Qualité : toutes</option><option>4K</option><option>1080p</option><option>720p</option><option>480p</option></select>
  <select data-f="status"><option value="">Statut : tous</option><option value="new">Non commencé</option><option value="cur">En cours</option><option value="done">Terminé</option></select>
  <select data-f="seasons"><option value="">Saisons : toutes</option><option value="1">1 saison</option><option value="2">2 saisons et +</option><option value="bonus">Avec bonus</option></select>
  <button id="reset" class="b" style="display:none;background:var(--card);color:var(--txt)">✕ Réinitialiser</button>
  <div id="letters" style="display:flex;gap:2px;flex-wrap:wrap;margin-left:auto"></div>
</div>
<div id="resume" style="display:none;padding:10px 14px 0"><div style="color:var(--dim);font-size:12px;margin-bottom:6px">REPRENDRE</div><div id="resumeRow" style="display:flex;gap:10px;overflow-x:auto;padding-bottom:6px"></div></div>
<div id="st">Chargement...</div>
<div id="fw" style="display:none;background:#5a1a1a;color:#ffc9c9;padding:8px 14px;font-size:13px">🔒 Le pare-feu Windows bloque l'accès depuis le téléphone / la télé. <button id="fwbtn" class="b" style="background:#f7768e;color:#0b0d10;margin-left:8px">Autoriser (Windows demandera Oui)</button></div>
<div id="offline" style="display:none;background:#5a3a1a;color:#ffd9a8;padding:8px 14px;font-size:13px">✈️ Hors connexion : catalogue mémorisé sur cet appareil. La lecture nécessite le PC (ou un épisode téléchargé à l'avance).</div>
<div id="share" style="display:none;background:#1b2a4a;color:#dbe6ff;padding:10px 14px;font-size:14px;display:flex;gap:10px;align-items:center;flex-wrap:wrap">
  <span>📱 Sur téléphone, tablette ou télé (même Wi‑Fi), ouvre : <b id="url"></b></span>
  <span style="margin-left:auto;display:flex;gap:8px;flex-wrap:wrap">
  <button id="ffm" class="b" style="display:none">Activer les miniatures</button>
  <a href="/installer"><button class="b" style="background:#2b4a2b;color:#9be29b" title="Faire tourner l'appli directement sur un téléphone / une tablette">📲 Installer sur un appareil</button></a>
  <button id="addroot" class="b" style="background:var(--card);color:var(--txt)">+ Ajouter un dossier</button>
  <button id="pwa" class="b" style="background:#5a3a1a;color:#ffd9a8" title="Garde le catalogue et les images sur cet appareil pour le mode avion">✈️ Mémoriser pour hors-ligne</button>
  <button id="thm" class="b" style="display:none">Miniatures manquantes</button>
  <button id="thmstop" class="b" style="display:none;background:#f7768e">Stop miniatures</button>
  <button id="exp" class="b" title="Cree Mediatheque.html a la racine du disque + images/titres pour les lecteurs de tele">Préparer pour hors-ligne</button>
  <button id="rescan" class="b">Rescanner les disques</button>
  <button id="quit" class="b" style="background:#f7768e">Quitter</button></span>
</div>
<style>.b{background:#7aa2f7;color:#0b0d10;border:none;padding:7px 12px;border-radius:8px;cursor:pointer;font-weight:600;font-size:13px}</style>
<main id="grid"></main>
<div id="dlg"><div class="box" id="box"></div></div>
<script>
/*__STATIC__*/
const STATIC=window.__DATA__||null;
const CATS=["Tout","Animes","Films","Series","Autres"];
let cat=localStorage.getItem("cat")||"Tout",data=null,q="",sort=localStorage.getItem("sort")||"az";
if(!CATS.includes(cat))cat="Tout";
const F={disk:"",added:"",year:"",lang:"",quality:"",status:"",seasons:"",letter:""};
let PROG={},OFFLINE=false;
if("serviceWorker" in navigator&&!window.__DATA__){navigator.serviceWorker.register("/sw.js").catch(()=>{});navigator.serviceWorker.addEventListener("message",e=>{if(e.data&&e.data.type==="thumbsDone"){document.getElementById("st").textContent="Images mémorisées pour le hors-ligne ("+e.data.n+")"}})}
function flushQueue(){let qd=[];try{qd=JSON.parse(localStorage.getItem("pending")||"[]")}catch(e){}if(!qd.length)return;localStorage.setItem("pending","[]");qd.forEach(([u,o])=>post(u,o))}
function post(url,obj){if(STATIC){if(url==="/api/progress"){if(obj.reset)delete PROG[obj.id];else PROG[obj.id]={t:obj.t||0,dur:obj.dur||0,done:obj.done!==undefined?obj.done:(obj.dur&&obj.t>=obj.dur*0.92),at:Date.now()/1000}}
  if(url==="/api/progress_many")obj.ids.forEach(id=>{if(obj.done)PROG[id]={t:0,dur:0,done:true,at:Date.now()/1000};else delete PROG[id]});
  try{localStorage.setItem("prog-static",JSON.stringify(PROG))}catch(e){}return Promise.resolve()}
  return fetch(url,{method:"POST",body:JSON.stringify(obj)}).then(r=>{if(!r.ok)throw 0}).catch(()=>{try{const qd=JSON.parse(localStorage.getItem("pending")||"[]");qd.push([url,obj]);localStorage.setItem("pending",JSON.stringify(qd.slice(-500)))}catch(e){}})}
function fileUrl(rel){const base=location.href.replace(/[^/]*$/,"");return base+rel.split("/").map(encodeURIComponent).join("/")}
function stat(e){const eps=e.items.filter(x=>x.season>0);const done=eps.filter(watched).length;const any=e.items.some(x=>PROG[x.id]);return eps.length&&done>=eps.length?"done":(any?"cur":"new")}
function pct(it){const p=PROG[it.id];if(!p)return 0;if(p.done)return 100;return p.dur?Math.min(99,Math.round(p.t/p.dur*100)):0}
function watched(it){const p=PROG[it.id];return !!(p&&p.done)}
function started(it){const p=PROG[it.id];return !!(p&&!p.done&&p.t>30)}
function coll(it){const c=it.collection||it.title;return c.charAt(0).toUpperCase()+c.slice(1)}
const tabs=document.getElementById("tabs");
CATS.forEach(c=>{const b=document.createElement("button");b.className="tab"+(c===cat?" on":"");b.textContent=c;b.onclick=()=>{cat=c;localStorage.setItem("cat",c);[...tabs.children].forEach(x=>x.classList.toggle("on",x.textContent===c));render()};tabs.appendChild(b)});
document.getElementById("q").oninput=e=>{q=e.target.value.toLowerCase();render()};
document.querySelectorAll("#filters select").forEach(sel=>sel.onchange=()=>{F[sel.dataset.f]=sel.value;sel.classList.toggle("on",!!sel.value);render()});
document.getElementById("reset").onclick=()=>{for(const k in F)F[k]="";document.querySelectorAll("#filters select").forEach(s=>{s.value="";s.classList.remove("on")});render()};
function renderDisks(){
  const box=document.getElementById("disks"),sel=document.querySelector('[data-f="disk"]');
  const ds=(data.disks||[]).filter(d=>d.count>0);
  if(ds.length<1||STATIC){box.style.display="none";sel.style.display="none";return}
  box.style.display="flex";
  box.innerHTML='<span style="color:var(--dim)">Disques :</span>'+ds.map(d=>`<span class="dk ${d.online?"":"off"}" title="${esc(d.root)}"><span class="dot"></span>${esc(d.label)} <span style="color:var(--dim)">· ${d.count} vidéos${d.online?"":" · débranché"}</span>${d.online?"":`<button data-id="${d.id}" title="Retirer ce disque de la bibliothèque">✕</button>`}</span>`).join("");
  box.querySelectorAll("button").forEach(b=>b.onclick=async()=>{const d=ds.find(x=>x.id===b.dataset.id);if(confirm("Retirer le disque « "+d.label+" » et ses "+d.count+" vidéos de la bibliothèque ? (rien n'est supprimé sur le disque)")){await fetch("/api/forget_disk",{method:"POST",body:JSON.stringify({id:d.id})});load()}});
  sel.style.display=ds.length>1?"":"none";
  const cur=sel.value;if(sel.options.length!==ds.length+1){sel.innerHTML='<option value="">Disque : tous</option>'+ds.map(d=>`<option value="${d.id}">${esc(d.label)}</option>`).join("");sel.value=cur}
}
function fillYears(){const sel=document.querySelector('[data-f="year"]');if(sel.options.length>1)return;const ys=[...new Set(data.items.map(x=>x.year).filter(Boolean))].sort((a,b)=>b-a);ys.forEach(y=>{const o=document.createElement("option");o.value=y;o.textContent=y;sel.appendChild(o)})}
function fillLetters(){const box=document.getElementById("letters");if(box.children.length)return;["#","A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"].forEach(L=>{const b=document.createElement("button");b.className="lt";b.textContent=L;b.onclick=()=>{F.letter=F.letter===L?"":L;box.querySelectorAll(".lt").forEach(x=>x.classList.toggle("on",x.textContent===F.letter));render()};box.appendChild(b)})}
const sortEl=document.getElementById("sort");sortEl.value=sort;sortEl.onchange=()=>{sort=sortEl.value;localStorage.setItem("sort",sort);render()};
function esc(s){return s.replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]))}
function col(t){let h=0;for(const c of t)h=(h*31+c.charCodeAt(0))>>>0;return`hsl(${h%360} 35% 32%)`}
function go(n){return(n/1073741824).toFixed(1)+" Go"}
function groups(){
  const g=new Map(),singles=[];
  for(const it of data.items){
    if(cat!=="Tout"&&it.category!==cat)continue;
    if(q&&!it.title.toLowerCase().includes(q)&&!coll(it).toLowerCase().includes(q)&&!it.file.toLowerCase().includes(q))continue;
    if(it.category==="Animes"||it.category==="Series"){
      const k=it.category+"|"+coll(it).toLowerCase();
      if(!g.has(k))g.set(k,{title:coll(it),cat:it.category,items:[]});
      g.get(k).items.push(it);
    }else singles.push({title:it.title,cat:it.category,items:[it]});
  }
  let all=[...g.values(),...singles];
  const now=Date.now()/1000;

  all=all.filter(e=>{
    if(F.disk&&!e.items.some(x=>x.drive_id===F.disk))return false;
    if(F.added&&!e.items.some(x=>(x.mtime||0)>now-F.added*86400))return false;
    if(F.year&&!e.items.some(x=>String(x.year)===F.year))return false;
    if(F.lang&&!e.items.some(x=>x.lang===F.lang))return false;
    if(F.quality&&!e.items.some(x=>x.quality===F.quality))return false;
    if(F.status&&stat(e)!==F.status)return false;
    if(F.seasons){const ns=new Set(e.items.filter(x=>x.season>0).map(x=>x.season)).size,nb=e.items.some(x=>x.season===0);
      if(F.seasons==="1"&&ns!==1)return false;if(F.seasons==="2"&&ns<2)return false;if(F.seasons==="bonus"&&!nb)return false}
    if(F.letter){const c=e.title.replace(/^(the|le|la|les|a|an)\s+/i,"").charAt(0).toUpperCase();if(F.letter==="#"?/[A-Z]/.test(c):c!==F.letter)return false}
    return true});
  document.getElementById("reset").style.display=Object.values(F).some(Boolean)?"":"none";
  const newest=e=>Math.max(...e.items.map(x=>x.mtime||0)),sz=e=>e.items.reduce((n,x)=>n+x.size,0);
  if(sort==="recent")all.sort((a,b)=>newest(b)-newest(a));
  else if(sort==="eps")all.sort((a,b)=>b.items.length-a.items.length||a.title.localeCompare(b.title,"fr"));
  else if(sort==="size")all.sort((a,b)=>sz(b)-sz(a));
  else all.sort((a,b)=>a.title.localeCompare(b.title,"fr",{sensitivity:"base",ignorePunctuation:true}));
  return all;
}
function renderResume(){
  const row=document.getElementById("resumeRow"),box=document.getElementById("resume");
  const byId=new Map(data.items.map(x=>[x.id,x]));
  const seenColl=new Set();
  const ent=Object.entries(PROG).filter(([id,p])=>byId.has(id)&&(p.at||0)>0).sort((a,b)=>(b[1].at||0)-(a[1].at||0)).filter(([id])=>{const it=byId.get(id);const k=it.category+"|"+coll(it).toLowerCase();if(seenColl.has(k))return false;seenColl.add(k);return true}).slice(0,12);
  if(!ent.length||q||STATIC){box.style.display="none";row.innerHTML="";return}
  row.innerHTML=ent.map(([id,p])=>{let it=byId.get(id);
    if(p.done){const eps=data.items.filter(x=>x.category===it.category&&x.title===it.title&&x.season===it.season).sort((a,b)=>(a.episode-b.episode));const i=eps.findIndex(x=>x.id===id);if(i>=0&&i+1<eps.length)it=eps[i+1];else return ""}
    const pr=PROG[it.id];const th=it.thumb?`<img src="/thumb/${it.id}">`:`<div class="ph"></div>`;
    const sub=(it.title.toLowerCase()!==coll(it).toLowerCase()?esc(it.title)+" · ":"")+(it.season===0?"Bonus":"S"+it.season+" · Ép. "+it.episode);
    const when=pr&&!pr.done&&pr.t>30?"Reprendre à "+fmt(pr.t):"Épisode suivant";
    return`<div class="rs" data-id="${it.id}" style="position:relative"><button class="rsx" data-coll="${esc(coll(it))}" data-cat="${it.category}" title="Retirer de la liste">✕</button>${th}<div style="min-width:0"><div class="t">${esc(coll(it))}</div><div class="e">${sub}</div><div class="e" style="color:var(--acc)">${when}</div>${pr&&!pr.done&&pr.dur?`<div class="pb" style="height:3px;background:#ffffff14;margin-top:4px"><div style="height:100%;width:${pct(it)}%;background:var(--acc)"></div></div>`:""}</div></div>`}).join("");
  box.style.display=row.innerHTML?"":"none";
  row.querySelectorAll(".rsx").forEach(b=>b.onclick=async ev=>{ev.stopPropagation();const c=b.dataset.coll.toLowerCase(),cat=b.dataset.cat;
    const ids=data.items.filter(x=>x.category===cat&&coll(x).toLowerCase()===c).map(x=>x.id);
    if(!confirm("Retirer « "+b.dataset.coll+" » des animés en cours ?\n(l'historique de visionnage de cet animé sera effacé)"))return;
    await post("/api/progress_many",{ids,done:false});ids.forEach(id=>delete PROG[id]);render()});
  row.querySelectorAll(".rs").forEach(r=>r.onclick=()=>{const it=byId.get(r.dataset.id);const g=groups().find(x=>x.items.some(y=>y.id===it.id))||{title:coll(it),cat:it.category,items:data.items.filter(y=>y.category===it.category&&coll(y).toLowerCase()===coll(it).toLowerCase())};open(g,it.season,it.id)});
}
function render(){
  if(!data)return;renderDisks();fillYears();fillLetters();renderResume();
  const grid=document.getElementById("grid");const gs=groups();
  document.getElementById("st").textContent=(data.scanning?"⏳ "+data.status+"  ·  ":"")+gs.length+" titres · "+gs.reduce((n,g)=>n+g.items.length,0)+" fichiers"+(data.installing?"  ·  ⬇ "+data.install_msg:(data.install_msg&&!data.ffmpeg?"  ·  "+data.install_msg:""))+(data.ffmpeg?"":"  ·  pas d'images : clique « Activer les miniatures »");
  if(data.thumb_job)document.getElementById("st").textContent="⏳ "+data.status+"  ·  "+document.getElementById("st").textContent;
  if(!gs.length){grid.innerHTML='<div class="empty">'+(data.scanning?'⏳ '+esc(data.status):'Aucune video pour le moment.<br><br>Disques détectés : <b>'+(data.drives.length?data.drives.map(esc).join(", "):"aucun")+'</b><br>Branche ton disque externe sur le PC : il est scanne automatiquement.<br>Le disque est deja branche ? Clique « Rescanner les disques ».')+'</div>';return}
  let h="";
  for(const [i,g] of gs.entries()){
    const first=g.items.find(x=>x.thumb)||g.items[0];
    const seasons=new Set(g.items.map(x=>x.season));
    const th=g.items.find(x=>x.thumb_data)||first;const bg=th.thumb_data?`background-image:url(${th.thumb_data})`:(first.thumb&&!STATIC?`background-image:url(/thumb/${first.id})`:`background:${col(g.title)}`);
    const subs=new Set(g.items.map(x=>x.title.toLowerCase())).size;
    const ns=new Set(g.items.filter(x=>x.season>0).map(x=>x.title.toLowerCase()+"|"+x.season)).size,neps=g.items.filter(x=>x.season>0).length,nb=g.items.filter(x=>x.season===0).length;
    const langs=[...new Set(g.items.map(x=>x.lang).filter(Boolean))],qs=[...new Set(g.items.map(x=>x.quality).filter(Boolean))],yr=Math.min(...g.items.map(x=>x.year||9999));
    const drv=[...new Set(g.items.map(x=>x.drive).filter(Boolean))],multiDisk=(data.disks||[]).length>1,off=!g.items.some(x=>x.online);
    const extra=`${multiDisk?drv.map(d=>`<span class="chip">💾 ${esc(d)}</span>`).join(""):""}${off?`<span class="chip" style="color:#f7768e">débranché</span>`:""}${yr<9999?`<span class="chip">${yr}</span>`:""}${langs.map(l=>`<span class="chip">${l}</span>`).join("")}${qs.length===1?`<span class="chip">${qs[0]}</span>`:""}`;
    const epsG=g.items.filter(x=>x.season>0),nv=epsG.filter(watched).length,st=stat(g);
    const prog=epsG.length?Math.round(epsG.reduce((n,x)=>n+pct(x),0)/epsG.length):0;
    const seen=st==="done"?`<span class="chip" style="background:#2b4a2b;color:#9be29b">✓ Terminé</span>`:(st==="cur"?`<span class="chip" style="background:#243252;color:var(--acc)">▶ En cours · ${nv}/${epsG.length} vus</span>`:"");
    const sub=(g.cat==="Animes"||g.cat==="Series")?`${seen}${subs>1?`<span class="chip">${subs} séries</span>`:""}<span class="chip">${ns>1?ns+" saisons":"1 saison"}</span><span class="chip">${neps} ép.</span>${nb?`<span class="chip">★ ${nb} bonus</span>`:""}${extra}`:(first.year?first.year+" · ":"")+g.cat+" · "+go(first.size);
    h+=`<div class="card ${off?"off":""}" tabindex="0" data-i="${i}"><div class="th" style="${bg}">${(th.thumb_data||(first.thumb&&!STATIC))?"":esc(g.title.slice(0,2).toUpperCase())}<span class="badge">${g.cat}</span></div>${(g.cat==="Animes"||g.cat==="Series")&&prog>0?`<div class="bar"><div style="width:${prog}%"></div></div>`:""}<div class="ti">${esc(g.title)}</div>${(g.cat==="Animes"||g.cat==="Series")?`<div class="meta">${sub}</div>`:`<div class="su">${sub}</div>`}</div>`;
  }
  grid.innerHTML=h;window._gs=gs;
  grid.querySelectorAll(".card").forEach(c=>{c.onclick=()=>open(gs[c.dataset.i]);c.onkeydown=e=>{if(e.key==="Enter")open(gs[c.dataset.i])}});
}
function open(g,startSeason,startId){
  const box=document.getElementById("box");
  const multi=new Set(g.items.map(x=>x.title.toLowerCase())).size>1;
  const tk=x=>(multi?x.title.toLowerCase()+"|":"")+x.season;
  const tabs=[];const seenT=new Set();
  for(const x of [...g.items].sort((a,b)=>a.title.localeCompare(b.title,"fr")||a.season-b.season)){const k=tk(x);if(!seenT.has(k)){seenT.add(k);tabs.push({k,title:x.title,season:x.season})}}
  tabs.sort((a,b)=>(a.season===0)-(b.season===0)||a.title.localeCompare(b.title,"fr")||a.season-b.season);
  const startItem=startId?g.items.find(x=>x.id===startId):null;
  let cur=startItem?tk(startItem):(tabs.find(t=>t.season>0)||tabs[0]).k;
  const seasons=tabs.map(t=>t.k);
  function draw(){
    const eps=g.items.filter(x=>tk(x)===cur).sort((a,b)=>(a.episode-b.episode)||a.file.localeCompare(b.file));
    box.innerHTML=`<div class="hd"><h2>${esc(g.title)}</h2><button class="x" id="x">×</button></div>
    <div id="player"></div>
    ${g.cat==="Series"||g.cat==="Animes"?`<div class="seasons">${tabs.map(t=>`<button class="${t.k===cur?"on":""}" data-s="${esc(t.k)}">${multi?esc(t.title)+" · ":""}${t.season===0?"Films & bonus":"Saison "+t.season}</button>`).join("")}</div>`:""}
    <div>${eps.map(e=>`<div class="ep ${e.online?"":"off"}" data-id="${e.id}"><div class="n">${e.season===0?"★":(e.episode||"•")}</div><div class="f"><span class="name">${e.season===0?esc(epName(e)):"Épisode "+(e.episode||"?")}</span><span class="fn">${esc(e.file)}</span>${started(e)?`<div class="pb"><div style="width:${pct(e)}%"></div></div>`:""}</div><div class="st">${epStatus(e)}</div><button class="chk" data-id="${e.id}" title="Marquer vu / non vu">${watched(e)?"✓":""}</button><button class="b pl" data-id="${e.id}">▶ Lire</button><button class="b vl" data-id="${e.id}" style="background:#ff8800;color:#000">VLC</button></div>`).join("")}</div>
    <div class="menu"><button class="b" id="allseen" style="background:var(--card);color:var(--txt)">${eps.every(watched)?"Marquer la saison non vue":"Marquer la saison comme vue"}</button>${g.items.some(x=>PROG[x.id])?`<button class="b" id="clearprog" style="background:var(--card);color:#f7768e">✕ Retirer des « en cours »</button>`:""}<span style="flex:1;color:var(--dim);font-size:12px;align-self:center">Mal classé ?</span>${CATS.slice(1).filter(c=>c!==g.cat).map(c=>`<button data-c="${c}">→ ${c}</button>`).join("")}<button data-c="auto" style="background:var(--hi)">↺ Classement automatique</button></div>
    <div class="note">Touche un episode pour le lire ici (les .mkv sont convertis a la volee, sous-titres inclus).</div>`;
    box.querySelector("#x").onclick=close;
    const cp=box.querySelector("#clearprog");if(cp)cp.onclick=async()=>{if(!confirm("Effacer tout l'historique de « "+g.title+" » (épisodes vus, temps d'arrêt) ?"))return;const ids=g.items.map(x=>x.id);await post("/api/progress_many",{ids,done:false});ids.forEach(id=>delete PROG[id]);draw();render()};
    box.querySelector("#allseen").onclick=async()=>{const all=eps.every(watched);await post("/api/progress_many",{ids:eps.map(e=>e.id),done:!all});eps.forEach(e=>{if(all)delete PROG[e.id];else PROG[e.id]={t:0,dur:0,done:true,at:Date.now()/1000}});draw()};
    box.querySelectorAll(".ep").forEach(e=>{const pr=PROG[e.dataset.id];if(pr&&pr.done)e.classList.add("done");else if(pr&&pr.t>30)e.classList.add("cur")});
    box.querySelectorAll(".chk").forEach(b=>b.onclick=async ev=>{ev.stopPropagation();const id=b.dataset.id;const p=PROG[id];if(p&&p.done){PROG[id]={t:0,dur:p.dur,done:false};await post("/api/progress",{id,reset:true})}else{PROG[id]={t:0,dur:0,done:true,at:Date.now()/1000};await post("/api/progress",{id,done:true})}draw()});
    box.querySelectorAll(".seasons button").forEach(b=>b.onclick=()=>{cur=b.dataset.s;draw()});
    box.querySelectorAll(".ep").forEach(e=>e.onclick=()=>play(e.dataset.id,g));
    box.querySelectorAll(".vl").forEach(b=>b.onclick=ev=>{ev.stopPropagation();vlc(b.dataset.id,g)});
    box.querySelectorAll(".menu button[data-c]").forEach(b=>b.onclick=async()=>{
      const ids=g.items.map(x=>x.id);
      if(b.dataset.c==="auto"){await fetch("/api/unclass",{method:"POST",body:JSON.stringify({ids})});close();load();return}
      if(!confirm("Déplacer « "+g.title+" » ("+ids.length+" fichiers) dans "+b.dataset.c+" ?"))return;
      await fetch("/api/reclass",{method:"POST",body:JSON.stringify({ids,cat:b.dataset.c})});close();load()});
  }
  draw();document.getElementById("dlg").classList.add("on");
  if(startId)play(startId,g);
}
const LANG={jpn:"Japonais",ja:"Japonais",fre:"Français",fra:"Français",fr:"Français",eng:"Anglais",en:"Anglais",ger:"Allemand",deu:"Allemand",spa:"Espagnol",ita:"Italien",por:"Portugais",kor:"Coréen",chi:"Chinois",zho:"Chinois",und:"Inconnu"};
function lab(a){const l=LANG[a.lang]||a.lang;return a.title?(l&&!a.title.toLowerCase().includes(l.toLowerCase())?a.title+" ("+l+")":a.title):(l||a.label)}
function nextEpisode(g,id){const it=g.items.find(x=>x.id===id);const eps=g.items.filter(x=>x.title===it.title&&x.season===it.season).sort((a,b)=>(a.episode-b.episode)||a.file.localeCompare(b.file));const i=eps.findIndex(x=>x.id===id);if(i>=0&&i+1<eps.length&&confirm("Épisode suivant ?"))play(eps[i+1].id,g)}
function epStatus(e){const p=PROG[e.id];if(!p)return "";if(p.done)return "✓ Vu";if(p.t>30)return "Arrêté à "+fmt(p.t)+(p.dur?" / "+fmt(p.dur):"");return ""}
function epName(e){let n=e.file.replace(/\.[^.]+$/,"").replace(/[\[\(][^\]\)]*[\]\)]/g," ").replace(/[_\.]/g," ").replace(/\s+/g," ").trim();return n.length>70?n.slice(0,70)+"…":n}
function vlc(id,g){
  const it=g.items.find(x=>x.id===id);
  if(window.Android&&window.Android.play){fetch("/api/path/"+id).then(r=>r.json()).then(j=>{if(j.path)window.Android.play(j.path,it.file)});return}
  if(STATIC){const path=decodeURIComponent(fileUrl(it.rel).replace(/^file:\/\//,""));if(/Android/.test(navigator.userAgent))location.href="intent://"+path.replace(/^\//,"")+"#Intent;scheme=file;package=org.videolan.vlc;type=video/*;end";else location.href=fileUrl(it.rel);return}
  const url=location.origin+"/video/"+id+"/"+encodeURIComponent(it.file);
  const local=["localhost","127.0.0.1"].includes(location.hostname);
  if(local){fetch("/api/open/"+id);return}                      // sur le PC : ouvre avec le lecteur par defaut (VLC)
  const ua=navigator.userAgent;
  if(/iPhone|iPad|iPod/.test(ua))location.href="vlc-x-callback://x-callback-url/stream?url="+encodeURIComponent(url);
  else if(/Android/.test(ua))location.href="intent://"+url.replace(/^https?:\/\//,"")+"#Intent;scheme=http;package=org.videolan.vlc;type=video/*;end";
  else location.href="vlc://"+url;
}
function fmt(t){t=Math.max(0,t|0);const h=t/3600|0,m=(t%3600)/60|0,s=t%60;return(h?h+":":"")+String(m).padStart(2,"0")+":"+String(s).padStart(2,"0")}
async function play(id,g){
  const it=g.items.find(x=>x.id===id);const p=document.getElementById("player");
  if(STATIC){const href=fileUrl(it.rel);const ua=navigator.userAgent;const android=/Android/.test(ua);
    const path=decodeURIComponent(href.replace(/^file:\/\//,""));
    const vlcA="intent://"+path.replace(/^\//,"")+"#Intent;scheme=file;package=org.videolan.vlc;type=video/*;end";
    p.innerHTML=`<div class="menu"><a href="${href}"><button class="b">▶ Ouvrir ${esc(it.file)}</button></a>${android?`<a href="${vlcA}"><button class="b" style="background:#ff8800;color:#000">Ouvrir dans VLC</button></a>`:""}<button class="b" id="mark" style="background:var(--card);color:var(--txt)">✓ Marquer vu</button></div><div class="note">Le fichier s'ouvre avec le lecteur de l'appareil. Sur tablette/téléphone, VLC est conseillé pour les .mkv.</div>`;
    p.querySelector("#mark").onclick=()=>{post("/api/progress",{id,done:true});PROG[id]={t:0,dur:0,done:true,at:Date.now()/1000};document.querySelectorAll("#box .ep").forEach(e=>{if(e.dataset.id===id)e.classList.add("done")})};
    p.scrollIntoView({behavior:"smooth"});return}
  const url=location.origin+"/video/"+id+"/"+encodeURIComponent(it.file);
  if(OFFLINE){p.innerHTML='<div class="note">✈️ Hors connexion : impossible de lire depuis le PC. Les épisodes téléchargés (⬇) sont dans l\'appli Fichiers / VLC de ton appareil.</div>';p.scrollIntoView({behavior:"smooth"});return}
  p.innerHTML='<div class="note">Preparation...</div>';p.scrollIntoView({behavior:"smooth"});
  let info={};try{info=await(await fetch("/api/probe/"+id)).json()}catch(e){}
  const native=info.native;const canConv=info.ffmpeg;
  if(window.Android&&window.Android.play&&!native&&!canConv){vlc(id,g);p.innerHTML='<div class="note">Lecture dans VLC (ou le lecteur choisi).</div>';return}
  let offset=0,audio=info.audio_default??0,sub=info.sub_default??-1,hq=720;
  const dur=info.duration||0;
  const tracks=(arr,cur,name)=>arr&&arr.length?`<select data-k="${name}">${(name==="s"?'<option value="-1"'+(cur===-1?" selected":"")+'>Sans sous-titres</option>':"")+arr.map(a=>`<option value="${a.i}"${a.i===cur?" selected":""}>${name==="a"?"🔊 ":"💬 "}${esc(lab(a))}</option>`).join("")}</select>`:"";
  p.innerHTML=`<div class="vwrap"><video id="v" playsinline ${native?"controls":""}></video></div>
  ${native?"":`<div class="ctl"><button id="pp">▶</button><span id="tm">0:00</span><input type="range" id="sk" min="0" max="${Math.max(1,dur|0)}" value="0" step="1"><span>${fmt(dur)}</span><button id="fs">⛶</button></div>`}
  <div class="menu">${native?"":tracks(info.audio,audio,"a")+tracks(info.subs,sub,"s")+`<select data-k="h"><option value="480">480p</option><option value="720" selected>720p</option><option value="1080">1080p</option></select>`}
  <button class="b" style="background:#ff8800;color:#000" id="vlcbtn">Ouvrir dans VLC</button>${canConv?`<a href="/download/${id}?h=720"><button class="b" style="background:var(--card);color:var(--txt)" title="mp4 720p lisible partout, pour regarder sans le PC">⬇ Télécharger (hors-ligne)</button></a>`:""}<a href="${url}" download><button class="b" style="background:var(--card);color:var(--txt)">Fichier original</button></a></div>
  ${(!native&&!canConv)?'<div class="note">Ce format ne se lit pas directement : clique « Activer les miniatures » en haut (installe ffmpeg) pour lire les .mkv ici.</div>':""}`;
  p.querySelector("#vlcbtn").onclick=()=>vlc(id,g);
  document.querySelectorAll("#box .ep").forEach(e=>e.classList.toggle("sel",e.dataset.id===id));
  const v=p.querySelector("#v");
  if(native){v.src=url;const pr=PROG[id];if(pr&&!pr.done&&pr.t>30)v.currentTime=pr.t;v.play().catch(()=>{});
    let ls=-1;v.ontimeupdate=()=>{const ti=v.currentTime|0;if(ti%5===0&&ti!==ls){ls=ti;PROG[id]={t:ti,dur:v.duration||0,done:v.duration&&ti>=v.duration*0.92,at:Date.now()/1000};if(!STATIC)post("/api/progress",{id,t:ti,dur:v.duration||0,quiet:true})}};
    v.onpause=()=>{if(!STATIC)post("/api/progress",{id,t:v.currentTime,dur:v.duration||0})};v.onended=()=>{PROG[id]={t:v.duration,dur:v.duration,done:true,at:Date.now()/1000};if(!STATIC)post("/api/progress",{id,t:v.duration,dur:v.duration,done:true});nextEpisode(g,id)};return}
  if(!canConv)return;
  const sk=p.querySelector("#sk"),tm=p.querySelector("#tm"),pp=p.querySelector("#pp");
  function src(t){offset=t;v.src=`/play/${id}?t=${t|0}&a=${audio}&s=${sub}&h=${hq}`;v.play().catch(()=>{});pp.textContent="⏸"}
  let lastSent=-1;
  const send=(t,quiet)=>{if(!STATIC)post("/api/progress",{id,t,dur,quiet:!!quiet})};
  if(!PROG[id])PROG[id]={t:0,dur,done:false,at:Date.now()/1000};
  v.ontimeupdate=()=>{const t=offset+v.currentTime;tm.textContent=fmt(t);if(!sk.matches(":active"))sk.value=t|0;
    const ti=t|0;if(ti%5===0&&ti!==lastSent){lastSent=ti;PROG[id]={t:ti,dur,done:dur&&ti>=dur*0.92,at:Date.now()/1000};send(ti,true)}};
  v.onpause=()=>{pp.textContent="▶";send(offset+v.currentTime)};
  window.onbeforeunload=()=>{try{navigator.sendBeacon("/api/progress",JSON.stringify({id,t:offset+v.currentTime,dur}))}catch(e){}};
  v.onended=()=>{pp.textContent="▶";PROG[id]={t:dur,dur,done:true,at:Date.now()/1000};send(dur);nextEpisode(g,id)};v.onplay=()=>{pp.textContent="⏸"};
  sk.onchange=()=>src(+sk.value);
  pp.onclick=()=>{v.paused?v.play():v.pause()};
  p.querySelector("#fs").onclick=()=>{if(v.webkitEnterFullscreen&&!v.requestFullscreen)v.webkitEnterFullscreen();else(v.requestFullscreen||v.webkitRequestFullscreen).call(v)};
  p.querySelectorAll("select").forEach(sel=>sel.onchange=()=>{const k=sel.dataset.k;const val=+sel.value;if(k==="a")audio=val;else if(k==="s")sub=val;else hq=val;src(offset+v.currentTime)});
  const pr=PROG[id];src(pr&&!pr.done&&pr.t>30&&(!dur||pr.t<dur-10)?pr.t:0);
}
function close(){document.getElementById("dlg").classList.remove("on");document.getElementById("box").innerHTML=""}
document.getElementById("dlg").onclick=e=>{if(e.target.id==="dlg")close()};
document.addEventListener("keydown",e=>{if(e.key==="Escape")close()});
document.getElementById("rescan").onclick=async()=>{await fetch("/api/rescan");load()};
document.getElementById("ffm").onclick=async()=>{await fetch("/api/install_ffmpeg");load()};
document.getElementById("exp").onclick=async()=>{if(!confirm("Écrire sur le disque :\n• Mediatheque.html à la racine (catalogue consultable partout)\n• folder.jpg + tvshow.nfo dans chaque dossier d'anime (image et titre reconnus par les lecteurs de télé/tablette et l'Explorateur)\n\nAucune vidéo n'est modifiée. Continuer ?"))return;await fetch("/api/export");await fetch("/api/prepare");load()};
document.getElementById("addroot").onclick=async()=>{const p=prompt("Chemin du dossier ou du disque à ajouter :\n(ex. E:\\  ou  /storage/1234-ABCD  ou  /sdcard/Movies)");if(!p)return;const r=await fetch("/api/add_root",{method:"POST",body:JSON.stringify({path:p})});if(!r.ok)alert("Dossier introuvable : "+p);else load()};
document.getElementById("fwbtn").onclick=async()=>{await fetch("/api/firewall");setTimeout(load,4000)};
document.getElementById("pwa").onclick=async()=>{const st=document.getElementById("st");
  if(!navigator.serviceWorker||!navigator.serviceWorker.controller){st.textContent="Recharge la page une fois puis réessaie (sur iPhone : ajoute d'abord l'appli à l'écran d'accueil via Partager → Sur l'écran d'accueil)";return}
  await fetch("/api/library");const seen=new Set(),urls=[];for(const it of data.items){const k=it.category+"|"+coll(it).toLowerCase();if(it.thumb&&!seen.has(k)){seen.add(k);urls.push("/thumb/"+it.id)}}
  st.textContent="Mémorisation de "+urls.length+" images...";navigator.serviceWorker.controller.postMessage({type:"cacheThumbs",urls});
  alert("Catalogue mémorisé. En mode avion, ouvre l'icône Mediatheque : tu retrouveras tout ton catalogue.\n\nPour regarder un épisode sans le PC, télécharge-le à l'avance (bouton ⬇ dans la fiche).")};
document.getElementById("thm").onclick=async()=>{await fetch("/api/thumbs");load()};
document.getElementById("thmstop").onclick=async()=>{await fetch("/api/thumbs_stop");load()};
document.getElementById("quit").onclick=async()=>{if(confirm("Fermer la Mediatheque ? (le telephone n'y aura plus acces)")){await fetch("/api/quit").catch(()=>{});document.body.innerHTML='<div class="empty">Mediatheque fermee. Tu peux fermer cette fenetre.</div>';setTimeout(()=>window.close(),800)}};
async function load(){if(STATIC){data=STATIC;PROG=Object.assign({},STATIC.progress||{});try{Object.assign(PROG,JSON.parse(localStorage.getItem("prog-static")||"{}"))}catch(e){}document.getElementById("share").style.display="none";document.getElementById("st").textContent="Mode hors-ligne · catalogue du "+new Date((STATIC.exported||0)*1000).toLocaleDateString("fr-FR")+" · lecture avec le lecteur de l'appareil";render();return}try{const r=await fetch("/api/library");const off=r.headers.get("X-Offline")==="1";data=await r.json();if(!off)flushQueue();
  OFFLINE=off;document.getElementById("offline").style.display=off?"":"none";
  if(data.embedded){["quit","pwa","fwbtn"].forEach(i=>{const e=document.getElementById(i);if(e)e.style.display="none"});const ia=document.querySelector('a[href="/installer"]');if(ia)ia.style.display="none"}document.getElementById("fw").style.display=(data.firewall===false&&["localhost","127.0.0.1"].includes(location.hostname))?"":"none";document.getElementById("share").style.display=off?"none":"flex";
  const srvProg=data.progress||{};let qd=[];try{qd=JSON.parse(localStorage.getItem("pending")||"[]")}catch(e){}
  qd.forEach(([u,o])=>{if(u==="/api/progress"){if(o.reset)delete srvProg[o.id];else srvProg[o.id]={t:o.t||0,dur:o.dur||0,done:o.done!==undefined?o.done:(o.dur&&o.t>=o.dur*0.92),at:Date.now()/1000}}if(u==="/api/progress_many")o.ids.forEach(id=>{if(o.done)srvProg[id]={t:0,dur:0,done:true,at:Date.now()/1000};else delete srvProg[id]})});
  PROG=srvProg;document.getElementById("url").textContent=data.url;document.getElementById("ffm").style.display=(!data.ffmpeg&&data.windows&&!data.installing)?"":"none";
const t=document.getElementById("thm"),ts=document.getElementById("thmstop");t.style.display=(data.ffmpeg&&!data.thumb_job&&data.missing_thumbs>0)?"":"none";t.textContent="Miniatures manquantes ("+data.missing_thumbs+")";ts.style.display=data.thumb_job?"":"none";render()}catch(e){document.getElementById("st").textContent="Serveur injoignable (PC éteint ou pas sur le même Wi-Fi)"}}
load();if(!STATIC)setInterval(()=>{if(!document.getElementById("dlg").classList.contains("on"))load()},5000);
</script></body></html>"""


INSTALL_HTML = r"""<!DOCTYPE html><html lang="fr"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Installer Mediatheque</title>
<style>body{font:16px/1.5 -apple-system,Segoe UI,Roboto,sans-serif;background:#0f1115;color:#e8ebf1;margin:0;padding:20px;max-width:720px;margin:auto}h1{font-size:22px}h2{font-size:18px;margin-top:28px;color:#7aa2f7}code,pre{background:#1e222b;padding:3px 7px;border-radius:6px;font-size:14px}pre{padding:12px;overflow-x:auto;white-space:pre-wrap;word-break:break-all}a{color:#7aa2f7}.b{display:inline-block;background:#7aa2f7;color:#0b0d10;padding:9px 14px;border-radius:8px;text-decoration:none;font-weight:600;margin:6px 0}ol li{margin:8px 0}.dim{color:#8b93a5}</style></head><body>
<h1>Installer Mediatheque sur cet appareil</h1>
<p class="dim">Pour que l'appli tourne <b>directement sur l'appareil</b>, disque branché dessus, sans le PC.</p>
<h2>Android (téléphone ou tablette)</h2>
<ol>
<li>Installe <b>Termux</b> (gratuit) : <a href="https://f-droid.org/packages/com.termux/">F-Droid</a> ou <a href="https://github.com/termux/termux-app/releases">GitHub</a> (la version Play Store est trop ancienne).</li>
<li>Ouvre Termux et tape (ou copie-colle) :<br><pre>curl -s http://{IP}:{PORT}/android.sh | bash</pre>Accepte l'accès au stockage quand Android le demande. Ça installe Python + ffmpeg et lance l'appli.</li>
<li>Ensuite, pour lancer l'appli : ouvre Termux et tape <code>~/mediatheque/lancer.sh</code> — ou installe <b>Termux:Widget</b> pour avoir un bouton « Mediatheque » sur l'écran d'accueil.</li>
<li>Branche le disque USB : il est détecté et scanné. La page s'ouvre sur <code>http://localhost:{PORT}</code>.</li>
</ol>
<h2>iPad</h2>
<ol>
<li>Installe <b>a-Shell</b> (gratuit, App Store).</li>
<li>Dans a-Shell : <pre>curl -o mediatheque.py http://{IP}:{PORT}/mediatheque.py
python3 mediatheque.py</pre></li>
<li>Ouvre Safari <b>en écran partagé</b> à côté d'a-Shell, sur <code>http://localhost:{PORT}</code>. Pour le disque : dans a-Shell, <code>pickFolder</code> puis choisis le disque, et ajoute ce dossier dans l'appli (bouton « Ajouter un dossier »).</li>
</ol>
<h2>iPhone et télé</h2>
<p>Pas de programme possible : utilise <b>VLC → Navigation</b> (iPhone) ou le lecteur de la télé pour parcourir le disque, rangé par dossiers avec ses images. Sur iPhone, l'appli « mémorisée » (icône Mediatheque) reste consultable hors-ligne.</p>
<h2>PC / Mac</h2>
<p><a class="b" href="/mediatheque.py">Télécharger mediatheque.py</a> puis <code>python3 mediatheque.py</code> (Python 3 requis, ffmpeg conseillé).</p>
</body></html>"""

SW_JS = r"""
const V="mediatheque-v3";
const SHELL=["/","/manifest.webmanifest","/icon.png"];
self.addEventListener("install",e=>{e.waitUntil(caches.open(V).then(c=>c.addAll(SHELL)).then(()=>self.skipWaiting()))});
self.addEventListener("activate",e=>{e.waitUntil(caches.keys().then(ks=>Promise.all(ks.filter(k=>k!==V).map(k=>caches.delete(k)))).then(()=>self.clients.claim()))});
function offline(r){const h=new Headers(r.headers);h.set("X-Offline","1");return r.blob().then(b=>new Response(b,{status:r.status,headers:h}))}
self.addEventListener("fetch",e=>{
  const u=new URL(e.request.url);
  if(e.request.method!=="GET")return;
  if(u.pathname==="/api/library"){
    e.respondWith(fetch(e.request).then(r=>{if(r.ok){const c=r.clone();caches.open(V).then(x=>x.put("/api/library",c))}return r})
      .catch(()=>caches.match("/api/library").then(r=>r?offline(r):new Response('{"items":[],"offline":true,"status":"Aucun catalogue en memoire"}',{headers:{"Content-Type":"application/json","X-Offline":"1"}}))));
    return}
  if(u.pathname.startsWith("/thumb/")){
    e.respondWith(caches.match(e.request).then(hit=>hit||fetch(e.request).then(r=>{if(r.ok){const c=r.clone();caches.open(V).then(x=>x.put(e.request,c))}return r}).catch(()=>new Response("",{status:404}))));
    return}
  if(u.pathname==="/"||u.pathname==="/manifest.webmanifest"||u.pathname==="/icon.png"){
    e.respondWith(fetch(e.request).then(r=>{if(r.ok){const c=r.clone();caches.open(V).then(x=>x.put(e.request,c))}return r}).catch(()=>caches.match(u.pathname)));
    return}
});
self.addEventListener("message",e=>{if(e.data&&e.data.type==="cacheThumbs"){caches.open(V).then(async c=>{let n=0;for(const url of e.data.urls){try{if(!(await c.match(url))){const r=await fetch(url);if(r.ok)await c.put(url,r)}n++}catch(x){}}
  const cl=await self.clients.matchAll();cl.forEach(w=>w.postMessage({type:"thumbsDone",n}))})}});
"""

MANIFEST = json.dumps({
    "name": "Mediatheque", "short_name": "Mediatheque", "start_url": "/", "scope": "/",
    "display": "standalone", "background_color": "#0f1115", "theme_color": "#0f1115",
    "icons": [{"src": "/icon.png", "sizes": "192x192", "type": "image/png"},
              {"src": "/icon.png", "sizes": "512x512", "type": "image/png"}]})


def make_icon_png(size=192):
    """Icone PNG simple (carre bleu avec un triangle 'play'), sans dependance."""
    import zlib, struct
    bg, fg = (0x1d, 0x20, 0x27), (0x7a, 0xa2, 0xf7)
    rows = []
    for y in range(size):
        row = bytearray([0])
        for x in range(size):
            # triangle play centre
            x0, x1 = size * 0.36, size * 0.72
            yc = size / 2
            inside = x0 <= x <= x1 and abs(y - yc) <= (x1 - x) * 0.8
            row += bytes(fg if inside else bg)
        rows.append(bytes(row))
    raw = b"".join(rows)
    def chunk(t, d):
        return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xffffffff)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


ICON_PNG = make_icon_png()


# --------------------------------------------------------------------------
# Serveur HTTP
# --------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="text/html; charset=utf-8", extra=None):
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        p = urlparse(self.path)
        parts = [unquote(x) for x in p.path.split("/") if x]
        if not parts:
            return self._send(200, HTML)
        if parts == ["mediatheque.py"]:
            with open(os.path.abspath(sys.argv[0]), "rb") as f:
                return self._send(200, f.read(), "text/x-python; charset=utf-8",
                                  {"Content-Disposition": "attachment; filename=\"mediatheque.py\""})
        if parts == ["android.sh"]:
            ip = local_ip()
            sh = ("#!/data/data/com.termux/files/usr/bin/bash\nset -e\n"
                  "echo '== Mediatheque : installation sur Android =='\n"
                  "pkg update -y >/dev/null 2>&1 || true\n"
                  "pkg install -y python ffmpeg termux-api curl\n"
                  "termux-setup-storage || true\n"
                  "mkdir -p ~/mediatheque\n"
                  "curl -fsS -o ~/mediatheque/mediatheque.py http://%s:%d/mediatheque.py\n"
                  "cat > ~/mediatheque/lancer.sh <<'EOS'\n#!/data/data/com.termux/files/usr/bin/bash\n"
                  "cd ~/mediatheque && python mediatheque.py\nEOS\nchmod +x ~/mediatheque/lancer.sh\n"
                  "mkdir -p ~/.shortcuts && cp ~/mediatheque/lancer.sh ~/.shortcuts/Mediatheque\n"
                  "echo\necho '== Termine. Lancement... (ensuite : tape  ~/mediatheque/lancer.sh  ou ajoute le widget Termux:Widget)'\n"
                  "~/mediatheque/lancer.sh\n") % (ip, PORT)
            return self._send(200, sh, "text/plain; charset=utf-8")
        if parts == ["installer"]:
            ip = local_ip()
            page = INSTALL_HTML.replace("{IP}", ip).replace("{PORT}", str(PORT))
            return self._send(200, page)
        if parts == ["sw.js"]:
            return self._send(200, SW_JS, "application/javascript; charset=utf-8",
                              {"Service-Worker-Allowed": "/"})
        if parts == ["manifest.webmanifest"]:
            return self._send(200, MANIFEST, "application/manifest+json")
        if parts == ["icon.png"]:
            return self._send(200, ICON_PNG, "image/png", {"Cache-Control": "max-age=86400"})
        if parts[0] == "download" and len(parts) >= 2:
            item = LIB.by_id(parts[1])
            if not item or not os.path.isfile(item["path"]) or not FFMPEG:
                return self._send(404, "Telechargement impossible", "text/plain")
            q = parse_qs(p.query)
            name = re.sub(r"[^\w\s\-\.]", "", "%s S%sE%s" % (item["title"], item["season"], item["episode"])).strip() + ".mp4"
            self._dl_name = name
            return self._transcode(item, 0, -1, -2, int(q.get("h", ["720"])[0]))
        if parts[0] == "api" and parts[1:] == ["library"]:
            return self._send(200, json.dumps(LIB.export(), ensure_ascii=False),
                              "application/json; charset=utf-8")
        if parts[0] == "api" and parts[1:] == ["quit"]:
            self._send(200, "{}", "application/json")
            STOP.set()
            threading.Timer(0.3, lambda: os._exit(0)).start()
            return
        if parts[0] == "api" and parts[1:] == ["install_ffmpeg"]:
            threading.Thread(target=install_ffmpeg, daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and parts[1:] == ["rescan"]:
            roots = [r for r in LIB.roots() if os.path.isdir(r)] or list_drives()
            threading.Thread(target=scan, args=(roots,), daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and len(parts) == 3 and parts[1] == "probe":
            item = LIB.by_id(parts[2])
            if not item:
                return self._send(404, "{}", "application/json")
            info = dict(probe(item))
            info["ffmpeg"] = bool(FFMPEG)
            info["native"] = item["file"].lower().endswith((".mp4", ".m4v", ".webm", ".mov"))
            return self._send(200, json.dumps(info), "application/json; charset=utf-8")
        if parts[0] == "api" and len(parts) == 3 and parts[1] == "open":
            item = LIB.by_id(parts[2])
            if item and os.path.isfile(item["path"]):
                open_with_player(item["path"])
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and len(parts) == 3 and parts[1] == "path" and EMBEDDED:
            item = LIB.by_id(parts[2])
            return self._send(200, json.dumps({"path": item["path"] if item else ""}), "application/json; charset=utf-8")
        if parts[0] == "api" and parts[1:] == ["diag"]:
            out = []
            cmds = [["ipconfig"], ["netsh", "advfirewall", "show", "currentprofile"],
                    ["netsh", "advfirewall", "firewall", "show", "rule", "name=Mediatheque"],
                    ["netstat", "-an", "-p", "tcp"]] if os.name == "nt" else [["ip", "addr"]]
            for c in cmds:
                try:
                    r = subprocess.run(c, capture_output=True, timeout=20, creationflags=NOWIN)
                    txt = r.stdout.decode("cp850" if os.name == "nt" else "utf-8", "replace")
                    if c[0] == "netstat":
                        txt = "\n".join(l for l in txt.splitlines() if "8765" in l)
                    out.append("### " + " ".join(c) + "\n" + txt)
                except Exception as exc:
                    out.append("### " + " ".join(c) + " : " + str(exc))
            out.append("### pare-feu ok : %s" % FIREWALL["ok"])
            return self._send(200, "\n\n".join(out), "text/plain; charset=utf-8")
        if parts[0] == "api" and parts[1:] == ["firewall"]:
            threading.Thread(target=ensure_firewall, daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and parts[1:] == ["thumbs"]:
            threading.Thread(target=make_all_thumbs, daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and parts[1:] == ["thumbs_stop"]:
            THUMB_JOB["cancel"] = True
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and parts[1:] == ["prepare"]:
            threading.Thread(target=prepare_disk, daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "api" and parts[1:] == ["export"]:
            threading.Thread(target=export_offline, daemon=True).start()
            return self._send(200, "{}", "application/json")
        if parts[0] == "play" and len(parts) >= 2:
            item = LIB.by_id(parts[1])
            if not item or not os.path.isfile(item["path"]) or not FFMPEG:
                return self._send(404, "Lecture impossible", "text/plain")
            q = parse_qs(p.query)
            def qi(k, d):
                try:
                    return int(float(q.get(k, [d])[0]))
                except Exception:
                    return d
            return self._transcode(item, qi("t", 0), qi("a", -1), qi("s", -2), qi("h", 720))
        if parts[0] == "thumb" and len(parts) == 2:
            item = LIB.by_id(parts[1])
            if item and os.path.isfile(thumb_path(item)):
                with open(thumb_path(item), "rb") as f:
                    return self._send(200, f.read(), "image/jpeg",
                                      {"Cache-Control": "max-age=86400"})
            return self._send(404, "")
        if parts[0] == "video" and len(parts) >= 2:
            item = LIB.by_id(parts[1])
            if not item or not os.path.isfile(item["path"]):
                return self._send(404, "Fichier absent (disque debranche ?)", "text/plain")
            return self._stream(item["path"])
        self._send(404, "Introuvable", "text/plain")

    def do_POST(self):
        p = urlparse(self.path)
        n = int(self.headers.get("Content-Length", 0))
        body = json.loads(self.rfile.read(n) or b"{}")
        if p.path == "/api/progress":
            iid = body.get("id")
            if iid:
                with LIB.lock:
                    cur = LIB.progress.get(iid, {})
                    if body.get("reset"):
                        LIB.progress.pop(iid, None)
                    else:
                        t = float(body.get("t", cur.get("t", 0)) or 0)
                        dur = float(body.get("dur", cur.get("dur", 0)) or 0)
                        done = bool(body.get("done")) if "done" in body else (dur > 0 and t >= dur * 0.92)
                        LIB.progress[iid] = {"t": round(t, 1), "dur": round(dur, 1), "done": done,
                                             "at": int(time.time())}
                    if not body.get("quiet"):
                        LIB.save()
            return self._send(200, "{}", "application/json")
        if p.path == "/api/progress_many":
            with LIB.lock:
                for iid in body.get("ids", []):
                    if body.get("done"):
                        cur = LIB.progress.get(iid, {})
                        LIB.progress[iid] = {"t": cur.get("dur", 0), "dur": cur.get("dur", 0), "done": True,
                                             "at": int(time.time())}
                    else:
                        LIB.progress.pop(iid, None)
                LIB.save()
            return self._send(200, "{}", "application/json")
        if p.path == "/api/add_root":
            root = (body.get("path") or "").strip()
            if root and os.path.isdir(root):
                roots = extra_roots()
                if root not in roots:
                    roots.append(root)
                    os.makedirs(DATA_DIR, exist_ok=True)
                    with open(EXTRA_ROOTS_FILE, "w", encoding="utf-8") as f:
                        json.dump(roots, f)
                threading.Thread(target=scan, args=([root],), daemon=True).start()
                return self._send(200, "{}", "application/json")
            return self._send(400, json.dumps({"error": "Dossier introuvable"}), "application/json")
        if p.path == "/api/forget_disk":
            did = body.get("id")
            with LIB.lock:
                LIB.items = [i for i in LIB.items if i.get("drive_id") != did]
                LIB.sources.pop(did, None)
                LIB.save()
            return self._send(200, "{}", "application/json")
        if p.path == "/api/unclass":
            with LIB.lock:
                for iid in body.get("ids", []):
                    LIB.overrides.pop(iid, None)
                LIB.save()
            return self._send(200, "{}", "application/json")
        if p.path == "/api/reclass":
            with LIB.lock:
                for iid in body.get("ids", []):
                    LIB.overrides[iid] = body.get("cat", "Autres")
                LIB.save()
            return self._send(200, "{}", "application/json")
        self._send(404, "")

    def _transcode(self, item, start, audio, sub, height):
        info = probe(item)
        if audio < 0:
            audio = info["audio_default"]
        if sub == -2:
            sub = info["sub_default"]
        cmd = transcode_cmd(item, start, audio, sub, height)
        try:
            os.makedirs(SUBS_DIR, exist_ok=True)
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                                    creationflags=NOWIN, cwd=SUBS_DIR)
        except Exception as exc:
            return self._send(500, str(exc), "text/plain")
        self.send_response(200)
        self.send_header("Content-Type", "video/mp4")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Connection", "close")
        if getattr(self, "_dl_name", None):
            self.send_header("Content-Disposition", "attachment; filename=\"%s\"; filename*=UTF-8''%s"
                             % (self._dl_name.encode("ascii", "replace").decode(), quote(self._dl_name)))
        self.end_headers()
        try:
            while True:
                chunk = proc.stdout.read(64 * 1024)
                if not chunk:
                    break
                self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
            pass
        finally:
            try:
                proc.kill()
            except Exception:
                pass

    def _stream(self, path):
        size = os.path.getsize(path)
        ctype = mimetypes.guess_type(path)[0] or "application/octet-stream"
        if path.lower().endswith(".mkv"):
            ctype = "video/x-matroska"
        start, end = 0, size - 1
        rng = self.headers.get("Range")
        if rng and rng.startswith("bytes="):
            a, _, b = rng[6:].partition("-")
            start = int(a) if a else max(0, size - int(b))
            end = int(b) if (b and a) else size - 1
            end = min(end, size - 1)
            self.send_response(206)
            self.send_header("Content-Range", "bytes %d-%d/%d" % (start, end, size))
        else:
            self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Content-Length", str(end - start + 1))
        self.end_headers()
        try:
            with open(path, "rb") as f:
                f.seek(start)
                left = end - start + 1
                while left > 0:
                    chunk = f.read(min(1024 * 512, left))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    left -= len(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass


def prepare_disk():
    """Ecrit folder.jpg + tvshow.nfo dans chaque dossier d'anime : reconnus par Kodi, Nova,
    les lecteurs de tele et l'Explorateur Windows (icone du dossier)."""
    import shutil
    LIB.status = "Preparation du disque..."
    with LIB.lock:
        items = list(LIB.items)
    roots = sorted(LIB.roots(), key=len)
    folders = {}
    for it in items:
        root = next((r for r in roots if it["path"].lower().startswith(r.lower())), None)
        if not root or not os.path.isdir(root):
            continue
        rel = it["path"][len(root):].replace("\\", "/").strip("/").split("/")
        # dossier de la collection = premier dossier sous anime/films/series (ou le premier segment)
        idx = 0
        for i, seg in enumerate(rel[:-1]):
            if folder_kind(seg) == ("root", None):
                idx = i + 1
        if idx >= len(rel) - 1:
            continue
        cdir = os.path.join(root, *rel[:idx + 1])
        folders.setdefault(cdir, []).append(it)
    n = 0
    for cdir, its in folders.items():
        try:
            if not os.path.isfile(os.path.join(cdir, "folder.jpg")):
                src = next((thumb_path(i) for i in its if os.path.isfile(thumb_path(i))), None)
                if src:
                    shutil.copyfile(src, os.path.join(cdir, "folder.jpg"))
            nfo = os.path.join(cdir, "tvshow.nfo")
            if not os.path.isfile(nfo):
                title = its[0].get("collection") or its[0]["title"]
                seasons = sorted({i["season"] for i in its if i["season"]})
                with open(nfo, "w", encoding="utf-8") as f:
                    f.write("<tvshow><title>%s</title><season>%d</season><episode>%d</episode></tvshow>\n"
                            % (title.replace("&", "&amp;").replace("<", "&lt;"), len(seasons), len(its)))
            n += 1
        except OSError:
            pass
    LIB.status = "Disque prepare : %d dossiers (folder.jpg + tvshow.nfo)" % n


def export_offline():
    """Ecrit Mediatheque.html a la racine du disque : catalogue consultable sans l'appli."""
    import base64
    LIB.status = "Export hors-ligne..."
    data = LIB.export()
    roots = sorted(LIB.roots(), key=len)
    for it in data["items"]:
        full = LIB.by_id(it["id"])["path"]
        root = next((r for r in roots if full.lower().startswith(r.lower())), None)
        it["rel"] = full[len(root):].replace("\\", "/").lstrip("/") if root else ""
    # une miniature par titre (base64) pour rester leger
    seen = set()
    for it in data["items"]:
        key = (it["category"], it["title"].lower())
        it["thumb_data"] = ""
        if key in seen or not it["thumb"]:
            continue
        try:
            with open(thumb_path(LIB.by_id(it["id"])), "rb") as f:
                it["thumb_data"] = "data:image/jpeg;base64," + base64.b64encode(f.read()).decode()
            seen.add(key)
        except Exception:
            pass
    data["exported"] = int(time.time())
    payload = "window.__DATA__=" + json.dumps(data, ensure_ascii=False) + ";"
    html = HTML.replace("/*__STATIC__*/", payload)
    written = []
    for root in roots + [DATA_DIR]:
        try:
            out = os.path.join(root, "Mediatheque.html")
            with open(out, "w", encoding="utf-8") as f:
                f.write(html)
            written.append(out)
        except Exception:
            pass
    LIB.status = "Export hors-ligne : " + (", ".join(written) if written else "echec")


FIREWALL = {"ok": None}


def firewall_rule_exists():
    try:
        r = subprocess.run(["netsh", "advfirewall", "firewall", "show", "rule", "name=Mediatheque"],
                           capture_output=True, timeout=15, creationflags=NOWIN)
        return b"8765" in r.stdout
    except Exception:
        return True


def ensure_firewall():
    """Ouvre le port 8765 dans le pare-feu Windows (une seule fois, demande l'accord UAC)."""
    if os.name != "nt":
        FIREWALL["ok"] = True
        return
    if firewall_rule_exists():
        FIREWALL["ok"] = True
        return
    try:
        import ctypes
        args = ('advfirewall firewall add rule name="Mediatheque" dir=in action=allow '
                'protocol=TCP localport=%d profile=any enable=yes' % PORT)
        rc = ctypes.windll.shell32.ShellExecuteW(None, "runas", "netsh", args, None, 0)
        time.sleep(3)
        FIREWALL["ok"] = firewall_rule_exists() if rc > 32 else False
    except Exception:
        FIREWALL["ok"] = False
    dbg("pare-feu : %s" % FIREWALL["ok"])


def open_with_player(path):
    import shutil
    if EMBEDDED:
        return
    try:
        if os.name == "nt":
            os.startfile(path)
        elif ANDROID:
            if shutil.which("termux-open"):
                subprocess.Popen(["termux-open", path])
            else:
                subprocess.Popen(["am", "start", "-a", "android.intent.action.VIEW",
                                  "-d", "file://" + path, "-t", "video/*"])
        elif sys.platform == "darwin":
            subprocess.Popen(["open", path])
        else:
            subprocess.Popen(["xdg-open", path])
    except Exception:
        pass


def find_app_browser():
    """Edge ou Chrome en mode application (fenetre sans barre d'adresse)."""
    pf = os.environ.get("ProgramFiles", r"C:\Program Files")
    pf86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
    local = os.environ.get("LocalAppData", "")
    for exe in (os.path.join(pf86, "Microsoft", "Edge", "Application", "msedge.exe"),
                os.path.join(pf, "Microsoft", "Edge", "Application", "msedge.exe"),
                os.path.join(pf, "Google", "Chrome", "Application", "chrome.exe"),
                os.path.join(pf86, "Google", "Chrome", "Application", "chrome.exe"),
                os.path.join(local, "Google", "Chrome", "Application", "chrome.exe"),
                os.path.join(pf, "BraveSoftware", "Brave-Browser", "Application", "brave.exe")):
        if os.path.isfile(exe):
            return exe
    return None


def open_window():
    import shutil
    url = "http://localhost:%d" % PORT
    if ANDROID:
        try:
            if shutil.which("termux-open-url"):
                subprocess.Popen(["termux-open-url", url])
            else:
                subprocess.Popen(["am", "start", "-a", "android.intent.action.VIEW", "-d", url])
        except Exception:
            pass
        return
    exe = find_app_browser()
    if exe:
        try:
            subprocess.Popen([exe, "--app=" + url, "--window-size=1280,820",
                              "--user-data-dir=" + os.path.join(DATA_DIR, "fenetre")],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return
        except Exception:
            pass
    webbrowser.open(url)


def show_error(msg):
    try:
        import tkinter as tk
        from tkinter import messagebox
        r = tk.Tk(); r.withdraw()
        messagebox.showerror("Mediatheque", msg)
    except Exception:
        pass


def dbg(msg):
    try:
        with open(os.path.join(DATA_DIR, "log.txt"), "a", encoding="utf-8") as f:
            f.write("%s [%d] %s\n" % (time.strftime("%H:%M:%S"), os.getpid(), msg))
    except Exception:
        pass


RELOAD = {"on": False}


def watch_self(srv):
    """Demande un redemarrage quand ce fichier est mis a jour."""
    me = os.path.abspath(sys.argv[0])
    try:
        last = os.path.getmtime(me)
    except OSError:
        return
    while not STOP.is_set():
        time.sleep(3)
        try:
            cur = os.path.getmtime(me)
        except OSError:
            continue
        if cur != last:
            time.sleep(2)
            dbg("fichier modifie : redemarrage")
            RELOAD["on"] = True
            STOP.set()
            LIB.status = "Mise a jour..."
            srv.shutdown()
            return


def relaunch():
    me = os.path.abspath(sys.argv[0])
    env = dict(os.environ, MEDIATHEQUE_RELOAD="1")
    try:
        subprocess.Popen([sys.executable, me], env=env, cwd=APP_DIR, close_fds=True,
                         creationflags=(0x00000008 | 0x00000200) if os.name == "nt" else 0)
        dbg("nouveau processus lance")
    except Exception as exc:
        dbg("echec relance : %s" % exc)


class Server(ThreadingHTTPServer):
    allow_reuse_address = os.name != "nt"   # Windows : sinon deux instances peuvent partager le port


_MUTEX = None


def acquire_instance_lock(tries=30):
    """Une seule Mediatheque a la fois (mutex nomme sous Windows, fichier verrou sinon)."""
    global _MUTEX
    if EMBEDDED:
        return True
    for _ in range(tries):
        if os.name == "nt":
            try:
                import ctypes
                h = ctypes.windll.kernel32.CreateMutexW(None, True, "Local\\Mediatheque-app")
                if h and ctypes.windll.kernel32.GetLastError() != 183:   # 183 = existe deja
                    _MUTEX = h
                    return True
                if h:
                    ctypes.windll.kernel32.CloseHandle(h)
            except Exception:
                return True
        else:
            try:
                import fcntl
                f = open(os.path.join(DATA_DIR, "instance.lock"), "w")
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                _MUTEX = f
                return True
            except Exception:
                pass
        time.sleep(0.5)
    return False


def main():
    os.makedirs(THUMB_DIR, exist_ok=True)
    try:
        sys.stderr = open(os.path.join(DATA_DIR, "log.txt"), "a", encoding="utf-8")
    except Exception:
        pass
    reloading = bool(os.environ.get("MEDIATHEQUE_RELOAD"))
    if not acquire_instance_lock(tries=30 if reloading else 1):
        if not reloading:
            open_window()          # deja lancee : on ouvre juste la fenetre
        else:
            dbg("instance deja active : abandon")
        return
    LIB.load()                     # (re)lecture apres obtention du verrou
    srv = None
    for _ in range(30):            # apres une mise a jour, le port se libere en quelques secondes
        try:
            srv = Server(("0.0.0.0", PORT), Handler)
            break
        except OSError:
            time.sleep(0.5)
    if srv is None:
        dbg("port occupe : abandon")
        return
    dbg("serveur demarre sur le port %d" % PORT)
    srv.daemon_threads = True
    threading.Thread(target=watch_drives, daemon=True).start()
    threading.Thread(target=autosave, daemon=True).start()
    threading.Thread(target=ensure_firewall, daemon=True).start()
    threading.Thread(target=watch_self, args=(srv,), daemon=True).start()
    if not os.environ.get("MEDIATHEQUE_RELOAD") and not EMBEDDED:
        threading.Timer(0.8, open_window).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass
    STOP.set()
    srv.server_close()
    if RELOAD["on"]:
        relaunch()


def start_embedded():
    """Appele par l'appli Android : demarre le serveur dans un thread, sans fenetre."""
    os.makedirs(THUMB_DIR, exist_ok=True)
    LIB.load()
    srv = Server(("0.0.0.0", PORT), Handler)
    srv.daemon_threads = True
    threading.Thread(target=watch_drives, daemon=True).start()
    threading.Thread(target=autosave, daemon=True).start()
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return PORT


if __name__ == "__main__":
    try:
        main()
    except Exception:
        show_error("Erreur au demarrage :\n\n" + traceback.format_exc())
        raise

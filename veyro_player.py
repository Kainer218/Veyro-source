"""
Veyro Player - modern video + audio player for Windows (works on any OS Qt supports)
=====================================================================================
Plays MP4, MKV, MOV, AVI, WebM, MP3, FLAC, M4A ... Built with PySide6 (Qt 6): hardware
accelerated playback, 17 colour themes (Settings > Appearance), custom line icons.

Install:    pip install PySide6 "yt-dlp[default]" imageio-ffmpeg   (+ Deno or Node.js for YouTube)
Run:        python veyro_player.py             (or: python veyro_player.py movie.mp4)
Build .exe: double-click build_veyro.bat       (uses veyro.ico, makes dist/Veyro/Veyro.exe)
Default player: Settings > Default player, or run  Veyro.exe --register   (--unregister removes it)

Shortcuts
  Space  play / pause        Left / Right  -5s / +5s      J / L  -10s / +10s
  Up / Down  volume          M  mute                       F  fullscreen (Esc exits)
  N / P  next / previous     O  open files                 Double-click video = fullscreen
  H  back to the library (home screen)
  A / V  switch the library to Music / Videos (home screen)
  Ctrl+M  mini player (music)      U  download from the internet (YouTube, Instagram, TikTok, X ...)
  Ctrl+V  paste a link to download it
  I  info about the file that is playing (name, size, length, resolution, codec ...)
  You can also drag & drop video files (or a link) onto the window.

Code map (top to bottom - search for the class / function name)
  Theme ............ THEME_SPECS, build_theme, get_theme, set_theme, build_style   (colours, QSS)
  Icons ............ make_icon, make_app_pixmap                                      (all drawn in code)
  Downloads ........ LinkInfoThread, DownloadThread, DownloadDialog                 (yt-dlp)
  Media helpers .... make_thumb, make_cover, embedded_art_bytes, quick_art          (thumbnails / covers)
  Library .......... LibraryThread, HRow, PlaylistDialog                            (scan folders, cards)
  Converter ........ ConvertThread, ConvertDialog                                   (ffmpeg)
  Settings ......... default_settings, SettingsDialog
  Queue widgets .... QueueList, QueuePickerDialog, PlaylistPicker
  Windows glue ..... style_main_window, enable_native_window_behavior, TitleBar     (frameless window)
  Widgets .......... ModeSwitch, Veil, ControlOverlay, MiniPlayer, PopOutWindow
  Main window ...... Player  (sections are marked with banners inside the class)
  Entry point ...... register_file_associations, main                               (single instance)

Conventions
  * One file on purpose: it is easy to build into a single .exe. Keep new code inside the matching section.
  * Colours always come from the active theme dict `T` (never hard-code a colour in a widget).
  * Slow work (disk scans, yt-dlp, ffmpeg) runs in QThread subclasses and reports back with signals.
  * Optional packages (yt_dlp, imageio_ffmpeg) are imported lazily inside the functions that need them.
"""
import ctypes
import hashlib
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.request
import uuid
from ctypes import wintypes

from PySide6.QtCore import (
    QEasingCurve,
    QEvent,
    QObject,
    QPoint,
    QPointF,
    QPropertyAnimation,
    QRect,
    QRectF,
    QSettings,
    QSize,
    QStandardPaths,
    QThread,
    QTimer,
    QUrl,
    QVariantAnimation,
    Qt,
    Signal,
)
from PySide6.QtGui import (
    QAction,
    QActionGroup,
    QColor,
    QCursor,
    QDesktopServices,
    QFont,
    QFontMetrics,
    QIcon,
    QImage,
    QKeySequence,
    QLinearGradient,
    QPainter,
    QPainterPath,
    QPalette,
    QPen,
    QPixmap,
    QPolygonF,
    QShortcut,
)
from PySide6.QtMultimedia import (
    QAudioOutput,
    QMediaFormat,
    QMediaMetaData,
    QMediaPlayer,
)
from PySide6.QtMultimediaWidgets import (
    QVideoWidget,
)
from PySide6.QtNetwork import (
    QLocalServer,
    QLocalSocket,
)
from PySide6.QtWidgets import (
    QAbstractButton,
    QApplication,
    QButtonGroup,
    QCheckBox,
    QColorDialog,
    QDialog,
    QFileDialog,
    QFrame,
    QGraphicsOpacityEffect,
    QGridLayout,
    QHBoxLayout,
    QInputDialog,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QMainWindow,
    QMenu,
    QMessageBox,
    QProgressBar,
    QPushButton,
    QScrollArea,
    QSizePolicy,
    QSlider,
    QStackedWidget,
    QStyle,
    QStyledItemDelegate,
    QToolButton,
    QToolTip,
    QVBoxLayout,
    QWidget,
)

# ---- application identity ---------------------------------------------------
APP_NAME = "Veyro Player"          # shown to the user (window title, Windows "Open with", settings texts)
APP_TITLE = APP_NAME
APP_ID = "Veyro"                   # internal id: Qt application name (= AppData folder), Windows registry keys.
                                   # Do not change it casually - users' saved covers / file associations live under it.
SETTINGS_ORG = "VideoPlayer"       # QSettings location. Kept from the old name so existing users keep their settings.
SETTINGS_APP = "VideoPlayer"
THUMB_CACHE_DIR = "VeyroPlayerThumbs"     # in the temp folder; safe to delete (rebuilt on demand)
COVERS_DIR_NAME = "VideoPlayerCovers"     # in AppData; holds the user's custom cover pictures

# ---- supported file types ---------------------------------------------------
EXTS = {".mp4", ".m4v", ".mov", ".mkv", ".avi", ".webm", ".wmv", ".flv", ".mpg", ".mpeg", ".ts"}
AUDIO_EXTS = {".mp3", ".m4a", ".aac", ".wav", ".flac", ".ogg", ".oga", ".opus", ".wma", ".aif", ".aiff", ".mka"}
MEDIA_EXTS = EXTS | AUDIO_EXTS


def is_audio(path):
    """True if the path (or URL) points to an audio file, judged by its extension."""
    return os.path.splitext((path or "").split("?")[0])[1].lower() in AUDIO_EXTS
ACCENT = "#7c6cff"      # kept in sync with the active theme (see set_theme)


# ----------------------------------------------------------------------------
# Themes
# ----------------------------------------------------------------------------
def _mix(a, b, t):
    """Blend colour `a` towards colour `b` by the fraction `t` (0..1); returns '#rrggbb'."""
    ca, cb = QColor(a), QColor(b)
    return QColor(round(ca.red() + (cb.red() - ca.red()) * t),
                  round(ca.green() + (cb.green() - ca.green()) * t),
                  round(ca.blue() + (cb.blue() - ca.blue()) * t)).name()


def _lum(c):
    """Perceived brightness of a colour: 0 (black) .. 1 (white)."""
    c = QColor(c)
    return (0.299 * c.red() + 0.587 * c.green() + 0.114 * c.blue()) / 255


def build_theme(name, bg, accent, text, over=None):
    """Derive a complete palette from 3 base colours (background, accent, text)."""
    dark = _lum(bg) < 0.5
    ac = QColor(accent)
    t = {"name": name, "dark": dark, "bg": bg, "accent": ac.name(), "text": text}
    if dark:
        t.update(panel=_mix(bg, text, 0.05), card=_mix(bg, text, 0.09), hover=_mix(bg, text, 0.15),
                 press=_mix(bg, text, 0.22), line=_mix(bg, text, 0.16), border=_mix(bg, text, 0.20),
                 line_hi=_mix(bg, text, 0.27), itemhover=_mix(bg, text, 0.10), libhover=_mix(bg, text, 0.10),
                 accent_hi=ac.lighter(115).name(), accent_lo=ac.darker(115).name(),
                 accent_soft=ac.lighter(135).name(), hero="#ffffff", handle="#ffffff",
                 handle_hi=_mix(accent, "#ffffff", 0.6),
                 home1=_mix(bg, accent, 0.14), home2=_mix(bg, text, 0.03),
                 ph1=_mix(bg, accent, 0.30), ph2=_mix(bg, accent, 0.07), newcard=_mix(bg, accent, 0.07))
        r, g, b = QColor(bg).red(), QColor(bg).green(), QColor(bg).blue()
        t["bar"] = f"rgba({r}, {g}, {b}, 105)"
    else:
        t.update(panel=_mix(bg, "#ffffff", 0.70), card=_mix(bg, text, 0.05), hover=_mix(bg, text, 0.10),
                 press=_mix(bg, text, 0.17), line=_mix(bg, text, 0.14), border=_mix(bg, text, 0.20),
                 line_hi=_mix(bg, text, 0.30), itemhover=_mix(bg, text, 0.07), libhover=_mix(bg, text, 0.07),
                 accent_hi=ac.lighter(112).name(), accent_lo=ac.darker(112).name(),
                 accent_soft=ac.darker(125).name(), hero=_mix(text, "#000000", 0.30), handle=ac.name(),
                 handle_hi=ac.lighter(120).name(),
                 home1=_mix(bg, accent, 0.10), home2=_mix(bg, "#ffffff", 0.50),
                 ph1=_mix(bg, accent, 0.35), ph2=_mix(bg, accent, 0.15), newcard=_mix(bg, "#ffffff", 0.60))
        r, g, b = QColor(bg).red(), QColor(bg).green(), QColor(bg).blue()
        t["bar"] = f"rgba({r}, {g}, {b}, 215)"
    t.update(text2=_mix(text, bg, 0.18), dim=_mix(text, bg, 0.42), muted=_mix(text, bg, 0.55),
             disabled=_mix(text, bg, 0.68), on_accent="#ffffff" if _lum(accent) < 0.55 else "#10121a")
    t.update(over or {})
    return t


# exact colours of the original look, so the default theme stays identical
_MIDNIGHT = dict(panel="#12151e", card="#1a1e2b", hover="#232838", press="#2d3350", border="#2f3550",
                 line="#2a2f40", line_hi="#3a4060", text2="#c9cde0", dim="#9aa1bb", muted="#6f7791",
                 disabled="#5b6280", accent_hi="#8f82ff", accent_lo="#6a5ae6", accent_soft="#a89cff",
                 home1="#151833", home2="#0f1119", ph1="#2b2556", ph2="#14172a", newcard="#141729",
                 itemhover="#1c2030", libhover="#1a1e2c", handle="#ffffff", handle_hi="#c3b6ff",
                 hero="#ffffff", bar="rgba(12, 14, 22, 105)", on_accent="#ffffff")
# OLED-style "super dark": true black everywhere, surfaces only a hair lighter, WHITE accent
_SUPERDARK = dict(panel="#070707", card="#0f0f10", hover="#171718", press="#1f1f21", line="#1b1b1d",
                  border="#232326", line_hi="#323236", itemhover="#121213", libhover="#101011",
                  home1="#0d0d0d", home2="#030303", ph1="#1d1d1f", ph2="#09090a", newcard="#0b0b0c",
                  accent_hi="#ffffff", accent_lo="#d4d4d4", accent_soft="#ffffff", handle_hi="#ffffff",
                  bar="rgba(0, 0, 0, 150)", text2="#b9b9c2", dim="#85858f", muted="#5e5e68", disabled="#47474f",
                  on_accent="#0a0a0a")
# "super white": true white everywhere, neutral grey surfaces, BLACK accent
_SUPERWHITE = dict(panel="#f7f7f7", card="#f2f2f2", hover="#e9e9e9", press="#dedede", line="#e7e7e7",
                   border="#dadada", line_hi="#bcbcbc", itemhover="#f4f4f4", libhover="#f0f0f0",
                   home1="#f3f3f3", home2="#ffffff", ph1="#d4d4d4", ph2="#eaeaea", newcard="#f8f8f8",
                   accent_hi="#262626", accent_lo="#000000", accent_soft="#333333", handle_hi="#333333",
                   bar="rgba(255, 255, 255, 215)", text2="#333333", dim="#666666", muted="#8c8c8c",
                   disabled="#b8b8b8", on_accent="#ffffff")
_ACCENT_KEYS = {"accent_hi", "accent_lo", "accent_soft", "handle_hi", "home1", "ph1", "ph2", "newcard", "on_accent"}

# id: (name, background, accent, text, overrides)
THEME_SPECS = {
    "midnight": ("Midnight", "#0b0d12", "#7c6cff", "#e9ebf7", _MIDNIGHT),
    "superdark": ("Super Dark", "#000000", "#ffffff", "#d9d9e0", _SUPERDARK),
    "superwhite": ("Super White", "#ffffff", "#000000", "#111111", _SUPERWHITE),
    "ocean": ("Ocean", "#08121c", "#38bdf8", "#e6f1fa", {}),
    "aqua": ("Aqua", "#071415", "#2dd4bf", "#e3f4f2", {}),
    "forest": ("Forest", "#0a130e", "#4ade80", "#e5f3ea", {}),
    "sunset": ("Sunset", "#150d0a", "#fb923c", "#f8ebe3", {}),
    "amber": ("Amber", "#14110a", "#fbbf24", "#f7f0dc", {}),
    "crimson": ("Crimson", "#130909", "#ef4444", "#f6e7e7", {}),
    "rose": ("Rose", "#150a10", "#fb7185", "#f8e8ee", {}),
    "orchid": ("Orchid", "#140a18", "#e879f9", "#f4e6f8", {}),
    "graphite": ("Graphite", "#111214", "#a1a1aa", "#e8e8ea", {}),
    "nord": ("Nord", "#2e3440", "#88c0d0", "#eceff4", {}),
    "dracula": ("Dracula", "#282a36", "#bd93f9", "#f8f8f2", {}),
    "daylight": ("Daylight", "#f2f3f8", "#6254f0", "#1b1e2e", {}),
    "sky": ("Sky Light", "#edf5fb", "#0284c7", "#10202c", {}),
    "mint": ("Mint Light", "#edf6f1", "#059669", "#12261d", {}),
    "sand": ("Sand Light", "#f7f1e8", "#c2410c", "#2b2118", {}),
    # --- more themes
    "tokyo": ("Tokyo Night", "#1a1b26", "#7aa2f7", "#c0caf5", {}),
    "solardark": ("Solar Dark", "#002b36", "#b58900", "#eee8d5", {}),
    "gruvbox": ("Gruvbox", "#282828", "#fe8019", "#ebdbb2", {}),
    "monokai": ("Monokai", "#272822", "#a6e22e", "#f8f8f2", {}),
    "cyber": ("Cyberpunk", "#0d0221", "#ff2a6d", "#d1f7ff", {}),
    "coffee": ("Coffee", "#17110d", "#d6a06b", "#f0e4d8", {}),
    "rosel": ("Rose Light", "#fbf1f3", "#e11d48", "#2a1218", {}),
    "lavender": ("Lavender", "#f4f0fb", "#7c3aed", "#221a35", {}),
    "sollight": ("Solar Light", "#fdf6e3", "#268bd2", "#073642", {}),
}
# how the themes are grouped in Settings > Appearance
THEME_GROUPS = [
    ("Black & white", ["superdark", "superwhite"]),
    ("Dark", ["midnight", "ocean", "aqua", "forest", "sunset", "amber", "crimson", "rose", "orchid", "graphite",
              "nord", "dracula", "tokyo", "solardark", "gruvbox", "monokai", "cyber", "coffee"]),
    ("Light", ["daylight", "sky", "mint", "sand", "rosel", "lavender", "sollight"]),
]
ACCENT_PRESETS = ["#7c6cff", "#3b82f6", "#38bdf8", "#2dd4bf", "#4ade80",
                  "#facc15", "#fb923c", "#ef4444", "#f472b6", "#e879f9"]


def get_theme(tid="superdark", accent=None):
    """Theme dict for the theme id `tid`, optionally with a custom accent colour."""
    name, bg, ac, text, over = THEME_SPECS.get(tid) or THEME_SPECS["superdark"]
    over = dict(over)
    if accent and QColor(accent).isValid():
        ac = QColor(accent).name()
        over = {k: v for k, v in over.items() if k not in _ACCENT_KEYS}
    return build_theme(name, bg, ac, text, over)


T = get_theme()


def set_theme(tid="superdark", accent=None):
    """Make a theme the active one (updates the globals T and ACCENT)."""
    global T, ACCENT
    T = get_theme(tid, accent)
    ACCENT = T["accent"]


def build_palette(t):
    """Qt palette (QPalette) built from the theme dict `t`."""
    pal = QPalette()
    R, G = QPalette.ColorRole, QPalette.ColorGroup
    for role, c in ((R.Window, t["bg"]), (R.WindowText, t["text"]), (R.Base, t["card"]),
                    (R.AlternateBase, t["panel"]), (R.Text, t["text"]), (R.Button, t["card"]),
                    (R.ButtonText, t["text"]), (R.ToolTipBase, t["card"]), (R.ToolTipText, t["text"]),
                    (R.Highlight, t["accent"]), (R.HighlightedText, t["on_accent"]),
                    (R.PlaceholderText, t["muted"]), (R.Link, t["accent_soft"])):
        pal.setColor(role, QColor(c))
    for role in (R.Text, R.ButtonText, R.WindowText):
        pal.setColor(G.Disabled, role, QColor(t["disabled"]))
    return pal


_STYLE_TMPL = """
* { font-family: "Segoe UI", "Inter", sans-serif; }
QMainWindow, QWidget#root { background: @bg@; }
QLabel { color: @text@; }
QLabel#title { font-size: 14px; font-weight: 600; color: @text2@; padding: 2px 6px; }
QLabel#time { color: @dim@; font-size: 12px; min-width: 52px; }
QLabel#hint { color: @muted@; font-size: 13px; }
QLabel#big { color: @text@; font-size: 24px; font-weight: 700; }
QFrame#titlebar { background: @panel@; border: none; border-bottom: 1px solid @line@; }
QLabel#apptitle { color: @dim@; font-size: 14px; font-weight: 700; background: transparent; }
QFrame#bar { background: @bar@; border-radius: 20px; }
QFrame#side { background: @panel@; border-radius: 20px; }
QFrame#nowcard { background: @card@; border: 1px solid @line@; border-radius: 16px; }
QLabel#nowtag { color: @accent@; font-size: 11px; font-weight: 800; background: transparent; }
QLabel#nowtitle { color: @text@; font-size: 13px; font-weight: 700; background: transparent; }
QToolButton { background: transparent; border: none; border-radius: 14px; padding: 8px;
               color: @text@; font-weight: 600; }
QToolButton:hover { background: @hover@; }
QToolButton:pressed { background: @press@; }
QToolButton::menu-indicator { image: none; }
QToolButton#play { background: @accent@; border-radius: 28px; padding: 0px; }
QToolButton#play:hover { background: @accent_hi@; }
QToolButton#play:pressed { background: @accent_lo@; }
QPushButton#open { background: @accent@; color: @on_accent@; border: none; border-radius: 14px;
                    padding: 12px 28px; font-size: 14px; font-weight: 600; }
QPushButton#open:hover { background: @accent_hi@; }
QPushButton#flat { background: transparent; color: @accent@; border: none; font-weight: 600; }
QPushButton#flat:hover { color: @accent_soft@; }
QPushButton#flat:disabled { color: @disabled@; }
QPushButton#nowlbl { background: transparent; border: none; color: @text@; font-size: 13px; font-weight: 700;
                      text-align: left; padding: 0px 2px; }
QPushButton#nowlbl:hover { color: @accent@; }
QSlider::groove:horizontal { height: 6px; background: @line@; border-radius: 3px; }
QSlider::sub-page:horizontal { background: @accent@; border-radius: 3px; }
QSlider::handle:horizontal { background: @handle@; width: 14px; height: 14px;
                              margin: -4px 0; border-radius: 7px; }
QSlider::handle:horizontal:hover { background: @handle_hi@; }
QListWidget { background: transparent; border: none; color: @text2@; font-size: 13px; outline: 0; }
QListWidget::item { padding: 10px 12px; border-radius: 10px; }
QListWidget::item:hover { background: @itemhover@; }
QListWidget::item:selected { background: @accent@; color: @on_accent@; }
QMenu { background: @card@; color: @text@; border: 1px solid @line@; border-radius: 10px;
         padding: 6px; }
QMenu::item { padding: 8px 24px; border-radius: 6px; }
QMenu::item:selected { background: @accent@; color: @on_accent@; }
QWidget#home { background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 @home1@, stop:0.55 @home2@, stop:1 @bg@);
                border-radius: 22px; }
QLabel#hero { font-size: 30px; font-weight: 800; color: @hero@; }
QLabel#section { font-size: 17px; font-weight: 700; color: @text@; }
QPushButton#ghost { background: @card@; color: @text@; border: 1px solid @border@; border-radius: 14px;
                     padding: 12px 28px; font-size: 14px; font-weight: 600; }
QPushButton#ghost:hover { background: @hover@; border-color: @accent@; }
QListWidget#library { background: transparent; border: none; outline: 0; color: @text2@; font-size: 12px; }
QListWidget#library::item { border-radius: 16px; padding: 8px; color: @text2@; }
QListWidget#library::item:hover { background: @libhover@; }
QListWidget#library::item:selected { background: transparent; color: @text2@; }
QScrollBar:vertical { background: transparent; width: 10px; margin: 2px; }
QScrollBar::handle:vertical { background: @line@; border-radius: 4px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: @line_hi@; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: none; }
QScrollArea#libscroll { background: transparent; border: none; }
QWidget#libcontent { background: transparent; }
QScrollBar:horizontal { background: transparent; height: 10px; margin: 2px; }
QScrollBar::handle:horizontal { background: @line@; border-radius: 4px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: @line_hi@; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
QScrollBar::add-page:horizontal, QScrollBar::sub-page:horizontal { background: none; }
QDialog { background: @panel@; }
QListWidget#queue { background: transparent; border: none; outline: 0; color: @text2@; font-size: 13px; }
QListWidget#queue::item { padding: 6px 46px 6px 10px; border-radius: 12px; color: @text2@; }
QListWidget#queue::item:hover { background: @itemhover@; }
QFrame#plpill { background: @hover@; border: 1px solid transparent; border-radius: 14px; }
QFrame#plpill:hover { border-color: @accent@; }
QLabel#plname { font-size: 14px; font-weight: 700; color: @accent@; background: transparent; }
QLabel#plsub { font-size: 12px; color: @text2@; background: transparent; }
QFrame#popup { background: @panel@; border: 1px solid @line@; border-radius: 18px; }
QListWidget#plist { background: transparent; border: none; outline: 0; color: @text2@; font-size: 13px; }
QListWidget#plist::item { padding: 6px 10px; border-radius: 12px; color: @text2@; }
QListWidget#plist::item:hover { background: @itemhover@; }
QListWidget#plist::item:selected { background: @hover@; color: @accent@; }
QListWidget#queue::item:selected { background: @hover@; color: @accent@; }
QFrame#rail { background: @panel@; border: none; border-right: 1px solid @line@; border-radius: 0px; }
QFrame#railsep { background: @line@; border: none; }
QToolButton#railbtn { border-radius: 18px; padding: 11px; }
QToolButton#railbtn:hover { background: @hover@; }
QToolButton#railbtn:pressed { background: @press@; }
QToolButton#platbtn { background: @card@; border: 2px solid @border@; border-radius: 14px;
                      padding: 6px 6px 4px 6px; color: @text2@; font-size: 12px; font-weight: 600; }
QToolButton#platbtn:hover { background: @hover@; border-color: @accent@; }
QToolButton#platbtn:checked { background: @hover@; border: 2px solid @accent@; color: @text@; }
QToolButton#platbtn:disabled { color: @disabled@; }
QPushButton#open:disabled { background: @card@; color: @disabled@; border: 1px solid @border@; }
QDialog#settings { background: transparent; }
QFrame#sidepanel { background: @bg@; border-left: 1px solid @line_hi@; }
QFrame#group { background: @panel@; border: 1px solid @line@; border-radius: 18px; }
QFrame#marker { background: @accent@; border-radius: 2px; }
QFrame#sep { background: @line@; }
QLabel#caption { color: @dim@; font-size: 13px; padding-top: 4px; }
QLabel#path { background: @card@; border: 1px solid @border@; border-radius: 10px; padding: 9px 12px;
              color: @text2@; font-size: 13px; }
QListWidget#roots { background: @card@; border: 1px solid @border@; border-radius: 12px; padding: 4px; }
QLineEdit { background: @card@; color: @text@; border: 1px solid @border@; border-radius: 10px;
             padding: 9px 12px; font-size: 14px; selection-background-color: @accent@; }
QLineEdit:focus { border-color: @accent@; }
QInputDialog QPushButton, QMessageBox QPushButton { background: @card@; color: @text@; border: 1px solid @border@;
                                                   border-radius: 10px; padding: 7px 18px; min-width: 70px; }
QInputDialog QPushButton:hover, QMessageBox QPushButton:hover { background: @hover@; border-color: @accent@; }
QListWidget#chklist::item { padding: 6px 10px; border-radius: 10px; color: @text@; background: transparent; }
QListWidget#chklist::item:hover, QListWidget#chklist::item:selected, QListWidget#chklist::item:focus { background: transparent; color: @text@; }
QListWidget::indicator { width: 18px; height: 18px; border-radius: 5px; border: 1px solid @line_hi@; background: @card@; }
QListWidget::indicator:checked { background: @accent@; border-color: @accent@; }
QPushButton#chip { background: @card@; color: @text2@; border: 1px solid @border@; border-radius: 12px;
                    padding: 8px 16px; font-weight: 600; }
QPushButton#chip:hover { border-color: @accent@; }
QPushButton#chip:checked { background: @accent@; color: @on_accent@; border-color: @accent@; }
QPushButton#chip:disabled { color: @disabled@; }
QProgressBar { background: @card@; border: none; border-radius: 7px; }
QProgressBar::chunk { background: @accent@; border-radius: 7px; }
QCheckBox { color: @text@; font-size: 14px; spacing: 10px; padding: 4px 0; }
QCheckBox::indicator { width: 20px; height: 20px; border-radius: 6px; border: 1px solid @line_hi@; background: @card@; }
QCheckBox::indicator:checked { background: @accent@; border-color: @accent@; }
QToolTip { background: @card@; color: @text@; border: 1px solid @line@; padding: 4px; }
"""


def build_style(t=None):
    """Application stylesheet for theme `t` (default: the active one); fills the @name@ slots of the template."""
    t = t or T
    return re.sub(r"@(\w+)@", lambda m: str(t[m.group(1)]), _STYLE_TMPL)


def apply_app_theme(app):
    """Apply the active theme (palette + stylesheet) to the whole application."""
    app.setPalette(build_palette(T))
    app.setStyleSheet(build_style(T))


# ----------------------------------------------------------------------------
# Vector icons drawn with QPainter (no image files needed)
# ----------------------------------------------------------------------------
def make_icon(name, color=None, size=96):
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.scale(size / 100, size / 100)
    c = QColor(color or T["text"])
    pen = QPen(c, 7, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)

    def fill():
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(c)

    def stroke():
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)

    def poly(*pts):
        p.drawPolygon(QPolygonF([QPointF(x, y) for x, y in pts]))

    def line(*pts):
        p.drawPolyline(QPolygonF([QPointF(x, y) for x, y in pts]))

    fill()
    if name == "play":
        poly((32, 18), (32, 82), (84, 50))
    elif name == "pause":
        p.drawRoundedRect(QRectF(25, 20, 18, 60), 6, 6)
        p.drawRoundedRect(QRectF(57, 20, 18, 60), 6, 6)
    elif name == "prev":
        p.drawRoundedRect(QRectF(18, 22, 10, 56), 4, 4)
        poly((82, 22), (82, 78), (36, 50))
    elif name == "next":
        p.drawRoundedRect(QRectF(72, 22, 10, 56), 4, 4)
        poly((18, 22), (18, 78), (64, 50))
    elif name == "back":
        poly((52, 26), (52, 74), (12, 50))
        poly((90, 26), (90, 74), (50, 50))
    elif name == "fwd":
        poly((48, 26), (48, 74), (88, 50))
        poly((10, 26), (10, 74), (50, 50))
    elif name in ("vol", "mute"):
        poly((12, 38), (30, 38), (54, 18), (54, 82), (30, 62), (12, 62))
        stroke()
        if name == "vol":
            p.drawArc(QRectF(32, 32, 36, 36), -45 * 16, 90 * 16)
            p.drawArc(QRectF(18, 18, 64, 64), -45 * 16, 90 * 16)
        else:
            line((66, 38), (90, 62))
            line((90, 38), (66, 62))
    elif name == "full":
        stroke()
        line((16, 38), (16, 16), (38, 16))
        line((62, 16), (84, 16), (84, 38))
        line((84, 62), (84, 84), (62, 84))
        line((38, 84), (16, 84), (16, 62))
    elif name == "list":
        stroke()
        for y in (28, 50, 72):
            p.drawLine(40, y, 88, y)
        fill()
        for y in (28, 50, 72):
            p.drawEllipse(QPointF(18, y), 5, 5)
    elif name == "settings":                      # a real gear: 8 rounded teeth and a hole
        n, r_out, r_in, hole = 8, 41.0, 31.0, 13.0
        step = 2 * math.pi / n
        pts = []
        for i in range(n):
            for da, rad in ((-0.27, r_in), (-0.15, r_out), (0.15, r_out), (0.27, r_in), (0.5, r_in)):
                ang = (i + da) * step
                pts.append(QPointF(50 + rad * math.cos(ang), 50 + rad * math.sin(ang)))
        gear = QPainterPath()
        gear.addPolygon(QPolygonF(pts))
        gear.closeSubpath()
        gear.addEllipse(QPointF(50, 50), hole, hole)      # even-odd fill makes it a hole
        p.setPen(QPen(c, 4, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin))
        p.drawPath(gear)
    elif name == "convert":
        stroke()
        p.drawLine(16, 34, 80, 34)
        p.drawLine(64, 18, 80, 34)
        p.drawLine(64, 50, 80, 34)
        p.drawLine(84, 68, 20, 68)
        p.drawLine(36, 52, 20, 68)
        p.drawLine(36, 84, 20, 68)
    elif name == "link":
        stroke()
        p.drawArc(QRectF(10, 34, 46, 32), 90 * 16, 180 * 16)
        p.drawArc(QRectF(44, 34, 46, 32), -90 * 16, 180 * 16)
        p.drawLine(33, 34, 67, 34)
        p.drawLine(33, 66, 67, 66)
    elif name == "add":
        stroke()
        p.drawLine(50, 20, 50, 80)
        p.drawLine(20, 50, 80, 50)
    elif name == "shuffle":
        stroke()
        line((12, 30), (30, 30), (62, 70), (80, 70))
        line((12, 70), (30, 70), (62, 30), (80, 30))
        line((68, 18), (80, 30), (68, 42))
        line((68, 58), (80, 70), (68, 82))
    elif name in ("repeat", "repeat1"):
        stroke()
        line((20, 54), (20, 40), (30, 29), (76, 29))
        line((65, 17), (78, 29), (65, 41))
        line((80, 46), (80, 60), (70, 71), (24, 71))
        line((35, 59), (22, 71), (35, 83))
        if name == "repeat1":
            p.setPen(c)
            f = QFont("Segoe UI")
            f.setPixelSize(32)
            f.setBold(True)
            p.setFont(f)
            p.drawText(QRectF(30, 36, 40, 30), Qt.AlignmentFlag.AlignCenter, "1")
    elif name == "chev_down":
        stroke()
        line((24, 38), (50, 64), (76, 38))
    elif name == "download":
        stroke()
        p.drawLine(50, 14, 50, 60)
        p.drawLine(30, 42, 50, 62)
        p.drawLine(70, 42, 50, 62)
        p.drawLine(18, 68, 18, 84)
        p.drawLine(18, 84, 82, 84)
        p.drawLine(82, 84, 82, 68)
    elif name == "video":
        stroke()
        p.drawRoundedRect(QRectF(11, 22, 78, 56), 12, 12)
        fill()
        poly((43, 38), (43, 62), (63, 50))
    elif name == "music":
        p.drawEllipse(QPointF(30, 74), 15, 12)
        p.drawEllipse(QPointF(70, 64), 15, 12)
        p.drawRoundedRect(QRectF(38, 22, 8, 52), 3, 3)
        p.drawRoundedRect(QRectF(78, 12, 8, 52), 3, 3)
        poly((38, 22), (86, 12), (86, 28), (38, 38))
    elif name == "mini":                          # a window with a small player in its corner
        stroke()
        p.drawRoundedRect(QRectF(10, 20, 80, 60), 12, 12)
        fill()
        p.drawRoundedRect(QRectF(46, 46, 34, 24), 6, 6)
    elif name == "pop":                           # a window with an arrow leaving its top-right corner
        stroke()
        p.drawRoundedRect(QRectF(12, 30, 56, 56), 10, 10)
        p.drawLine(46, 54, 84, 16)
        line((58, 14), (86, 14), (86, 42))
    elif name == "exit":                          # an arrow leaving a bracket: back to the library
        stroke()
        line((58, 18), (82, 18), (82, 82), (58, 82))
        p.drawLine(16, 50, 68, 50)
        line((38, 28), (16, 50), (38, 72))
    elif name == "info":                          # a circle with an "i"
        stroke()
        p.drawEllipse(QPointF(50, 50), 36, 36)
        p.drawLine(50, 46, 50, 70)
        fill()
        p.drawEllipse(QPointF(50, 31), 5, 5)
    p.end()
    return QIcon(pm)


URL_RE = re.compile(r"^https?://", re.I)


def is_url(text):
    return bool(URL_RE.match((text or "").strip()))


def app_dir():
    """Folder of the program: next to the .exe when built, next to this script otherwise."""
    return os.path.dirname(sys.executable if getattr(sys, "frozen", False) else os.path.abspath(__file__))


def find_ffmpeg():
    path = shutil.which("ffmpeg")
    if not path:
        try:                                         # pip install imageio-ffmpeg (bundles ffmpeg.exe)
            import imageio_ffmpeg
            path = imageio_ffmpeg.get_ffmpeg_exe()
        except Exception:
            path = None
    return path


def clean_err(ex):
    """Last line of an exception message, without the 'ERROR: ' prefix."""
    t = str(ex).replace("ERROR: ", "").strip()
    return t.splitlines()[-1] if t else "Unknown error"


def cookie_sources():
    """Cookie sources to try, in order: cookies.txt next to the app, none, then the chosen browser(s)."""
    pref = QSettings(SETTINGS_ORG, SETTINGS_APP).value("cookie_browser", "auto", str)
    src = []
    cfile = os.path.join(app_dir(), "cookies.txt")
    if os.path.isfile(cfile):
        src.append(("cookies.txt", {"cookiefile": cfile}))
    src.append(("no cookies", {}))
    if pref == "off":
        return src
    browsers = ("firefox", "edge", "chrome", "brave", "opera", "vivaldi") if pref == "auto" else (pref,)
    for br in browsers:
        src.append((br, {"cookiesfrombrowser": (br,)}))
    return src


def ydl_options(**extra):
    """Default yt-dlp options; keyword arguments override them."""
    o = {"quiet": True, "no_warnings": True, "noplaylist": True, "retries": 3, "playlist_items": "1-20",
         # YouTube now needs a JavaScript runtime to solve its challenges
         "js_runtimes": {"deno": {}, "node": {}, "bun": {}, "quickjs": {}},
         "remote_components": ["ejs:github"]}
    o.update(extra)
    return o


YTDLP_MISSING = 'yt-dlp is not installed.  Run:  pip install -U "yt-dlp[default]"'
LOGIN_WORDS = ("sign in", "log in", "login", "cookies", "not a bot", "authenticat", "private",
               "age-restricted", "confirm your age", "empty media response", "rate-limit")


def needs_login(ex):
    """True if a download error means the site wants the user to sign in."""
    low = str(ex).lower()
    return any(w in low for w in LOGIN_WORDS)


def login_hint(site):
    """Message that tells the user how to get past a sign-in wall on `site`."""
    return (f"{site} asks you to sign in. Fix: log in to {site} in Firefox (best) and close it, "
            "or export cookies to a file named cookies.txt next to this program, then try again.")


# ----------------------------------------------------------------------------
# Download from the internet: apps (YouTube, Instagram, TikTok, X ...), threads, dialog helpers
# ----------------------------------------------------------------------------
PLATFORMS = [
    # key, name, home page, short tip shown under the link box
    ("youtube", "YouTube", "https://www.youtube.com",
     "Paste the link of a video, a Short or a song."),
    ("instagram", "Instagram", "https://www.instagram.com",
     "Reels and video posts. Private accounts and stories need your browser login (Settings > Sign-in cookies)."),
    ("tiktok", "TikTok", "https://www.tiktok.com",
     "Paste a video link (tiktok.com/@user/video/…  or a short vm.tiktok.com link)."),
    ("twitter", "Twitter / X", "https://x.com",
     "Paste the link of a post that has a video (x.com/user/status/…)."),
    ("other", "Other", "",
     "Any link that yt-dlp supports: Facebook, Vimeo, SoundCloud, Reddit, Dailymotion and many more."),
]
PLATFORM_NAME = {k: n for k, n, _h, _t in PLATFORMS}
PLATFORM_HOME = {k: h for k, _n, h, _t in PLATFORMS}
PLATFORM_TIP = {k: t for k, _n, _h, t in PLATFORMS}
PLATFORM_HOSTS = {
    "youtube": ("youtube.com", "youtu.be", "youtube-nocookie.com"),
    "instagram": ("instagram.com", "instagr.am"),
    "tiktok": ("tiktok.com",),
    "twitter": ("twitter.com", "x.com", "t.co"),
}


QUALITY_TIERS = (2160, 1440, 1080, 720, 480, 360, 240, 144)     # the qualities offered to the user


def quality_tier(f):
    """Standard quality (1080, 720 ...) of a format. Uses the SHORT side, so vertical videos (TikTok, Reels)
    count as 1080p / 720p too instead of showing odd numbers like 1920 or 1024."""
    h, w = int(f.get("height") or 0), int(f.get("width") or 0)
    q = min(h, w) if w and h else h
    return next((t for t in QUALITY_TIERS if q >= t * 0.9), QUALITY_TIERS[-1])


def detect_platform(url):
    """'youtube' / 'instagram' / 'tiktok' / 'twitter' / 'other' for a link, '' if it is not a link."""
    m = re.match(r"^https?://([^/:?#]+)", (url or "").strip(), re.I)
    if not m:
        return ""
    host = m.group(1).lower()
    for key, hosts in PLATFORM_HOSTS.items():
        if any(host == h or host.endswith("." + h) for h in hosts):
            return key
    return "other"


def platform_icon(key, color, size=88):
    """One-colour app glyphs (YouTube, Instagram, TikTok, X, link) in the given colour: they follow the theme."""
    if key not in ("youtube", "instagram", "tiktok", "twitter"):
        return make_icon("link", color, size)
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.scale(size / 100.0, size / 100.0)
    col = QColor(color)

    def pen(w):
        return QPen(col, w, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)

    if key == "youtube":                                  # rounded screen with the play triangle cut out
        body = QPainterPath()
        body.addRoundedRect(QRectF(6, 22, 88, 56), 18, 18)
        tri = QPainterPath()
        tri.moveTo(41, 36)
        tri.lineTo(41, 64)
        tri.lineTo(65, 50)
        tri.closeSubpath()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        p.drawPath(body.subtracted(tri))
    elif key == "instagram":
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(pen(7))
        p.drawRoundedRect(QRectF(12, 12, 76, 76), 22, 22)
        p.drawEllipse(QPointF(50, 50), 18, 18)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(col)
        p.drawEllipse(QPointF(72, 28), 5, 5)
    elif key == "tiktok":                                 # the music note
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.setPen(pen(9))
        p.drawLine(QPointF(60, 14), QPointF(60, 68))
        p.drawEllipse(QPointF(46, 70), 14, 14)
        flag = QPainterPath()
        flag.moveTo(60, 14)
        flag.cubicTo(62, 32, 74, 36, 86, 38)
        p.drawPath(flag)
    else:                                                 # twitter / X
        p.setPen(pen(11))
        p.drawLine(QPointF(22, 18), QPointF(78, 82))
        p.setPen(pen(6))
        p.drawLine(QPointF(78, 18), QPointF(22, 82))
    p.end()
    return QIcon(pm)


def rounded_pixmap(src, w, h, radius=12):
    """Picture cropped to w x h with rounded corners (a gradient card when there is no picture)."""
    out = QPixmap(w, h)
    out.fill(Qt.GlobalColor.transparent)
    p = QPainter(out)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addRoundedRect(0, 0, w, h, radius, radius)
    p.setClipPath(clip)
    if src is not None and not src.isNull():
        s = src.scaled(w, h, Qt.AspectRatioMode.KeepAspectRatioByExpanding, Qt.TransformationMode.SmoothTransformation)
        p.drawPixmap((w - s.width()) // 2, (h - s.height()) // 2, s)
    else:
        g = QLinearGradient(0, 0, w, h)
        g.setColorAt(0, QColor(T["ph1"]))
        g.setColorAt(1, QColor(T["ph2"]))
        p.fillRect(0, 0, w, h, g)
    p.end()
    return out


class LinkInfoThread(QThread):
    """Reads title, uploader, duration, cover picture and the available video qualities of a link."""
    info = Signal(object)              # dict
    failed = Signal(str)
    status = Signal(str)

    def __init__(self, url, site, parent=None):
        super().__init__(parent)
        self.url, self.site = url, site
        self.cancelled = False

    @staticmethod
    def _fetch_bytes(url):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=10) as r:
                return r.read(4000000)
        except Exception:
            return b""

    def run(self):
        try:
            import yt_dlp
        except ImportError:
            self.failed.emit(YTDLP_MISSING)
            return
        login, errors = False, []
        for label, extra in cookie_sources():
            if self.cancelled:
                return
            self.status.emit(f"Reading the link…  ({label})")
            try:
                with yt_dlp.YoutubeDL(ydl_options(skip_download=True, ignore_no_formats_error=True, **extra)) as y:
                    info = y.extract_info(self.url, download=False)
                entries, count = info.get("entries"), 1
                if entries is not None:                      # a post / playlist with several items
                    entries = [e for e in entries if e]
                    if not entries:
                        raise ValueError("Nothing to download was found in this link")
                    count, first = len(entries), entries[0]
                else:
                    first = info
                formats = first.get("formats") or []
                if not formats and not first.get("url"):
                    login = True                             # no formats usually means login / bot check
                    continue
                heights = sorted({quality_tier(f) for f in formats
                                  if f.get("height") and f.get("vcodec") != "none"}, reverse=True)
                turl = first.get("thumbnail") or ((first.get("thumbnails") or [{}])[-1].get("url"))
                self.info.emit({"title": first.get("title") or info.get("title") or self.url,
                                "uploader": first.get("uploader") or first.get("channel") or "",
                                "duration": first.get("duration"), "heights": heights, "count": count,
                                "thumb": self._fetch_bytes(turl) if turl else b""})
                return
            except Exception as ex:
                if needs_login(ex):
                    login = True
                errors.append(clean_err(ex))
                if not login:
                    break
        if not self.cancelled:
            self.failed.emit(login_hint(self.site) if login else (errors[0] if errors else "No formats found"))


class DownloadCancelled(Exception):
    """Raised inside DownloadThread when the user cancels a download."""
    pass


class DownloadThread(QThread):
    """Downloads one link with yt-dlp: video (+ audio merged with ffmpeg) or audio only, converted to MP3 / M4A
    with the video's thumbnail embedded as the cover picture of the song."""
    progress = Signal(int, str)        # percent (-1 = unknown), text
    done = Signal(object, str)         # [final file paths], note
    failed = Signal(str)

    PP_TEXT = {"FFmpegExtractAudio": "Converting to audio…", "EmbedThumbnail": "Adding the cover picture…",
               "FFmpegMerger": "Merging video and audio…", "FFmpegMetadata": "Writing the tags…",
               "FFmpegThumbnailsConvertor": "Preparing the cover picture…", "MoveFiles": "Finishing…"}

    def __init__(self, req, parent=None):
        super().__init__(parent)
        self.req = dict(req)
        self.cancelled = False

    def cancel(self):
        self.cancelled = True

    def _download(self, yt_dlp, extra, with_cover, ffmpeg):
        r = self.req
        audio = r["kind"] == "audio"
        h = int(r.get("height") or 0)
        paths = []

        def hook(d):
            if self.cancelled:
                raise DownloadCancelled()
            if d.get("status") == "downloading":
                total = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
                got = d.get("downloaded_bytes") or 0
                pct = int(got * 100 / total) if total else -1
                text = f"Downloading…  {pct}%" if pct >= 0 else "Downloading…"
                if d.get("speed"):
                    text += f"    {human_size(d['speed'])}/s"
                self.progress.emit(pct, text)
            elif d.get("status") == "finished":
                self.progress.emit(-1, "Processing…")

        def pp_hook(d):
            if self.cancelled:
                raise DownloadCancelled()
            if d.get("status") == "started":
                self.progress.emit(-1, self.PP_TEXT.get(d.get("postprocessor"), "Processing…"))

        opts = ydl_options(progress_hooks=[hook], postprocessor_hooks=[pp_hook], post_hooks=[paths.append], **extra)
        if audio:
            opts["format"] = "bestaudio/best"
            opts["outtmpl"] = os.path.join(r["folder"], "%(title).100s [%(id)s].%(ext)s")
            pps = [{"key": "FFmpegExtractAudio", "preferredcodec": r["codec"], "preferredquality": str(r["kbps"])},
                   {"key": "FFmpegMetadata", "add_metadata": True, "add_chapters": False}]
            if with_cover:                               # the video's thumbnail becomes the song's cover
                opts["writethumbnail"] = True
                pps.append({"key": "FFmpegThumbnailsConvertor", "format": "jpg", "when": "before_dl"})
                pps.append({"key": "EmbedThumbnail", "already_have_thumbnail": bool(r.get("keep_cover"))})
            opts["postprocessors"] = pps
        else:
            fmt = "bv*+ba/b" if ffmpeg else "b"
            if h:                                        # "res" = the short side, so vertical videos work too
                opts["format_sort"] = [f"res:{h}"]
            opts.update(format=fmt, merge_output_format="mp4",
                        outtmpl=os.path.join(r["folder"], f"%(title).100s [%(id)s]{f' {h}p' if h else ''}.%(ext)s"))
        if ffmpeg:
            opts["ffmpeg_location"] = ffmpeg
        with yt_dlp.YoutubeDL(opts) as y:
            info = y.extract_info(r["url"], download=True)
        out = [p for p in dict.fromkeys(paths) if p and os.path.isfile(p)]
        if not out and info:
            for e in (info.get("entries") or [info]):
                for rd in (e or {}).get("requested_downloads") or []:
                    fp = rd.get("filepath")
                    if fp and os.path.isfile(fp):
                        out.append(fp)
        return out

    def run(self):
        r = self.req
        try:
            import yt_dlp
        except ImportError:
            self.failed.emit(YTDLP_MISSING)
            return
        try:
            os.makedirs(r["folder"], exist_ok=True)
        except OSError as ex:
            self.failed.emit(f"Cannot create folder: {ex}")
            return
        ffmpeg = find_ffmpeg()
        audio = r["kind"] == "audio"
        if audio and not ffmpeg:
            self.failed.emit("Saving audio needs ffmpeg.  Run:  pip install imageio-ffmpeg")
            return
        site = PLATFORM_NAME.get(r.get("platform"), "This site") if r.get("platform") != "other" else "This site"
        need_login, errors, note = False, [], ""
        for label, extra in cookie_sources():
            if self.cancelled:
                break
            self.progress.emit(-1, f"Connecting…  ({label})")
            with_cover = bool(audio and r.get("cover"))
            while True:
                try:
                    paths = self._download(yt_dlp, extra, with_cover, ffmpeg)
                except Exception as ex:
                    if self.cancelled:
                        self.failed.emit("Cancelled")
                        return
                    low = str(ex).lower()
                    if with_cover and any(w in low for w in ("thumbnail", "mutagen", "atomicparsley")):
                        with_cover, note = False, "The cover picture could not be embedded."
                        self.progress.emit(-1, "Cover picture failed - saving without it…")
                        continue
                    if needs_login(ex):
                        need_login = True
                    errors.append(clean_err(ex))
                    break
                if paths:
                    self.done.emit(paths, note)
                    return
                errors.append("Nothing was downloaded")
                break
            if not need_login:
                break
        if self.cancelled:
            self.failed.emit("Cancelled")
            return
        msg = login_hint(site) if need_login else (errors[0] if errors else "Unknown error")
        if not audio and not ffmpeg:
            msg += "   -> Install ffmpeg:  pip install imageio-ffmpeg"
        self.failed.emit(msg)


def fmt_time(ms):
    """Milliseconds -> 'mm:ss' (or 'h:mm:ss')."""
    s = max(0, int(ms // 1000))
    h, rem = divmod(s, 3600)
    m, s = divmod(rem, 60)
    return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"


def user_videos_dir():
    d = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.MoviesLocation)
    if d and os.path.isdir(d):
        return d
    d = os.path.join(os.path.expanduser("~"), "Videos")
    return d if os.path.isdir(d) else os.path.expanduser("~")


def user_music_dir():
    d = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.MusicLocation)
    if d and os.path.isdir(d):
        return d
    d = os.path.join(os.path.expanduser("~"), "Music")
    return d if os.path.isdir(d) else os.path.expanduser("~")


def default_download_dir():
    """Default folder for downloaded videos."""
    return os.path.join(user_videos_dir(), "mp4player")


def human_size(n):
    """Bytes -> '12 KB' / '3.4 MB' style text."""
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit in ("B", "KB") else f"{n:.1f} {unit}"
        n /= 1024


def pretty_title(path):
    """File name without extension and without the '[id] 720p' tail that downloaders add."""
    name = os.path.splitext(os.path.basename(path))[0]
    name = re.sub(r"\s*\[(?:[\w-]{11}|\d{15,20})\]\s*(?:\d{3,4}p)?$", "", name)   # "Title [id] 720p" -> "Title"
    return name


def make_thumb(image_path, duration, w=256, h=144, radius=14, label=None, tag=None, audio=False):
    """Rounded 16:9 thumbnail (video frame or a gradient placeholder) with a duration badge."""
    if audio and (w, h) == (256, 144):               # songs are square album-art tiles
        w = h = 176
        radius = 12
    elif audio and (w, h) == (160, 90):
        w = h = 90
    elif audio and (w, h) == (112, 63):              # Convert dialog list
        w = h = 63
    pm = QPixmap(w, h)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addRoundedRect(0, 0, w, h, radius, radius)
    p.setClipPath(clip)
    src = QPixmap(image_path) if image_path else QPixmap()
    if not src.isNull():
        src = src.scaled(w, h, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                         Qt.TransformationMode.SmoothTransformation)
        p.drawPixmap((w - src.width()) // 2, (h - src.height()) // 2, src)
    else:
        g = QLinearGradient(0, 0, w, h)
        g.setColorAt(0, QColor(T["ph1"]))
        g.setColorAt(1, QColor(T["ph2"]))
        p.fillRect(0, 0, w, h, g)
        p.drawPixmap((w - 54) // 2, (h - 54) // 2,
                     make_icon("music" if audio else "play", T["accent_hi"], 96).pixmap(54, 54))
    if label or (duration and duration > 0):
        text = label or fmt_time(int(duration * 1000))
        f = QFont("Segoe UI", 9)
        f.setBold(True)
        p.setFont(f)
        tw = QFontMetrics(f).horizontalAdvance(text)
        bw, bh = tw + 14, 20
        r = QRectF(w - bw - 8, h - bh - 8, bw, bh)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(0, 0, 0, 175))
        p.drawRoundedRect(r, 7, 7)
        p.setPen(QColor("#ffffff"))
        p.drawText(r, Qt.AlignmentFlag.AlignCenter, text)
    if tag:
        f = QFont("Segoe UI", 8)
        f.setBold(True)
        p.setFont(f)
        tw = QFontMetrics(f).horizontalAdvance(tag)
        r = QRectF(8, 8, tw + 16, 20)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(ACCENT))
        p.drawRoundedRect(r, 7, 7)
        p.setPen(QColor(T["on_accent"]))
        p.drawText(r, Qt.AlignmentFlag.AlignCenter, tag)
    p.end()
    return pm


def make_cover(image_path, size=300, radius=18):
    """Big rounded square cover for the audio page (album art if the file has any, else a music-note card)."""
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
    clip = QPainterPath()
    clip.addRoundedRect(0, 0, size, size, radius, radius)
    p.setClipPath(clip)
    src = QPixmap(image_path) if image_path else QPixmap()
    if not src.isNull():
        src = src.scaled(size, size, Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                         Qt.TransformationMode.SmoothTransformation)
        p.drawPixmap((size - src.width()) // 2, (size - src.height()) // 2, src)
    else:
        g = QLinearGradient(0, 0, size, size)
        g.setColorAt(0, QColor(T["ph1"]))
        g.setColorAt(1, QColor(T["ph2"]))
        p.fillRect(0, 0, size, size, g)
        icon = size // 2
        p.drawPixmap((size - icon) // 2, (size - icon) // 2,
                     make_icon("music", T["accent_hi"], 160).pixmap(icon, icon))
    p.end()
    return pm


IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp", ".bmp")
COVER_NAMES = ("cover", "folder", "front", "album", "albumart", "artwork")


def thumb_paths(path, size, mtime):
    """Cache files (picture, duration) for one media file."""
    folder = os.path.join(tempfile.gettempdir(), THUMB_CACHE_DIR)
    os.makedirs(folder, exist_ok=True)
    key = hashlib.sha1(f"{path}|{mtime}|{size}".encode("utf-8", "ignore")).hexdigest()[:16]
    return os.path.join(folder, key + ".jpg"), os.path.join(folder, key + ".dur")


def covers_dir():
    """Folder (created if needed) that holds the user's custom cover pictures."""
    d = os.path.join(QStandardPaths.writableLocation(QStandardPaths.StandardLocation.AppDataLocation),
                     COVERS_DIR_NAME)
    os.makedirs(d, exist_ok=True)
    return d


def save_square(img, out, size=512):
    """Covers are always square: centre-crop, shrink, save as JPEG."""
    if img.isNull():
        return False
    side = min(img.width(), img.height())
    img = img.copy((img.width() - side) // 2, (img.height() - side) // 2, side, side)
    if side > size:
        img = img.scaled(size, size, Qt.AspectRatioMode.IgnoreAspectRatio, Qt.TransformationMode.SmoothTransformation)
    return img.convertToFormat(QImage.Format.Format_RGB32).save(out, "JPG", 90)


def folder_cover(path):
    """cover.jpg / folder.jpg / AlbumArt_*.jpg ... lying next to the song."""
    d = os.path.dirname(path)
    try:
        names = os.listdir(d)
    except OSError:
        return ""
    low = {n.lower(): n for n in names}
    for base in COVER_NAMES:
        for ext in IMG_EXTS:
            n = low.get(base + ext)
            if n:
                return os.path.join(d, n)
    for n in names:
        ln = n.lower()
        if ln.startswith("albumart") and "small" not in ln and os.path.splitext(ln)[1] in IMG_EXTS:
            return os.path.join(d, n)
    return ""


def _image_start(b):
    """Offset of the first JPEG / PNG signature in `b`, or -1."""
    hits = [i for i in (b.find(b"\xff\xd8\xff"), b.find(b"\x89PNG\r\n\x1a\n")) if i >= 0]
    return min(hits) if hits else -1


def _id3_art(f, head):
    """Cover picture bytes from an ID3v2 tag (MP3)."""
    ver, flags = head[3], head[5]
    size = ((head[6] & 0x7F) << 21) | ((head[7] & 0x7F) << 14) | ((head[8] & 0x7F) << 7) | (head[9] & 0x7F)
    data = f.read(min(size, 16 * 1024 * 1024))
    if flags & 0x80 and ver < 4:
        data = data.replace(b"\xff\x00", b"\xff")
    pos = 0
    if flags & 0x40 and ver >= 3 and len(data) >= 4:             # extended header
        n = data[:4]
        pos = (((n[0] & 0x7F) << 21) | ((n[1] & 0x7F) << 14) | ((n[2] & 0x7F) << 7) | (n[3] & 0x7F)) if ver == 4 \
            else 4 + int.from_bytes(n, "big")
    idlen, hdr = (3, 6) if ver == 2 else (4, 10)
    found = []
    while pos + hdr <= len(data):
        fid = data[pos:pos + idlen]
        if fid[:1] == b"\x00":
            break
        raw = data[pos + idlen:pos + idlen + (3 if ver == 2 else 4)]
        if ver == 2:
            fsize = int.from_bytes(raw, "big")
        elif ver == 4:
            fsize = ((raw[0] & 0x7F) << 21) | ((raw[1] & 0x7F) << 14) | ((raw[2] & 0x7F) << 7) | (raw[3] & 0x7F)
        else:
            fsize = int.from_bytes(raw, "big")
        body = data[pos + hdr:pos + hdr + fsize]
        if fid in (b"APIC", b"PIC"):
            i = _image_start(body)
            if i >= 0:
                ptype = 3
                try:                                             # picture type sits after the mime type
                    z = body.index(b"\x00", 1) if ver != 2 else 4
                    ptype = body[z + 1]
                except (ValueError, IndexError):
                    pass
                found.append((ptype, body[i:]))
        pos += hdr + max(fsize, 0)
        if fsize <= 0:
            break
    for ptype, img in found:
        if ptype == 3:                                           # front cover first
            return img
    return found[0][1] if found else b""


def _flac_art(f):
    """Cover picture bytes from a FLAC file's metadata blocks."""
    found = []
    while True:
        h = f.read(4)
        if len(h) < 4:
            break
        last, btype, n = h[0] & 0x80, h[0] & 0x7F, int.from_bytes(h[1:4], "big")
        if btype == 6 and n < 16 * 1024 * 1024:
            b = f.read(n)
            try:
                ptype = int.from_bytes(b[0:4], "big")
                ml = int.from_bytes(b[4:8], "big")
                o = 8 + ml
                dl = int.from_bytes(b[o:o + 4], "big")
                o += 4 + dl + 16
                il = int.from_bytes(b[o:o + 4], "big")
                found.append((ptype, b[o + 4:o + 4 + il]))
            except Exception:
                pass
        else:
            f.seek(n, 1)
        if last:
            break
    for ptype, img in found:
        if ptype == 3:
            return img
    return found[0][1] if found else b""


def _mp4_walk(f, start, end):
    """Iterate over the MP4 boxes (atoms) between `start` and `end`."""
    pos = start
    while pos + 8 <= end:
        f.seek(pos)
        hdr = f.read(8)
        if len(hdr) < 8:
            return
        size, typ, hsz = int.from_bytes(hdr[:4], "big"), hdr[4:8], 8
        if size == 1:
            size, hsz = int.from_bytes(f.read(8), "big"), 16
        elif size == 0:
            size = end - pos
        if size < hsz:
            return
        yield typ, pos + hsz, pos + size
        pos += size


def _mp4_find(f, start, end, names):
    """Find the nested MP4 box described by the name path `names`; returns (start, end) or None."""
    for typ, s_, e_ in _mp4_walk(f, start, end):
        if typ == names[0]:
            if len(names) == 1:
                return s_, e_
            r = _mp4_find(f, s_ + 4 if typ == b"meta" else s_, e_, names[1:])
            if r:
                return r
    return None


def _mp4_art(f):
    """Cover picture bytes from an MP4 / M4A file (the 'covr' box)."""
    f.seek(0, 2)
    r = _mp4_find(f, 0, f.tell(), [b"moov", b"udta", b"meta", b"ilst", b"covr", b"data"])
    if not r:
        return b""
    f.seek(r[0] + 8)
    return f.read(min(r[1] - r[0] - 8, 16 * 1024 * 1024))


def embedded_art_bytes(path):
    """Album art stored inside the audio file (MP3 / FLAC / M4A) - plain Python, works without ffmpeg."""
    try:
        with open(path, "rb") as f:
            head = f.read(10)
            if head[:3] == b"ID3" and len(head) == 10:
                return _id3_art(f, head)
            if head[:4] == b"fLaC":
                f.seek(4)
                return _flac_art(f)
            if os.path.splitext(path)[1].lower() in (".m4a", ".mp4", ".m4b", ".aac"):
                return _mp4_art(f)
    except Exception:
        pass
    return b""


def quick_art(path):
    """Cover of one song, right now: embedded art, else the folder picture ('' if none)."""
    try:
        st = os.stat(path)
    except OSError:
        return ""
    out, _dur = thumb_paths(path, st.st_size, st.st_mtime)
    if os.path.isfile(out):
        return out
    data = embedded_art_bytes(path)
    if data and save_square(QImage.fromData(data), out):
        return out
    f = folder_cover(path)
    if f and save_square(QImage(f), out):
        return out
    return ""


class SmoothScroller(QObject):
    """Eased mouse-wheel scrolling for a QScrollArea / QListWidget (instead of jumping a few lines at a time)."""

    def __init__(self, area, step=110, ms=260):
        super().__init__(area)
        self.bar = area.verticalScrollBar()
        self.step, self.ms, self.target = step, ms, 0.0
        self.anim = QVariantAnimation(self)
        self.anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self.anim.valueChanged.connect(lambda v: self.bar.setValue(int(round(v))))
        area.viewport().installEventFilter(self)

    def eventFilter(self, obj, ev):
        if ev.type() != QEvent.Type.Wheel or ev.modifiers() != Qt.KeyboardModifier.NoModifier:
            return False
        bar = self.bar
        if bar.maximum() <= bar.minimum():
            return False
        pd, ad = ev.pixelDelta().y(), ev.angleDelta().y()
        if not (pd or ad):
            return False
        delta = pd if pd else ad / 120.0 * self.step
        running = self.anim.state() == QVariantAnimation.State.Running
        base = self.target if running else float(bar.value())
        self.target = max(float(bar.minimum()), min(float(bar.maximum()), base - delta))
        self.anim.stop()
        self.anim.setDuration(self.ms)
        self.anim.setStartValue(float(bar.value()))
        self.anim.setEndValue(self.target)
        self.anim.start()
        ev.accept()
        return True


class LibraryThread(QThread):
    """Scans the videos folders and makes thumbnails (needs ffmpeg; without it placeholders are used)."""
    found = Signal(int, object)              # token, [(path, size, mtime), ...]
    thumb = Signal(int, str, str, float)     # token, video path, thumbnail path or '', duration (s)

    def __init__(self, token, roots, ffmpeg, parent=None, audio=False):
        super().__init__(parent)
        self.token, self.roots, self.ffmpeg = token, roots, ffmpeg
        self.audio = audio
        self.exts = AUDIO_EXTS if audio else EXTS
        self.stop = False

    def _scan(self):
        seen, items = set(), []
        for root in self.roots:
            if not root or not os.path.isdir(root):
                continue
            base_depth = root.rstrip("\\/").count(os.sep)
            for dirpath, dirnames, filenames in os.walk(root):
                if dirpath.count(os.sep) - base_depth >= 3:
                    dirnames[:] = []
                dirnames[:] = [d for d in dirnames if not d.startswith(".")]
                for fn in filenames:
                    if os.path.splitext(fn)[1].lower() not in self.exts or re.search(r"\.f\d+\.", fn):
                        continue
                    full = os.path.join(dirpath, fn)
                    key = os.path.normcase(os.path.abspath(full))
                    if key in seen:
                        continue
                    seen.add(key)
                    try:
                        st = os.stat(full)
                    except OSError:
                        continue
                    items.append((full, st.st_size, st.st_mtime))
                if self.stop:
                    return items
        items.sort(key=lambda x: x[2], reverse=True)
        return items[:300]

    def _thumb(self, path, size, mtime):
        out, dur_file = thumb_paths(path, size, mtime)
        if os.path.isfile(out) and os.path.isfile(dur_file):
            try:
                return out, float(open(dur_file).read() or 0)
            except Exception:
                pass
        dur = 0.0
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        have = False
        if self.audio:                                   # album art straight from the file - no ffmpeg needed
            data = embedded_art_bytes(path)
            if data:
                have = save_square(QImage.fromData(data), out)
        if self.ffmpeg:
            for ss in (("0",) if self.audio else ("3", "0")):    # audio: cover art only, no seeking
                cmd = ([self.ffmpeg, "-hide_banner", "-i", path] if have       # art found: only ask for the length
                       else [self.ffmpeg, "-hide_banner", "-y", "-ss", ss, "-i", path, "-frames:v", "1",
                             "-vf", "scale=512:-2", "-q:v", "4", out])
                try:
                    r = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
                                       timeout=30, creationflags=flags)
                    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", r.stderr or "")
                    if m:
                        dur = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
                except Exception:
                    pass
                if have or os.path.isfile(out):
                    break
        if self.audio and not os.path.isfile(out):       # no art inside the file: cover.jpg / folder.jpg next to it
            f = folder_cover(path)
            if f:
                save_square(QImage(f), out)
        try:
            open(dur_file, "w").write(str(dur))
        except OSError:
            pass
        return (out if os.path.isfile(out) else ""), dur

    def run(self):
        items = self._scan()
        if self.stop:
            return
        self.found.emit(self.token, items)
        if not self.ffmpeg and not self.audio:           # songs get covers even without ffmpeg
            return
        for path, size, mtime in items:
            if self.stop:
                return
            thumb, dur = self._thumb(path, size, mtime)
            if not self.stop:
                self.thumb.emit(self.token, path, thumb, dur)


def make_new_card(w=256, h=144, radius=14):
    """The dashed placeholder card of the library (the 'add new' tile)."""
    pm = QPixmap(w, h)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.setBrush(QColor(T["newcard"]))
    p.setPen(QPen(QColor(T["line_hi"]), 2, Qt.PenStyle.DashLine))
    p.drawRoundedRect(QRectF(1, 1, w - 2, h - 2), radius, radius)
    p.setPen(QPen(QColor(ACCENT), 5, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap))
    cx, cy = w / 2, h / 2
    p.drawLine(QPointF(cx - 17, cy), QPointF(cx + 17, cy))
    p.drawLine(QPointF(cx, cy - 17), QPointF(cx, cy + 17))
    p.end()
    return pm


class _HandOnItems(QObject):
    """Pointing-hand cursor only while the mouse is over a clickable row / card of a list.
    Over empty space inside the list it stays a normal arrow."""

    def __init__(self, lst):
        super().__init__(lst)
        self.lst = lst
        lst.setMouseTracking(True)
        vp = lst.viewport()
        vp.setMouseTracking(True)
        vp.setCursor(Qt.CursorShape.ArrowCursor)
        vp.installEventFilter(self)

    def eventFilter(self, obj, ev):
        t = ev.type()
        if t == QEvent.Type.MouseMove:
            it = self.lst.itemAt(ev.position().toPoint())
            hand = it is not None and bool(it.flags() & Qt.ItemFlag.ItemIsEnabled)
            obj.setCursor(Qt.CursorShape.PointingHandCursor if hand else Qt.CursorShape.ArrowCursor)
        elif t == QEvent.Type.Leave:
            obj.setCursor(Qt.CursorShape.ArrowCursor)
        return False


def hand_on_items(lst):
    """Show the pointing-hand cursor while the mouse is over the items of the list widget `lst`."""
    return _HandOnItems(lst)


class HRow(QListWidget):
    """One horizontal row of cards. The mouse wheel scrolls the page; Shift+wheel scrolls the row."""
    CARD_W, CARD_H = 284, 212
    SQ_W, SQ_H = 204, 244                            # square cards (music)

    def __init__(self, square=False):
        super().__init__()
        cw, ch = (self.SQ_W, self.SQ_H) if square else (self.CARD_W, self.CARD_H)
        self.setObjectName("library")
        self.setViewMode(QListWidget.ViewMode.IconMode)
        self.setFlow(QListWidget.Flow.LeftToRight)
        self.setWrapping(False)
        self.setResizeMode(QListWidget.ResizeMode.Adjust)
        self.setMovement(QListWidget.Movement.Static)
        self.setIconSize(QSize(176, 176) if square else QSize(256, 144))
        self.setGridSize(QSize(cw, ch))
        self.setSpacing(4)
        self.setWordWrap(False)
        self.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.setUniformItemSizes(True)
        self.setSelectionMode(QListWidget.SelectionMode.NoSelection)   # no highlight / tint on cards
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        hand_on_items(self)
        self.setFixedHeight(ch + 26)

    def wheelEvent(self, ev):
        dx, dy = ev.angleDelta().x(), ev.angleDelta().y()
        if dx or (ev.modifiers() & Qt.KeyboardModifier.ShiftModifier):
            bar = self.horizontalScrollBar()
            bar.setValue(bar.value() - (dx or dy))
            ev.accept()
        else:
            ev.ignore()                              # let the page scroll vertically

    def mouseReleaseEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton:
            super().mouseReleaseEvent(ev)
        else:
            ev.accept()


class PlaylistDialog(QDialog):
    """Create / edit a playlist: name and tick the tracks / videos."""

    def __init__(self, name, candidates, selected, heading, parent=None, audio=False):
        super().__init__(parent)
        self.audio = audio
        self.setWindowTitle(heading)
        self.setMinimumSize(500, 560)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(22, 20, 22, 18)
        lay.setSpacing(10)
        h = QLabel(heading)
        h.setStyleSheet("font-size: 20px; font-weight: 800;")
        lay.addWidget(h)
        self.name = QLineEdit(name)
        self.name.setPlaceholderText("Playlist name")
        lay.addWidget(self.name)
        lay.addWidget(QLabel(("Tracks" if audio else "Videos") + "   (tick to include)", objectName="hint"))
        self.list = QListWidget(objectName="chklist")
        self.list.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.list.setSelectionMode(QListWidget.SelectionMode.NoSelection)      # rows are never selected / shaded
        _HandOnCheckBoxes(self.list)
        for p in list(selected) + [c for c in candidates if c not in selected]:
            self._add(p, p in selected)
        lay.addWidget(self.list, 1)
        row = QHBoxLayout()
        addf = QPushButton("+  Add files…", objectName="flat")
        addf.setCursor(Qt.CursorShape.PointingHandCursor)
        addf.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        addf.clicked.connect(self._add_files)
        row.addWidget(addf)
        row.addStretch(1)
        cancel = QPushButton("Cancel", objectName="flat")
        save = QPushButton("Save", objectName="open")
        for b in (cancel, save):
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        cancel.clicked.connect(self.reject)
        save.clicked.connect(self.accept)
        row.addWidget(cancel)
        row.addWidget(save)
        lay.addLayout(row)

    def _add(self, path, checked):
        it = QListWidgetItem(pretty_title(path))
        it.setData(Qt.ItemDataRole.UserRole, path)
        it.setToolTip(path)
        it.setFlags((it.flags() | Qt.ItemFlag.ItemIsUserCheckable) & ~Qt.ItemFlag.ItemIsDragEnabled)
        it.setCheckState(Qt.CheckState.Checked if checked else Qt.CheckState.Unchecked)
        self.list.addItem(it)

    def _add_files(self):
        pat = " ".join(f"*{e}" for e in sorted(AUDIO_EXTS if self.audio else EXTS))
        what = "audio" if self.audio else "videos"
        files, _ = QFileDialog.getOpenFileNames(self, f"Add {what}", user_music_dir() if self.audio else user_videos_dir(),
                                                f"{what.capitalize()} ({pat});;All files (*)")
        have = {self.list.item(i).data(Qt.ItemDataRole.UserRole) for i in range(self.list.count())}
        for f in files:
            if f in have:
                for i in range(self.list.count()):
                    if self.list.item(i).data(Qt.ItemDataRole.UserRole) == f:
                        self.list.item(i).setCheckState(Qt.CheckState.Checked)
            else:
                self._add(f, True)

    def result_data(self):
        paths = [self.list.item(i).data(Qt.ItemDataRole.UserRole) for i in range(self.list.count())
                 if self.list.item(i).checkState() == Qt.CheckState.Checked]
        return self.name.text().strip(), paths


# ----------------------------------------------------------------------------
# Format converter (ffmpeg)
# ----------------------------------------------------------------------------
CONVERT_IN_EXTS = EXTS | AUDIO_EXTS
# (label, extension, kind)
CONVERT_FORMATS = [("MP4", "mp4", "video"), ("MKV", "mkv", "video"), ("WebM", "webm", "video"),
                   ("AVI", "avi", "video"), ("MOV", "mov", "video"), ("GIF", "gif", "video"),
                   ("MP3", "mp3", "audio"), ("M4A", "m4a", "audio"), ("OGG", "ogg", "audio"),
                   ("WAV", "wav", "audio"), ("FLAC", "flac", "audio")]
QUALITY_NAMES = ("High", "Balanced", "Small file")


def build_convert_args(ext, q):
    """ffmpeg output options for a target format. q: 0 = high quality, 1 = balanced, 2 = small file."""
    crf = str((18, 23, 28)[q])
    ab = ("256k", "192k", "128k")[q]
    vmap = ["-map", "0:v:0", "-map", "0:a:0?"]
    if ext in ("mp4", "mkv", "mov"):
        a = vmap + ["-c:v", "libx264", "-preset", "medium", "-crf", crf, "-pix_fmt", "yuv420p",
                    "-c:a", "aac", "-b:a", ab]
        if ext == "mp4":
            a += ["-movflags", "+faststart"]
        return a
    if ext == "webm":
        return vmap + ["-c:v", "libvpx-vp9", "-crf", str((27, 33, 39)[q]), "-b:v", "0", "-row-mt", "1",
                       "-deadline", "good", "-cpu-used", "4", "-c:a", "libopus",
                       "-b:a", ("160k", "128k", "96k")[q]]
    if ext == "avi":
        return vmap + ["-c:v", "mpeg4", "-q:v", str((2, 5, 9)[q]), "-c:a", "libmp3lame", "-b:a", ab]
    if ext == "gif":
        w, fps = ((640, 15), (480, 12), (320, 10))[q]
        return ["-map", "0:v:0", "-an", "-vf",
                f"fps={fps},scale={w}:-1:flags=lanczos,split[a][b];[a]palettegen[p];[b][p]paletteuse", "-loop", "0"]
    if ext == "mp3":
        return ["-vn", "-c:a", "libmp3lame", "-b:a", ab]
    if ext == "m4a":
        return ["-vn", "-c:a", "aac", "-b:a", ab]
    if ext == "ogg":
        return ["-vn", "-c:a", "libvorbis", "-b:a", ab]
    if ext == "wav":
        return ["-vn", "-c:a", "pcm_s16le"]
    if ext == "flac":
        return ["-vn", "-c:a", "flac"]
    return []


def unique_path(path):
    """`path` itself, or 'name (1).ext', 'name (2).ext' ... when it already exists."""
    if not os.path.exists(path):
        return path
    base, ext = os.path.splitext(path)
    n = 1
    while os.path.exists(f"{base} ({n}){ext}"):
        n += 1
    return f"{base} ({n}){ext}"


class ConvertThread(QThread):
    """Runs ffmpeg for a list of files in the background; the signals report progress and results."""
    progress = Signal(int, float)      # file index, 0..1
    file_done = Signal(int, str)
    file_failed = Signal(int, str)
    all_done = Signal(bool)            # True if cancelled

    def __init__(self, ffmpeg, jobs, parent=None):
        super().__init__(parent)
        self.ffmpeg, self.jobs = ffmpeg, jobs      # jobs: [(src, out, args)]
        self._proc, self._cancel = None, False

    def cancel(self):
        self._cancel = True
        if self._proc is not None:
            try:
                self._proc.terminate()
            except Exception:
                pass

    def run(self):
        flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        for i, (src, out, args) in enumerate(self.jobs):
            if self._cancel:
                break
            cmd = [self.ffmpeg, "-hide_banner", "-y", "-i", src] + args + ["-progress", "pipe:1", "-nostats", out]
            dur, tail, rc = 0.0, [], -1
            try:
                self._proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                                              encoding="utf-8", errors="replace", creationflags=flags)
                for line in self._proc.stdout:
                    line = line.strip()
                    if not dur:
                        m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", line)
                        if m:
                            dur = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
                    if line.startswith("out_time_us="):
                        try:
                            us = int(line.split("=", 1)[1])
                        except ValueError:
                            continue
                        if dur > 0 and us >= 0:
                            self.progress.emit(i, min(us / 1e6 / dur, 0.99))
                    elif line and not re.match(r"^\w+=", line):
                        tail = (tail + [line])[-6:]
                    if self._cancel:
                        self._proc.terminate()
                        break
                rc = self._proc.wait()
            except Exception as ex:
                tail = [str(ex)]
            self._proc = None
            if self._cancel or rc != 0:
                try:
                    if os.path.isfile(out):
                        os.remove(out)
                except OSError:
                    pass
            if self._cancel:
                break
            if rc == 0:
                self.file_done.emit(i, out)
            else:
                self.file_failed.emit(i, tail[-1] if tail else "ffmpeg failed")
        self.all_done.emit(self._cancel)


FORMAT_INFO = {"mp4": "H.264  ·  plays everywhere", "mkv": "H.264  ·  flexible container",
               "webm": "VP9  ·  made for the web", "avi": "MPEG-4  ·  older devices",
               "mov": "H.264  ·  Apple friendly", "gif": "Animated  ·  no sound",
               "mp3": "Most compatible", "m4a": "AAC  ·  small and clean",
               "ogg": "Vorbis  ·  open format", "wav": "Lossless  ·  big files",
               "flac": "Lossless  ·  compressed"}
QUALITY_HINTS = ("Best quality, biggest files.", "Good quality, medium size  (recommended).",
                 "Smallest files, some quality loss.")


def section_card(text, sub=""):
    """A rounded card with a title; returns (card, content layout, header layout)."""
    card = QFrame(objectName="group")
    cl = QVBoxLayout(card)
    cl.setContentsMargins(20, 16, 20, 18)
    cl.setSpacing(10)
    hr = QHBoxLayout()
    hr.setSpacing(10)
    mark = QFrame(objectName="marker")
    mark.setFixedSize(4, 18)
    hr.addWidget(mark)
    hr.addWidget(QLabel(text, objectName="section"))
    if sub:
        hr.addWidget(QLabel("·  " + sub, objectName="hint"))
    hr.addStretch(1)
    cl.addLayout(hr)
    return card, cl, hr


class FormatCard(QAbstractButton):
    """Big selectable format card: name, short description, video / music icon. Greyed out when disabled."""

    def __init__(self, label, info, kind, ext, parent=None, compact=False):
        super().__init__(parent)
        self.label, self.info = label, info
        self.compact = compact
        if compact:
            self.setToolTip(info)
        self.setCheckable(True)
        self.setProperty("ext", ext)
        self.setProperty("kind", kind)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)
        self.setMinimumHeight(50 if compact else 80)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)

    def sizeHint(self):
        return QSize(96, 50) if self.compact else QSize(190, 80)

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        r = QRectF(self.rect()).adjusted(1.5, 1.5, -1.5, -1.5)
        on, off = self.isChecked(), not self.isEnabled()
        if off:
            bg, fg, sub, border, style = QColor(0, 0, 0, 0), T["disabled"], T["disabled"], T["line_hi"], Qt.PenStyle.DashLine
        elif on:
            bg, fg, sub, border, style = QColor(T["accent"]), T["on_accent"], T["on_accent"], T["accent"], Qt.PenStyle.SolidLine
        else:
            hot = self.underMouse()
            bg, fg, sub = QColor(T["hover"] if hot else T["card"]), T["text"], T["dim"]
            border, style = (T["accent"] if hot else T["border"]), Qt.PenStyle.SolidLine
        p.setPen(QPen(QColor(border), 1.5, style))
        p.setBrush(bg)
        p.drawRoundedRect(r, 12 if self.compact else 16, 12 if self.compact else 16)
        if self.compact:                       # small card: name + short note, both centred
            f = QFont(self.font())
            f.setPointSize(12)
            f.setBold(True)
            p.setFont(f)
            p.setPen(QColor(fg))
            p.drawText(QRectF(r.left() + 4, r.top() + 5, r.width() - 8, 22), Qt.AlignmentFlag.AlignCenter, self.label)
            f2 = QFont(self.font())
            f2.setPointSize(8)
            p.setFont(f2)
            p.setPen(QColor(sub))
            txt = QFontMetrics(f2).elidedText(self.info, Qt.TextElideMode.ElideRight, int(r.width() - 12))
            p.drawText(QRectF(r.left() + 6, r.top() + 26, r.width() - 12, 16), Qt.AlignmentFlag.AlignCenter, txt)
            p.end()
            return
        icon_name = "play" if self.property("kind") == "video" else "music"
        p.drawPixmap(int(r.right()) - 38, int(r.top()) + 14, make_icon(icon_name, fg, 64).pixmap(24, 24))
        f = QFont(self.font())
        f.setPointSize(15)
        f.setBold(True)
        p.setFont(f)
        p.setPen(QColor(fg))
        p.drawText(QRectF(r.left() + 18, r.top() + 10, r.width() - 64, 30), Qt.AlignmentFlag.AlignVCenter, self.label)
        f2 = QFont(self.font())
        f2.setPointSize(9)
        p.setFont(f2)
        p.setPen(QColor(sub))
        txt = QFontMetrics(f2).elidedText(self.info, Qt.TextElideMode.ElideRight, int(r.width() - 36))
        p.drawText(QRectF(r.left() + 18, r.top() + 42, r.width() - 36, 24), Qt.AlignmentFlag.AlignVCenter, txt)
        p.end()


class ThumbThread(QThread):
    """Makes a preview picture (video frame / cover art) + duration for each file, without freezing the dialog."""
    done = Signal(str, str, float)             # path, thumbnail path or '', duration (s)

    def __init__(self, ffmpeg, paths, parent=None):
        super().__init__(parent)
        self.ffmpeg, self.paths = ffmpeg, list(paths)
        self.stop = False

    def run(self):
        for p in self.paths:
            if self.stop:
                return
            try:
                st = os.stat(p)
            except OSError:
                continue
            thumb, dur = LibraryThread(0, [], self.ffmpeg, None, audio=is_audio(p))._thumb(p, st.st_size, st.st_mtime)
            if not self.stop:
                self.done.emit(p, thumb, dur)


class ConvertDialog(QDialog):
    """Convert videos / audio between popular formats with ffmpeg."""
    PV_W, PV_H = 176, 99                    # preview box
    LI_W, LI_H = 112, 63                    # thumbnails in the list

    def __init__(self, paths, out_dir, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Convert formats")
        # same window size as "Download from the internet": width 700, height = the download window's height
        scr = QApplication.primaryScreen().availableGeometry()
        w, h = 700, 640
        try:
            tmp = DownloadDialog(parent.settings, out_dir, None)
            w = tmp.width() if tmp.width() > 0 else 700
            h = max(tmp.sizeHint().height(), tmp.minimumSizeHint().height())
            tmp.deleteLater()
        except Exception:
            pass
        self.setFixedSize(min(w, scr.width() - 40), min(max(h, 560), scr.height() - 60))
        self.setAcceptDrops(True)
        self.out_dir = out_dir
        self.thread_obj = None
        self.running = False
        self.meta = {}                             # path -> {"size", "thumb", "dur"}
        self._thumb_threads = set()
        self._jobs, self._ok, self._errors = [], 0, []

        def card_of(text, sub=""):                 # compact card: small paddings so more fits on screen
            c, l, h = section_card(text, sub)
            l.setContentsMargins(14, 10, 14, 12)
            l.setSpacing(6)
            return c, l, h

        outer = QVBoxLayout(self)
        outer.setContentsMargins(18, 14, 18, 12)
        outer.setSpacing(8)
        head = QHBoxLayout()
        head.setSpacing(10)
        title = QLabel("Convert formats", objectName="hero")
        title.setStyleSheet("font-size: 22px;")
        head.addWidget(title)
        head.addWidget(QLabel("drop files here too", objectName="hint"))
        head.addStretch(1)
        outer.addLayout(head)

        scroll = QScrollArea(objectName="libscroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.viewport().setAutoFillBackground(False)
        content = QWidget(objectName="libcontent")
        lay = QVBoxLayout(content)
        lay.setContentsMargins(0, 0, 8, 0)
        lay.setSpacing(8)
        scroll.setWidget(content)
        outer.addWidget(scroll, 1)

        # ---- 1. files: small preview on the left, list on the right
        card, cl, _h = card_of("Files", "what to convert")
        body = QHBoxLayout()
        body.setSpacing(12)
        pv = QVBoxLayout()
        pv.setSpacing(3)
        self.pv_img = QLabel()
        self.pv_img.setFixedSize(self.PV_W, self.PV_H)
        pv.addWidget(self.pv_img)
        self.pv_title = QLabel("")
        self.pv_title.setFixedWidth(self.PV_W)
        self.pv_title.setStyleSheet("font-size: 12px; font-weight: 700;")
        self.pv_info = QLabel("", objectName="hint")
        self.pv_info.setFixedWidth(self.PV_W)
        pv.addWidget(self.pv_title)
        pv.addWidget(self.pv_info)
        pv.addStretch(1)
        body.addLayout(pv)
        self.src = QListWidget()
        self.src.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.src.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection)
        self.src.setIconSize(QSize(self.LI_W, self.LI_H))
        self.src.setSpacing(2)
        self.src.setMinimumHeight(self.PV_H + 36)
        self.src.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.src.currentItemChanged.connect(lambda *_: self._update_preview())
        body.addWidget(self.src, 1)
        cl.addLayout(body)
        r = QHBoxLayout()
        self.b_add = self._flat("+  Add files…", self._add_files)
        self.b_rm = self._flat("Remove selected", self._remove)
        self.count_lbl = QLabel("", objectName="hint")
        r.addWidget(self.b_add)
        r.addWidget(self.b_rm)
        r.addStretch(1)
        r.addWidget(self.count_lbl)
        cl.addLayout(r)
        lay.addWidget(card)

        # ---- 2. formats: video in one row, audio in one row (greyed out for audio files)
        card, cl, _h = card_of("Convert to", "pick the new format")
        self.fmt_group = QButtonGroup(self)
        self.fmt_buttons = []
        self.video_note = None
        for title_text, kind in (("Video formats", "video"), ("Audio only", "audio")):
            hr = QHBoxLayout()
            hr.addWidget(QLabel(title_text, objectName="caption"))
            if kind == "video":
                self.video_note = QLabel("", objectName="hint")
                hr.addWidget(self.video_note)
            hr.addStretch(1)
            cl.addLayout(hr)
            grid = QGridLayout()
            grid.setSpacing(6)
            n = 0
            for label, ext, k in CONVERT_FORMATS:
                if k != kind:
                    continue
                b = FormatCard(label, FORMAT_INFO.get(ext, ""), kind, ext, compact=True)
                self.fmt_group.addButton(b)
                self.fmt_buttons.append(b)
                b.toggled.connect(lambda _on=False: self._sync_quality())
                grid.addWidget(b, 0, n)
                n += 1
            for c in range(6):
                grid.setColumnStretch(c, 1)
            cl.addLayout(grid)
        self.fmt_buttons[0].setChecked(True)
        lay.addWidget(card)

        # ---- 3. quality + destination in one card
        card, cl, _h = card_of("Quality and folder")
        qrow = QHBoxLayout()
        qrow.setSpacing(8)
        self.q_group = QButtonGroup(self)
        self.q_buttons = []
        for i, name in enumerate(QUALITY_NAMES):
            b = QPushButton(name, objectName="chip")
            b.setCheckable(True)
            b.setMinimumHeight(34)
            b.setMinimumWidth(96)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            self.q_group.addButton(b, i)
            self.q_buttons.append(b)
            b.toggled.connect(lambda _on=False: self._sync_quality())
            qrow.addWidget(b)
        self.q_buttons[1].setChecked(True)
        self.q_hint = QLabel("", objectName="hint")
        self.q_hint.setWordWrap(True)
        qrow.addWidget(self.q_hint, 1)
        cl.addLayout(qrow)
        frow = QHBoxLayout()
        frow.setSpacing(8)
        self.folder_lbl = QLabel(self.out_dir, objectName="path")
        self.folder_lbl.setTextInteractionFlags(Qt.TextInteractionFlag.NoTextInteraction)
        self.folder_lbl.setMinimumWidth(10)
        self.folder_lbl.setToolTip(self.out_dir)
        self.b_change = self._flat("Change folder…", self._change_folder)
        self.b_open = self._flat("Open folder", self._open_folder)
        frow.addWidget(QLabel("Save to", objectName="caption"))
        frow.addWidget(self.folder_lbl, 1)
        frow.addWidget(self.b_change)
        frow.addWidget(self.b_open)
        cl.addLayout(frow)
        lay.addWidget(card)
        lay.addStretch(1)

        # ---- bottom bar (always visible): progress, then status + buttons on one row
        self.bar = QProgressBar()
        self.bar.setRange(0, 1000)
        self.bar.setTextVisible(False)
        self.bar.setFixedHeight(10)
        outer.addWidget(self.bar)
        brow = QHBoxLayout()
        self.status = QLabel("", objectName="hint")
        self.status.setWordWrap(True)
        brow.addWidget(self.status, 1)
        self.b_close = self._flat("Close", self.reject)
        self.b_go = QPushButton("Convert", objectName="open")
        self.b_go.setCursor(Qt.CursorShape.PointingHandCursor)
        self.b_go.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.b_go.setMinimumSize(150, 42)
        self.b_go.clicked.connect(self._toggle)
        brow.addWidget(self.b_close)
        brow.addWidget(self.b_go)
        outer.addLayout(brow)

        new = [p for p in paths if self._add_path(p)]
        self._after_add(new)
        self._update_preview()
        if not find_ffmpeg():
            self.status.setText("ffmpeg was not found.  Run:  pip install imageio-ffmpeg")

    # ---- small helpers
    def _flat(self, text, slot):
        b = QPushButton(text, objectName="flat")
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        b.clicked.connect(lambda _=False: slot())
        return b

    def _paths(self):
        return [self.src.item(i).data(Qt.ItemDataRole.UserRole) for i in range(self.src.count())]

    def _checked_fmt(self):
        return next((b for b in self.fmt_buttons if b.isChecked()), None)

    # ---- files list + preview box
    def _item_text(self, p):
        m = self.meta.get(p, {})
        bits = [human_size(m.get("size", 0)), os.path.splitext(p)[1][1:].upper()]
        if m.get("dur"):
            bits.append(fmt_time(int(m["dur"] * 1000)))
        return pretty_title(p) + "\n" + "  ·  ".join(bits)

    def _add_path(self, p):
        if not os.path.isfile(p) or os.path.splitext(p)[1].lower() not in CONVERT_IN_EXTS:
            return False
        if p in self.meta:
            return False
        try:
            size = os.path.getsize(p)
        except OSError:
            size = 0
        self.meta[p] = {"size": size, "thumb": "", "dur": 0.0}
        it = QListWidgetItem(QIcon(make_thumb(None, 0, self.LI_W, self.LI_H, 10, audio=is_audio(p))), self._item_text(p))
        it.setData(Qt.ItemDataRole.UserRole, p)
        it.setToolTip(p)
        self.src.addItem(it)
        return True

    def _after_add(self, new):
        ff = find_ffmpeg()
        if new and ff:
            owner = self.parent() or self
            t = ThumbThread(ff, new, owner)
            t.done.connect(self._on_thumb)
            t.finished.connect(lambda t=t: self._thumb_threads.discard(t))
            self._thumb_threads.add(t)
            t.start()
        if self.src.count() and self.src.currentItem() is None:
            self.src.setCurrentRow(0)
        self._sync_formats()
        self._update_preview()

    def _on_thumb(self, path, thumb, dur):
        m = self.meta.get(path)
        if m is None:
            return
        m["thumb"], m["dur"] = thumb, dur
        for i in range(self.src.count()):
            it = self.src.item(i)
            if it.data(Qt.ItemDataRole.UserRole) == path:
                it.setIcon(QIcon(make_thumb(thumb or None, 0, self.LI_W, self.LI_H, 10, audio=is_audio(path))))
                it.setText(self._item_text(path))
        cur = self.src.currentItem()
        if cur is not None and cur.data(Qt.ItemDataRole.UserRole) == path:
            self._update_preview()

    def _update_preview(self):
        it = self.src.currentItem()
        n = self.src.count()
        self.count_lbl.setText(f"{n} file{'s' if n != 1 else ''}" if n else "")
        if it is None:
            self.pv_img.setPixmap(make_thumb(None, 0, self.PV_W, self.PV_H, 12))
            self.pv_title.setText("No file selected")
            self.pv_info.setText("Add a video or a music file to see it here.")
            return
        p = it.data(Qt.ItemDataRole.UserRole)
        m = self.meta.get(p, {})
        audio = is_audio(p)
        self.pv_img.setPixmap(make_thumb(m.get("thumb") or None, m.get("dur", 0), self.PV_W, self.PV_H, 12,
                                         tag="AUDIO" if audio else "VIDEO", audio=audio))
        self.pv_title.setText(pretty_title(p))
        bits = [os.path.splitext(p)[1][1:].upper(), human_size(m.get("size", 0))]
        if m.get("dur"):
            bits.append(fmt_time(int(m["dur"] * 1000)))
        self.pv_info.setText("  ·  ".join(bits))

    def _add_files(self):
        pat = " ".join(f"*{e}" for e in sorted(CONVERT_IN_EXTS))
        files, _ = QFileDialog.getOpenFileNames(self, "Choose files to convert", user_videos_dir(),
                                                f"Media files ({pat});;All files (*)")
        self._after_add([f for f in files if self._add_path(f)])

    def _remove(self):
        for it in self.src.selectedItems():
            self.meta.pop(it.data(Qt.ItemDataRole.UserRole), None)
            self.src.takeItem(self.src.row(it))
        self._sync_formats()
        self._update_preview()

    # ---- formats: video formats are shaded when every file is audio
    def _sync_formats(self):
        paths = self._paths()
        all_audio = bool(paths) and all(is_audio(p) for p in paths)
        for b in self.fmt_buttons:
            if b.property("kind") == "video":
                b.setEnabled(not all_audio)
        self.video_note.setText("·  not available for audio files" if all_audio else "")
        cur = self._checked_fmt()
        if cur is None or not cur.isEnabled():
            nxt = next((b for b in self.fmt_buttons if b.isEnabled()), None)
            if nxt is not None:
                nxt.setChecked(True)
        for b in self.fmt_buttons:
            b.update()
        self._sync_quality()

    def _sync_quality(self):
        if not hasattr(self, "q_hint"):              # still building the dialog
            return
        cur = self._checked_fmt()
        lossless = cur is not None and cur.property("ext") in ("wav", "flac")
        for b in self.q_buttons:
            b.setEnabled(not lossless and not self.running)
        if lossless:
            self.q_hint.setText("Lossless format  -  keeps the full quality, so there is no quality setting.")
        else:
            self.q_hint.setText(QUALITY_HINTS[max(0, self.q_group.checkedId())])

    # ---- folder
    def _change_folder(self):
        start = self.out_dir if os.path.isdir(self.out_dir) else os.path.dirname(self.out_dir)
        d = QFileDialog.getExistingDirectory(self, "Choose output folder", start)
        if d:
            self.out_dir = os.path.normpath(d)
            self.folder_lbl.setText(self.out_dir)
            self.folder_lbl.setToolTip(self.out_dir)

    def _open_folder(self):
        os.makedirs(self.out_dir, exist_ok=True)
        QDesktopServices.openUrl(QUrl.fromLocalFile(self.out_dir))

    # ---- converting
    def _set_busy(self, busy):
        self.running = busy
        for w in [self.src, self.b_add, self.b_rm, self.b_change, self.b_close] + self.fmt_buttons:
            w.setEnabled(not busy)
        self.b_go.setText("Cancel" if busy else "Convert")
        if busy:
            for b in self.q_buttons:
                b.setEnabled(False)
        else:
            self._sync_formats()                     # re-applies the greyed-out video formats / quality

    def _toggle(self):
        if self.running:
            if self.thread_obj:
                self.thread_obj.cancel()
            self.status.setText("Cancelling…")
            return
        ffmpeg = find_ffmpeg()
        if not ffmpeg:
            self.status.setText("ffmpeg was not found.  Run:  pip install imageio-ffmpeg")
            return
        paths = self._paths()
        if not paths:
            self.status.setText("Add at least one file first.")
            return
        fmt = self._checked_fmt()
        ext, kind = fmt.property("ext"), fmt.property("kind")
        q = max(0, self.q_group.checkedId())
        try:
            os.makedirs(self.out_dir, exist_ok=True)
        except OSError as ex:
            self.status.setText(f"Cannot create folder: {ex}")
            return
        jobs, skipped = [], []
        for p in paths:
            if kind == "video" and is_audio(p):      # an audio file has no picture to make a video from
                skipped.append(f"{os.path.basename(p)}: audio file, skipped")
                continue
            out = unique_path(os.path.join(self.out_dir, os.path.splitext(os.path.basename(p))[0] + "." + ext))
            jobs.append((p, out, build_convert_args(ext, q)))
        if not jobs:
            self.status.setText("Audio files can only be converted to the audio formats.")
            return
        self._jobs, self._ok, self._errors = jobs, 0, skipped
        self.bar.setValue(0)
        self._set_busy(True)
        self.status.setText(f"Converting 1/{len(jobs)}…")
        t = ConvertThread(ffmpeg, jobs, self)
        t.progress.connect(self._on_progress)
        t.file_done.connect(self._on_done)
        t.file_failed.connect(self._on_failed)
        t.all_done.connect(self._on_finished)
        self.thread_obj = t
        t.start()

    def _on_progress(self, i, frac):
        n = len(self._jobs)
        self.bar.setValue(int((i + frac) / n * 1000))
        self.status.setText(f"Converting {i + 1}/{n}:  {os.path.basename(self._jobs[i][0])}  ({int(frac * 100)}%)")

    def _on_done(self, i, out):
        self._ok += 1
        self.bar.setValue(int((i + 1) / len(self._jobs) * 1000))

    def _on_failed(self, i, msg):
        self._errors.append(f"{os.path.basename(self._jobs[i][0])}: {msg}")

    def _on_finished(self, cancelled):
        self._set_busy(False)
        self.thread_obj = None
        if cancelled:
            self.status.setText("Cancelled.")
            return
        text = f"Done - {self._ok} file{'s' if self._ok != 1 else ''} converted."
        if self._errors:
            text += "  Failed:  " + "  |  ".join(self._errors)
        self.status.setText(text)
        if self._ok:
            self.bar.setValue(1000)
            p = self.parent()
            if p is not None and hasattr(p, "refresh_library"):
                p.refresh_library()

    # ---- drag & drop files onto the dialog
    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dropEvent(self, e):
        if self.running:
            return
        files = [u.toLocalFile() for u in e.mimeData().urls() if u.isLocalFile()]
        self._after_add([f for f in files if self._add_path(f)])

    def done(self, r):
        for t in list(self._thumb_threads):          # thumbnail jobs are not needed any more
            t.stop = True
        super().done(r)

    def reject(self):
        if self.running and self.thread_obj:
            self.thread_obj.cancel()
            self.thread_obj.wait(3000)
        super().reject()


# ----------------------------------------------------------------------------
# Settings
# ----------------------------------------------------------------------------
def default_settings():
    """Default value of every user setting (see SettingsDialog)."""
    return {"download_dir": default_download_dir(),
            "convert_dir": os.path.join(default_download_dir(), "converted"),
            "yt_quality": "best", "cookie_browser": "auto",
            "autoplay_next": True, "remember_volume": True, "hide_ms": 2000,
            "extra_roots": [], "extra_audio_roots": [], "theme": "superdark", "accent": ""}


class ThemeSwatch(QAbstractButton):
    """Small preview card of one theme (drawn with that theme's own colours)."""

    def __init__(self, tid, th, parent=None):
        super().__init__(parent)
        self.tid, self.th = tid, th
        self.setCheckable(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setFixedSize(118, 84)
        self.setToolTip(th["name"])

    def paintEvent(self, _e):
        th = self.th
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        sel = self.isChecked()
        r = QRectF(self.rect()).adjusted(2, 2, -2, -2)
        ring = T["accent"] if sel else (th["line_hi"] if self.underMouse() else th["line"])
        p.setBrush(QColor(th["bg"]))
        p.setPen(QPen(QColor(ring), 2.5 if sel else 1.5))
        p.drawRoundedRect(r, 14, 14)
        p.setPen(Qt.PenStyle.NoPen)
        x, y = r.left() + 14, r.top() + 14
        p.setBrush(QColor(th["accent"]))
        p.drawEllipse(QPointF(x + 8, y + 8), 8, 8)
        p.setBrush(QColor(th["text2"]))
        p.drawRoundedRect(QRectF(x + 22, y + 1, 44, 6), 3, 3)
        p.setBrush(QColor(th["muted"]))
        p.drawRoundedRect(QRectF(x + 22, y + 11, 28, 5), 2.5, 2.5)
        w, by = r.width() - 28, r.top() + 40
        p.setBrush(QColor(th["line"]))
        p.drawRoundedRect(QRectF(x, by, w, 5), 2.5, 2.5)
        p.setBrush(QColor(th["accent"]))
        p.drawRoundedRect(QRectF(x, by, w * 0.55, 5), 2.5, 2.5)
        p.setBrush(QColor(th["handle"]))
        p.drawEllipse(QPointF(x + w * 0.55, by + 2.5), 5, 5)
        f = QFont("Segoe UI", 8)
        f.setBold(True)
        p.setFont(f)
        p.setPen(QColor(th["text"]))
        p.drawText(QRectF(x, r.bottom() - 26, w, 18), Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, th["name"])
        p.end()


class AccentDot(QAbstractButton):
    """Round colour button for the accent-colour picker."""

    def __init__(self, color, parent=None):
        super().__init__(parent)
        self.color = color
        self.setCheckable(True)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setFixedSize(28, 28)
        self.setToolTip(color.upper())

    def paintEvent(self, _e):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(self.color))
        p.drawEllipse(QRectF(self.rect()).adjusted(4, 4, -4, -4))
        if self.isChecked():
            p.setBrush(Qt.BrushStyle.NoBrush)
            p.setPen(QPen(QColor(T["text"]), 2))
            p.drawEllipse(QRectF(self.rect()).adjusted(1, 1, -1, -1))
        p.end()


class SettingsDialog(QDialog):
    """Settings as a side panel: a see-through window over the main window with a panel that slides in from the right."""

    def __init__(self, cur, parent=None):
        super().__init__(parent, Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setObjectName("settings")
        self.setWindowTitle("Settings")
        if parent is not None:
            self.setGeometry(QRect(parent.mapToGlobal(QPoint(0, 0)), parent.size()))
        else:
            self.resize(1000, 700)
        self._pw = min(500, max(360, self.width() - 40))
        self._shown, self._closing, self._anims = False, False, []
        self.panel = QFrame(self, objectName="sidepanel")
        self.panel.setGeometry(self.width(), 0, self._pw, self.height())      # starts outside the window
        self.v = dict(cur)
        self.v["extra_roots"] = list(cur.get("extra_roots", []))
        self.v["extra_audio_roots"] = list(cur.get("extra_audio_roots", []))
        self.cache_cleared = False
        self._set = {}

        outer = QVBoxLayout(self.panel)
        outer.setContentsMargins(24, 22, 20, 16)
        outer.setSpacing(14)
        head = QHBoxLayout()
        col = QVBoxLayout()
        col.setSpacing(2)
        title = QLabel("Settings", objectName="hero")
        title.setStyleSheet("font-size: 26px;")
        col.addWidget(title)
        col.addWidget(QLabel("Theme changes preview instantly", objectName="hint"))
        head.addLayout(col, 1)
        close = QPushButton("✕", objectName="flat")
        close.setToolTip("Close without saving  (Esc)")
        close.setCursor(Qt.CursorShape.PointingHandCursor)
        close.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        close.setFixedSize(36, 36)
        close.setStyleSheet("font-size: 17px;")
        close.clicked.connect(self.reject)
        head.addWidget(close, alignment=Qt.AlignmentFlag.AlignTop)
        outer.addLayout(head)

        scroll = QScrollArea(objectName="libscroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.viewport().setAutoFillBackground(False)
        content = QWidget(objectName="libcontent")
        lay = QVBoxLayout(content)
        lay.setContentsMargins(0, 0, 10, 0)
        lay.setSpacing(14)
        scroll.setWidget(content)
        outer.addWidget(scroll, 1)

        c = self._section(lay, "Appearance", "theme & colors")
        self._caption(c, "Theme")
        self._themes_grid(c)
        self._caption(c, "Accent color  (replaces the highlight color of the theme)")
        self._accent_row(c)

        c = self._section(lay, "Folders")
        self._folder(c, "download_dir", "Downloads  (files from the internet are saved here)")
        self._folder(c, "convert_dir", "Converted files")

        c = self._section(lay, "Internet downloads", "YouTube, Instagram, TikTok, X")
        self._caption(c, "Default video quality")
        self._chips(c, "yt_quality", [("Best", "best"), ("1080p", "1080"), ("720p", "720"), ("480p", "480")])
        self._caption(c, "Sign-in cookies from browser  (use this if a site asks you to sign in)")
        self._chips(c, "cookie_browser", [("Auto", "auto"), ("Firefox", "firefox"), ("Chrome", "chrome"),
                                          ("Edge", "edge"), ("Brave", "brave"), ("Off", "off")])

        c = self._section(lay, "Playback")
        self._check(c, "autoplay_next", "Play the next video automatically")
        self._check(c, "remember_volume", "Remember the volume")
        self._caption(c, "Hide the control bar after")
        self._chips(c, "hide_ms", [("1 s", 1000), ("2 s", 2000), ("3 s", 3000), ("5 s", 5000)])

        c = self._section(lay, "Library")
        self._roots_editor(c, "extra_roots", "Extra folders for the video library  (your Videos folder is always included)",
                           user_videos_dir)
        self._roots_editor(c, "extra_audio_roots", "Extra folders for the music library  (your Music folder is always included)",
                           user_music_dir)
        cr = QHBoxLayout()
        cr.addWidget(self._flat("Clear thumbnail cache", self._clear_cache))
        self.cache_lbl = QLabel("", objectName="hint")
        cr.addWidget(self.cache_lbl)
        cr.addStretch(1)
        c.addLayout(cr)

        if sys.platform == "win32":
            c = self._section(lay, "Default player", f"open files with {APP_NAME}")
            note = QLabel(f"Adds {APP_NAME} to 'Open with' and to Windows Default apps. Windows asks you to pick "
                          f"{APP_NAME} there - after that, double-clicking a video or song opens it here.", objectName="hint")
            note.setWordWrap(True)
            c.addWidget(note)
            dr = QHBoxLayout()
            dr.addWidget(self._flat(f"Make {APP_NAME} the default player…", self._make_default))
            dr.addStretch(1)
            c.addLayout(dr)
            self.def_lbl = QLabel("", objectName="hint")
            self.def_lbl.setWordWrap(True)
            c.addWidget(self.def_lbl)
        lay.addStretch(1)

        sep = QFrame(objectName="sep")
        sep.setFixedHeight(1)
        outer.addWidget(sep)
        brow = QHBoxLayout()
        brow.setSpacing(10)
        brow.addWidget(self._flat("Reset to defaults", self._reset))
        brow.addStretch(1)
        cancel = QPushButton("Cancel", objectName="ghost")
        save = QPushButton("Save", objectName="open")
        for b_ in (cancel, save):
            b_.setCursor(Qt.CursorShape.PointingHandCursor)
            b_.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        cancel.clicked.connect(self.reject)
        save.clicked.connect(self.accept)
        brow.addWidget(cancel)
        brow.addWidget(save)
        outer.addLayout(brow)

    def _make_default(self):
        if register_file_associations():
            self.def_lbl.setText(f"{APP_NAME} is registered.  In the Windows window that opens, choose {APP_NAME} for the file types you want.")
            QDesktopServices.openUrl(QUrl(f"ms-settings:defaultapps?registeredAppUser={APP_ID}"))
        else:
            self.def_lbl.setText(f"Could not register {APP_NAME} with Windows.")

    # ---- side panel: dim the window, slide in / out
    def paintEvent(self, _e):
        p = QPainter(self)
        p.fillRect(self.rect(), QColor(0, 0, 0, 125))
        p.end()

    def mousePressEvent(self, e):
        if not self.panel.geometry().contains(e.position().toPoint()):
            self.reject()                         # click on the dimmed area closes the panel
        else:
            super().mousePressEvent(e)

    def _slide(self, x_to, opacity_to, ms, on_done=None):
        a = QPropertyAnimation(self.panel, b"pos", self)
        a.setDuration(ms)
        a.setEasingCurve(QEasingCurve.Type.OutCubic if x_to < self.width() else QEasingCurve.Type.InCubic)
        a.setStartValue(self.panel.pos())
        a.setEndValue(QPoint(x_to, 0))
        b = QPropertyAnimation(self, b"windowOpacity", self)
        b.setDuration(ms)
        b.setStartValue(self.windowOpacity())
        b.setEndValue(opacity_to)
        if on_done:
            a.finished.connect(on_done)
        self._anims = [a, b]
        a.start()
        b.start()

    def showEvent(self, e):
        super().showEvent(e)
        if self._shown:
            return
        self._shown = True
        self.panel.setGeometry(self.width(), 0, self._pw, self.height())
        self.setWindowOpacity(0.0)
        self._slide(self.width() - self._pw, 1.0, 300)

    def done(self, r):
        if self._closing:
            return
        self._closing = True
        self._slide(self.width(), 0.0, 220, lambda: QDialog.done(self, r))

    # ---- appearance
    def _preview(self):
        cb = getattr(self.parent(), "apply_theme", None)
        if cb:
            cb(self.v["theme"], self.v["accent"])

    def _themes_grid(self, lay):
        self._swatches = []
        groups = list(THEME_GROUPS)
        rest = [t for t in THEME_SPECS if not any(t in ids for _n, ids in groups)]
        if rest:
            groups.append(("More", rest))
        for gname, ids in groups:
            self._caption(lay, gname)
            grid = QGridLayout()
            grid.setSpacing(10)
            for i, tid in enumerate(ids):
                sw = ThemeSwatch(tid, get_theme(tid))
                sw.clicked.connect(lambda _=False, t=tid: self._pick_theme(t))
                grid.addWidget(sw, i // 3, i % 3)
                self._swatches.append(sw)
            grid.setColumnStretch(3, 1)
            lay.addLayout(grid)
        self._sync_theme()
        self._set["theme"] = lambda _v: self._sync_theme()

    def _accent_row(self, lay):
        row = QHBoxLayout()
        row.setSpacing(4)
        self._dots = []
        for c in ACCENT_PRESETS:
            d = AccentDot(c)
            d.clicked.connect(lambda _=False, c=c: self._pick_accent(c))
            row.addWidget(d)
            self._dots.append(d)
        row.addStretch(1)
        lay.addLayout(row)
        row2 = QHBoxLayout()
        row2.addWidget(self._flat("Custom color…", self._custom_accent))
        row2.addWidget(self._flat("Use theme color", lambda: self._pick_accent("")))
        self.accent_lbl = QLabel("", objectName="hint")
        row2.addWidget(self.accent_lbl)
        row2.addStretch(1)
        lay.addLayout(row2)
        self._sync_accent()
        self._set["accent"] = lambda _v: self._sync_accent()

    def _sync_theme(self):
        for sw in self._swatches:
            sw.setChecked(sw.tid == self.v["theme"])
            sw.update()

    def _sync_accent(self):
        acc = (self.v["accent"] or "").lower()
        for d in self._dots:
            d.setChecked(d.color.lower() == acc)
            d.update()
        self.accent_lbl.setText(f"Custom: {acc.upper()}" if acc else "Using the theme's own color")

    def _pick_theme(self, tid):
        self.v["theme"] = tid
        self.v["accent"] = ""            # a new theme starts with its own accent colour
        self._sync_theme()
        self._sync_accent()
        self._preview()

    def _pick_accent(self, color):
        self.v["accent"] = color
        self._sync_accent()
        self._preview()

    def _custom_accent(self):
        start = QColor(self.v["accent"] or get_theme(self.v["theme"])["accent"])
        col = QColorDialog.getColor(start, self, "Choose accent color",
                                    QColorDialog.ColorDialogOption.DontUseNativeDialog)
        if col.isValid():
            self._pick_accent(col.name())

    # ---- small builders
    def _put(self, key, val):
        self.v[key] = val

    def _flat(self, text, slot):
        b = QPushButton(text, objectName="flat")
        b.setCursor(Qt.CursorShape.PointingHandCursor)
        b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        b.clicked.connect(lambda _=False: slot())
        return b

    def _section(self, lay, text, sub=""):
        """A rounded card with a title; returns the layout to fill it."""
        card = QFrame(objectName="group")
        cl = QVBoxLayout(card)
        cl.setContentsMargins(20, 16, 20, 18)
        cl.setSpacing(10)
        hr = QHBoxLayout()
        hr.setSpacing(10)
        mark = QFrame(objectName="marker")
        mark.setFixedSize(4, 18)
        hr.addWidget(mark)
        hr.addWidget(QLabel(text, objectName="section"))
        if sub:
            hr.addWidget(QLabel("·  " + sub, objectName="hint"))
        hr.addStretch(1)
        cl.addLayout(hr)
        lay.addWidget(card)
        return cl

    def _caption(self, lay, text):
        lab = QLabel(text, objectName="caption")
        lab.setWordWrap(True)
        lay.addWidget(lab)

    def _folder(self, lay, key, caption):
        self._caption(lay, caption)
        row = QHBoxLayout()
        lbl = QLabel(self.v[key], objectName="path")
        lbl.setWordWrap(True)
        row.addWidget(lbl, 1)

        def pick():
            start = self.v[key] if os.path.isdir(self.v[key]) else os.path.dirname(self.v[key])
            d = QFileDialog.getExistingDirectory(self, "Choose folder", start)
            if d:
                self.v[key] = os.path.normpath(d)
                lbl.setText(self.v[key])
        row.addWidget(self._flat("Change…", pick))
        lay.addLayout(row)
        self._set[key] = lbl.setText

    def _chips(self, lay, key, options):
        row = QGridLayout()
        row.setSpacing(8)
        cols = 3 if len(options) > 4 else 4
        group = QButtonGroup(self)
        btns = []
        for n, (label, val) in enumerate(options):
            b = QPushButton(label, objectName="chip")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            group.addButton(b)
            btns.append((b, val))
            row.addWidget(b, n // cols, n % cols)
            b.clicked.connect(lambda _=False, k=key, x=val: self._put(k, x))
        row.setColumnStretch(cols, 1)
        lay.addLayout(row)

        def setter(val):
            for b, x in btns:
                b.setChecked(x == val)
        setter(self.v[key])
        self._set[key] = setter

    def _check(self, lay, key, text):
        c = BoxCheck(text)
        c.setChecked(bool(self.v[key]))
        c.toggled.connect(lambda on, k=key: self._put(k, on))
        lay.addWidget(c)
        self._set[key] = c.setChecked

    # ---- library folders / cache
    def _roots_editor(self, lay, key, caption, start_fn):
        """A list of extra library folders with Add / Remove buttons, stored in self.v[key]."""
        self._caption(lay, caption)
        lst = QListWidget(objectName="roots")
        lst.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        lst.setFixedHeight(92)
        lst.addItems(self.v[key])
        lay.addWidget(lst)

        def sync():
            self.v[key] = [lst.item(i).text() for i in range(lst.count())]

        def add():
            d = QFileDialog.getExistingDirectory(self, "Add a folder to the library", start_fn())
            if d:
                d = os.path.normpath(d)
                if d not in [lst.item(i).text() for i in range(lst.count())]:
                    lst.addItem(d)
                    sync()

        def remove():
            for it in lst.selectedItems():
                lst.takeItem(lst.row(it))
            sync()

        def setter(val):
            lst.clear()
            lst.addItems(val)
            sync()

        rr = QHBoxLayout()
        rr.addWidget(self._flat("+  Add folder…", add))
        rr.addWidget(self._flat("Remove selected", remove))
        rr.addStretch(1)
        lay.addLayout(rr)
        self._set[key] = setter

    def _clear_cache(self):
        shutil.rmtree(os.path.join(tempfile.gettempdir(), THUMB_CACHE_DIR), ignore_errors=True)
        self.cache_cleared = True
        self.cache_lbl.setText("Cleared - thumbnails will be rebuilt")

    def _reset(self):
        d = default_settings()
        for k, val in d.items():
            self.v[k] = val
            self._set[k](val)
        self._preview()

    def values(self):
        return self.v


class ClickSlider(QSlider):
    """Slider that jumps to the clicked position."""

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            v = QStyle.sliderValueFromPosition(self.minimum(), self.maximum(),
                                               int(e.position().x()), self.width())
            self.setValue(v)
            self.sliderMoved.emit(v)
        super().mousePressEvent(e)


def tool_button(icon_name, tip, size=24, parent=None):
    """Flat icon-only QToolButton with a tooltip."""
    b = QToolButton(parent)
    b.setIcon(make_icon(icon_name))
    b.setProperty("icon_name", icon_name)
    b.setIconSize(QSize(size, size))
    b.setToolTip(tip)
    b.setCursor(Qt.CursorShape.PointingHandCursor)
    b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
    return b


class BoxCheck(QCheckBox):
    """Check box where ONLY the little box reacts. The text is a plain label: clicking it does nothing,
    and nothing gets highlighted."""
    BOX = 20

    def __init__(self, text="", parent=None):
        super().__init__(text, parent)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    def hitButton(self, pos):
        box = QRect(0, (self.height() - self.BOX) // 2, self.BOX, self.BOX)
        return box.adjusted(-5, -5, 5, 5).contains(pos)

    def mouseMoveEvent(self, ev):
        on = self.hitButton(ev.position().toPoint())
        self.setCursor(Qt.CursorShape.PointingHandCursor if on else Qt.CursorShape.ArrowCursor)
        super().mouseMoveEvent(ev)

    def leaveEvent(self, ev):
        self.unsetCursor()
        super().leaveEvent(ev)


class _HandOnCheckBoxes(QObject):
    """For lists whose rows have a check box: pointing hand only over the box itself."""

    def __init__(self, lst):
        super().__init__(lst)
        self.lst = lst
        lst.setMouseTracking(True)
        vp = lst.viewport()
        vp.setMouseTracking(True)
        vp.setCursor(Qt.CursorShape.ArrowCursor)
        vp.installEventFilter(self)

    def eventFilter(self, obj, ev):
        t = ev.type()
        if t == QEvent.Type.MouseMove:
            pt = ev.position().toPoint()
            it = self.lst.itemAt(pt)
            hand = False
            if it is not None and (it.flags() & Qt.ItemFlag.ItemIsUserCheckable):
                hand = pt.x() - self.lst.visualItemRect(it).left() <= 40       # the box sits at the left end
            obj.setCursor(Qt.CursorShape.PointingHandCursor if hand else Qt.CursorShape.ArrowCursor)
        elif t == QEvent.Type.Leave:
            obj.setCursor(Qt.CursorShape.ArrowCursor)
        return False


class ElideLabel(QLabel):
    """One-line label that never changes size: text that does not fit is cut and ends with '...'."""
    _full = ""

    def __init__(self, text="", parent=None):
        super().__init__(parent)
        self._full = text or ""
        self.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.setMinimumWidth(10)
        self._apply()

    def setText(self, t):
        self._full = t or ""
        self._apply()

    def fullText(self):
        return self._full

    def _apply(self):
        w = self.width() - 2 if self.width() > 20 else 4000
        el = self.fontMetrics().elidedText(self._full, Qt.TextElideMode.ElideRight, max(10, w))
        if el != QLabel.text(self):
            QLabel.setText(self, el)
        self.setToolTip(self._full if el != self._full else "")

    def resizeEvent(self, ev):
        super().resizeEvent(ev)
        self._apply()

    def changeEvent(self, ev):
        super().changeEvent(ev)
        if ev.type() in (QEvent.Type.FontChange, QEvent.Type.StyleChange):
            self._apply()

    def sizeHint(self):
        return QSize(10, super().sizeHint().height())

    def minimumSizeHint(self):
        return QSize(10, super().minimumSizeHint().height())


class ClickFrame(QFrame):
    """QFrame that emits `clicked` on a left mouse click."""
    clicked = Signal()

    def mousePressEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton:
            self.clicked.emit()
        ev.accept()


class PlaylistPicker(QFrame):
    """Small popup under the playlist button: pick another playlist to switch to it."""
    chosen = Signal(str)

    def __init__(self, items, current, parent=None):
        super().__init__(parent, Qt.WindowType.Popup | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        outer = QVBoxLayout(self)
        outer.setContentsMargins(6, 6, 6, 6)
        box = QFrame(objectName="popup")
        outer.addWidget(box)
        lay = QVBoxLayout(box)
        lay.setContentsMargins(10, 10, 10, 10)
        lay.setSpacing(6)
        lay.addWidget(QLabel("Your playlists", objectName="hint"))
        if not items:
            e = QLabel("No playlists yet.\nCreate one from the library.", objectName="hint")
            e.setStyleSheet("padding: 14px;")
            lay.addWidget(e)
            self.setFixedWidth(300)
            return
        lst = QListWidget(objectName="plist")
        lst.setIconSize(QSize(44, 44))
        lst.setSpacing(2)
        lst.setWordWrap(False)
        lst.setTextElideMode(Qt.TextElideMode.ElideRight)
        lst.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        lst.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        hand_on_items(lst)
        for pid, name, sub, icon in items:
            it = QListWidgetItem(icon, f"{name}\n{sub}")
            it.setData(Qt.ItemDataRole.UserRole, pid)
            lst.addItem(it)
            if pid == current:
                lst.setCurrentItem(it)
        lst.itemClicked.connect(lambda it: (self.chosen.emit(it.data(Qt.ItemDataRole.UserRole)), self.close()))
        lay.addWidget(lst)
        self.setFixedWidth(320)
        lst.setFixedHeight(min(360, 62 * len(items) + 8))


class QueueDelegate(QStyledItemDelegate):
    """Normal row + a small x at its right end (removes the song from the queue)."""

    def paint(self, painter, opt, idx):
        if idx.data(Qt.ItemDataRole.UserRole) == "spacer":
            return
        super().paint(painter, opt, idx)
        lst = self.parent()
        r = lst.x_rect(opt.rect)
        hot = lst._hover_x == idx.row()
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        if hot:
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QColor(T["line_hi"]))
            painter.drawEllipse(r)
        painter.setPen(QPen(QColor(T["text"] if hot else T["dim"]), 1.8, Qt.PenStyle.SolidLine,
                            Qt.PenCapStyle.RoundCap))
        c, d = QRectF(r).center(), 5.0
        painter.drawLine(QPointF(c.x() - d, c.y() - d), QPointF(c.x() + d, c.y() + d))
        painter.drawLine(QPointF(c.x() - d, c.y() + d), QPointF(c.x() + d, c.y() - d))
        painter.restore()


class QueueList(QListWidget):
    """The queue: a click on a song plays it, the x at the end of the row removes it."""
    playRequested = Signal(int)
    removeRequested = Signal(int)
    orderChanged = Signal()                              # the user dropped a song somewhere else
    X = 26

    def __init__(self):
        super().__init__(objectName="queue")
        self._hover_x = -1
        self._swallow_release = False
        self.setMouseTracking(True)
        self.setSelectionMode(QListWidget.SelectionMode.SingleSelection)
        self.setItemDelegate(QueueDelegate(self))
        self.setDragEnabled(True)                        # drag a song up / down to decide what plays next
        self.setAcceptDrops(True)
        self.viewport().setAcceptDrops(True)
        self.setDragDropMode(QListWidget.DragDropMode.InternalMove)
        self.setDefaultDropAction(Qt.DropAction.MoveAction)
        self.setDropIndicatorShown(True)
        self.setAutoScroll(True)

    def dropEvent(self, ev):
        super().dropEvent(ev)
        self._hover_x = -1
        QTimer.singleShot(0, self.orderChanged.emit)     # let Qt finish the move before we read the new order

    def x_rect(self, rect):
        return QRect(rect.right() - self.X - 10, rect.center().y() - self.X // 2, self.X, self.X)

    def _hit(self, pos):
        it = self.itemAt(pos)
        if it is None or it.data(Qt.ItemDataRole.UserRole) == "spacer":
            return -1, False
        return self.row(it), self.x_rect(self.visualItemRect(it)).adjusted(-4, -4, 4, 4).contains(pos)

    def _set_hover(self, row):
        if row != self._hover_x:
            self._hover_x = row
            self.viewport().update()

    def mouseMoveEvent(self, ev):
        row, on_x = self._hit(ev.position().toPoint())
        self._set_hover(row if on_x else -1)
        super().mouseMoveEvent(ev)

    def viewportEvent(self, ev):
        if ev.type() == QEvent.Type.Leave:
            self._set_hover(-1)
        return super().viewportEvent(ev)

    def mouseDoubleClickEvent(self, ev):
        # The 2nd press of a quick double-click: never plays anything (the list has already shifted
        # after the 1st click); on the x it simply removes the next song, like a fast second click.
        if ev.button() == Qt.MouseButton.LeftButton:
            row, on_x = self._hit(ev.position().toPoint())
            self._swallow_release = True
            if row >= 0 and on_x:
                self.removeRequested.emit(row)
            ev.accept()
            return
        super().mouseDoubleClickEvent(ev)

    def mouseReleaseEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton:
            if self._swallow_release:
                self._swallow_release = False
            else:
                row, on_x = self._hit(ev.position().toPoint())
                if row >= 0:
                    (self.removeRequested if on_x else self.playRequested).emit(row)
            ev.accept()
            return
        super().mouseReleaseEvent(ev)


class QueuePickerDialog(QDialog):
    """Pick songs from the music library (inside the app) to add to the queue."""

    def __init__(self, tracks, queued, icon_for, parent=None, video=False):
        super().__init__(parent)
        self.setWindowTitle("Add to queue")
        self.setMinimumSize(520, 600)
        self._order = []                                 # songs in the order they were picked
        lay = QVBoxLayout(self)
        lay.setContentsMargins(22, 20, 22, 18)
        lay.setSpacing(10)
        h = QLabel("Add to queue")
        h.setStyleSheet("font-size: 20px; font-weight: 800;")
        lay.addWidget(h)
        self.search = QLineEdit()
        self.search.setPlaceholderText("Search your videos…" if video else "Search your music…")
        self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(self._filter)
        lay.addWidget(self.search)
        lay.addWidget(QLabel(f"Click {'videos' if video else 'songs'} to select them  ·  pick as many as you like", objectName="hint"))
        self.list = QListWidget()
        self.list.setSelectionMode(QListWidget.SelectionMode.MultiSelection)
        self.list.setIconSize(QSize(82, 46) if video else QSize(46, 46))
        self.list.setSpacing(2)
        self.list.setUniformItemSizes(True)
        self.list.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.list.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.list.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        hand_on_items(self.list)
        self.list.setVerticalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
        SmoothScroller(self.list)
        for path in tracks:
            sub = os.path.basename(os.path.dirname(path))
            if path in queued:
                sub += "   ·   already in queue"
            it = QListWidgetItem(icon_for(path), f"{pretty_title(path)}\n{sub}")
            it.setData(Qt.ItemDataRole.UserRole, path)
            it.setToolTip(path)
            if path in queued:
                it.setFlags(Qt.ItemFlag.NoItemFlags)
            self.list.addItem(it)
        self.list.itemSelectionChanged.connect(self._sel_changed)
        lay.addWidget(self.list, 1)
        self.empty = QLabel("No videos found yet\nAdd your video folder in Settings" if video
                            else "No music found yet\nAdd your music folder in Settings", objectName="hint")
        self.empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.empty.setStyleSheet("font-size: 14px; padding: 30px;")
        lay.addWidget(self.empty, 1)
        self.list.setVisible(bool(tracks))
        self.empty.setVisible(not tracks)
        row = QHBoxLayout()
        self.count = QLabel("", objectName="hint")
        row.addWidget(self.count)
        row.addStretch(1)
        cancel = QPushButton("Cancel", objectName="flat")
        self.ok = QPushButton("Add", objectName="open")
        self.ok.setEnabled(False)
        for b in (cancel, self.ok):
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        cancel.clicked.connect(self.reject)
        self.ok.clicked.connect(self.accept)
        row.addWidget(cancel)
        row.addWidget(self.ok)
        lay.addLayout(row)

    def _filter(self, text):
        t = text.strip().lower()
        for i in range(self.list.count()):
            it = self.list.item(i)
            it.setHidden(bool(t) and t not in it.text().lower())

    def _sel_changed(self):
        cur = {it.data(Qt.ItemDataRole.UserRole) for it in self.list.selectedItems()}
        self._order = [p for p in self._order if p in cur]
        for i in range(self.list.count()):
            path = self.list.item(i).data(Qt.ItemDataRole.UserRole)
            if path in cur and path not in self._order:
                self._order.append(path)
        n = len(self._order)
        self.count.setText(f"{n} selected" if n else "")
        self.ok.setText(f"Add {n}" if n else "Add")
        self.ok.setEnabled(n > 0)

    def paths(self):
        return list(self._order)


# ----------------------------------------------------------------------------
# Custom title bar: the window frame is drawn by the app and follows the theme
# ----------------------------------------------------------------------------
TITLEBAR_H = 40
_BAR_STYLER = None


def make_app_pixmap(size=256):
    """The app icon (taskbar + title bar): a V on a rounded square. It follows the theme - square = theme
    background, V = theme accent - so Super Dark gives the white V on black of veyro_simple.ico."""
    pm = QPixmap(size, size)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    p.scale(size / 100, size / 100)
    p.setPen(Qt.PenStyle.NoPen)
    p.setBrush(QColor(T["bg"]))
    p.drawRoundedRect(QRectF(0, 0, 100, 100), 22, 22)
    # the V: every corner is rounded with a small curve (corner point, how far the curve starts from it)
    pts = ((20.5, 26.5, 3.4), (39.5, 26.5, 3.6), (50, 52, 5.2), (60.5, 26.5, 3.6), (79.5, 26.5, 3.4), (50, 78, 4.2))
    path = QPainterPath()
    n = len(pts)
    for i, (x, y, d) in enumerate(pts):
        px, py, _ = pts[i - 1]
        nx, ny, _ = pts[(i + 1) % n]
        lp = math.hypot(px - x, py - y)
        ln = math.hypot(nx - x, ny - y)
        a = QPointF(x + (px - x) / lp * d, y + (py - y) / lp * d)
        b = QPointF(x + (nx - x) / ln * d, y + (ny - y) / ln * d)
        if i == 0:
            path.moveTo(a)
        else:
            path.lineTo(a)
        path.quadTo(QPointF(x, y), b)
    path.closeSubpath()
    p.setBrush(QColor(T["accent"]))
    p.drawPath(path)
    p.end()
    return pm


def _colorref(c):
    """QColor -> Windows COLORREF integer (0x00BBGGRR)."""
    c = QColor(c)
    return c.red() | (c.green() << 8) | (c.blue() << 16)


def _dwm_set(widget, attr, value):
    v = ctypes.c_int(int(value))
    ctypes.windll.dwmapi.DwmSetWindowAttribute(ctypes.c_void_p(int(widget.winId())), ctypes.c_uint(attr),
                                               ctypes.byref(v), ctypes.c_uint(ctypes.sizeof(v)))


def style_native_titlebar(w):
    """Windows: tint the system title bar of a dialog with the theme colours (the main window has its own bar)."""
    if sys.platform != "win32":
        return
    for attr, val in ((20, 1 if T["dark"] else 0),        # dark / light caption buttons
                      (35, _colorref(T["panel"])),         # caption colour   (Windows 11)
                      (36, _colorref(T["text"])),          # caption text     (Windows 11)
                      (34, _colorref(T["line"]))):         # window border    (Windows 11)
        try:
            _dwm_set(w, attr, val)
        except Exception:
            pass


def style_main_window(w):
    """Windows 11: rounded corners and a theme coloured border for the frameless main window."""
    if sys.platform != "win32":
        return
    for attr, val in ((33, 2), (34, _colorref(T["line"]))):
        try:
            _dwm_set(w, attr, val)
        except Exception:
            pass


_WS_CAPTION, _WS_THICKFRAME, _WS_SYSMENU = 0x00C00000, 0x00040000, 0x00080000
_WS_MINBOX, _WS_MAXBOX = 0x00020000, 0x00010000
_NATIVE_FRAME_BITS = _WS_CAPTION | _WS_THICKFRAME | _WS_SYSMENU | _WS_MINBOX | _WS_MAXBOX


def enable_native_window_behavior(w):
    """Windows: give the frameless window the real window styles (caption / resizable frame / system menu /
    min + max boxes). The title bar is still drawn by the app and WM_NCCALCSIZE (see Player.nativeEvent) hides the
    system frame, so the look does not change - but Windows now treats it like any other window: open / minimize /
    restore / maximize animations, Snap (drag to the edges / top), Snap layouts, Win+arrows, the system menu
    (right-click on the title bar, Alt+Space) and the taskbar thumbnail menu."""
    if sys.platform != "win32":
        return
    try:
        user32 = ctypes.WinDLL("user32", use_last_error=True)        # private copy: our argtypes stay ours
        hwnd = wintypes.HWND(int(w.winId()))
        get = getattr(user32, "GetWindowLongPtrW", None) or user32.GetWindowLongW
        put = getattr(user32, "SetWindowLongPtrW", None) or user32.SetWindowLongW
        get.restype, get.argtypes = ctypes.c_ssize_t, [wintypes.HWND, ctypes.c_int]
        put.restype, put.argtypes = ctypes.c_ssize_t, [wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t]
        style = get(hwnd, -16)                                       # GWL_STYLE
        if (style & _NATIVE_FRAME_BITS) == _NATIVE_FRAME_BITS:
            return
        put(hwnd, -16, style | _NATIVE_FRAME_BITS)
        user32.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int, ctypes.c_int,
                                        ctypes.c_int, wintypes.UINT]
        # NOMOVE | NOSIZE | NOZORDER | NOACTIVATE | FRAMECHANGED
        user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, 0x0001 | 0x0002 | 0x0004 | 0x0010 | 0x0020)
        if sys.getwindowsversion().build < 22000:                    # Windows 10: bring back the soft shadow
            class MARGINS(ctypes.Structure):
                _fields_ = [("l", ctypes.c_int), ("r", ctypes.c_int), ("t", ctypes.c_int), ("b", ctypes.c_int)]
            m = MARGINS(1, 1, 1, 1)
            ctypes.windll.dwmapi.DwmExtendFrameIntoClientArea(hwnd, ctypes.byref(m))
    except Exception:
        pass


def win_nc_calcsize(w, hwnd_value, wparam, lparam):
    """WM_NCCALCSIZE: the client area is the whole window (no system frame is painted). A maximized resizable
    window overhangs the screen by the frame width, so that overhang is cut off here."""
    user32 = ctypes.windll.user32
    hwnd = ctypes.c_void_p(int(hwnd_value or 0))      # from the message: winId() here would re-enter window creation
    if not wparam or w.isFullScreen() or not user32.IsZoomed(hwnd):
        return
    try:
        dpi = user32.GetDpiForWindow(hwnd) or 96
    except Exception:
        dpi = 96

    def metric(i):
        try:
            return user32.GetSystemMetricsForDpi(i, dpi)
        except Exception:
            return user32.GetSystemMetrics(i)

    class NCCALCSIZE_PARAMS(ctypes.Structure):
        _fields_ = [("rgrc", wintypes.RECT * 3), ("lppos", ctypes.c_void_p)]

    fx, fy = metric(32) + metric(92), metric(33) + metric(92)       # SM_CXFRAME/CYFRAME + SM_CXPADDEDBORDER
    r = NCCALCSIZE_PARAMS.from_address(lparam).rgrc[0]
    r.left += fx
    r.right -= fx
    r.top += fy
    r.bottom -= fy


def bring_to_front(w):
    """Windows only lets the active program take the foreground, so a plain activateWindow() leaves the player
    behind Explorer. This restores the window if it is minimized and forces it above the other windows."""
    if sys.platform != "win32":
        return
    try:
        user32 = ctypes.WinDLL("user32", use_last_error=True)
        kernel32 = ctypes.WinDLL("kernel32")
        user32.SetWindowPos.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_int,
                                        ctypes.c_int, ctypes.c_int, ctypes.c_uint]
        user32.GetWindowThreadProcessId.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        hwnd = ctypes.c_void_p(int(w.winId()))
        if user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, 9)                                   # SW_RESTORE (keeps a maximized window maximized)
        fg = user32.GetForegroundWindow()
        cur = kernel32.GetCurrentThreadId()
        fg_thread = user32.GetWindowThreadProcessId(ctypes.c_void_p(fg), None) if fg else 0
        attached = bool(fg_thread and fg_thread != cur and user32.AttachThreadInput(fg_thread, cur, True))
        for after in (-1, -2):                                           # HWND_TOPMOST, then back to HWND_NOTOPMOST
            user32.SetWindowPos(hwnd, ctypes.c_void_p(after), 0, 0, 0, 0, 0x0001 | 0x0002)
        user32.BringWindowToTop(hwnd)
        user32.SetForegroundWindow(hwnd)
        if attached:
            user32.AttachThreadInput(fg_thread, cur, False)
    except Exception:
        pass


class _NativeBarStyler(QObject):
    """Dialogs (Convert, Download, message boxes ...) keep the system title bar - it is painted in the theme colours."""

    @staticmethod
    def eligible(w):
        if not (isinstance(w, QWidget) and w.isWindow()):
            return False
        fl = w.windowFlags()
        return bool(fl & Qt.WindowType.WindowTitleHint) and not (fl & Qt.WindowType.FramelessWindowHint)

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.Type.Show and self.eligible(obj):
            style_native_titlebar(obj)
        return False

    def refresh(self):
        for w in QApplication.topLevelWidgets():
            if w.isVisible() and self.eligible(w):
                style_native_titlebar(w)


class CaptionButton(QAbstractButton):
    """Minimize / maximize / restore / close button of the title bar, drawn in the theme's colours."""

    def __init__(self, kind, parent=None):
        super().__init__(parent)
        self.kind = kind
        self.nc_hot = self.nc_down = False          # set by Player.nativeEvent while Windows owns the mouse (Snap layouts)
        self.setFixedSize(46, TITLEBAR_H)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)
        self.set_kind(kind)

    def set_kind(self, kind):
        self.kind = kind
        self.setToolTip({"min": "Minimize", "max": "Maximize", "restore": "Restore", "close": "Close"}[kind])
        self.update()

    def paintEvent(self, _e):
        p = QPainter(self)
        hot, down = self.underMouse() or self.nc_hot, self.isDown() or self.nc_down
        if self.kind == "close" and hot:
            p.fillRect(self.rect(), QColor("#c42b1c" if down else "#e81123"))
            fg = QColor("#ffffff")
        elif hot:
            p.fillRect(self.rect(), QColor(T["press"] if down else T["hover"]))
            fg = QColor(T["text"])
        else:
            fg = QColor(T["text2"])
        cx, cy = self.width() // 2, self.height() // 2
        p.setPen(QPen(fg, 1))
        p.setBrush(Qt.BrushStyle.NoBrush)
        k = self.kind
        if k == "min":
            p.drawLine(cx - 5, cy, cx + 5, cy)
        elif k == "max":
            p.drawRect(cx - 5, cy - 5, 9, 9)
        elif k == "restore":
            p.drawRect(cx - 5, cy - 2, 8, 8)
            p.drawPolyline(QPolygonF([QPointF(cx - 2, cy - 2), QPointF(cx - 2, cy - 5), QPointF(cx + 5, cy - 5),
                                      QPointF(cx + 5, cy + 2), QPointF(cx + 3, cy + 2)]))
        else:
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            p.setPen(QPen(fg, 1.2))
            p.drawLine(QPointF(cx - 5, cy - 5), QPointF(cx + 5, cy + 5))
            p.drawLine(QPointF(cx + 5, cy - 5), QPointF(cx - 5, cy + 5))
        p.end()


class TitleBar(QFrame):
    """The top bar of the window: app icon + name on the left, minimize / maximize / close on the right.
    On Windows the Player answers WM_NCHITTEST, so dragging, double-click and snapping are done by the system;
    the mouse handlers below are the fallback for other systems."""

    def __init__(self, win):
        super().__init__(win)
        self.setObjectName("titlebar")
        self.win = win
        self.setFixedHeight(TITLEBAR_H)
        lay = QHBoxLayout(self)
        lay.setContentsMargins(14, 0, 0, 0)
        lay.setSpacing(0)
        self.icon = QLabel()
        self.icon.setFixedSize(28, 28)
        self.icon.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.label = QLabel(APP_TITLE, objectName="apptitle")
        self.label.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        lay.addWidget(self.icon)
        lay.addSpacing(8)
        lay.addWidget(self.label)
        lay.addStretch(1)
        self.b_min = CaptionButton("min")
        self.b_max = CaptionButton("max")
        self.b_close = CaptionButton("close")
        for b in (self.b_min, self.b_max, self.b_close):
            lay.addWidget(b)
        self.b_min.clicked.connect(win.showMinimized)
        self.b_max.clicked.connect(win.toggle_maximize)
        self.b_close.clicked.connect(win.close)
        self.refresh()

    def refresh(self):
        pm = make_app_pixmap(112).scaled(56, 56, Qt.AspectRatioMode.KeepAspectRatio,
                                         Qt.TransformationMode.SmoothTransformation)
        pm.setDevicePixelRatio(2.0)
        self.icon.setPixmap(pm)
        for b in (self.b_min, self.b_max, self.b_close):
            b.update()

    def sync_state(self):
        self.b_max.set_kind("restore" if self.win.isMaximized() else "max")

    def mousePressEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton and not self.win.isMaximized():
            h = self.win.windowHandle()
            if h is not None:
                h.startSystemMove()
        ev.accept()

    def mouseDoubleClickEvent(self, ev):
        if ev.button() == Qt.MouseButton.LeftButton:
            self.win.toggle_maximize()
        ev.accept()


# ----------------------------------------------------------------------------
# File info: ffmpeg reads codec, resolution, bitrate, tags ...
# ----------------------------------------------------------------------------
def probe_media(ffmpeg, path):
    """Technical details of one file, read from the text `ffmpeg -i` prints."""
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
    r = subprocess.run([ffmpeg, "-hide_banner", "-i", path], capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=25, creationflags=flags)
    txt = r.stderr or ""
    info = {"tags": {}}
    m = re.search(r"Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)", txt)
    if m:
        info["duration"] = int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    m = re.search(r"Duration:[^\n]*?bitrate:\s*(\d+)\s*kb/s", txt)
    if m:
        info["bitrate"] = int(m.group(1))
    head = txt.split("Duration:")[0]                       # the file's own tags come before the first stream
    for k, v in re.findall(r"^\s{4}([\w ]+?)\s*:\s*(.+?)\s*$", head, re.M):
        info["tags"].setdefault(k.strip().lower(), v)

    def codec_of(s, key):
        m = re.search(key + r":\s*([\w\-]+)(?:\s*\(([^)]*)\))?", s)
        if not m:
            return ""
        prof = m.group(2)
        return m.group(1) + (f" ({prof})" if prof and "0x" not in prof else "")

    for line in txt.splitlines():
        s = line.strip()
        if not s.startswith("Stream #"):
            continue
        if "Video:" in s:
            if "attached pic" in s or "video" in info:     # cover art inside an mp3 is not a video
                continue
            v = {"codec": codec_of(s, "Video")}
            m = re.search(r"\b(\d{2,5})x(\d{2,5})\b", s)
            if m:
                v["size"] = (int(m.group(1)), int(m.group(2)))
            m = re.search(r"([\d.]+)\s*fps", s)
            if m:
                try:
                    v["fps"] = float(m.group(1))
                except ValueError:
                    pass
            m = re.search(r"(\d+)\s*kb/s", s)
            if m:
                v["kbps"] = int(m.group(1))
            info["video"] = v
        elif "Audio:" in s and "audio" not in info:
            a = {"codec": codec_of(s, "Audio")}
            m = re.search(r"(\d+)\s*Hz", s)
            if m:
                a["hz"] = int(m.group(1))
            m = re.search(r"Hz,\s*([^,]+)", s)
            if m:
                a["channels"] = m.group(1).strip()
            m = re.search(r"(\d+)\s*kb/s", s)
            if m:
                a["kbps"] = int(m.group(1))
            info["audio"] = a
    return info


class ProbeThread(QThread):
    """Reads the details (and a preview picture) of one file without freezing the window."""
    done = Signal(object)

    def __init__(self, ffmpeg, path, parent=None):
        super().__init__(parent)
        self.ffmpeg, self.path = ffmpeg, path

    def run(self):
        try:
            info = probe_media(self.ffmpeg, self.path)
        except Exception:
            info = {}
        try:
            st = os.stat(self.path)
            thumb, _dur = LibraryThread(0, [], self.ffmpeg, None, audio=is_audio(self.path))._thumb(
                self.path, st.st_size, st.st_mtime)
            if thumb:
                info["thumb"] = thumb
        except Exception:
            pass
        self.done.emit(info)


class MediaInfoDialog(QDialog):
    """Information about the file that is playing: name, size, length, resolution, codecs, tags ..."""

    def __init__(self, entry, local, qmeta, duration_ms, cover, parent=None):
        super().__init__(parent)
        self.setWindowTitle("File info")
        self.entry, self.local, self.q = entry, local, dict(qmeta or {})
        self.duration_ms, self.cover_path = int(duration_ms or 0), cover or ""
        self.probe, self.state = {}, ""
        self.link = bool(entry["url"])
        self.audio = (not self.link) and is_audio(entry["src"])
        scr = QApplication.primaryScreen().availableGeometry()
        self.setMinimumSize(480, 460)
        self.resize(min(600, scr.width() - 80), min(720, scr.height() - 80))

        outer = QVBoxLayout(self)
        outer.setContentsMargins(24, 22, 24, 18)
        outer.setSpacing(12)
        head = QHBoxLayout()
        head.setSpacing(16)
        self.pic = QLabel()
        head.addWidget(self.pic, 0, Qt.AlignmentFlag.AlignTop)
        col = QVBoxLayout()
        col.setSpacing(4)
        self.h_title = QLabel("")
        self.h_title.setWordWrap(True)
        self.h_title.setStyleSheet("font-size: 19px; font-weight: 800;")
        self.h_sub = QLabel("", objectName="hint")
        self.h_sub.setWordWrap(True)
        self.note = QLabel("", objectName="hint")
        self.note.setWordWrap(True)
        col.addWidget(self.h_title)
        col.addWidget(self.h_sub)
        col.addWidget(self.note)
        col.addStretch(1)
        head.addLayout(col, 1)
        outer.addLayout(head)

        scroll = QScrollArea(objectName="libscroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.viewport().setAutoFillBackground(False)
        content = QWidget(objectName="libcontent")
        self.body = QVBoxLayout(content)
        self.body.setContentsMargins(0, 0, 8, 0)
        self.body.setSpacing(12)
        scroll.setWidget(content)
        outer.addWidget(scroll, 1)

        brow = QHBoxLayout()
        if self.local:
            show = QPushButton("Show in folder", objectName="flat")
            show.setCursor(Qt.CursorShape.PointingHandCursor)
            show.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            show.clicked.connect(lambda _=False: QDesktopServices.openUrl(
                QUrl.fromLocalFile(os.path.dirname(self.local))))
            brow.addWidget(show)
        brow.addStretch(1)
        close = QPushButton("Close", objectName="open")
        close.setCursor(Qt.CursorShape.PointingHandCursor)
        close.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        close.clicked.connect(self.accept)
        brow.addWidget(close)
        outer.addLayout(brow)
        self._render()

    # ---- state shown under the title
    def set_state(self, state):
        self.state = state
        self._note()

    def _note(self):
        self.note.setText({"loading": "Reading more details…",
                           "noffmpeg": "Install ffmpeg  (pip install imageio-ffmpeg)  to also see codecs and bitrate."
                           }.get(self.state, ""))

    def set_probe(self, info):
        self.probe = info or {}
        self.state = ""
        self._note()
        self._render()

    # ---- building the page
    def _clear(self):
        while self.body.count():
            it = self.body.takeAt(0)
            w = it.widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()

    def _rows(self, cl, rows):
        grid = QGridLayout()
        grid.setHorizontalSpacing(16)
        grid.setVerticalSpacing(8)
        for i, (k, v) in enumerate(rows):
            a = QLabel(k, objectName="hint")
            a.setMinimumWidth(104)
            text = str(v)
            if k == "Location":                                 # let long paths break after a slash
                text = text.replace("\\", "\\\u200b").replace("/", "/\u200b")
            b = QLabel(text)
            b.setWordWrap(True)
            b.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
            grid.addWidget(a, i, 0, Qt.AlignmentFlag.AlignTop)
            grid.addWidget(b, i, 1)
        grid.setColumnStretch(1, 1)
        cl.addLayout(grid)

    def _render(self):
        e, q, pr = self.entry, self.q, self.probe
        path = e["src"]
        title = e["title"] if self.link else pretty_title(path)
        ext = os.path.splitext(path.split("?")[0])[1][1:].upper()
        kind = "Link" if self.link else ("Audio" if self.audio else "Video")
        st = None
        if self.local:
            try:
                st = os.stat(self.local)
            except OSError:
                st = None

        # header
        self.h_title.setText(title)
        self.h_sub.setText("  ·  ".join(x for x in (ext, kind, human_size(st.st_size) if st else "") if x))
        cov = self.cover_path or pr.get("thumb") or ""
        if self.audio:
            self.pic.setPixmap(make_cover(cov or None, 112, 16))
        else:
            self.pic.setPixmap(make_thumb(cov or None, 0, 200, 112, 14))

        secs = []
        # general
        gen = [("Name", title if self.link else os.path.basename(path)),
               ("Type", kind + (f"  ·  {ext}" if ext else ""))]
        if st:
            gen.append(("Size", f"{human_size(st.st_size)}   ({st.st_size:,} bytes)"))
        dur = self.duration_ms or int(pr.get("duration", 0) * 1000)
        if dur > 0:
            gen.append(("Duration", fmt_time(dur)))
        if pr.get("bitrate"):
            gen.append(("Bitrate", f"{pr['bitrate']} kbps"))
        if st:
            gen.append(("Modified", time.strftime("%Y-%m-%d   %H:%M", time.localtime(st.st_mtime))))
        gen.append(("Location", os.path.dirname(path) if self.local else path))
        secs.append(("General", gen))

        # video
        if not self.audio:
            v = {}
            if q.get("size"):
                v["size"] = q["size"]
            if q.get("fps"):
                v["fps"] = q["fps"]
            if q.get("vcodec"):
                v["codec"] = q["vcodec"]
            v.update({k: x for k, x in pr.get("video", {}).items() if x})
            rows = []
            if v.get("size"):
                w, h = v["size"]
                res = f"{w} × {h}"
                if min(w, h) >= 130:
                    res += f"   ·   {quality_tier({'width': w, 'height': h})}p"
                rows.append(("Resolution", res))
            if v.get("fps"):
                rows.append(("Frame rate", f"{v['fps']:g} fps"))
            if v.get("codec"):
                rows.append(("Video codec", v["codec"]))
            if v.get("kbps"):
                rows.append(("Video bitrate", f"{v['kbps']} kbps"))
            if rows:
                secs.append(("Video", rows))

        # audio
        a = {}
        if q.get("acodec"):
            a["codec"] = q["acodec"]
        a.update({k: x for k, x in pr.get("audio", {}).items() if x})
        rows = []
        if a.get("codec"):
            rows.append(("Audio codec", a["codec"]))
        if a.get("hz"):
            rows.append(("Sample rate", f"{a['hz'] / 1000:g} kHz"))
        if a.get("channels"):
            rows.append(("Channels", a["channels"].capitalize()))
        if a.get("kbps"):
            rows.append(("Audio bitrate", f"{a['kbps']} kbps"))
        if rows:
            secs.append(("Audio", rows))

        # tags
        tags = dict(pr.get("tags", {}))
        for k in ("title", "artist", "album", "genre"):
            if q.get(k) and k not in tags:
                tags[k] = q[k]
        rows = [(label, tags[key]) for key, label in (("title", "Title"), ("artist", "Artist"),
                                                      ("album_artist", "Album artist"), ("album", "Album"),
                                                      ("genre", "Genre")) if tags.get(key)]
        year = tags.get("date") or tags.get("year")
        if year:
            rows.append(("Year", year[:4] if re.match(r"\d{4}", year) else year))
        if tags.get("track"):
            rows.append(("Track", tags["track"]))
        if rows:
            secs.append(("Tags", rows))

        self._clear()
        for name, rws in secs:
            card, cl, _h = section_card(name)
            self._rows(cl, rws)
            self.body.addWidget(card)
        self.body.addStretch(1)


# ----------------------------------------------------------------------------
# Main window
# ----------------------------------------------------------------------------
class ModeSwitch(QWidget):
    """Vertical pill that switches between the Video and the Music library.
    The accent 'thumb' slides between the two icons."""
    changed = Signal(str)
    KEYS = ("video", "audio")
    TIPS = ("Videos  (V)", "Music  (A)")

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedSize(48, 104)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._key = "video"
        self._pos = 0.0
        self._anim = QVariantAnimation(self)
        self._anim.setDuration(260)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._anim.valueChanged.connect(self._on_anim)

    def _on_anim(self, v):
        self._pos = float(v)
        self.update()

    def set_mode(self, key, animate=True):
        if key not in self.KEYS:
            return
        self._key = key
        target = float(self.KEYS.index(key))
        self._anim.stop()
        if animate and self.isVisible():
            self._anim.setStartValue(self._pos)
            self._anim.setEndValue(target)
            self._anim.start()
        else:
            self._pos = target
        self.update()

    def mousePressEvent(self, ev):
        if ev.button() != Qt.MouseButton.LeftButton:
            return
        key = self.KEYS[0 if ev.position().y() < self.height() / 2 else 1]
        if key != self._key:
            self.set_mode(key)
            self.changed.emit(key)

    def event(self, ev):
        if ev.type() == QEvent.Type.ToolTip:
            i = 0 if ev.pos().y() < self.height() / 2 else 1
            QToolTip.showText(ev.globalPos(), self.TIPS[i], self)
            return True
        return super().event(ev)

    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        w, h = self.width(), self.height()
        p.setPen(QPen(QColor(T["line"]), 1))
        p.setBrush(QColor(T["card"]))
        p.drawRoundedRect(QRectF(0.5, 0.5, w - 1, h - 1), w / 2, w / 2)
        seg = (h - 8) / 2
        thumb = QRectF(4, 4 + self._pos * seg, w - 8, seg)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(ACCENT))
        p.drawRoundedRect(thumb, (w - 8) / 2, (w - 8) / 2)
        for i, name in enumerate(("video", "music")):
            active = max(0.0, 1.0 - abs(self._pos - i))
            col = _mix(T["dim"], T["on_accent"], active)
            pm = make_icon(name, col, 96).pixmap(24, 24)
            cy = 4 + seg * (i + 0.5)
            p.drawPixmap(int(w / 2 - 12), int(cy - 12), pm)
        p.end()


class Veil(QWidget):
    """A snapshot of the old screen that fades away on top of the new one -> smooth page / mode changes."""

    def __init__(self, parent):
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground)
        self._pm, self._op, self.busy = None, 0.0, False
        self._anim = QVariantAnimation(self)
        self._anim.valueChanged.connect(self._on_value)
        self._anim.finished.connect(self._done)
        self.hide()

    def prepare(self, pm, rect):
        """Cover `rect` with the snapshot (fully opaque) - call before changing what is underneath."""
        self._anim.stop()
        self._pm, self._op, self.busy = pm, 1.0, True
        self.setGeometry(rect)
        self.show()
        self.raise_()
        self.repaint()                               # paint the snapshot now, before the change below happens

    def go(self, ms=260):
        self._anim.setDuration(ms)
        self._anim.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._anim.setStartValue(1.0)
        self._anim.setEndValue(0.0)
        self._anim.start()

    def _on_value(self, v):
        self._op = float(v)
        self.update()

    def _done(self):
        self.hide()
        self._pm, self.busy = None, False

    def paintEvent(self, _ev):
        if self._pm is None:
            return
        p = QPainter(self)
        p.setOpacity(self._op)
        p.drawPixmap(0, 0, self._pm)
        p.end()


class ControlOverlay(QWidget):
    """Transparent, frameless window that floats over the bottom of the video, with fade in/out.
    (A separate window is used because the video surface is a native window that
    normal child widgets cannot be drawn on top of.)"""

    def __init__(self, owner):
        super().__init__(owner, Qt.WindowType.Tool | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowDoesNotAcceptFocus)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_ShowWithoutActivating)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.lay = QVBoxLayout(self)
        self.lay.setContentsMargins(0, 0, 0, 0)
        self.setWindowOpacity(0.0)
        self._target = False
        self.followers = []                          # other overlays that show / hide together with this one
        self.anim = QPropertyAnimation(self, b"windowOpacity", self)
        self.anim.finished.connect(self._done)

    def _fade(self, to, ms, curve):
        self.anim.stop()
        self.anim.setEasingCurve(curve)
        self.anim.setDuration(ms)
        self.anim.setStartValue(self.windowOpacity())
        self.anim.setEndValue(to)
        self.anim.start()

    def fade_in(self):
        for f in self.followers:
            f.fade_in()
        if self._target and self.isVisible():
            return
        self._target = True
        if not self.isVisible():
            self.setWindowOpacity(0.0)
            self.show()
        self._fade(1.0, 220, QEasingCurve.Type.OutCubic)

    def fade_out(self):
        for f in self.followers:
            f.fade_out()
        if not self._target:
            return
        self._target = False
        if self.isVisible():
            self._fade(0.0, 320, QEasingCurve.Type.InOutCubic)

    def hide_now(self):
        for f in self.followers:
            f.hide_now()
        self.anim.stop()
        self._target = False
        self.setWindowOpacity(0.0)
        self.hide()

    def is_shown(self):
        return self._target and self.isVisible()

    def _done(self):
        if not self._target:
            self.hide()


class DownloadDialog(QDialog):
    """'Download from the internet'. Layout: app icons on top, the video cover (left) and the download settings
    (right, only after the link was read), the link, then folder / play option and the Download / Cancel button.
    Not modal: the download keeps running if you close the window."""
    downloaded = Signal(object, bool)          # [file paths], play now
    folder_changed = Signal(str)

    HEIGHTS = (1080, 720, 480, 360)            # shown until the real list of the link is known
    COVER_W, COVER_H = 304, 171
    LEFT_W = 340

    def __init__(self, settings, folder, parent=None):
        super().__init__(parent)
        self.settings = settings
        self._folder = folder
        self.setWindowTitle("Download from the internet")
        self.setFixedWidth(700)
        self._threads = set()
        self._info_token = 0
        self._info_th = None
        self._dl = None
        self._busy = False
        self._ready = False                         # True once the link has been read successfully
        self._play_after = True
        self.kind = "video"
        self.platform = settings.value("dl_platform", "youtube", str)
        if self.platform not in PLATFORM_NAME:
            self.platform = "youtube"
        self._codec = settings.value("dl_codec", "mp3", str)
        self._codec = self._codec if self._codec in ("mp3", "m4a") else "mp3"
        self._kbps = settings.value("dl_kbps", 192, int)
        self._kbps = self._kbps if self._kbps in (320, 256, 192, 128) else 192
        self._height = self._saved_height()

        outer = QVBoxLayout(self)
        outer.setContentsMargins(22, 18, 22, 16)
        outer.setSpacing(10)

        # ---- 1. app select
        apps = QFrame(objectName="group")
        arow = QHBoxLayout(apps)
        arow.setContentsMargins(12, 10, 12, 10)
        arow.setSpacing(8)
        self.plat_btns = {}
        group = QButtonGroup(self)
        for key, name, _home, _tip in PLATFORMS:
            b = QToolButton(objectName="platbtn")
            b.setCheckable(True)
            b.setIconSize(QSize(34, 34))
            b.setText(name)
            b.setToolButtonStyle(Qt.ToolButtonStyle.ToolButtonTextUnderIcon)
            b.setToolTip(f"Download from {name}" if key != "other" else "Download from any other site")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            b.setFixedHeight(74)                     # same size for every app
            b.setMinimumWidth(90)
            group.addButton(b)
            b.clicked.connect(lambda _=False, k=key: self._on_platform_click(k))
            self.plat_btns[key] = b
            arow.addWidget(b, 1)
        outer.addWidget(apps)
        self._refresh_icons()

        # ---- 2. video cover (left) + settings (right)
        mid = QHBoxLayout()
        mid.setSpacing(10)
        cover = QFrame(objectName="group")
        cover.setFixedWidth(self.LEFT_W)
        cv = QVBoxLayout(cover)
        cv.setContentsMargins(14, 14, 14, 12)
        cv.setSpacing(8)
        self.thumb = QLabel()
        self.thumb.setFixedSize(self.COVER_W, self.COVER_H)
        cv.addWidget(self.thumb, 0, Qt.AlignmentFlag.AlignHCenter)
        self.p_title = QLabel("")
        self.p_title.setStyleSheet("font-size: 13px; font-weight: 600;")
        self.p_title.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.p_meta = QLabel("", objectName="hint")
        self.p_meta.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        cv.addWidget(self.p_title)
        cv.addWidget(self.p_meta)
        mid.addWidget(cover)

        sp = QFrame(objectName="group")
        sl = QVBoxLayout(sp)
        sl.setContentsMargins(14, 14, 14, 12)
        sl.setSpacing(0)
        self.set_hint = QLabel("Download settings appear\nonce the link has been read", objectName="hint")
        self.set_hint.setAlignment(Qt.AlignmentFlag.AlignCenter)
        sl.addWidget(self.set_hint, 1)
        self.set_box = QWidget()
        self.set_box.setStyleSheet("QPushButton#chip { padding: 6px 10px; }")
        bl = QVBoxLayout(self.set_box)
        bl.setContentsMargins(0, 0, 0, 0)
        bl.setSpacing(6)
        self.kind_row, self.kind_btns = self._chip_row([("Video", "video"), ("Audio", "audio")],
                                                       self.kind, self._set_kind)
        bl.addLayout(self.kind_row)
        self.video_box = QWidget()
        vl = QVBoxLayout(self.video_box)
        vl.setContentsMargins(0, 0, 0, 0)
        vl.setSpacing(6)
        vl.addWidget(QLabel("Quality", objectName="caption"))
        self.q_grid = QGridLayout()
        self.q_grid.setSpacing(8)
        vl.addLayout(self.q_grid)
        vl.addStretch(1)
        self.q_group = QButtonGroup(self)
        bl.addWidget(self.video_box)
        self.audio_box = QWidget()
        al = QVBoxLayout(self.audio_box)
        al.setContentsMargins(0, 0, 0, 0)
        al.setSpacing(6)
        al.addWidget(QLabel("Format", objectName="caption"))
        row, self.codec_btns = self._chip_row([("MP3", "mp3"), ("M4A", "m4a")], self._codec, self._set_codec)
        al.addLayout(row)
        al.addWidget(QLabel("Bitrate (kbps)", objectName="caption"))
        row, self.kbps_btns = self._chip_row([("320", 320), ("256", 256), ("192", 192), ("128", 128)],
                                             self._kbps, self._set_kbps)
        al.addLayout(row)
        al.addStretch(1)
        bl.addWidget(self.audio_box)
        bl.addStretch(1)
        sl.addWidget(self.set_box, 1)
        mid.addWidget(sp, 1)
        outer.addLayout(mid, 1)

        # ---- 3. link (+ status and progress)
        lp = QFrame(objectName="group")
        ll = QVBoxLayout(lp)
        ll.setContentsMargins(12, 10, 12, 10)
        ll.setSpacing(6)
        lrow = QHBoxLayout()
        self.url_edit = QLineEdit()
        self.url_edit.setClearButtonEnabled(True)
        self.url_edit.returnPressed.connect(self._fetch_info)
        self.url_edit.textChanged.connect(self._on_url_changed)
        lrow.addWidget(self.url_edit, 1)
        paste = QPushButton("Paste", objectName="flat")
        paste.setCursor(Qt.CursorShape.PointingHandCursor)
        paste.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        paste.clicked.connect(self._paste)
        lrow.addWidget(paste)
        ll.addLayout(lrow)
        self.bar = QProgressBar()
        self.bar.setFixedHeight(6)
        self.bar.setTextVisible(False)
        self.bar.setRange(0, 100)
        self.bar.setValue(0)
        ll.addWidget(self.bar)
        self.status = QLabel("", objectName="hint")
        self.status.setFixedHeight(20)
        self.status.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        ll.addWidget(self.status)
        outer.addWidget(lp)

        # ---- 4. additional settings (left) + download / cancel (right)
        bottom = QHBoxLayout()
        bottom.setSpacing(10)
        extra = QFrame(objectName="group")
        extra.setFixedWidth(self.LEFT_W)
        xl = QVBoxLayout(extra)
        xl.setContentsMargins(14, 10, 14, 10)
        xl.setSpacing(6)
        frow = QHBoxLayout()
        frow.setSpacing(6)
        self.folder_lbl = QLabel("", objectName="hint")
        self.folder_lbl.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Preferred)
        frow.addWidget(self.folder_lbl, 1)
        for text, slot in (("Change…", self._change_folder), ("Open", self._open_folder)):
            b = QPushButton(text, objectName="flat")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.clicked.connect(lambda _=False, s=slot: s())
            frow.addWidget(b)
        xl.addLayout(frow)
        self.cb_play = BoxCheck("Play it when the download is finished")
        self.cb_play.setChecked(settings.value("dl_play", True, bool))
        xl.addWidget(self.cb_play)
        bottom.addWidget(extra)
        gp = QFrame(objectName="group")
        gl = QVBoxLayout(gp)
        gl.setContentsMargins(10, 10, 10, 10)
        self.go = QPushButton("Download", objectName="open")
        self.go.setCursor(Qt.CursorShape.PointingHandCursor)
        self.go.setDefault(True)
        self.go.setMinimumHeight(48)
        self.go.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.go.clicked.connect(self._go)
        gl.addWidget(self.go)
        bottom.addWidget(gp, 1)
        outer.addLayout(bottom)

        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(700)
        self._timer.timeout.connect(self._fetch_info)
        self.set_folder(folder)
        self._build_quality([])
        self._pick_platform(self.platform)
        self._set_kind("video")
        self._clear_info()
        QApplication.instance().aboutToQuit.connect(self.shutdown)

    # ---- small builders
    def _saved_height(self):
        q = self.settings.value("yt_quality", "best", str)
        return int(q) if q.isdigit() else 0

    def _refresh_icons(self):
        """One colour for every app icon: the theme's text colour."""
        for key, b in self.plat_btns.items():
            b.setIcon(platform_icon(key, T["text"]))

    def _chip_row(self, options, current, slot):
        row = QHBoxLayout()
        row.setSpacing(8)
        group = QButtonGroup(self)
        btns = {}
        for label, val in options:
            b = QPushButton(label, objectName="chip")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setChecked(val == current)
            group.addButton(b)
            btns[val] = b
            b.clicked.connect(lambda _=False, v=val: slot(v))
            row.addWidget(b)
        row.addStretch(1)
        return row, btns

    def _build_quality(self, heights):
        """Quality chips: 'Best' + the standard qualities the link really offers (a standard list before it is read)."""
        while self.q_grid.count():
            item = self.q_grid.takeAt(0)
            w = item.widget()
            if w is not None:
                self.q_group.removeButton(w)
                w.deleteLater()
        shown = list(heights) or list(self.HEIGHTS)
        if self._height and shown:                   # keep the wish if possible, else the nearest lower quality
            self._height = next((h for h in shown if h <= self._height), shown[-1])
        opts = [("Best", 0)] + [(f"{h}p", h) for h in shown]
        cols = 3
        for n, (label, val) in enumerate(opts):
            b = QPushButton(label, objectName="chip")
            b.setCheckable(True)
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setChecked(val == self._height)
            self.q_group.addButton(b)
            b.clicked.connect(lambda _=False, v=val: self._pick_height(v))
            self.q_grid.addWidget(b, n // cols, n % cols)
        self.q_grid.setColumnStretch(cols, 1)

    # ---- choices
    def _pick_height(self, v):
        self._height = v

    def _set_codec(self, v):
        self._codec = v

    def _set_kbps(self, v):
        self._kbps = v

    def _set_kind(self, kind):
        self.kind = kind
        for k, b in self.kind_btns.items():
            b.setChecked(k == kind)
        self.video_box.setVisible(kind == "video")
        self.audio_box.setVisible(kind == "audio")

    def _pick_platform(self, key):
        self.platform = key
        self.plat_btns[key].setChecked(True)
        name = PLATFORM_NAME[key]
        self.url_edit.setPlaceholderText("Paste a link…" if key == "other" else f"Paste a {name} link…")
        self.settings.setValue("dl_platform", key)
        if not self._ready:
            self._show_placeholder()

    def _on_platform_click(self, key):
        """Choosing another app starts from scratch: the link, the video and the settings are cleared."""
        if key == self.platform:
            return
        self._pick_platform(key)
        self.url_edit.clear()
        self._clear_info()

    def _paste(self):
        clip = QApplication.clipboard().text().strip()
        if clip:
            self.url_edit.setText(clip)
            self.url_edit.setFocus()

    def _change_folder(self):
        start = self._folder if os.path.isdir(self._folder) else os.path.dirname(self._folder)
        d = QFileDialog.getExistingDirectory(self, "Choose download folder", start)
        if d:
            self.set_folder(os.path.normpath(d))
            self.folder_changed.emit(self._folder)

    def _open_folder(self):
        os.makedirs(self._folder, exist_ok=True)
        QDesktopServices.openUrl(QUrl.fromLocalFile(self._folder))

    def set_folder(self, folder):
        if self._busy or not folder:
            return
        self._folder = folder
        self.folder_lbl.setText(folder)
        self.folder_lbl.setToolTip(folder)

    def prepare(self, audio, url=""):
        """Called every time the dialog is opened (from the video or the music side of the player)."""
        self._refresh_icons()
        if not self._busy:
            self._set_kind("audio" if audio else "video")
        if url:
            self.url_edit.setText(url)
        elif not self.url_edit.text().strip():
            clip = QApplication.clipboard().text().strip()
            if is_url(clip):
                self.url_edit.setText(clip)
        self.url_edit.setFocus()
        self.url_edit.selectAll()

    # ---- cover + settings area
    def _show_placeholder(self):
        pm = rounded_pixmap(None, self.COVER_W, self.COVER_H, 14)
        p = QPainter(pm)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setOpacity(0.45)
        p.drawPixmap((self.COVER_W - 64) // 2, (self.COVER_H - 64) // 2,
                     platform_icon(self.platform, T["text"], 64).pixmap(64, 64))
        p.end()
        self.thumb.setPixmap(pm)
        self.p_title.setText("No video yet")
        self.p_title.setToolTip("")
        self.p_meta.setText("Paste a link and the video appears here")

    def _show_settings(self, ready):
        self.set_box.setVisible(ready)
        self.set_hint.setVisible(not ready)

    def _clear_info(self):
        """Forget the link that was read: placeholder cover, no settings, Download greyed."""
        self._timer.stop()
        self._info_token += 1
        self._ready = False
        self._set_status("")
        self._show_placeholder()
        self._show_settings(False)
        self.go.setEnabled(self._busy)
        self._height = self._saved_height()
        self._build_quality([])

    # ---- reading the link
    def _on_url_changed(self, text):
        text = text.strip()
        self._clear_info()
        if not is_url(text):
            return
        key = detect_platform(text)
        if key and key != self.platform:                 # the link tells which app it belongs to
            self._pick_platform(key)
        self._timer.start()

    def _set_status(self, text, error=False):
        self.status.setText(text)
        self.status.setStyleSheet("color: #ef4444;" if error else "")

    def _fetch_info(self):
        url = self.url_edit.text().strip()
        if not is_url(url) or self._busy or self._ready:
            return
        self._timer.stop()
        if self._info_th is not None:
            self._info_th.cancelled = True
        self._info_token += 1
        token = self._info_token
        site = "This site" if self.platform == "other" else PLATFORM_NAME[self.platform]
        th = LinkInfoThread(url, site, self)
        th.status.connect(lambda msg, t=token: self._set_status(msg) if t == self._info_token else None)
        th.info.connect(lambda d, t=token: self._on_info(t, d))
        th.failed.connect(lambda msg, t=token: self._on_info_failed(t, msg))
        th.finished.connect(lambda th=th: self._threads.discard(th))
        self._threads.add(th)
        self._info_th = th
        self._set_status("Reading the link…")
        th.start()

    def _on_info(self, token, d):
        if token != self._info_token:
            return
        self._set_status("")
        pm = QPixmap()
        if d.get("thumb"):
            pm.loadFromData(d["thumb"])
        self.thumb.setPixmap(rounded_pixmap(pm, self.COVER_W, self.COVER_H, 14))
        title = d["title"]
        self.p_title.setText(self.p_title.fontMetrics().elidedText(title, Qt.TextElideMode.ElideRight, self.COVER_W))
        self.p_title.setToolTip(title)
        meta = [d["uploader"]] if d.get("uploader") else []
        if d.get("duration"):
            meta.append(fmt_time(int(d["duration"] * 1000)))
        if d.get("count", 1) > 1:
            meta.append(f"{d['count']} items (max 20)")
        self.p_meta.setText("   ·   ".join(meta))
        self._ready = True
        self.go.setEnabled(True)
        if not self._busy:
            self._build_quality(d["heights"])
        self._show_settings(True)

    def _on_info_failed(self, token, msg):
        if token == self._info_token:
            self._set_status(msg, error=True)
            self.status.setToolTip(msg)

    # ---- downloading
    def _go(self):
        if self._busy:
            if self._dl is not None:
                self._dl.cancel()
                self._set_status("Cancelling…")
            return
        url = self.url_edit.text().strip()
        if not self._ready or not is_url(url):
            return
        st = self.settings
        st.setValue("dl_codec", self._codec)
        st.setValue("dl_kbps", self._kbps)
        st.setValue("dl_play", self.cb_play.isChecked())
        # audio always carries the video's cover picture (embedded as the song's album art)
        req = {"url": url, "kind": self.kind, "folder": self._folder, "height": self._height,
               "codec": self._codec, "kbps": self._kbps, "platform": self.platform,
               "cover": True, "keep_cover": False}
        self._play_after = self.cb_play.isChecked()
        self._timer.stop()
        th = DownloadThread(req, self)
        th.progress.connect(self._on_progress)
        th.done.connect(self._on_done)
        th.failed.connect(self._on_failed)
        th.finished.connect(lambda th=th: self._threads.discard(th))
        self._threads.add(th)
        self._dl = th
        self._set_busy(True)
        self._set_status("Starting…")
        self.bar.setRange(0, 0)
        th.start()

    def _set_busy(self, busy):
        self._busy = busy
        self.go.setText("Cancel" if busy else "Download")
        self.go.setEnabled(busy or self._ready)
        for w in [self.url_edit, self.cb_play, self.set_box] + list(self.plat_btns.values()):
            w.setEnabled(not busy)

    def _on_progress(self, pct, text):
        if pct < 0:
            self.bar.setRange(0, 0)
        else:
            self.bar.setRange(0, 100)
            self.bar.setValue(pct)
        self._set_status(text)

    def _on_done(self, paths, note):
        self._dl = None
        self._set_busy(False)
        self.bar.setRange(0, 100)
        self.bar.setValue(100)
        names = ", ".join(os.path.basename(p) for p in paths[:2]) + (f"  (+{len(paths) - 2} more)" if len(paths) > 2 else "")
        self._set_status(f"✓  Saved: {names}" + (f"   ({note})" if note else ""))
        self.status.setToolTip(names)
        self.downloaded.emit(list(paths), self._play_after)
        if self._play_after and self.isVisible():
            self.hide()                                   # the player is starting it: get out of the way

    def _on_failed(self, msg):
        self._dl = None
        self._set_busy(False)
        self.bar.setRange(0, 100)
        self.bar.setValue(0)
        if msg == "Cancelled":
            self._set_status("Download cancelled")
        else:
            self._set_status(msg, error=True)
            self.status.setToolTip(msg)

    def shutdown(self):
        """The app is closing: stop what is running."""
        self._timer.stop()
        if self._dl is not None:
            self._dl.cancel()
        if self._info_th is not None:
            self._info_th.cancelled = True
        for t in list(self._threads):
            t.wait(3000)


class MiniPlayer(QWidget):
    """Small always-on-top music controller, shown while the main window is minimized: cover, title,
    previous / round play / next, shuffle / repeat, volume and a seek line. Drag it anywhere; double-click
    (or the corner button) brings the full player back. Mouse wheel = volume."""
    W, H = 480, 174                  # includes a 10 px margin on every side for the soft shadow

    def __init__(self, app):
        # no Qt parent: a child window would be hidden together with the minimized main window
        super().__init__(None, Qt.WindowType.Window | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowStaysOnTopHint | Qt.WindowType.Tool)
        self.app = app
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_QuitOnClose, False)
        self.setWindowTitle(APP_TITLE)
        self.setFixedSize(self.W, self.H)
        self._drag = None
        self._sig = None

        root = QHBoxLayout(self)
        root.setContentsMargins(24, 24, 24, 24)
        root.setSpacing(14)
        self.cover = QLabel()
        self.cover.setFixedSize(84, 84)
        root.addWidget(self.cover, 0, Qt.AlignmentFlag.AlignVCenter)
        col = QVBoxLayout()
        col.setSpacing(4)
        top = QHBoxLayout()
        top.setSpacing(4)
        self.title = QLabel("Nothing playing")
        self.title.setStyleSheet("font-size: 14px; font-weight: 700;")
        self.title.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.title.setFixedHeight(24)
        top.addWidget(self.title, 1)
        self.btn_expand = tool_button("full", "Back to the full player", 18)
        self.btn_expand.setFixedSize(26, 26)
        top.addWidget(self.btn_expand)
        col.addLayout(top)
        self.sub = QLabel("", objectName="hint")
        self.sub.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Fixed)
        self.sub.setFixedHeight(18)
        col.addWidget(self.sub)
        crow = QHBoxLayout()
        crow.setSpacing(2)
        self.btn_shuffle = tool_button("shuffle", "Shuffle", 18)
        self.btn_prev = tool_button("prev", "Previous", 20)
        self.btn_play = tool_button("play", "Play / Pause", 22)
        self.btn_play.setObjectName("play")
        self.btn_play.setFixedSize(46, 46)                      # a real circle (see _apply_style)
        self.btn_next = tool_button("next", "Next", 20)
        self.btn_repeat = tool_button("repeat", "Repeat", 18)
        for b in (self.btn_shuffle, self.btn_prev, self.btn_next, self.btn_repeat):
            b.setFixedSize(34, 34)               # compact: the default tool button padding made the row too tall
        for b in (self.btn_shuffle, self.btn_prev, self.btn_play, self.btn_next, self.btn_repeat):
            crow.addWidget(b, 0, Qt.AlignmentFlag.AlignVCenter)
        crow.addStretch(1)
        self.btn_vol = tool_button("vol", "Mute", 18)
        self.vol = ClickSlider(Qt.Orientation.Horizontal)
        self.vol.setRange(0, 100)
        self.vol.setFixedWidth(80)
        self.vol.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_vol.setFixedSize(30, 30)
        crow.addWidget(self.btn_vol, 0, Qt.AlignmentFlag.AlignVCenter)
        crow.addWidget(self.vol, 0, Qt.AlignmentFlag.AlignVCenter)
        col.addLayout(crow)
        col.addSpacing(2)
        self.seek = ClickSlider(Qt.Orientation.Horizontal)
        self.seek.setFixedHeight(16)
        self.seek.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        col.addWidget(self.seek)
        root.addLayout(col, 1)
        self._apply_style()

        pl = app.player
        self.btn_expand.clicked.connect(self.expand)
        self.btn_prev.clicked.connect(app.prev)
        self.btn_play.clicked.connect(app.toggle_play)
        self.btn_next.clicked.connect(app.next)
        self.btn_shuffle.clicked.connect(lambda _=False: (app.toggle_shuffle(), self._sync_modes()))
        self.btn_repeat.clicked.connect(lambda _=False: (app.cycle_repeat(), self._sync_modes()))
        self.btn_vol.clicked.connect(self._toggle_mute)
        self.vol.valueChanged.connect(self._set_volume)
        app.vol.valueChanged.connect(lambda _v: self._sync_volume())
        self.seek.sliderMoved.connect(pl.setPosition)
        pl.positionChanged.connect(self._on_pos)
        pl.durationChanged.connect(self._on_dur)
        pl.playbackStateChanged.connect(self._on_state)
        pl.sourceChanged.connect(lambda _u: self.sync_track())

    def _apply_style(self):
        # the play button is a perfect circle in the accent colour (radius = half of its size)
        r = self.btn_play.width() // 2
        self.setStyleSheet(
            "QToolButton { padding: 0px; }"
            f"QToolButton#play {{ background: {T['accent']}; border: none; border-radius: {r}px; padding: 0px; }}"
            f"QToolButton#play:hover {{ background: {T['accent_hi']}; }}"
            f"QToolButton#play:pressed {{ background: {T['accent_lo']}; }}")

    # ---- showing / placing
    def place(self):
        st = self.app.settings
        if st.contains("mini_x") and st.contains("mini_y"):
            pos = QPoint(st.value("mini_x", 0, int), st.value("mini_y", 0, int))
            if any(sc.availableGeometry().contains(pos) for sc in QApplication.screens()):
                self.move(pos)
                return
        g = QApplication.primaryScreen().availableGeometry()      # first time: bottom-right corner
        self.move(g.right() - self.W - 8, g.bottom() - self.H - 8)

    def sync_all(self):
        pl = self.app.player
        self._sig = None
        self.sync_track()
        self._sync_modes()
        self._sync_volume()
        self._on_dur(pl.duration())
        self._on_pos(pl.position())
        self._on_state(pl.playbackState())

    def refresh_theme(self):
        for b in self.findChildren(QToolButton):
            name = b.property("icon_name")
            if name and b not in (self.btn_play, self.btn_shuffle, self.btn_repeat, self.btn_vol):
                b.setIcon(make_icon(name))
        self._apply_style()
        self.sync_all()
        self.update()

    def expand(self):
        self.hide()
        self.app.leave_mini()

    # ---- keeping in step with the player
    def sync_track(self):
        if not self.isVisible():
            return
        a = self.app
        thumb, title = "", "Nothing playing"
        if 0 <= a.index < len(a.playlist):
            e = a.playlist[a.index]
            title = e["title"] if e["url"] else pretty_title(e["src"])
            thumb = "" if e["url"] else a._cover_of(e["src"])
        key = (a.index, title, thumb)
        if key == self._sig:
            return
        self._sig = key
        self.cover.setPixmap(make_cover(thumb or None, 84, 16))
        self.title.setText(self.title.fontMetrics().elidedText(title, Qt.TextElideMode.ElideRight, 290))
        self.title.setToolTip(title)

    def _sync_modes(self):
        a = self.app
        on, off = T["accent"], T["dim"]
        self.btn_shuffle.setIcon(make_icon("shuffle", on if a.shuffle_on else off))
        self.btn_repeat.setIcon(make_icon("repeat1" if a.repeat_mode == "one" else "repeat",
                                          off if a.repeat_mode == "off" else on))

    # ---- volume (shares the main player's volume and mute state)
    def _sync_volume(self):
        a = self.app
        v = a.vol.value()
        self.vol.blockSignals(True)
        self.vol.setValue(v)
        self.vol.blockSignals(False)
        muted = a.audio.isMuted() or v == 0
        self.btn_vol.setIcon(make_icon("mute" if muted else "vol", T["dim"] if muted else None))
        self.vol.setToolTip(f"{v}%")

    def _set_volume(self, v):
        self.app.vol.setValue(v)                 # the main window applies it, saves it and tells us back

    def _toggle_mute(self):
        self.app.toggle_mute()
        self._sync_volume()

    def wheelEvent(self, e):
        step = 5 if e.angleDelta().y() > 0 else -5
        self.app.vol.setValue(max(0, min(100, self.app.vol.value() + step)))

    def _on_dur(self, d):
        self.seek.setRange(0, max(0, d))

    def _on_pos(self, pos):
        if not self.seek.isSliderDown():
            self.seek.setValue(pos)
        self.sub.setText(f"{fmt_time(pos)}  /  {fmt_time(self.app.player.duration())}")

    def _on_state(self, state):
        playing = state == QMediaPlayer.PlaybackState.PlayingState
        self.btn_play.setIcon(make_icon("pause" if playing else "play", T["on_accent"]))

    # ---- look + dragging
    def paintEvent(self, _ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        card = QRectF(10, 10, self.W - 20, self.H - 20)
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QColor(0, 0, 0, 11))
        for grow in range(1, 9):                                  # soft drop shadow
            p.drawRoundedRect(card.adjusted(-grow, -grow + 3, grow, grow + 3), 22 + grow, 22 + grow)
        g = QLinearGradient(0, card.top(), 0, card.bottom())
        g.setColorAt(0, QColor(T["card"]))
        g.setColorAt(1, QColor(T["panel"]))
        p.setPen(QPen(QColor(T["line_hi"]), 1))
        p.setBrush(g)
        p.drawRoundedRect(card, 22, 22)

    def mousePressEvent(self, e):
        if e.button() == Qt.MouseButton.LeftButton:
            self._drag = e.globalPosition().toPoint() - self.frameGeometry().topLeft()

    def mouseMoveEvent(self, e):
        if self._drag is not None and e.buttons() & Qt.MouseButton.LeftButton:
            self.move(e.globalPosition().toPoint() - self._drag)

    def mouseReleaseEvent(self, e):
        if self._drag is not None:
            self._drag = None
            self.app.settings.setValue("mini_x", self.x())
            self.app.settings.setValue("mini_y", self.y())

    def mouseDoubleClickEvent(self, e):
        self.expand()


class PopOutWindow(QWidget):
    """The video in its own window that stays above every other window (also above other apps).
    While it is open the main window is hidden. It floats the very same control bar as the player (the bar
    is moved over from the main window), without the library / settings / queue buttons, and the bar fades
    in and out with the mouse. Click = play / pause, double-click or Esc = back into the player, wheel = volume."""
    closed = Signal()

    def __init__(self, app):
        super().__init__(None, Qt.WindowType.Window | Qt.WindowType.WindowStaysOnTopHint)
        self.app = app
        self.setWindowTitle(APP_TITLE)
        self.setAttribute(Qt.WidgetAttribute.WA_QuitOnClose, False)
        self.setWindowIcon(QIcon(make_app_pixmap(256)))
        self.setMinimumSize(640, 360)
        self.setStyleSheet(f"PopOutWindow {{ background: {T['bg']}; }}")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        self.video = QVideoWidget()
        self.video.setStyleSheet("background: black;")
        self.video.setMouseTracking(True)
        self.video.installEventFilter(self)
        lay.addWidget(self.video, 1)

        self.overlay = ControlOverlay(self)          # floats the app's control bar over the bottom of the video
        self._last_mouse = QPoint(-1, -1)
        self.hide_timer = QTimer(self, singleShot=True, interval=app.settings.value("hide_ms", 2000, int))
        self.hide_timer.timeout.connect(self._auto_hide)
        self.poll = QTimer(self, interval=80)
        self.poll.timeout.connect(self._poll_mouse)

        def bind(key, fn):
            QShortcut(QKeySequence(key), self).activated.connect(fn)
        bind("Space", app.toggle_play)
        bind("Esc", app.pop_in)
        bind("Ctrl+P", app.pop_in)
        bind("Left", lambda: app.skip(-5000))
        bind("Right", lambda: app.skip(5000))
        bind("J", lambda: app.skip(-10000))
        bind("L", lambda: app.skip(10000))
        bind("Up", lambda: app.vol.setValue(min(100, app.vol.value() + 5)))
        bind("Down", lambda: app.vol.setValue(max(0, app.vol.value() - 5)))
        bind("M", app.toggle_mute)
        bind("N", app.next)
        bind("P", app.prev)
        bind("S", app.toggle_shuffle)

    # ---- the control bar of the main window lives here while the video is popped out
    def take_bar(self):
        bar = self.app.bar
        self.app.overlay.lay.removeWidget(bar)
        self.overlay.lay.addWidget(bar)
        bar.show()

    def give_bar(self):
        self.overlay.hide_now()
        bar = self.app.bar
        self.overlay.lay.removeWidget(bar)
        self.app.overlay.lay.addWidget(bar)
        bar.show()

    def sync_all(self):
        self.setWindowTitle(self.app.windowTitle())

    def refresh_theme(self):
        self.setWindowIcon(QIcon(make_app_pixmap(256)))
        self.setStyleSheet(f"PopOutWindow {{ background: {T['bg']}; }}")

    # ---- show / hide the bar with the mouse (same behaviour as in the main window)
    def _place_overlay(self):
        r = self.video.rect()
        tl = self.video.mapToGlobal(r.topLeft())
        w = max(320, r.width() - 40)
        h = self.app.bar.sizeHint().height()
        g = QRect(tl.x() + (r.width() - w) // 2, tl.y() + r.height() - h - 18, w, h)
        if self.overlay.geometry() != g:
            self.overlay.setGeometry(g)

    def _mouse_on_bar(self):
        return (self.overlay.isVisible() and self.overlay.geometry().contains(QCursor.pos())) \
            or self.app.seek.isSliderDown() or self.app.vol.isSliderDown()

    def _show_controls(self):
        self._place_overlay()
        self.overlay.fade_in()
        self.overlay.raise_()
        self.video.unsetCursor()

    def _auto_hide(self):
        if self.isVisible() and self.app._is_playing() and not self._mouse_on_bar():
            self.overlay.fade_out()
            self.video.setCursor(Qt.CursorShape.BlankCursor)

    def _poll_mouse(self):
        if not self.isVisible() or self.isMinimized():
            self.overlay.hide_now()
            return
        pos = QCursor.pos()
        moved, self._last_mouse = pos != self._last_mouse, pos
        area = QRect(self.video.mapToGlobal(QPoint(0, 0)), self.video.size())
        if self._mouse_on_bar():
            self._show_controls()
            self.hide_timer.start()
        elif area.contains(pos):
            if moved:
                self._show_controls()
                self.hide_timer.start()
            elif not self.app._is_playing() and not self.overlay.is_shown():
                self._show_controls()                # paused: keep the controls reachable
        else:
            self.overlay.fade_out()                  # the mouse left the video
            self.video.unsetCursor()
        if self.overlay.isVisible():
            self._place_overlay()

    def showEvent(self, ev):
        super().showEvent(ev)
        self.poll.start()

    def hideEvent(self, ev):
        super().hideEvent(ev)
        self.poll.stop()
        self.overlay.hide_now()

    def eventFilter(self, obj, ev):
        if obj is self.video:
            t = ev.type()
            if t == QEvent.Type.MouseButtonPress and ev.button() == Qt.MouseButton.LeftButton:
                self.app.toggle_play()
            elif t == QEvent.Type.MouseButtonDblClick:
                self.app.toggle_play()              # undo the toggle caused by the first click
                self.app.pop_in()
                return True
            elif t == QEvent.Type.Wheel:
                step = 5 if ev.angleDelta().y() > 0 else -5
                self.app.vol.setValue(max(0, min(100, self.app.vol.value() + step)))
                return True
        return super().eventFilter(obj, ev)

    def closeEvent(self, ev):
        ev.ignore()                                 # the X button = back into the player (video keeps playing)
        self.app.pop_in()


class Player(QMainWindow):
    """Main window: library, video page, audio page, queues, playlists, theme and the native-window glue.

    The code is grouped in sections - look for the "# ----" banners inside the class.
    """
    # --------------------------------------------------------------------------
    # Setup
    # --------------------------------------------------------------------------

    def __init__(self):
        super().__init__(None, Qt.WindowType.Window | Qt.WindowType.FramelessWindowHint
                         | Qt.WindowType.WindowMinMaxButtonsHint)      # the title bar is drawn by the app (TitleBar)
        self.setWindowTitle(APP_TITLE)                                 # always the app name, never the file name
        self.setWindowIcon(QIcon(make_app_pixmap(256)))
        enable_native_window_behavior(self)           # before the first show, so the open animation plays too
        self.resize(1180, 700)
        self.setMinimumSize(780, 500)
        self.setAcceptDrops(True)
        self.playlist, self.index = [], -1     # items: {'src', 'title', 'url', 'stream'}
        self._token = 0
        self.settings = QSettings(SETTINGS_ORG, SETTINGS_APP)
        self.download_dir = self.settings.value("download_dir", default_download_dir(), str)
        self._history, self._shuf_done, self._from_back = [], set(), False
        self.shuffle_on = self.settings.value("shuffle", False, bool)
        self.repeat_mode = self.settings.value("repeat", "off", str)
        if self.repeat_mode not in ("off", "all", "one"):
            self.repeat_mode = "off"
        self._threads = set()
        self._mini = None                            # the mini player window (created on first use)
        self._popout = None                          # the always-on-top video window (created on first use)
        self._dl_dialog = None                       # 'Download from the internet' window (created on first use)
        self._theme_key = (self.settings.value("theme", "superdark", str), self.settings.value("accent", "", str))

        self.player = QMediaPlayer(self)
        self.audio = QAudioOutput(self)
        self.player.setAudioOutput(self.audio)
        self.audio.setVolume(0.7)

        self._build_ui()
        self._connect()
        self._shortcuts()
        if self.settings.value("remember_volume", True, bool):
            self.vol.setValue(self.settings.value("volume", 70, int))
        self._update_mode_buttons()
        self._show_page(0)                           # start on the library / home screen

        self.hide_timer = QTimer(self, singleShot=True, interval=self.settings.value("hide_ms", 2000, int))
        self.hide_timer.timeout.connect(self._auto_hide)
        self._last_mouse = QPoint(-1, -1)
        self.poll = QTimer(self, interval=80)        # watches the mouse: show on move, hide on leave
        self.poll.timeout.connect(self._poll_mouse)
        self.poll.start()

    # ------------------------------------------------------------------ UI
    def _build_ui(self):
        """Build the main window layout (title bar, pages, side panel, control bar)."""
        root = QWidget(objectName="root")
        self.setCentralWidget(root)
        frame = QVBoxLayout(root)                    # [ title bar / ( icon rail | everything else ) ]
        frame.setContentsMargins(0, 0, 0, 0)
        frame.setSpacing(0)
        self.titlebar = TitleBar(self)
        frame.addWidget(self.titlebar)
        self.content = QWidget()
        frame.addWidget(self.content, 1)
        shell = QHBoxLayout(self.content)            # [ icon rail | everything else ]
        shell.setContentsMargins(0, 0, 0, 0)
        shell.setSpacing(0)
        self.rail = self._build_rail()
        shell.addWidget(self.rail)
        body = QWidget()
        outer = QHBoxLayout(body)
        outer.setContentsMargins(14, 12, 14, 14)
        outer.setSpacing(12)
        shell.addWidget(body, 1)
        self.outer = outer
        self.body = body

        left = QVBoxLayout()
        left.setSpacing(10)
        outer.addLayout(left, 1)

        self.title_row = QWidget()
        trl = QHBoxLayout(self.title_row)
        trl.setContentsMargins(0, 0, 0, 0)
        trl.setSpacing(6)
        self.btn_home = QPushButton("‹  Library", objectName="flat")
        self.btn_home.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_home.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_home.clicked.connect(self.go_home)
        self.title = QLabel("Nothing playing", objectName="title")
        trl.addWidget(self.btn_home)
        trl.addWidget(self.title, 1)
        self.btn_settings = tool_button("settings", "Settings (Ctrl+,)", 22)
        self.btn_settings.clicked.connect(lambda _=False: self.open_settings())
        trl.addWidget(self.btn_settings)
        left.addWidget(self.title_row)

        # video / placeholder
        self.stack = QStackedWidget()
        self.stack.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        left.addWidget(self.stack, 1)
        self.stack.installEventFilter(self)          # keeps the in-window control bar glued to the bottom

        self.stack.addWidget(self._build_home())

        self.video = QVideoWidget()
        self.video.setStyleSheet("background: black;")
        self.video.setMouseTracking(True)
        self.video.installEventFilter(self)
        self.player.setVideoOutput(self.video)
        self.stack.addWidget(self.video)
        self.audio_view = self._build_audio_view()          # page 2: "now playing" page for audio files
        self.audio_view.installEventFilter(self)
        self.stack.addWidget(self.audio_view)

        # control bar
        self.bar = QFrame(objectName="bar")
        bl = QVBoxLayout(self.bar)
        bl.setContentsMargins(20, 14, 20, 12)
        bl.setSpacing(6)
        self.now_lbl = QPushButton("Nothing playing", objectName="nowlbl")      # what is playing (music views)
        self.now_lbl.setCursor(Qt.CursorShape.PointingHandCursor)
        self.now_lbl.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.now_lbl.setToolTip("Open the now-playing page and the queue")
        self.now_lbl.clicked.connect(lambda _=False: self._open_now_playing())
        bl.addWidget(self.now_lbl)

        seek_row = QHBoxLayout()
        self.t_cur = QLabel("00:00", objectName="time")
        self.t_dur = QLabel("00:00", objectName="time")
        self.t_dur.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self.seek = ClickSlider(Qt.Orientation.Horizontal)
        self.seek.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.seek.setCursor(Qt.CursorShape.PointingHandCursor)
        seek_row.addWidget(self.t_cur)
        seek_row.addWidget(self.seek, 1)
        seek_row.addWidget(self.t_dur)
        bl.addLayout(seek_row)

        row = QHBoxLayout()
        row.setSpacing(4)
        self.btn_open = tool_button("add", "Open files (O)")
        left_box = QHBoxLayout()
        left_box.addWidget(self.btn_open)
        left_box.addStretch(1)

        self.btn_prev = tool_button("prev", "Previous (P)")
        self.btn_back = tool_button("back", "Back 10 s (J)")
        self.btn_play = tool_button("play", "Play / Pause (Space)", 26)
        self.btn_play.setObjectName("play")
        self.btn_play.setFixedSize(56, 56)
        self.btn_fwd = tool_button("fwd", "Forward 10 s (L)")
        self.btn_next = tool_button("next", "Next (N)")
        self.btn_shuffle = tool_button("shuffle", "Shuffle  (S)")
        self.btn_repeat = tool_button("repeat", "Repeat  (R)")
        for b in (self.btn_shuffle, self.btn_repeat):
            b.setProperty("icon_name", "")            # coloured by _update_mode_buttons, not by the theme loop
        center = QHBoxLayout()
        center.setSpacing(6)
        for b in (self.btn_shuffle, self.btn_prev, self.btn_back, self.btn_play, self.btn_fwd, self.btn_next,
                  self.btn_repeat):
            center.addWidget(b)

        self.btn_speed = QToolButton()
        self.btn_speed.setText("1×")
        self.btn_speed.setToolTip("Playback speed")
        self.btn_speed.setPopupMode(QToolButton.ToolButtonPopupMode.InstantPopup)
        self.btn_speed.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_speed.setCursor(Qt.CursorShape.PointingHandCursor)
        menu = QMenu(self.btn_speed)
        group = QActionGroup(self)
        for r in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0):
            act = QAction(f"{r:g}×", self, checkable=True)
            act.setChecked(r == 1.0)
            act.triggered.connect(lambda _=False, r=r: self.set_speed(r))
            group.addAction(act)
            menu.addAction(act)
        self.btn_speed.setMenu(menu)

        self.btn_mute = tool_button("vol", "Mute (M)")
        self.vol = ClickSlider(Qt.Orientation.Horizontal)
        self.vol.setRange(0, 100)
        self.vol.setValue(70)
        self.vol.setFixedWidth(96)
        self.vol.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_queue = tool_button("list", "Queue")          # opens the music queue page (music views only)
        self.btn_mini = tool_button("mini", "Mini player  (Ctrl+M)")   # music views only
        self.btn_full = tool_button("full", "Fullscreen (F)")
        self.btn_pop = tool_button("pop", "Pop out - video above all windows  (Ctrl+P)")
        self.btn_pop.setCheckable(True)
        self.btn_convert = tool_button("convert", "Convert format (C)")
        self.btn_info = tool_button("info", "File info  (I)")
        right = QHBoxLayout()
        right.setSpacing(4)
        right.addStretch(1)
        for w in (self.btn_speed, self.btn_mute, self.vol, self.btn_info, self.btn_convert, self.btn_mini,
                  self.btn_queue, self.btn_pop, self.btn_full):
            right.addWidget(w)

        row.addLayout(left_box, 1)
        row.addLayout(center, 0)
        row.addLayout(right, 1)
        bl.addLayout(row)
        self.overlay = ControlOverlay(self)
        self.overlay.lay.addWidget(self.bar)

        # video page corners: exit arrow (top-left), queue + settings (top-right); they fade with the control bar
        def corner(*buttons):
            ov = ControlOverlay(self)
            fr = QFrame(objectName="cornerscrim")
            fr.setStyleSheet("QFrame#cornerscrim { background: rgba(12, 14, 22, 150); border-radius: 22px; }"
                             "QToolButton { background: transparent; border: none; border-radius: 18px; padding: 0px; }"
                             "QToolButton:hover { background: rgba(255, 255, 255, 45); }"
                             "QToolButton:pressed { background: rgba(255, 255, 255, 70); }")
            fl = QHBoxLayout(fr)
            fl.setContentsMargins(4, 4, 4, 4)
            fl.setSpacing(2)
            for b in buttons:
                b.setFixedSize(36, 36)
                b.setIconSize(QSize(20, 20))
                b.setProperty("icon_name", "")        # always white on the dark disc, not coloured by the theme loop
                fl.addWidget(b)
            ov.lay.addWidget(fr)
            return ov

        self.btn_exit = tool_button("exit", "Back to the library  (H)")
        self.btn_exit.setIcon(make_icon("exit", "#ffffff"))
        self.btn_exit.clicked.connect(lambda _=False: self.exit_video())
        self.btn_vq = tool_button("list", "Queue  (Q)")           # video page: shows / hides the queue panel
        self.btn_vq.clicked.connect(lambda _=False: self.toggle_video_queue())
        self.btn_set_v = tool_button("settings", "Settings (Ctrl+,)")
        self.btn_set_v.setIcon(make_icon("settings", "#ffffff"))
        self.btn_set_v.clicked.connect(lambda _=False: self.open_settings())
        self.overlay.followers = [corner(self.btn_exit), corner(self.btn_vq, self.btn_set_v)]
        self._bar_embedded = False                   # True: the bar is a normal part of the window (music views)
        self._veil = Veil(self.content)

        self._build_video_queue(outer)
        self._sync_vq_button()

    # ------------------------------------------------------------ video queue panel
    # --------------------------------------------------------------------------
    # Video queue side panel
    # --------------------------------------------------------------------------

    def _build_video_queue(self, outer):
        """Side panel of the video page: what plays now + the video queue (click plays, drag reorders, x removes)."""
        self._vq_open = self.settings.value("vq_open", True, bool)
        self._vqmap, self._vq_sig, self._vq_row, self._vq_now_sig = [], None, -2, None
        self._vq_thumbing = set()
        self.SIDE_W = 340
        side = QFrame(objectName="side")                 # its width is animated; the content keeps a fixed width
        side.setFixedWidth(self.SIDE_W)
        shell = QHBoxLayout(side)
        shell.setContentsMargins(0, 0, 0, 0)
        inner = QWidget()
        inner.setFixedWidth(self.SIDE_W)
        shell.addWidget(inner, 0, Qt.AlignmentFlag.AlignLeft)
        sl = QVBoxLayout(inner)
        sl.setContentsMargins(16, 16, 16, 16)
        sl.setSpacing(10)

        head = QHBoxLayout()
        head.setSpacing(4)
        self.queue_title = QLabel("Queue", objectName="big")
        self.queue_title.setStyleSheet("font-size: 18px;")
        self.vq_count = QLabel("", objectName="hint")
        head.addWidget(self.queue_title)
        head.addWidget(self.vq_count)
        head.addStretch(1)
        for text, tip, slot in (("Save", "Save this queue as a playlist", self.save_queue_as_playlist),
                                ("Clear", "Remove every video from the queue", self.vqueue_clear),
                                ("✕", "Hide the queue  (Q)", self.toggle_video_queue)):
            b = QPushButton(text, objectName="flat")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.setToolTip(tip)
            if text == "✕":
                b.setFixedWidth(30)
            b.clicked.connect(lambda _=False, f=slot: f())
            head.addWidget(b)
        sl.addLayout(head)

        card = QFrame(objectName="nowcard")
        cl = QHBoxLayout(card)
        cl.setContentsMargins(10, 10, 12, 10)
        cl.setSpacing(12)
        self.vq_thumb = QLabel()
        self.vq_thumb.setFixedSize(120, 68)
        cl.addWidget(self.vq_thumb)
        col = QVBoxLayout()
        col.setSpacing(2)
        col.addWidget(QLabel("NOW PLAYING", objectName="nowtag"))
        self.vq_now_title = QLabel("Nothing playing", objectName="nowtitle")
        self.vq_now_title.setWordWrap(True)
        self.vq_now_title.setMaximumHeight(38)
        self.vq_now_meta = QLabel("", objectName="hint")
        col.addWidget(self.vq_now_title)
        col.addWidget(self.vq_now_meta)
        col.addStretch(1)
        cl.addLayout(col, 1)
        sl.addWidget(card)

        sl.addWidget(QLabel("In the queue", objectName="caption"))
        self.v_queue = QueueList()
        self.v_queue.setIconSize(QSize(96, 54))
        self.v_queue.setSpacing(2)
        self.v_queue.setUniformItemSizes(False)
        self.v_queue.setVerticalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
        SmoothScroller(self.v_queue)
        self.v_queue.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.v_queue.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.v_queue.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        hand_on_items(self.v_queue)
        self.v_queue.setToolTip("Click a video to play it  ·  drag to reorder  ·  x removes it")
        self.v_queue.playRequested.connect(self._vqueue_play_row)
        self.v_queue.removeRequested.connect(lambda row: self.queue_remove([row], video=True))
        self.v_queue.orderChanged.connect(lambda: self._apply_queue_order(True))
        sl.addWidget(self.v_queue, 1)
        self.vq_empty = QLabel("Your queue is empty\nAdd videos with the button below,\n"
                               "or right-click a video in the library", objectName="hint")
        self.vq_empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.vq_empty.setStyleSheet("font-size: 13px; padding: 24px 10px;")
        sl.addWidget(self.vq_empty, 1)
        add = QPushButton("+  Add videos", objectName="open")
        add.setCursor(Qt.CursorShape.PointingHandCursor)
        add.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        add.clicked.connect(lambda _=False: self._vqueue_add_dialog())
        sl.addWidget(add)
        outer.addWidget(side)
        self.side = side
        side.setVisible(False)

    def _sync_vq_button(self):
        if hasattr(self, "btn_vq"):
            self.btn_vq.setIcon(make_icon("list", "#ffffff" if self._vq_open else "#9aa0b0"))
            self.btn_vq.setToolTip("Hide the queue  (Q)" if self._vq_open else "Show the queue  (Q)")

    def toggle_video_queue(self):
        if self.stack.currentIndex() != 1 or self.isFullScreen():
            return
        self._vq_open = not self._vq_open
        self.settings.setValue("vq_open", self._vq_open)
        self._sync_vq_button()
        if self._vq_open:
            self._refresh_video_queue()
        self._side_animate(self._vq_open)

    # ---- the panel slides in / out (the video grows and shrinks with it)
    def _side_set_width(self, v):
        self.side.setFixedWidth(max(0, int(v)))
        if self.overlay.isVisible():
            self._place_overlay()                        # the control bar follows the video while it resizes

    def _side_instant(self, show):
        a = getattr(self, "_side_anim", None)
        if a is not None:
            a.stop()
        self.side.setFixedWidth(self.SIDE_W)
        self.side.setVisible(show)

    def _side_animate(self, show):
        if not hasattr(self, "_side_anim"):
            a = QVariantAnimation(self)
            a.setDuration(240)
            a.setEasingCurve(QEasingCurve.Type.OutCubic)
            a.valueChanged.connect(self._side_set_width)
            a.finished.connect(self._side_done)
            self._side_anim = a
        a = self._side_anim
        a.stop()
        self._side_target = show
        start = self.side.width() if self.side.isVisible() else 0
        end = self.SIDE_W if show else 0
        if start == end:
            self._side_done()
            return
        self.side.setFixedWidth(start)
        self.side.setVisible(True)
        a.setStartValue(start)
        a.setEndValue(end)
        a.start()

    def _side_done(self):
        self.side.setFixedWidth(self.SIDE_W)
        self.side.setVisible(self._side_target)
        QTimer.singleShot(0, self._place_overlay)

    def _refresh_video_queue(self):
        if not hasattr(self, "v_queue"):
            return
        q = self.v_queue
        ks = [k for k in range(len(self.playlist)) if not self._is_audio_entry(k)]
        self._vqmap = ks                                 # visible row -> index in self.playlist
        sig = (tuple((self.playlist[k]["src"], self.playlist[k]["title"]) for k in ks),
               sum(1 for k in ks if self.playlist[k]["src"] in self._icon_cache))
        if sig != self._vq_sig:                          # rebuild only when the queue / thumbnails changed
            self._vq_sig = sig
            bar = q.verticalScrollBar()
            keep = bar.value()
            q.clear()
            q._hover_x = -1
            for k in ks:
                e = self.playlist[k]
                p = e["src"]
                if e["url"]:
                    title, sub, icon = e["title"], "Link", self._ph_icon
                else:
                    dur = self._thumb_cache.get(p, ("", 0))[1]
                    title = pretty_title(p)
                    sub = os.path.basename(os.path.dirname(p)) + (f"   ·   {fmt_time(int(dur * 1000))}" if dur else "")
                    icon = self._icon_cache.get(p, self._ph_icon)
                it = QListWidgetItem(icon, f"{title}\n{sub}")
                it.setToolTip(p)
                it.setData(Qt.ItemDataRole.UserRole + 1, k)              # which entry of self.playlist this row is
                it.setFlags(it.flags() & ~Qt.ItemFlag.ItemIsDropEnabled)   # drop BETWEEN rows, never on a row
                q.addItem(it)
            bar.setValue(keep)
            self._vq_fetch_thumbs([self.playlist[k]["src"] for k in ks if not self.playlist[k]["url"]])
        row = ks.index(self.index) if self.index in ks else -1
        if row >= 0:
            q.setCurrentRow(row)                         # the playing video is shaded
            if row != self._vq_row:
                q.scrollToItem(q.item(row), QListWidget.ScrollHint.EnsureVisible)
        else:
            q.clearSelection()
            q.setCurrentRow(-1)
        self._vq_row = row
        n = len(ks)
        self.vq_count.setText(f"·  {n} video{'s' if n != 1 else ''}" if n else "")
        self.vq_empty.setVisible(n == 0)
        q.setVisible(n > 0)
        self._refresh_now_card()

    def _refresh_now_card(self):
        e = self.playlist[self.index] if 0 <= self.index < len(self.playlist) else None
        if e is None or self._is_audio_entry(self.index):
            title, meta, thumb = "Nothing playing", "", ""
        else:
            title = e["title"] if e["url"] else pretty_title(e["src"])
            thumb = "" if e["url"] else self._cover_of(e["src"])
            dur = 0 if e["url"] else self._thumb_cache.get(e["src"], ("", 0))[1]
            folder = "Link" if e["url"] else os.path.basename(os.path.dirname(e["src"]))
            meta = folder + (f"   ·   {fmt_time(int(dur * 1000))}" if dur else "")
        key = (title, thumb, meta)
        if key == self._vq_now_sig:
            return
        self._vq_now_sig = key
        self.vq_thumb.setPixmap(rounded_pixmap(QPixmap(thumb) if thumb else None, 120, 68, 10))
        self.vq_now_title.setText(title)
        self.vq_now_title.setToolTip(title)
        self.vq_now_meta.setText(meta)

    def _vq_fetch_thumbs(self, paths):
        """Videos that are not in the library have no thumbnail yet: make them in the background."""
        ff = find_ffmpeg()
        need = [p for p in paths if p not in self._thumb_cache and p not in self._vq_thumbing and os.path.isfile(p)]
        if not ff or not need:
            return
        self._vq_thumbing.update(need)
        t = ThumbThread(ff, need, self)
        t.done.connect(self._on_vq_thumb)
        t.finished.connect(lambda t=t: self._threads.discard(t))
        self._threads.add(t)
        t.start()

    def _on_vq_thumb(self, path, thumb, dur):
        self._thumb_cache[path] = (thumb, dur)
        self._icon_cache[path] = QIcon(make_thumb(self._custom_cover(path) or thumb or None, dur, audio=is_audio(path)))
        self._vq_sig = self._vq_now_sig = None
        self._refresh_video_queue()

    def _vqueue_play_row(self, row):
        """A click on a queue row plays it. Nothing leaves the queue: the other videos stay."""
        if not (0 <= row < len(self._vqmap)):
            return
        k = self._vqmap[row]
        if k >= len(self.playlist):
            return
        if k == self.index:
            if not self._is_playing():
                self.player.play()
            return
        self.play_index(k)

    def _video_library_tracks(self):
        items = self._lib_cache.get("video") or []
        if not items:                                    # video library not opened yet: scan it now
            QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
            try:
                items = LibraryThread(0, self._library_roots("video"), None, None, audio=False)._scan()
            finally:
                QApplication.restoreOverrideCursor()
            self._lib_cache["video"] = items
        return [p for p, _s, _m in items if os.path.isfile(p)]

    def _vqueue_add_dialog(self):
        queued = {self.playlist[k]["src"] for k in self._vqmap if k < len(self.playlist)}
        dlg = QueuePickerDialog(self._video_library_tracks(), queued,
                                lambda p: self._icon_cache.get(p, self._ph_icon), self, video=True)
        if dlg.exec() == QDialog.DialogCode.Accepted and dlg.paths():
            self.queue_add(dlg.paths())

    # --------------------------------------------------------------------------
    # Audio view: now playing + music queue
    # --------------------------------------------------------------------------

    def _build_audio_view(self):
        w = QWidget(objectName="home")
        w.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        page = QVBoxLayout(w)
        page.setContentsMargins(46, 22, 36, 0)          # the queue scrolls under the (transparent) control bar
        page.setSpacing(12)
        self._cur_pl = None                              # id of the playlist that is playing, if any

        # top-left corner: cover + name of the playlist, with an arrow that lists your other playlists
        self.pl_pill = ClickFrame(objectName="plpill")
        self.pl_pill.setCursor(Qt.CursorShape.PointingHandCursor)
        self.pl_pill.setFixedSize(320, 64)               # fixed: nothing moves when the name changes
        self.pl_pill.setToolTip("Switch playlist")
        pl = QHBoxLayout(self.pl_pill)
        pl.setContentsMargins(9, 7, 14, 7)
        pl.setSpacing(12)
        self.pl_cover = QLabel()
        self.pl_cover.setFixedSize(46, 46)
        self.pl_cover.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        col = QVBoxLayout()
        col.setContentsMargins(0, 0, 0, 0)
        col.setSpacing(0)
        self.pl_name = ElideLabel()
        self.pl_name.setObjectName("plname")
        self.pl_name.setFixedHeight(22)
        self.pl_name.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.pl_sub = ElideLabel()
        self.pl_sub.setObjectName("plsub")
        self.pl_sub.setFixedHeight(18)
        self.pl_sub.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        col.addWidget(self.pl_name)
        col.addWidget(self.pl_sub)
        arrow = tool_button("chev_down", "Switch playlist", 18)
        arrow.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        pl.addWidget(self.pl_cover)
        pl.addLayout(col, 1)
        pl.addWidget(arrow)
        self.pl_pill.clicked.connect(self._open_pl_picker)
        top = QHBoxLayout()
        top.addWidget(self.pl_pill)
        top.addStretch(1)
        page.addLayout(top)

        h = QHBoxLayout()
        h.setContentsMargins(0, 0, 0, 0)
        h.setSpacing(44)
        page.addLayout(h, 1)

        left = QVBoxLayout()                             # big square cover + title
        left.setSpacing(6)
        left.setContentsMargins(0, 0, 0, 150)            # keep the cover clear of the bar
        tag = QLabel("NOW PLAYING", objectName="hint")
        tag.setStyleSheet("letter-spacing: 3px; font-weight: 700; font-size: 11px;")
        tag.setAlignment(Qt.AlignmentFlag.AlignCenter)
        left.addWidget(tag)
        self.cover = QLabel()
        self.cover.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.cover.setMinimumSize(1, 1)
        self.cover.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Ignored)
        self.cover.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.cover.customContextMenuRequested.connect(self._cover_menu)
        self.cover.setToolTip("Right-click to set a cover")
        left.addWidget(self.cover, 1)
        self.a_title = ElideLabel()                      # one line, fixed height: the cover above never moves
        self.a_title.setObjectName("hero")
        self.a_title.setStyleSheet("font-size: 28px;")
        self.a_title.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.a_title.setFixedHeight(46)
        self.a_sub = ElideLabel()
        self.a_sub.setObjectName("hint")
        self.a_sub.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.a_sub.setFixedHeight(24)
        left.addWidget(self.a_title)
        left.addWidget(self.a_sub)
        h.addLayout(left, 5)

        right = QVBoxLayout()                            # the queue: only what the user added
        right.setSpacing(8)
        head = QHBoxLayout()
        head.addWidget(QLabel("Queue", objectName="section"))
        self.a_count = QLabel("", objectName="hint")
        head.addWidget(self.a_count)
        head.addStretch(1)
        self.a_add = tool_button("add", "Add songs to the queue", size=18)
        self.a_add.clicked.connect(lambda _=False: self._queue_add_dialog())
        head.addWidget(self.a_add)
        save = QPushButton("Save", objectName="flat")
        save.setToolTip("Save this queue as a playlist")
        save.setCursor(Qt.CursorShape.PointingHandCursor)
        save.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        save.clicked.connect(lambda _=False: self.save_queue_as_playlist())
        head.addWidget(save)
        clear = QPushButton("Clear", objectName="flat")
        clear.setCursor(Qt.CursorShape.PointingHandCursor)
        clear.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        clear.clicked.connect(lambda _=False: self.queue_clear())
        head.addWidget(clear)
        right.addLayout(head)
        self.a_queue = QueueList()
        self.a_queue.setIconSize(QSize(46, 46))
        self.a_queue.setSpacing(2)
        self.a_queue.setUniformItemSizes(False)
        self.a_queue.setVerticalScrollMode(QListWidget.ScrollMode.ScrollPerPixel)
        SmoothScroller(self.a_queue)
        self.a_queue.setTextElideMode(Qt.TextElideMode.ElideRight)
        self.a_queue.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.a_queue.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        hand_on_items(self.a_queue)
        self.a_queue.setToolTip("Click a song to play it  ·  drag to reorder  ·  x removes it")
        self.a_queue.playRequested.connect(self._queue_play_row)
        self.a_queue.removeRequested.connect(lambda row: self.queue_remove([row]))
        self.a_queue.orderChanged.connect(self._apply_queue_order)
        right.addWidget(self.a_queue, 1)
        self.a_empty = QLabel("Your queue is empty\nAdd songs with the  +  button,\nor right-click a track in the library",
                              objectName="hint")
        self.a_empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.a_empty.setStyleSheet("font-size: 14px; padding: 30px 30px 180px 30px;")
        right.addWidget(self.a_empty, 1)
        h.addLayout(right, 4)
        self._aq_sig = None
        self._aq_row = -2
        self._qmap = []
        return w

    def _pl_cover_path(self, pl):
        cv = pl.get("cover") if pl.get("cover") and os.path.isfile(pl["cover"]) else ""
        first = self._first_path(pl)
        return cv or (self._cover_of(first) if first else "")

    def _refresh_pl_pill(self):
        if not hasattr(self, "pl_pill"):
            return
        pl = self._find_playlist(self._cur_pl) if self._cur_pl else None
        if pl is None:
            self._cur_pl = None
        self.pl_cover.setPixmap(make_cover(self._pl_cover_path(pl) or None, 46, 11) if pl else make_cover(None, 46, 11))
        self.pl_name.setText(pl["name"] if pl else "No playlist")
        if pl:
            n = len(pl["items"])
            self.pl_sub.setText(f"{n} track{'s' if n != 1 else ''}")
        else:
            self.pl_sub.setText("Choose a playlist")

    def _open_pl_picker(self):
        items = []
        for pl in self.playlists:
            if self._pl_kind(pl) != "audio":
                continue
            n = len(pl["items"])
            items.append((pl["id"], pl["name"], f"{n} track{'s' if n != 1 else ''}",
                          QIcon(make_cover(self._pl_cover_path(pl) or None, 44, 10))))
        pick = PlaylistPicker(items, self._cur_pl, self)
        pick.chosen.connect(self._switch_playlist)
        pick.move(self.pl_pill.mapToGlobal(QPoint(0, self.pl_pill.height() + 6)))
        pick.show()

    def _switch_playlist(self, pid):
        if pid and pid != self._cur_pl:
            self.play_playlist(pid)

    def _refresh_audio_view(self):
        if not hasattr(self, "cover"):
            return
        self._refresh_queue()
        self._refresh_pl_pill()
        size = max(120, min(400, self.cover.width() - 8, self.cover.height() - 8))
        if not (0 <= self.index < len(self.playlist)):
            self.cover.setPixmap(make_cover(None, size))
            self.a_title.setText("Nothing playing")
            self.a_sub.setText("Pick a song from your library")
            return
        e = self.playlist[self.index]
        thumb = "" if e["url"] else self._cover_of(e["src"])
        self.cover.setPixmap(make_cover(thumb or None, size))
        self.a_title.setText(pretty_title(e["src"]) if not e["url"] else e["title"])
        folder = os.path.basename(os.path.dirname(e["src"])) if not e["url"] else ""
        n = len(self._qmap)
        extra = f"{n} in queue" if n else "queue is empty"
        self.a_sub.setText(f"{folder}   ·   {extra}" if folder else extra)

    def _apply_queue_order(self, video=False):
        """The user dragged songs in the queue: reorder self.playlist the same way (what plays next follows it)."""
        q = self.v_queue if video else self.a_queue
        order = []
        for r in range(q.count()):
            k = q.item(r).data(Qt.ItemDataRole.UserRole + 1)
            if k is not None:
                order.append(k)
        slots = list(self._vqmap if video else self._qmap)                         # the places of self.playlist that the visible rows occupy
        if order == slots or sorted(order) != sorted(slots):
            self._aq_sig = self._vq_sig = None           # nothing moved (or the list changed meanwhile): just redraw
            self._refresh_queue()
            return
        old = list(self.playlist)
        cur = old[self.index] if 0 <= self.index < len(old) else None
        for slot, k in zip(slots, order):
            self.playlist[slot] = old[k]
        pos = {id(e): i for i, e in enumerate(self.playlist)}
        if cur is not None:
            self.index = pos[id(cur)]
        self._history = [pos[id(old[h])] for h in self._history if 0 <= h < len(old)]
        self._shuf_done = {pos[id(old[h])] for h in self._shuf_done if 0 <= h < len(old)}
        self._aq_sig = self._vq_sig = None
        self._refresh_queue()

    def _refresh_queue(self):
        self._refresh_video_queue()                      # the video queue panel follows every change
        if not hasattr(self, "a_queue"):
            return
        q = self.a_queue
        ks = [k for k, e in enumerate(self.playlist) if not e.get("adhoc") and self._is_audio_entry(k)]
        self._qmap = ks                                  # visible row -> index in self.playlist
        paths = [self.playlist[k]["src"] for k in ks]
        sig = (tuple(paths), sum(1 for p in paths if p in self._icon_cache))
        if sig != self._aq_sig:                          # rebuild only when the queue / thumbnails changed
            self._aq_sig = sig
            bar = q.verticalScrollBar()
            keep = bar.value()
            q.clear()
            q._hover_x = -1
            for k in ks:
                e = self.playlist[k]
                p = e["src"]
                if e["url"]:
                    title, sub = e["title"], "Link"
                else:
                    dur = self._thumb_cache.get(p, ("", 0))[1]
                    title = pretty_title(p)
                    sub = os.path.basename(os.path.dirname(p)) + (f"   ·   {fmt_time(int(dur * 1000))}" if dur else "")
                it = QListWidgetItem(self._song_icon(p) if not e["url"] else self._ph_icon_a, f"{title}\n{sub}")
                it.setToolTip(p)
                it.setData(Qt.ItemDataRole.UserRole + 1, k)              # which entry of self.playlist this row is
                it.setFlags(it.flags() & ~Qt.ItemFlag.ItemIsDropEnabled)   # drop BETWEEN rows, never on a row
                q.addItem(it)
            sp = QListWidgetItem()                       # empty room at the end: the last rows can scroll above the bar
            sp.setFlags(Qt.ItemFlag.NoItemFlags)
            sp.setData(Qt.ItemDataRole.UserRole, "spacer")
            sp.setSizeHint(QSize(10, 150))
            q.addItem(sp)
            bar.setValue(keep)
        row = ks.index(self.index) if self.index in ks else -1
        if row >= 0:
            q.setCurrentRow(row)                         # the playing song is shaded
            if row != self._aq_row:
                q.scrollToItem(q.item(row), QListWidget.ScrollHint.EnsureVisible)
        else:
            q.clearSelection()
            q.setCurrentRow(-1)
        self._aq_row = row
        n = len(ks)
        self.a_count.setText(f"·  {n} track{'s' if n != 1 else ''}" if n else "")
        self.a_empty.setVisible(n == 0)
        q.setVisible(n > 0)

    # --------------------------------------------------------------------------
    # Signals and keyboard shortcuts
    # --------------------------------------------------------------------------

    def _connect(self):
        p = self.player
        p.positionChanged.connect(self._on_position)
        p.durationChanged.connect(lambda d: (self.seek.setRange(0, d), self.t_dur.setText(fmt_time(d))))
        p.playbackStateChanged.connect(self._on_state)
        p.mediaStatusChanged.connect(self._on_status)
        p.errorOccurred.connect(self._on_error)
        self.seek.sliderMoved.connect(p.setPosition)
        self.vol.valueChanged.connect(self._on_volume)
        self.btn_open.clicked.connect(self.open_dialog)
        self.btn_play.clicked.connect(self.toggle_play)
        self.btn_prev.clicked.connect(self.prev)
        self.btn_next.clicked.connect(self.next)
        self.btn_back.clicked.connect(lambda: self.skip(-10000))
        self.btn_fwd.clicked.connect(lambda: self.skip(10000))
        self.btn_mute.clicked.connect(self.toggle_mute)
        self.btn_queue.clicked.connect(lambda _=False: self._open_now_playing())
        self.btn_mini.clicked.connect(lambda _=False: self.enter_mini())
        self.btn_full.clicked.connect(self.toggle_fullscreen)
        self.btn_pop.clicked.connect(lambda _=False: self.toggle_popout())
        self.btn_convert.clicked.connect(lambda _=False: self.open_converter())
        self.btn_info.clicked.connect(lambda _=False: self.show_info())
        self.btn_shuffle.clicked.connect(lambda _=False: self.toggle_shuffle())
        self.btn_repeat.clicked.connect(lambda _=False: self.cycle_repeat())

    def _shortcuts(self):
        def bind(key, fn):
            QShortcut(QKeySequence(key), self).activated.connect(fn)
        bind("Space", self.toggle_play)
        bind("Left", lambda: self.skip(-5000))
        bind("Right", lambda: self.skip(5000))
        bind("J", lambda: self.skip(-10000))
        bind("L", lambda: self.skip(10000))
        bind("Up", lambda: self.vol.setValue(min(100, self.vol.value() + 5)))
        bind("Down", lambda: self.vol.setValue(max(0, self.vol.value() - 5)))
        bind("M", self.toggle_mute)
        bind("F", self.toggle_fullscreen)
        bind("Ctrl+P", self.toggle_popout)
        bind("C", self.open_converter)
        bind("I", self.show_info)
        bind("Ctrl+,", self.open_settings)
        bind("Esc", lambda: self.isFullScreen() and self.toggle_fullscreen())
        bind("O", self.open_dialog)
        bind("U", self.open_url_dialog)
        bind("Ctrl+M", self.enter_mini)
        bind("H", self.exit_video)
        bind("A", lambda: self.stack.currentIndex() == 0 and self.set_mode("audio"))
        bind("V", lambda: self.stack.currentIndex() == 0 and self.set_mode("video"))
        bind("Ctrl+V", self.paste_link)
        bind("N", self.next)
        bind("P", self.prev)
        bind("S", self.toggle_shuffle)
        bind("Q", self.toggle_video_queue)
        bind("R", self.cycle_repeat)

    # ------------------------------------------------------------ playlist
    # --------------------------------------------------------------------------
    # Opening media and managing the queue
    # --------------------------------------------------------------------------

    def open_dialog(self):
        v_pat = " ".join(f"*{e}" for e in sorted(EXTS))
        a_pat = " ".join(f"*{e}" for e in sorted(AUDIO_EXTS))
        vid, aud = f"Videos ({v_pat})", f"Audio ({a_pat})"
        both = f"All media ({v_pat} {a_pat})"
        home = self.stack.currentIndex() == 0
        if not home:
            order = [both, vid, aud]
        else:
            order = [aud, vid, both] if self._mode == "audio" else [vid, aud, both]
        if home and self._mode == "audio":
            start = user_music_dir()
        else:
            start = self.download_dir if os.path.isdir(self.download_dir) else ""
        files, _ = QFileDialog.getOpenFileNames(self, "Open media", start, ";;".join(order + ["All files (*)"]))
        self.add_files(files)

    def _new_entry(self, p):
        return {"src": p, "title": os.path.basename(p), "url": False, "stream": None, "height": None, "prog": False}

    @staticmethod
    def _ok_media(paths):
        return [p for p in paths if os.path.splitext(p)[1].lower() in MEDIA_EXTS and os.path.isfile(p)]

    def _insert_entries(self, paths, pos, adhoc=False):
        for k, p in enumerate(paths):
            e = self._new_entry(p)
            if adhoc:
                e["adhoc"] = True
            self.playlist.insert(pos + k, e)
        n = len(paths)                               # keep the history / shuffle bookkeeping valid
        self._history = [h + n if h >= pos else h for h in self._history]
        self._shuf_done = {h + n if h >= pos else h for h in self._shuf_done}

    def add_files(self, paths, adhoc=False):
        """Play these files now. They go right after the current item.
        adhoc=True: a song played straight from the library - it is NOT part of the queue and is
        forgotten as soon as playback moves on; the queue only ever holds what the user added."""
        paths = self._ok_media(paths)
        if not paths:
            return
        pos = self.index + 1 if self.index >= 0 else 0
        self._insert_entries(paths, pos, adhoc)
        self.play_index(pos)

    def queue_add(self, paths):
        """Add to the end of the queue without playing."""
        paths = self._ok_media(paths)
        for p in paths:
            self.playlist.append(self._new_entry(p))
        self._refresh_queue()
        return len(paths)

    def queue_play_next(self, paths):
        paths = self._ok_media(paths)
        if paths:
            self._insert_entries(paths, self.index + 1 if self.index >= 0 else 0)
            self._refresh_queue()
        return len(paths)

    def _delete_entries(self, ks):
        """Delete playlist entries (indices ks) and keep every index-based bookkeeping valid."""
        ks = sorted({k for k in ks if 0 <= k < len(self.playlist)})
        if not ks:
            return

        def remap(h):
            return -1 if h in ks else h - sum(1 for k in ks if k < h)

        for k in reversed(ks):
            del self.playlist[k]
        self._history = [r for r in (remap(h) for h in self._history) if r >= 0]
        self._shuf_done = {r for r in (remap(h) for h in self._shuf_done) if r >= 0}
        if self.index >= 0:
            self.index = remap(self.index)
        prev = getattr(self, "_prev_index", -1)
        if prev >= 0:
            self._prev_index = remap(prev)

    def queue_remove(self, rows, video=False):
        """rows: positions in the visible queue (the music queue, or the video queue with video=True). Something
        only leaves the queue when the user removes it."""
        qmap = list(self._vqmap if video else self._qmap)
        ks = sorted({qmap[r] for r in rows if 0 <= r < len(qmap)})
        if not ks:
            return
        cur_removed = self.index in ks
        nxt = -1
        if cur_removed:                                  # removed what is playing -> go on with the next one of its kind
            video_now = not self._is_audio_entry(self.index)
            for k in range(self.index + 1, len(self.playlist)):
                if k not in ks and (not self._is_audio_entry(k)) == video_now:
                    nxt = k - sum(1 for r in ks if r < k)
                    break
        self._delete_entries(ks)
        if cur_removed:
            if nxt >= 0:
                self.play_index(nxt)
                return
            self._token += 1
            self.player.stop()
            self.player.setSource(QUrl())
            self.title.setText("Nothing playing")
            self.setWindowTitle(APP_TITLE)
            if video:
                self._show_page(0)                       # nothing left to watch: back to the library
        self._refresh_audio_view()
        self._refresh_queue()
        self._update_bar_context()

    def queue_clear(self):
        self.queue_remove(list(range(len(self._qmap))))

    def vqueue_clear(self):
        self.queue_remove(list(range(len(self._vqmap))), video=True)

    def _audio_library_tracks(self):
        items = self._lib_cache.get("audio") or []
        if not items:                                    # music library not opened yet: scan it now
            QApplication.setOverrideCursor(Qt.CursorShape.WaitCursor)
            try:
                items = LibraryThread(0, self._library_roots("audio"), None, None, audio=True)._scan()
            finally:
                QApplication.restoreOverrideCursor()
            self._lib_cache["audio"] = items
        return [p for p, _s, _m in items if os.path.isfile(p)]

    def _queue_add_dialog(self):
        queued = {self.playlist[k]["src"] for k in self._qmap if k < len(self.playlist)}
        dlg = QueuePickerDialog(self._audio_library_tracks(), queued,
                                lambda p: self._icon_cache.get(p, self._ph_icon_a), self)
        if dlg.exec() == QDialog.DialogCode.Accepted and dlg.paths():
            self.queue_add(dlg.paths())
            self._refresh_audio_view()

    def _queue_play_row(self, row):
        """A click on a queue row shades it and plays it. Nothing leaves the queue: the other songs stay and
        come back later with repeat / shuffle."""
        if not (0 <= row < len(self._qmap)):
            return
        k = self._qmap[row]
        if k >= len(self.playlist):
            return
        if k == self.index:
            if not self._is_playing():
                self.player.play()
            return
        self.play_index(k)

    def _toast(self, text):
        QToolTip.showText(QCursor.pos(), text, self, QRect(), 1800)

    # ---- links: download from the internet (YouTube, Instagram, TikTok, X ...)
    def open_url_dialog(self):
        self.open_download_dialog()

    def open_download_dialog(self, url=""):
        """Open the download-from-the-internet dialog."""
        if self._dl_dialog is None:
            dlg = DownloadDialog(self.settings, self.download_dir, self)
            dlg.downloaded.connect(self._on_downloaded)
            dlg.folder_changed.connect(self._on_dl_folder)
            self._dl_dialog = dlg
        dlg = self._dl_dialog
        dlg.set_folder(self.download_dir)
        dlg.prepare(self._mode == "audio", url)      # opened from the music side: audio is pre-selected
        dlg.show()
        dlg.raise_()
        dlg.activateWindow()

    def _on_dl_folder(self, folder):
        self.download_dir = folder
        self.settings.setValue("download_dir", folder)

    def _on_downloaded(self, paths, play):
        paths = [p for p in paths if os.path.isfile(p)]
        if not paths:
            return
        self.refresh_library()
        if play:
            first = paths[0]
            self.add_files([first], adhoc=is_audio(first))
            if len(paths) > 1:
                self.queue_add(paths[1:])

    def paste_link(self):
        clip = QApplication.clipboard().text().strip()
        if is_url(clip):
            self.open_download_dialog(clip)

    def add_url(self, url):
        """A link typed, dropped or given on the command line. A direct link to a media file is streamed as it is;
        anything else (YouTube, Instagram, TikTok, X ...) opens the download window."""
        url = url.strip()
        if not is_url(url):
            QMessageBox.warning(self, "Invalid link", "Please enter a link starting with http:// or https://")
            return
        if os.path.splitext(url.split("?")[0])[1].lower() not in MEDIA_EXTS:
            self.open_download_dialog(url)
            return
        entry = {"src": url, "title": url, "url": True, "stream": None, "height": None, "prog": False}
        self.playlist.append(entry)
        self.play_index(len(self.playlist) - 1)

    def _resolve(self, i):
        """Direct links to a media file (.mp4, .mp3 ...) are streamed as they are."""
        entry = self.playlist[i]
        self._token += 1
        self.title.setText("Loading link…")
        self._show_page(1)
        self._start_stream(i, entry["src"], entry["title"])

    def _on_error(self, _err, msg):
        self.title.setText(f"Cannot play this: {msg}")

    def _start_stream(self, i, stream, title):
        entry = self.playlist[i]
        entry["stream"], entry["title"] = stream, title
        self.player.setSource(QUrl.fromLocalFile(stream) if os.path.isfile(stream) else QUrl(stream))
        self._show_page(1)
        self.title.setText(title)
        self.player.play()
        self._refresh_video_queue()

    def clear_playlist(self):
        self._reset_playlist()
        self._show_page(0)
        self.title.setText("Nothing playing")
        self.setWindowTitle(APP_TITLE)

    # --------------------------------------------------------------------------
    # Playback control
    # --------------------------------------------------------------------------

    def play_index(self, i):
        if not (0 <= i < len(self.playlist)):
            return
        cur = self.index
        if 0 <= cur < len(self.playlist) and cur != i and self.playlist[cur].get("adhoc"):
            self._delete_entries([cur])                  # a song played from the library leaves once we move on
            if i > cur:
                i -= 1
        if 0 <= self.index < len(self.playlist) and self.index != i and not self._from_back:
            self._history.append(self.index)
            del self._history[:-300]
        self._shuf_done.add(i)
        self.index = i
        entry = self.playlist[i]
        if entry["url"]:
            if entry["stream"]:
                self._start_stream(i, entry["stream"], entry["title"])
            else:
                self._resolve(i)
            return
        self._token += 1                             # cancel any pending link resolve
        audio = is_audio(entry["src"])
        self.player.setSource(QUrl.fromLocalFile(entry["src"]))
        if audio:
            if self.stack.currentIndex() != 0:       # music keeps playing while you browse the library
                self._show_page(2)
            self._refresh_audio_view()
        else:
            self._show_page(1)
        self.title.setText(entry["title"])
        self.player.play()
        self._refresh_video_queue()
        self._update_bar_context()

    def _is_audio_entry(self, k):
        e = self.playlist[k]
        return (not e["url"]) and is_audio(e["src"])

    def _same_kind(self, k):
        """True if entry k is the same kind (video / audio) as the one playing."""
        if not (0 <= self.index < len(self.playlist)):
            return True
        return self._is_audio_entry(k) == self._is_audio_entry(self.index)

    def _pick_next(self, wrap):
        n = len(self.playlist)
        if n == 0:
            return -1
        ok = [k for k in range(n) if self._same_kind(k)]          # never jump between video and audio
        if self.shuffle_on and len(ok) > 1:
            pool = [k for k in ok if k != self.index and k not in self._shuf_done]
            if not pool:
                if not wrap:
                    return -1
                self._shuf_done = {self.index} if self.index >= 0 else set()
                pool = [k for k in ok if k != self.index]
            return random.choice(pool)
        after = [k for k in ok if k > self.index]
        if after:
            return after[0]
        return (ok[0] if ok else -1) if wrap else -1

    def next(self):
        j = self._pick_next(self.repeat_mode == "all")
        if j >= 0:
            self.play_index(j)

    def prev(self):
        # restart the current item if we are more than 3 s in, else go back to the previous one
        if self.player.position() > 3000:
            self.player.setPosition(0)
            return
        while self._history:
            j = self._history.pop()
            if 0 <= j < len(self.playlist) and self._same_kind(j):
                self._from_back = True
                try:
                    self.play_index(j)
                finally:
                    self._from_back = False
                return
        if not self.shuffle_on:
            for k in range(self.index - 1, -1, -1):
                if self._same_kind(k):
                    self.play_index(k)
                    return
        self.player.setPosition(0)

    def toggle_shuffle(self):
        """Turn shuffle on / off."""
        self.shuffle_on = not self.shuffle_on
        self._shuf_done = {self.index} if self.index >= 0 else set()
        self.settings.setValue("shuffle", self.shuffle_on)
        self._update_mode_buttons()
        self._toast("Shuffle on" if self.shuffle_on else "Shuffle off")

    def cycle_repeat(self):
        order = ("off", "all", "one")
        self.repeat_mode = order[(order.index(self.repeat_mode) + 1) % 3]
        self.settings.setValue("repeat", self.repeat_mode)
        self._update_mode_buttons()
        self._toast({"off": "Repeat off", "all": "Repeat all", "one": "Repeat one"}[self.repeat_mode])

    def _update_mode_buttons(self):
        on, off = ACCENT, T["dim"]
        self.btn_shuffle.setIcon(make_icon("shuffle", on if self.shuffle_on else off))
        self.btn_shuffle.setToolTip("Shuffle: " + ("on" if self.shuffle_on else "off") + "  (S)")
        self.btn_repeat.setIcon(make_icon("repeat1" if self.repeat_mode == "one" else "repeat",
                                          off if self.repeat_mode == "off" else on))
        self.btn_repeat.setToolTip({"off": "Repeat: off", "all": "Repeat: all", "one": "Repeat: one"}[self.repeat_mode]
                                   + "  (R)")

    # ------------------------------------------------------------- controls
    def toggle_play(self):
        """Play / pause."""
        if self.player.source().isEmpty():
            if self.playlist:                        # something was queued while nothing played: start it
                self.play_index(self.index if self.index >= 0 else 0)
            else:
                self.open_dialog()
        elif self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
        else:
            self.player.play()

    def skip(self, ms):
        if self.player.source().isEmpty():
            return
        self.player.setPosition(max(0, min(self.player.duration(), self.player.position() + ms)))

    def set_speed(self, r):
        self.player.setPlaybackRate(r)
        self.btn_speed.setText(f"{r:g}×")

    def toggle_mute(self):
        """Mute / unmute."""
        self.audio.setMuted(not self.audio.isMuted())
        self._update_vol_icon()

    def _on_volume(self, v):
        self.audio.setVolume(v / 100)
        if v > 0 and self.audio.isMuted():
            self.audio.setMuted(False)
        self._update_vol_icon()
        self.vol.setToolTip(f"{v}%")
        if self.settings.value("remember_volume", True, bool):
            self.settings.setValue("volume", v)

    def _update_vol_icon(self):
        muted = self.audio.isMuted() or self.vol.value() == 0
        self.btn_mute.setIcon(make_icon("mute" if muted else "vol"))

    def _on_position(self, pos):
        if not self.seek.isSliderDown():
            self.seek.setValue(pos)
        self.t_cur.setText(fmt_time(pos))

    def _on_state(self, state):
        playing = state == QMediaPlayer.PlaybackState.PlayingState
        self.btn_play.setIcon(make_icon("pause" if playing else "play", T["on_accent"]))
        if playing:
            self.hide_timer.start()
        else:
            self._show_controls()

    # ------------------------------------------------------------ themes
    # --------------------------------------------------------------------------
    # Theme, media status and playlist storage
    # --------------------------------------------------------------------------

    def apply_theme(self, tid=None, accent=None):
        """Switch the whole app to another theme (colours + icons + library thumbnails) live."""
        key = (tid or "superdark", accent or "")
        if key == getattr(self, "_theme_key", None):
            return
        self._theme_key = key
        set_theme(*key)
        apply_app_theme(QApplication.instance())
        self.setWindowIcon(QIcon(make_app_pixmap(256)))
        self.titlebar.refresh()
        style_main_window(self)
        if _BAR_STYLER is not None:
            _BAR_STYLER.refresh()
        for b in self.findChildren(QToolButton):
            name = b.property("icon_name")
            if name:
                b.setIcon(make_icon(name))
        self.btn_play.setIcon(make_icon("pause" if self._is_playing() else "play", T["on_accent"]))
        self._update_vol_icon()
        self._update_mode_buttons()
        self._sync_vq_button()
        self._apply_mode_ui()
        if self._mini is not None:
            self._mini.refresh_theme()
        if self._popout is not None:
            self._popout.refresh_theme()
        self._aq_sig = None
        self._refresh_pl_pill()
        # thumbnails carry theme colours (placeholder, badges) - redraw them
        self._ph_icon = QIcon(make_thumb(None, 0))
        self._ph_icon_a = QIcon(make_thumb(None, 0, audio=True))
        self._icon_cache = {p: QIcon(make_thumb(self._custom_cover(p) or th or None, dur, audio=is_audio(p)))
                            for p, (th, dur) in self._thumb_cache.items()}
        if self.stack.currentIndex() == 2:
            self._refresh_audio_view()
        pos = self._lib_scroll.verticalScrollBar().value()
        self._rebuild_library()
        QTimer.singleShot(0, lambda: self._lib_scroll.verticalScrollBar().setValue(pos))

    def _on_status(self, status):
        if status != QMediaPlayer.MediaStatus.EndOfMedia:
            return
        if self.repeat_mode == "one":
            self.player.setPosition(0)
            self.player.play()
            return
        j = self._pick_next(self.repeat_mode == "all")
        if j >= 0 and (self.repeat_mode != "off" or self.settings.value("autoplay_next", True, bool)):
            self.play_index(j)

    # ------------------------------------------------------------ home / library
    def _load_playlists(self):
        try:
            data = json.loads(self.settings.value("playlists", "[]", str) or "[]")
            return [p for p in data if isinstance(p, dict) and "id" in p and "name" in p
                    and isinstance(p.get("items"), list)]
        except Exception:
            return []

    def _save_playlists(self):
        self.settings.setValue("playlists", json.dumps(self.playlists, ensure_ascii=False))
        self.settings.sync()

    # --------------------------------------------------------------------------
    # Home screen, side rail and Music / Videos mode
    # --------------------------------------------------------------------------

    def _build_home(self):
        self.playlists = self._load_playlists()
        try:                                         # covers the user picked: {song path: square image}
            raw = json.loads(self.settings.value("custom_covers", "{}", str) or "{}")
            self._custom = {k: v for k, v in raw.items() if isinstance(k, str) and isinstance(v, str)}
        except Exception:
            self._custom = {}
        self._cover_mem = {}
        self._lib_data, self._thumb_cache, self._icon_cache = [], {}, {}
        self._lib_items, self._first_map = {}, {}
        self._lib_token, self._lib_thread = 0, None
        self._ph_icon = QIcon(make_thumb(None, 0))
        self._ph_icon_a = QIcon(make_thumb(None, 0, audio=True))
        self._mode = self.settings.value("lib_mode", "video", str)       # which library is shown
        if self._mode not in ("video", "audio"):
            self._mode = "video"
        self._lib_cache = {"video": [], "audio": []}

        home = QWidget(objectName="home")
        home.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        v = QVBoxLayout(home)
        v.setContentsMargins(32, 28, 32, 16)
        v.setSpacing(16)

        self._head_w = QWidget()                     # logo + title: fades away while the library is scrolled
        head = QHBoxLayout(self._head_w)
        head.setContentsMargins(0, 0, 0, 0)
        head.setSpacing(16)
        self._logo = logo = QLabel()
        logo.setPixmap(make_icon("play", ACCENT, 140).pixmap(58, 58))
        head.addWidget(logo)
        col = QVBoxLayout()
        col.setSpacing(0)
        self._hero = QLabel("", objectName="hero")
        self._sub = QLabel("", objectName="hint")
        col.addWidget(self._hero)
        col.addWidget(self._sub)
        head.addLayout(col, 1)
        v.addWidget(self._head_w)

        actions = QHBoxLayout()
        actions.setSpacing(12)
        b_file = QPushButton("  Play a video from files", objectName="open")
        b_file.setIcon(make_icon("play", T["on_accent"]))
        self._home_btns = (b_file,)
        b_file.setIconSize(QSize(20, 20))
        b_file.setCursor(Qt.CursorShape.PointingHandCursor)
        b_file.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        b_file.clicked.connect(self.open_dialog)
        actions.addWidget(b_file)
        actions.addStretch(1)
        v.addLayout(actions)

        sec = QHBoxLayout()
        self._lib_title = QLabel("Your library", objectName="hero")
        self._lib_title.setStyleSheet("font-size: 20px;")
        sec.addWidget(self._lib_title)
        self.lib_count = QLabel("", objectName="hint")
        sec.addWidget(self.lib_count)
        sec.addStretch(1)
        refresh = QPushButton("Refresh", objectName="flat")
        openf = QPushButton("Open folder", objectName="flat")
        for b in (refresh, openf):
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            sec.addWidget(b)
        refresh.clicked.connect(self.refresh_library)
        openf.clicked.connect(self._open_videos_folder)
        v.addLayout(sec)

        scroll = QScrollArea(objectName="libscroll")
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        scroll.viewport().setAutoFillBackground(False)
        content = QWidget(objectName="libcontent")
        self.lib_layout = QVBoxLayout(content)
        self.lib_layout.setContentsMargins(0, 0, 6, 0)
        self.lib_layout.setSpacing(10)
        scroll.setWidget(content)
        v.addWidget(scroll, 1)
        self._lib_scroll = scroll
        SmoothScroller(scroll)
        self._home_v = v
        self._head_eff = QGraphicsOpacityEffect(self._head_w)
        self._head_eff.setEnabled(False)
        self._head_w.setGraphicsEffect(self._head_eff)
        self._head_w.setMinimumHeight(1)
        self._head_t, self._head_full = 0.0, 0
        scroll.verticalScrollBar().valueChanged.connect(self._update_head_collapse)
        self._apply_mode_ui()
        self._rebuild_library()
        return home

    def _build_rail(self):
        """Slim icon bar on the left of the home page: mode switch + quick actions (icons only)."""
        rail = QFrame(objectName="rail")
        rail.setFixedWidth(70)
        lay = QVBoxLayout(rail)
        lay.setContentsMargins(10, 14, 10, 14)
        lay.setSpacing(8)
        self.mode_switch = ModeSwitch()
        mode = self.settings.value("lib_mode", "video", str)
        self.mode_switch.set_mode(mode if mode in ("video", "audio") else "video", animate=False)
        self.mode_switch.changed.connect(self.set_mode)
        lay.addWidget(self.mode_switch, alignment=Qt.AlignmentFlag.AlignHCenter)
        lay.addSpacing(6)
        sep = QFrame(objectName="railsep")
        sep.setFixedSize(28, 1)
        lay.addWidget(sep, alignment=Qt.AlignmentFlag.AlignHCenter)
        lay.addSpacing(4)

        def rail_button(icon, tip, slot):
            b = tool_button(icon, tip, 26)
            b.setObjectName("railbtn")
            b.clicked.connect(lambda _=False: slot())
            lay.addWidget(b, alignment=Qt.AlignmentFlag.AlignHCenter)
            return b

        self.rail_yt = rail_button("download", "Download from the internet  (U)", self.open_url_dialog)
        rail_button("convert", "Convert formats  (C)", self.open_converter)
        lay.addStretch(1)
        rail_button("settings", "Settings  (Ctrl+,)", self.open_settings)
        return rail

    def _apply_mode_ui(self):
        """Texts / icons of the home page for the current library (videos or music)."""
        audio = self._mode == "audio"
        self.mode_switch.set_mode(self._mode)
        self.mode_switch.update()
        self._logo.setPixmap(make_icon("music" if audio else "play", ACCENT, 140).pixmap(58, 58))
        self._hero.setText("Music Player" if audio else "Video Player")
        self._sub.setText("Listen to your music, or download songs from the internet" if audio
                          else "Watch your videos or download new ones from the internet")
        self._lib_title.setText("Your music library" if audio else "Your library")
        b_file = self._home_btns[0]
        b_file.setText("  Play audio from files" if audio else "  Play a video from files")
        b_file.setIcon(make_icon("music" if audio else "play", T["on_accent"]))
        self._update_bar_context()

    def set_mode(self, mode):
        """Switch the home page between the video library and the music library."""
        if mode not in ("video", "audio"):
            return
        changed = mode != self._mode

        def apply():
            self._mode = mode
            self.settings.setValue("lib_mode", mode)
            self._apply_mode_ui()
            if changed:
                self._lib_data = self._lib_cache.get(mode, [])     # show what we already know at once
                self._rebuild_library()

        if changed and self.stack.currentIndex() == 0:
            self._crossfade(apply, whole=False)
        else:
            apply()
        if changed:
            self.refresh_library()

    # --------------------------------------------------------------------------
    # Library: folders, rows and cards
    # --------------------------------------------------------------------------

    def _load_roots(self, key):
        try:
            extra = json.loads(self.settings.value(key, "[]", str) or "[]")
        except Exception:
            extra = []
        return [r for r in extra if isinstance(r, str)]

    def _library_roots(self, mode=None):
        if (mode or self._mode) == "audio":
            roots = [user_music_dir(), self.download_dir] + self._load_roots("extra_audio_roots")
        else:
            roots = [user_videos_dir(), self.download_dir] + self._load_roots("extra_roots")
        out = []
        for r in roots:
            if r and os.path.isdir(r) and not any(os.path.normcase(r).startswith(os.path.normcase(o)) for o in out):
                out.append(r)
        return out

    def refresh_library(self):
        self._lib_token += 1
        if self._lib_thread is not None:
            self._lib_thread.stop = True
        t = LibraryThread(self._lib_token, self._library_roots(), find_ffmpeg(), self, audio=self._mode == "audio")
        t.found.connect(self._on_lib_found)
        t.thumb.connect(self._on_lib_thumb)
        t.finished.connect(lambda t=t: self._threads.discard(t))
        self._threads.add(t)
        self._lib_thread = t
        t.start()

    # ---- building the rows
    @staticmethod
    def _clear_layout(layout):
        while layout.count():
            it = layout.takeAt(0)
            w = it.widget()
            if w is not None:
                w.setParent(None)
                w.deleteLater()

    def _section_header(self, title, count_text="", action=None, action_text=""):
        w = QWidget()
        h = QHBoxLayout(w)
        h.setContentsMargins(2, 6, 0, 0)
        h.setSpacing(8)
        h.addWidget(QLabel(title, objectName="section"))
        if count_text:
            h.addWidget(QLabel(count_text, objectName="hint"))
        h.addStretch(1)
        if action:
            b = QPushButton(action_text, objectName="flat")
            b.setCursor(Qt.CursorShape.PointingHandCursor)
            b.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            b.clicked.connect(lambda _=False, f=action: f())
            h.addWidget(b)
        return w

    def _make_row(self):
        row = HRow(square=self._mode == "audio")
        row.itemClicked.connect(self._card_clicked)
        row.itemDoubleClicked.connect(self._card_double_clicked)
        row.customContextMenuRequested.connect(lambda pos, r=row: self._card_menu(r, pos))
        return row

    def _folder_label(self, folder):
        base, name = (user_music_dir(), "Music") if self._mode == "audio" else (user_videos_dir(), "Videos")
        try:
            rel = os.path.relpath(folder, base)
        except ValueError:
            rel = ".."
        if rel == ".":
            return name
        if not rel.startswith(".."):
            return name + "  /  " + rel.replace(os.sep, "  /  ")
        parts = [p for p in os.path.normpath(folder).split(os.sep) if p]
        return "  /  ".join(parts[-2:]) or folder

    def _first_path(self, pl):
        return next((p for p in pl["items"] if os.path.isfile(p)), None)

    @staticmethod
    def _pl_kind(pl):
        return pl.get("kind", "video")              # playlists made before the music library are video playlists

    # ---- covers (always square)
    # --------------------------------------------------------------------------
    # Covers (custom pictures for songs and playlists)
    # --------------------------------------------------------------------------

    def _custom_cover(self, path):
        f = self._custom.get(path)
        return f if f and os.path.isfile(f) else ""

    def _cover_of(self, path):
        """Best cover picture for a file: the one the user set, else the library thumbnail, else (songs) what
        is inside the file / next to it."""
        c = self._custom_cover(path)
        if c:
            return c
        t = self._thumb_cache.get(path, ("", 0))[0]
        if t:
            return t
        if path not in self._cover_mem:
            self._cover_mem[path] = quick_art(path) if (os.path.isfile(path) and is_audio(path)) else ""
        return self._cover_mem[path]

    def _song_icon(self, path):
        ic = self._icon_cache.get(path)
        if ic is not None:
            return ic
        cv = self._cover_of(path)
        if not cv:
            return self._ph_icon_a
        dur = self._thumb_cache.get(path, ("", 0))[1]
        ic = QIcon(make_thumb(cv, dur, audio=True))
        self._icon_cache[path] = ic
        return ic

    def _playlist_icon(self, pl):
        first = self._first_path(pl)
        cv = pl.get("cover") if pl.get("cover") and os.path.isfile(pl["cover"]) else ""
        thumb = cv or (self._cover_of(first) if first else "")
        n = len(pl["items"])
        audio = self._pl_kind(pl) == "audio"
        unit = ("track" if n == 1 else "tracks") if audio else ("video" if n == 1 else "videos")
        return QIcon(make_thumb(thumb or None, 0, label=f"{n} {unit}", tag="PLAYLIST", audio=audio))

    def _pick_cover_image(self):
        start = QStandardPaths.writableLocation(QStandardPaths.StandardLocation.PicturesLocation) or os.path.expanduser("~")
        f, _ = QFileDialog.getOpenFileName(self, "Choose a cover image", start,
                                           "Images (*.png *.jpg *.jpeg *.webp *.bmp)")
        if not f:
            return None
        img = QImage(f)
        if img.isNull():
            QMessageBox.warning(self, "Cover", "That image could not be opened.")
            return None
        return img

    def _new_cover_file(self, prefix, img):
        name = f"{prefix}-{hashlib.sha1(os.urandom(8)).hexdigest()[:12]}.jpg"
        dest = os.path.join(covers_dir(), name)
        return dest if save_square(img, dest, 600) else ""

    @staticmethod
    def _drop_file(path):
        try:
            if path and os.path.isfile(path) and os.path.basename(os.path.dirname(path)) == COVERS_DIR_NAME:
                os.remove(path)
        except OSError:
            pass

    def _save_custom(self):
        self.settings.setValue("custom_covers", json.dumps(self._custom, ensure_ascii=False))
        self.settings.sync()

    def _cover_changed(self, path):
        """Refresh every place that shows this song's cover."""
        cv = self._cover_of(path)
        dur = self._thumb_cache.get(path, ("", 0))[1]
        ic = QIcon(make_thumb(cv or None, dur, audio=True))
        self._icon_cache[path] = ic
        it = self._lib_items.get(path)
        if it is not None:
            it.setIcon(ic)
        for item, pid in self._first_map.get(path, []):
            pl = self._find_playlist(pid)
            if pl:
                item.setIcon(self._playlist_icon(pl))
        self._aq_sig = None
        self._refresh_audio_view()

    def set_song_cover(self, path):
        img = self._pick_cover_image()
        if img is None:
            return
        dest = self._new_cover_file("song", img)
        if not dest:
            return
        self._drop_file(self._custom.get(path))
        self._custom[path] = dest
        self._save_custom()
        self._cover_changed(path)

    def remove_song_cover(self, path):
        self._drop_file(self._custom.pop(path, None))
        self._save_custom()
        self._cover_changed(path)

    def set_playlist_cover(self, pid):
        pl = self._find_playlist(pid)
        img = self._pick_cover_image() if pl else None
        if img is None:
            return
        dest = self._new_cover_file("playlist", img)
        if not dest:
            return
        self._drop_file(pl.get("cover"))
        pl["cover"] = dest
        self._save_playlists()
        self._rebuild_library()

    def remove_playlist_cover(self, pid):
        pl = self._find_playlist(pid)
        if pl and pl.get("cover"):
            self._drop_file(pl.pop("cover", None))
            self._save_playlists()
            self._rebuild_library()

    def _cover_menu(self, pos):
        """Right-click on the big cover of the now-playing page."""
        if not (0 <= self.index < len(self.playlist)) or self.playlist[self.index]["url"]:
            return
        path = self.playlist[self.index]["src"]
        menu = QMenu(self)
        menu.addAction("Set cover…").triggered.connect(lambda: self.set_song_cover(path))
        if self._custom_cover(path):
            menu.addAction("Remove custom cover").triggered.connect(lambda: self.remove_song_cover(path))
        menu.exec(self.cover.mapToGlobal(pos))

    # --------------------------------------------------------------------------
    # Library cards: build, click, context menu
    # --------------------------------------------------------------------------

    def _rebuild_library(self):
        self._lib_sig = (self._mode, tuple(self._lib_data))
        audio = self._mode == "audio"
        unit, units = ("track", "tracks") if audio else ("video", "videos")
        ph = self._ph_icon_a if audio else self._ph_icon
        self._clear_layout(self.lib_layout)
        self._lib_items, self._first_map = {}, {}
        self.lib_layout.setContentsMargins(0, 0, 6, 170 if audio else 0)     # room so the last row clears the bar

        # --- playlists row (only the playlists that belong to the current library)
        pls = [pl for pl in self.playlists if self._pl_kind(pl) == self._mode]
        self.lib_layout.addWidget(self._section_header(
            "Playlists", f"·  {len(pls)}" if pls else "", lambda: self.edit_playlist(), "+  New playlist"))
        row = self._make_row()
        for pl in pls:
            n = len(pl["items"])
            it = QListWidgetItem(self._playlist_icon(pl), f"{pl['name']}\n{n} {unit if n == 1 else units}")
            it.setData(Qt.ItemDataRole.UserRole, {"kind": "playlist", "id": pl["id"]})
            it.setToolTip("Click to play  ·  right-click for more")
            row.addItem(it)
            first = self._first_path(pl)
            if first:
                self._first_map.setdefault(first, []).append((it, pl["id"]))
        new = QListWidgetItem(QIcon(make_new_card(176, 176) if audio else make_new_card()),
                              "New playlist\nPick tracks & order them" if audio else "New playlist\nPick videos & order them")
        new.setData(Qt.ItemDataRole.UserRole, {"kind": "new"})
        row.addItem(new)
        self.lib_layout.addWidget(row)

        # --- one horizontal row per folder
        groups = {}
        for path, size, mtime in self._lib_data:
            groups.setdefault(os.path.dirname(path), []).append((path, size, mtime))
        ordered = sorted(groups.items(), key=lambda kv: max(f[2] for f in kv[1]), reverse=True)
        for folder, files in ordered:
            files.sort(key=lambda f: f[2], reverse=True)
            label = self._folder_label(folder)
            paths = [f[0] for f in files]
            self.lib_layout.addWidget(self._section_header(
                label, f"·  {len(files)}", lambda ps=paths, t=label: self._play_paths(ps, t), "▶  Play all"))
            r = self._make_row()
            for path, size, _m in files:
                it = QListWidgetItem(self._icon_cache.get(path, ph),
                                     f"{pretty_title(path)}\n{human_size(size)}")
                it.setData(Qt.ItemDataRole.UserRole, {"kind": "media", "path": path})
                it.setToolTip(path)
                r.addItem(it)
                self._lib_items[path] = it
            self.lib_layout.addWidget(r)

        if not self._lib_data:
            msg = ("No music found yet\nPlay a file, download a song from the internet, or add your music folder in Settings" if audio
                   else "No videos found yet\nPlay a file or download one from the internet")
            empty = QLabel(msg, objectName="hint")
            empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
            empty.setStyleSheet("font-size: 15px; padding: 30px;")
            self.lib_layout.addWidget(empty)
        self.lib_layout.addStretch(1)
        QTimer.singleShot(0, self._update_head_collapse)
        self._refresh_pl_pill()

        n, f = len(self._lib_data), len(groups)
        self.lib_count.setText(f"·  {n} {unit if n == 1 else units} in {f} folder{'s' if f != 1 else ''}" if n else "")

    def _on_lib_found(self, token, items):
        if token != self._lib_token:
            return
        same = (self._mode, tuple(items)) == getattr(self, "_lib_sig", None)
        self._lib_data = items
        self._lib_cache[self._mode] = items
        if not same:                                 # unchanged library: keep what is on screen (no flicker)
            self._rebuild_library()

    def _on_lib_thumb(self, token, path, thumb, dur):
        if token != self._lib_token:
            return
        self._thumb_cache[path] = (thumb, dur)
        icon = QIcon(make_thumb(self._custom_cover(path) or thumb or None, dur, audio=is_audio(path)))
        self._icon_cache[path] = icon
        it = self._lib_items.get(path)
        if it is not None:
            it.setIcon(icon)
        for item, pid in self._first_map.get(path, []):
            pl = self._find_playlist(pid)
            if pl:
                item.setIcon(self._playlist_icon(pl))

    # ---- clicks & menus
    def _card_clicked(self, item):
        d = item.data(Qt.ItemDataRole.UserRole) or {}
        kind = d.get("kind")
        key = d.get("path") or d.get("id") or kind
        now = time.monotonic() * 1000
        last_key, last_t = getattr(self, "_last_card_click", (None, 0))
        self._last_card_click = (key, now)
        if key == last_key and now - last_t <= QApplication.doubleClickInterval():
            return                                   # 2nd click of a double-click: don't restart what the 1st started
        if kind == "media":
            self._lib_open(d["path"])
        elif kind == "playlist":
            self.play_playlist(d["id"])
        elif kind == "new":
            self.edit_playlist()

    def _card_double_clicked(self, item):
        """Double-click a song / music playlist in the library -> open the full now-playing page with the queue."""
        d = item.data(Qt.ItemDataRole.UserRole) or {}
        if d.get("kind") not in ("media", "playlist"):
            return
        if not self._audio_active():                 # videos already open their own page
            return
        if self.stack.currentIndex() == 0:
            self._open_now_playing()

    def _card_menu(self, row, pos):
        it = row.itemAt(pos)
        if it is None:
            return
        d = it.data(Qt.ItemDataRole.UserRole) or {}
        menu = QMenu(self)
        if d.get("kind") == "media":
            path = d["path"]
            menu.addAction("Play").triggered.connect(lambda: self._lib_open(path))
            menu.addAction("Play next").triggered.connect(
                lambda: self._toast("Playing next") if self.queue_play_next([path]) else None)
            menu.addAction("Add to queue").triggered.connect(
                lambda: self._toast("Added to queue") if self.queue_add([path]) else None)
            sub = menu.addMenu("Add to playlist")
            mine = [pl for pl in self.playlists if self._pl_kind(pl) == self._mode]
            for pl in mine:
                sub.addAction(pl["name"]).triggered.connect(
                    lambda _=False, pid=pl["id"]: self._add_to_playlist(pid, path))
            if mine:
                sub.addSeparator()
            sub.addAction("New playlist…").triggered.connect(lambda: self.edit_playlist(None, [path]))
            if is_audio(path):
                menu.addSeparator()
                menu.addAction("Set cover…").triggered.connect(lambda: self.set_song_cover(path))
                if self._custom_cover(path):
                    menu.addAction("Remove custom cover").triggered.connect(lambda: self.remove_song_cover(path))
                menu.addSeparator()
            menu.addAction("Convert…").triggered.connect(lambda: self.open_converter([path]))
            menu.addAction("Show in folder").triggered.connect(
                lambda: QDesktopServices.openUrl(QUrl.fromLocalFile(os.path.dirname(path))))
        elif d.get("kind") == "playlist":
            pid = d["id"]
            menu.addAction("Play").triggered.connect(lambda: self.play_playlist(pid))
            menu.addAction("Add to queue").triggered.connect(lambda: self._queue_playlist(pid))
            menu.addAction("Edit…").triggered.connect(lambda: self.edit_playlist(pid))
            menu.addAction("Rename…").triggered.connect(lambda: self._rename_playlist(pid))
            menu.addAction("Set cover…").triggered.connect(lambda: self.set_playlist_cover(pid))
            if (self._find_playlist(pid) or {}).get("cover"):
                menu.addAction("Remove cover").triggered.connect(lambda: self.remove_playlist_cover(pid))
            menu.addAction("Delete").triggered.connect(lambda: self._delete_playlist(pid))
        else:
            return
        menu.exec(row.viewport().mapToGlobal(pos))

    def _queue_playlist(self, pid):
        pl = self._find_playlist(pid)
        if pl:
            n = self.queue_add(pl["items"])
            self._toast(f"Added {n} to queue" if n else "Nothing to add")

    def _lib_open(self, path):
        if not path or not os.path.isfile(path):
            return
        if 0 <= self.index < len(self.playlist) and self.playlist[self.index]["src"] == path:
            self.player.setPosition(0)
            self.player.play()
            return
        for k, e in enumerate(self.playlist):        # already in the queue: just play it from there
            if e["src"] == path and not e.get("adhoc"):
                self.play_index(k)
                return
        self.add_files([path], adhoc=is_audio(path))  # not queued: plays only this song, the queue is untouched

    def open_settings(self):
        """Open the settings dialog."""
        st = self.settings
        try:
            extra = json.loads(st.value("extra_roots", "[]", str) or "[]")
        except Exception:
            extra = []
        cur = {"download_dir": self.download_dir,
               "convert_dir": st.value("convert_dir", os.path.join(self.download_dir, "converted"), str),
               "yt_quality": st.value("yt_quality", "best", str).replace("ask", "best"),
               "cookie_browser": st.value("cookie_browser", "auto", str),
               "autoplay_next": st.value("autoplay_next", True, bool),
               "remember_volume": st.value("remember_volume", True, bool),
               "hide_ms": st.value("hide_ms", 2000, int),
               "theme": st.value("theme", "superdark", str),
               "accent": st.value("accent", "", str),
               "extra_roots": [r for r in extra if isinstance(r, str)],
               "extra_audio_roots": self._load_roots("extra_audio_roots")}
        saved_theme = (cur["theme"], cur["accent"])
        dlg = SettingsDialog(cur, self)
        accepted = dlg.exec() == QDialog.DialogCode.Accepted
        # the dialog previews themes live: keep the choice on Save, roll back on Cancel
        self.apply_theme(*(((dlg.values()["theme"], dlg.values()["accent"]) if accepted else saved_theme)))
        if dlg.cache_cleared:
            self._icon_cache.clear()
            self._thumb_cache.clear()
            self._cover_mem.clear()
        if accepted:
            v = dlg.values()
            for k in ("download_dir", "convert_dir", "yt_quality", "cookie_browser",
                      "autoplay_next", "remember_volume", "hide_ms", "theme", "accent"):
                st.setValue(k, v[k])
            st.setValue("extra_roots", json.dumps(v["extra_roots"], ensure_ascii=False))
            st.setValue("extra_audio_roots", json.dumps(v["extra_audio_roots"], ensure_ascii=False))
            if v["remember_volume"]:
                st.setValue("volume", self.vol.value())
            self.download_dir = v["download_dir"]
            self.hide_timer.setInterval(v["hide_ms"])
            st.sync()
        if accepted or dlg.cache_cleared:
            self.refresh_library()

    def open_converter(self, paths=None):
        """Open the format converter dialog."""
        if paths is None:
            paths = []
            if 0 <= self.index < len(self.playlist):
                e = self.playlist[self.index]
                p = e["src"] if not e["url"] else e.get("stream")
                if p and os.path.isfile(p):
                    paths = [p]
        out = self.settings.value("convert_dir", os.path.join(self.download_dir, "converted"), str)
        dlg = ConvertDialog(paths, out, self)
        dlg.exec()
        self.settings.setValue("convert_dir", dlg.out_dir)

    def _open_videos_folder(self):
        if self._mode == "audio":
            folder = user_music_dir()
        else:
            folder = self.download_dir if os.path.isdir(self.download_dir) else user_videos_dir()
        QDesktopServices.openUrl(QUrl.fromLocalFile(folder))

    # ---- playlists
    # --------------------------------------------------------------------------
    # Playlists: create, edit, rename, delete
    # --------------------------------------------------------------------------

    def _find_playlist(self, pid):
        return next((p for p in self.playlists if p["id"] == pid), None)

    def _reset_playlist(self):
        self._token += 1
        self.player.stop()
        self.player.setSource(QUrl())
        self.playlist.clear()
        self.index = -1
        self._history.clear()
        self._shuf_done = set()
        self._cur_pl = None
        self.queue_title.setText("Queue")
        self._refresh_queue()
        self._update_bar_context()

    def _play_paths(self, paths, title="Queue"):
        paths = [p for p in paths if os.path.isfile(p)]
        if not paths:
            return
        self._reset_playlist()
        self.add_files(paths)
        self.queue_title.setText(title if len(title) <= 18 else title[:17] + "…")

    def play_playlist(self, pid):
        pl = self._find_playlist(pid)
        if not pl:
            return
        if not any(os.path.isfile(p) for p in pl["items"]):
            QMessageBox.information(self, "Playlist", "This playlist has no playable videos yet.\n"
                                    "Right-click it and choose Edit to add some.")
            return
        self._play_paths(pl["items"], pl["name"])
        self._cur_pl = pid
        self._refresh_pl_pill()

    def edit_playlist(self, pid=None, preselect=None):
        pl = self._find_playlist(pid) if pid else None
        kind = self._pl_kind(pl) if pl else self._mode
        selected = list(pl["items"]) if pl else list(preselect or [])
        candidates = [p for p, _s, _m in self._lib_data]
        dlg = PlaylistDialog(pl["name"] if pl else "", candidates, selected,
                             "Edit playlist" if pl else "New playlist", self, audio=(kind == "audio"))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        name, paths = dlg.result_data()
        name = name or (pl["name"] if pl else f"Playlist {len(self.playlists) + 1}")
        if pl:
            pl["name"], pl["items"] = name, paths
        else:
            self.playlists.append({"id": uuid.uuid4().hex[:8], "name": name, "items": paths, "kind": kind})
        self._save_playlists()
        self._rebuild_library()

    def _add_to_playlist(self, pid, path):
        pl = self._find_playlist(pid)
        if pl and path not in pl["items"]:
            pl["items"].append(path)
            self._save_playlists()
            self._rebuild_library()

    def _rename_playlist(self, pid):
        pl = self._find_playlist(pid)
        if not pl:
            return
        name, ok = QInputDialog.getText(self, "Rename playlist", "Playlist name:", text=pl["name"])
        if ok and name.strip():
            pl["name"] = name.strip()
            self._save_playlists()
            self._rebuild_library()

    def _delete_playlist(self, pid):
        pl = self._find_playlist(pid)
        if not pl:
            return
        ans = QMessageBox.question(self, "Delete playlist",
                                   f"Delete the playlist \"{pl['name']}\"?\nYour video files are not touched.")
        if ans == QMessageBox.StandardButton.Yes:
            self.playlists.remove(pl)
            self._drop_file(pl.get("cover"))
            self._save_playlists()
            self._rebuild_library()

    def save_queue_as_playlist(self):
        paths = []
        if self.stack.currentIndex() == 2:           # from the queue page: exactly the songs listed there
            entries = [self.playlist[k] for k in self._qmap if k < len(self.playlist)]
        elif self.stack.currentIndex() == 1:         # from the video page: exactly the videos listed there
            entries = [self.playlist[k] for k in self._vqmap if k < len(self.playlist)]
        else:
            entries = [e for e in self.playlist if not e.get("adhoc")]
        for e in entries:
            p = e["src"] if not e["url"] else e.get("stream")
            if p and os.path.isfile(p) and p not in paths:
                paths.append(p)
        if not paths:
            QMessageBox.information(self, "Save playlist", "Nothing to save yet - add some items first.")
            return
        cur = self.queue_title.text()
        name, ok = QInputDialog.getText(self, "Save as playlist", "Playlist name:",
                                        text="" if cur == "Queue" else cur)
        if ok and name.strip():
            kind = "audio" if all(is_audio(p) for p in paths) else "video"
            new_id = uuid.uuid4().hex[:8]
            self.playlists.append({"id": new_id, "name": name.strip(), "items": paths, "kind": kind})
            self._save_playlists()
            self._cur_pl = new_id
            self._rebuild_library()
            self.queue_title.setText(name.strip()[:18])

    # --------------------------------------------------------------------------
    # Pages, transitions and mini player
    # --------------------------------------------------------------------------

    def _crossfade(self, change, whole=True):
        """Run change() under a snapshot of the old screen and fade the snapshot away."""
        veil = self._veil
        if not self.isVisible() or self.isMinimized() or veil.busy:
            change()
            return
        target = self.content if whole else self.body
        pm = target.grab()
        veil.prepare(pm, target.rect() if whole else target.geometry())
        try:
            change()
        finally:
            veil.go()

    def _show_page(self, n):
        if n != self.stack.currentIndex():
            self._crossfade(lambda: self._show_page_now(n))
        else:
            self._show_page_now(n)

    def _show_page_now(self, n):
        if n != 1 and self._popout_on():
            self.pop_in()
        self.stack.setCurrentIndex(n)
        self._dock_bar(n)
        self.title_row.setVisible(n == 2 and not self.isFullScreen())      # the video page has no top row any more
        self.rail.setVisible(n == 0 and not self.isFullScreen())
        self.btn_vq.setVisible(n == 1)
        self._side_instant(n == 1 and self._vq_open and not self.isFullScreen())
        if n == 1:
            self._refresh_video_queue()
        if n == 0:
            self.side.hide()
            self.setWindowTitle(APP_TITLE)
            if not self._bar_on_home():
                self.overlay.hide_now()
            self.refresh_library()
        self._update_bar_context()

    def _audio_active(self):
        return 0 <= self.index < len(self.playlist) and is_audio(self.playlist[self.index]["src"])

    def _bar_on_home(self):
        """On the library page the floating bar belongs to the music library only - never to the video
        library, even while a song keeps playing."""
        return self._mode == "audio"

    def _update_head_collapse(self, _v=None):
        """Fade the big logo/title out as the library scrolls; the 'play from files' button stays."""
        if not hasattr(self, "_head_w"):
            return
        sb = self._lib_scroll.verticalScrollBar()
        if self._head_t == 0:
            self._head_full = max(40, self._head_w.sizeHint().height())
        hh = self._head_full
        content_h = self.lib_layout.sizeHint().height()
        vexp = self._lib_scroll.viewport().height() - hh * self._head_t      # viewport height when expanded
        t = 0.0
        if content_h - vexp >= hh + 80:              # only when there is enough to scroll (no flicker)
            t = max(0.0, min(1.0, sb.value() / 70.0))
        if t == self._head_t:
            return
        self._head_t = t
        self._head_eff.setEnabled(t > 0)
        self._head_eff.setOpacity(1.0 - t)
        self._head_w.setMaximumHeight(16777215 if t <= 0 else max(0, int(hh * (1.0 - t))))

    def _update_bar_context(self):
        if not hasattr(self, "now_lbl") or not hasattr(self, "_home_v"):
            return
        pg = self.stack.currentIndex()
        ctx = pg == 2 or (pg == 0 and self._bar_on_home())
        vid = pg == 1
        self.now_lbl.setVisible(ctx or vid)           # the name of what is playing sits above the seek bar
        self.now_lbl.setCursor(Qt.CursorShape.ArrowCursor if vid else Qt.CursorShape.PointingHandCursor)
        self.now_lbl.setToolTip("" if vid else "Open the now-playing page and the queue")
        self.now_lbl.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, vid)    # video: just a name
        self.btn_full.setVisible(not ctx and not self._popout_on())      # music views / popped out: no fullscreen button
        self.btn_pop.setVisible(not ctx)             # ... and no pop out button
        if hasattr(self, "btn_queue"):
            self.btn_queue.setVisible(ctx)           # the queue button only exists in the music views
            self.btn_mini.setVisible(ctx)
        self._home_v.setContentsMargins(32, 28, 32, 16)      # the library scrolls under the transparent bar
        if 0 <= self.index < len(self.playlist):
            e = self.playlist[self.index]
            text = ("♪  " if is_audio(e["src"]) else "") + (e["title"] if e["url"] else pretty_title(e["src"]))
        else:
            text = "Nothing playing"
        width = max(200, (self._popout.width() if self._popout_on() else self.stack.width()) - 120) if vid else 480
        self.now_lbl.setText(self.now_lbl.fontMetrics().elidedText(text, Qt.TextElideMode.ElideRight, width))
        self._sync_bar()

    def _open_now_playing(self):
        if self.stack.currentIndex() == 1:           # on the video page the label is only a name
            return
        if self.stack.currentIndex() == 2:
            self.go_home()
            return
        self._show_page(2)
        QTimer.singleShot(0, self._refresh_audio_view)

    def exit_video(self):
        if self.isFullScreen():
            self.toggle_fullscreen()
        self.go_home()

    def go_home(self):
        """Back to the library (home screen)."""
        if not self._audio_active() and not self._popout_on():     # music / a popped-out video keeps playing
            self.player.pause()
        self._show_page(0)

    # ------------------------------------------------------------ mini player
    def enter_mini(self):
        """Minimize the app and show the small always-on-top music controller."""
        if self._mini is None:
            self._mini = MiniPlayer(self)
        m = self._mini
        m.show()
        m.sync_all()
        m.place()
        m.raise_()
        self.showMinimized()

    def leave_mini(self):
        self.setWindowState(self.windowState() & ~Qt.WindowState.WindowMinimized)
        self.show()
        self.raise_()
        self.activateWindow()

    # --------------------------------------------------------------------------
    # Window behaviour (native frame on Windows, maximize, close)
    # --------------------------------------------------------------------------

    def changeEvent(self, ev):
        super().changeEvent(ev)
        if ev.type() == QEvent.Type.WindowStateChange and getattr(self, "titlebar", None) is not None:
            self.titlebar.sync_state()
        if ev.type() == QEvent.Type.WindowStateChange and sys.platform == "win32" and not self.isFullScreen():
            QTimer.singleShot(0, lambda: enable_native_window_behavior(self))     # Qt drops the styles in fullscreen
        mini = getattr(self, "_mini", None)
        if (ev.type() == QEvent.Type.WindowStateChange and mini is not None and mini.isVisible()
                and not (self.windowState() & Qt.WindowState.WindowMinimized)):
            mini.hide()                              # the app was restored (taskbar): the mini player leaves

    def closeEvent(self, ev):
        if self._mini is not None:
            self._mini.close()
        if self._popout is not None:
            self.settings.setValue("popout_geometry", self._popout.saveGeometry())
            self._popout.hide()
        super().closeEvent(ev)

    # ------------------------------------------------ window frame (custom title bar)
    def toggle_maximize(self):
        if self.isFullScreen():
            return
        if self.isMaximized():
            self.showNormal()
        else:
            self.showMaximized()

    def showEvent(self, ev):
        super().showEvent(ev)
        enable_native_window_behavior(self)
        style_main_window(self)

    def _nc_hit_test(self):
        """Windows asks where the mouse is: window edge (resize), title bar (drag) or normal content. 0 = default."""
        if self.isFullScreen() or self.isMinimized():
            return 0
        pt = self.mapFromGlobal(QCursor.pos())
        x, y, w, h = pt.x(), pt.y(), self.width(), self.height()
        if not (0 <= x < w and 0 <= y < h):
            return 0
        if not self.isMaximized():
            m = 6
            left, right, top, bottom = x < m, x >= w - m, y < m, y >= h - m
            if top and left:
                return 13                                   # HTTOPLEFT
            if top and right:
                return 14                                   # HTTOPRIGHT
            if bottom and left:
                return 16                                   # HTBOTTOMLEFT
            if bottom and right:
                return 17                                   # HTBOTTOMRIGHT
            if left:
                return 10                                   # HTLEFT
            if right:
                return 11                                   # HTRIGHT
            if top:
                return 12                                   # HTTOP
            if bottom:
                return 15                                   # HTBOTTOM
        tb = self.titlebar
        if tb.isVisible() and y < tb.height():
            child = self.childAt(pt)
            if isinstance(child, CaptionButton):
                return 9 if child.kind in ("max", "restore") else 1             # HTMAXBUTTON / HTCLIENT
            return 2                                                            # HTCAPTION
        return 0

    def _max_btn_state(self, hot=None, down=None):
        b = self.titlebar.b_max
        old = (b.nc_hot, b.nc_down)
        if hot is not None:
            b.nc_hot = hot
        if down is not None:
            b.nc_down = down
        if old != (b.nc_hot, b.nc_down):
            b.update()

    def _track_nc_leave(self):
        """Ask Windows for WM_NCMOUSELEAVE, so the maximize button un-highlights when the mouse leaves it."""

        class TRACKMOUSEEVENT(ctypes.Structure):
            _fields_ = [("cbSize", wintypes.DWORD), ("dwFlags", wintypes.DWORD),
                        ("hwndTrack", wintypes.HWND), ("dwHoverTime", wintypes.DWORD)]
        t = TRACKMOUSEEVENT(ctypes.sizeof(TRACKMOUSEEVENT), 0x02 | 0x10, int(self.winId()), 0)   # TME_LEAVE | TME_NONCLIENT
        ctypes.windll.user32.TrackMouseEvent(ctypes.byref(t))

    def nativeEvent(self, eventType, message):
        if sys.platform == "win32" and getattr(self, "titlebar", None) is not None:     # not while the window is being created
            try:
                msg = wintypes.MSG.from_address(int(message))
                m = msg.message
                if m == 0x0084:                             # WM_NCHITTEST
                    code = self._nc_hit_test()
                    self._max_btn_state(hot=(code == 9))
                    if code:
                        return True, code
                elif m == 0x0083:                           # WM_NCCALCSIZE: no system frame, client = whole window
                    win_nc_calcsize(self, msg.hWnd, msg.wParam, msg.lParam)
                    return True, 0
                elif m == 0x00A3 and msg.wParam == 2:       # WM_NCLBUTTONDBLCLK on the title bar
                    self.toggle_maximize()
                    return True, 0
                elif m == 0x00A1 and msg.wParam == 9:       # WM_NCLBUTTONDOWN on the maximize button
                    self._max_btn_state(down=True)
                    return True, 0
                elif m == 0x00A2 and msg.wParam == 9:       # WM_NCLBUTTONUP on the maximize button
                    self._max_btn_state(down=False)
                    self.toggle_maximize()
                    return True, 0
                elif m == 0x00A0 and msg.wParam == 9:       # WM_NCMOUSEMOVE over the maximize button
                    self._max_btn_state(hot=True)
                    self._track_nc_leave()
                elif m == 0x02A2:                           # WM_NCMOUSELEAVE
                    self._max_btn_state(hot=False, down=False)
            except Exception:
                pass
        return super().nativeEvent(eventType, message)

    # ------------------------------------------------------------ file info
    # --------------------------------------------------------------------------
    # File info
    # --------------------------------------------------------------------------

    def _qt_meta(self):
        """What Qt itself knows about the playing file (used when ffmpeg is missing, and as a base)."""
        out = {}
        try:
            md = self.player.metaData()
            K = QMediaMetaData.Key

            def get(key):
                try:
                    return md.value(key)
                except Exception:
                    return None

            for key, name in ((K.Title, "title"), (K.Author, "artist"), (K.AlbumTitle, "album"), (K.Genre, "genre")):
                v = get(key)
                if isinstance(v, (list, tuple)):
                    v = ", ".join(str(x) for x in v)
                if v:
                    out[name] = str(v)
            res = get(K.Resolution)
            if res is not None and hasattr(res, "width") and res.width() > 0:
                out["size"] = (res.width(), res.height())
            try:
                fps = float(get(K.VideoFrameRate) or 0)
                if fps > 0:
                    out["fps"] = fps
            except (TypeError, ValueError):
                pass
            for key, name, fn in ((K.VideoCodec, "vcodec", QMediaFormat.videoCodecName),
                                  (K.AudioCodec, "acodec", QMediaFormat.audioCodecName)):
                v = get(key)
                if v is not None:
                    try:
                        out[name] = fn(v)
                    except Exception:
                        pass
        except Exception:
            pass
        return out

    def show_info(self):
        """Show the info dialog of the file that is playing."""
        if not (0 <= self.index < len(self.playlist)):
            self._toast("Nothing is playing")
            return
        e = self.playlist[self.index]
        local = e["src"] if (not e["url"] and os.path.isfile(e["src"])) else ""
        cover = self._cover_of(local) if local else ""
        dlg = MediaInfoDialog(e, local, self._qt_meta(), self.player.duration(), cover, self)
        ff = find_ffmpeg()
        if local and ff:
            t = ProbeThread(ff, local, self)
            t.done.connect(dlg.set_probe)
            t.finished.connect(lambda t=t: self._threads.discard(t))
            self._threads.add(t)
            dlg.set_state("loading")
            t.start()
        elif local:
            dlg.set_state("noffmpeg")
        dlg.exec()
        dlg.deleteLater()

    # ----------------------------------------------------------- files from Windows (Open with / default player)
    # --------------------------------------------------------------------------
    # Files from outside (command line, second instance, drag & drop)
    # --------------------------------------------------------------------------

    def open_from_args(self, args, delay=350):
        """Files and links sent by Windows (double-click, 'Open with', default player). They are collected for a
        moment, so several selected files start together as one playlist, then the window comes to the front."""
        if not hasattr(self, "_open_pending"):
            self._open_pending = []
            self._open_timer = QTimer(self)
            self._open_timer.setSingleShot(True)
            self._open_timer.timeout.connect(self._flush_open)
        self._open_pending.extend(a for a in args if a not in self._open_pending)
        if args:
            self._open_timer.start(delay)
        if not self.isVisible():                      # started with a file: stay hidden until its page is ready
            if not args:
                if self._popout_on():
                    self._popout.raise_()
                else:
                    self.show()
            return
        if self._mini is not None and self._mini.isVisible():
            self.leave_mini()
        elif self.isMinimized():
            self.showNormal()
        self.raise_()
        self.activateWindow()
        bring_to_front(self)

    def _flush_open(self):
        items, self._open_pending = self._open_pending, []
        files = [a for a in items if not is_url(a)]
        if files:
            self.add_files(files)
            if self._audio_active() and self.stack.currentIndex() != 2:      # music: open the page with the queue
                self._show_page(2)
                QTimer.singleShot(0, self._refresh_audio_view)
        for u in (a for a in items if is_url(a)):
            self.add_url(u)
        if self._popout_on() and not self.isVisible():      # popped out: the video window comes forward instead
            self._popout.raise_()
            self._popout.activateWindow()
            return
        if not self.isVisible():                      # first start with a file: the window opens straight on the video
            self.show()
        if self._mini is not None and self._mini.isVisible():
            self.leave_mini()
        elif self.isMinimized():
            self.showNormal()
        self.raise_()
        self.activateWindow()
        bring_to_front(self)

    # ----------------------------------------------------------- pop out (video above all windows)
    # --------------------------------------------------------------------------
    # Pop-out video window
    # --------------------------------------------------------------------------

    def _popout_on(self):
        return self._popout is not None and self._popout.isVisible()

    def toggle_popout(self):
        if self._popout_on():
            self.pop_in()
        elif self.stack.currentIndex() == 1:
            self.pop_out()

    def pop_out(self):
        if self._popout_on() or self._audio_active():
            return
        if self.isFullScreen():
            self.toggle_fullscreen()
        if self._popout is None:
            self._popout = PopOutWindow(self)
            geo = self.settings.value("popout_geometry")
            if not (geo and self._popout.restoreGeometry(geo)):
                scr = QApplication.primaryScreen().availableGeometry()
                w, h = 720, 405
                self._popout.resize(w, h)
                self._popout.move(scr.right() - w - 24, scr.bottom() - h - 24)
        pw = self._popout
        self.player.setVideoOutput(pw.video)
        pw.sync_all()
        pw.take_bar()                                 # the same control bar floats over the popped-out video
        self.overlay.hide_now()
        for b in self._popout_hidden_buttons():       # these open dialogs that would hide behind the always-on-top video
            b.hide()
        self.btn_pop.setChecked(True)
        self.btn_pop.setToolTip("Back into the player  (Ctrl+P)")
        pw.show()
        pw.raise_()
        pw.activateWindow()
        self._update_bar_context()                    # (after pw.show(): the name is fitted to the popout's width)
        self.hide()                                   # the main window goes away while the video is popped out

    def pop_in(self):
        if self._popout is None:
            return
        pw = self._popout
        self.settings.setValue("popout_geometry", pw.saveGeometry())
        pw.give_bar()
        pw.hide()
        self.player.setVideoOutput(self.video)
        for b in self._popout_hidden_buttons():
            b.show()
        self.btn_pop.setChecked(False)
        self.btn_pop.setToolTip("Pop out - video above all windows  (Ctrl+P)")
        self.show()                                   # the main window comes back
        self.raise_()
        self.activateWindow()
        bring_to_front(self)
        self._update_bar_context()

    def _popout_hidden_buttons(self):
        return (self.btn_full, self.btn_open, self.btn_info, self.btn_convert)

    # ----------------------------------------------------------- fullscreen
    # --------------------------------------------------------------------------
    # Fullscreen and the control bar (docked / overlay / auto-hide)
    # --------------------------------------------------------------------------

    def toggle_fullscreen(self):
        """Enter / leave fullscreen."""
        if self._popout_on():
            self.pop_in()
        if self.isFullScreen():
            self.showNormal()
            self.titlebar.show()
            self.title_row.setVisible(self.stack.currentIndex() == 2)
            self.rail.setVisible(self.stack.currentIndex() == 0)
            self._side_instant(self.stack.currentIndex() == 1 and self._vq_open)
            self.outer.setContentsMargins(14, 12, 14, 14)
            self.video.unsetCursor()
        else:
            self.showFullScreen()
            self.titlebar.hide()
            self.title_row.hide()
            self.rail.hide()
            self._side_instant(False)
            self.outer.setContentsMargins(0, 0, 0, 0)
        self.hide_timer.start()

    # ------------------------------------------------- floating control bar
    def _is_playing(self):
        return self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState

    def _dock_bar(self, n):
        """Video page: the bar floats in its own window over the native video surface.
        Music pages: the very same bar is a normal child of the main window, so it moves with it."""
        want = n != 1
        if want == self._bar_embedded:
            return
        self._bar_embedded = want
        self.bar.hide()
        if want:
            self.overlay.hide_now()
            self.overlay.lay.removeWidget(self.bar)
            self.bar.setParent(self.body)
        else:
            self.overlay.lay.addWidget(self.bar)
            self.bar.show()

    def _place_embedded_bar(self):
        if not getattr(self, "_bar_embedded", False):
            return
        r = self.stack.geometry()                    # the stack's parent is the body widget
        w = max(320, r.width() - 40)
        h = self.bar.sizeHint().height()
        g = QRect(r.x() + (r.width() - w) // 2, r.y() + r.height() - h - 18, w, h)
        if self.bar.geometry() != g:
            self.bar.setGeometry(g)

    def _sync_bar(self):
        """Show the in-window bar on the music pages (now-playing page, music library) and nowhere else."""
        if not getattr(self, "_bar_embedded", False):
            return
        pg = self.stack.currentIndex()
        want = pg == 2 or (pg == 0 and self._bar_on_home())
        if want:
            self._place_embedded_bar()
            self.bar.show()
            self.bar.raise_()
        else:
            self.bar.hide()

    def _place_overlay(self):
        r = self.stack.rect()
        tl = self.stack.mapToGlobal(r.topLeft())
        w = max(320, r.width() - 40)
        h = self.bar.sizeHint().height()
        g = QRect(tl.x() + (r.width() - w) // 2, tl.y() + r.height() - h - 18, w, h)
        if self.overlay.geometry() != g:
            self.overlay.setGeometry(g)
        for i, f in enumerate(self.overlay.followers):       # top-left: exit arrow, top-right: queue + settings
            sz = f.sizeHint()
            x = tl.x() + 14 if i == 0 else tl.x() + r.width() - sz.width() - 14
            g2 = QRect(x, tl.y() + 12, sz.width(), sz.height())
            if f.geometry() != g2:
                f.setGeometry(g2)

    def _show_controls(self):
        if self.stack.currentIndex() != 1 or not self.isVisible():   # only the video page uses the floating bar window
            return
        self._place_overlay()
        self.overlay.fade_in()
        self.overlay.raise_()
        for f in self.overlay.followers:
            f.raise_()
        self.video.unsetCursor()

    def _hide_controls(self):
        self.overlay.fade_out()

    def _auto_hide(self):
        if self.stack.currentIndex() == 1 and self._is_playing() and not self._mouse_on_controls():
            self._hide_controls()
            if self.stack.currentIndex() == 1:
                self.video.setCursor(Qt.CursorShape.BlankCursor)

    def _mouse_on_controls(self):
        pos = QCursor.pos()
        return (self.overlay.isVisible() and self.overlay.geometry().contains(pos)) \
            or any(f.isVisible() and f.geometry().contains(pos) for f in self.overlay.followers) \
            or self.seek.isSliderDown() or self.vol.isSliderDown()

    def _poll_mouse(self):
        usable = (self.isVisible() and not self.isMinimized()
                  and QApplication.applicationState() == Qt.ApplicationState.ApplicationActive
                  and QApplication.activeModalWidget() is None)
        page = self.stack.currentIndex()
        if page != 1:                                # music views use the bar that is part of the window
            if self.overlay.isVisible():
                self.overlay.hide_now()
            self._place_embedded_bar()
            return
        if not usable:
            self.overlay.hide_now()
            return
        pos = QCursor.pos()
        moved, self._last_mouse = pos != self._last_mouse, pos
        area = QRect(self.stack.mapToGlobal(QPoint(0, 0)), self.stack.size())
        if self._mouse_on_controls():
            self._show_controls()
            self.hide_timer.start()
        elif area.contains(pos):
            if moved:
                self._show_controls()
                self.hide_timer.start()
            elif not self._is_playing() and not self.overlay.is_shown():
                self._show_controls()            # paused / nothing playing: keep controls reachable
        else:
            self._hide_controls()                # mouse left the video area
            self.video.unsetCursor()
        if self.overlay.isVisible():
            self._place_overlay()

    def eventFilter(self, obj, ev):
        if obj is self.stack:
            if ev.type() in (QEvent.Type.Resize, QEvent.Type.Move):
                self._place_embedded_bar()
            if ev.type() == QEvent.Type.Resize and self.stack.currentIndex() == 1:
                QTimer.singleShot(0, self._update_bar_context)       # re-fit the name to the new width
            return super().eventFilter(obj, ev)
        if obj is getattr(self, "audio_view", None):
            t = ev.type()
            if t == QEvent.Type.Resize:
                QTimer.singleShot(0, self._refresh_audio_view)
            elif t == QEvent.Type.MouseButtonPress and ev.button() == Qt.MouseButton.LeftButton:
                self.toggle_play()
            return super().eventFilter(obj, ev)
        if obj is self.video:
            t = ev.type()
            if t == QEvent.Type.MouseButtonPress and ev.button() == Qt.MouseButton.LeftButton:
                self.toggle_play()
            elif t == QEvent.Type.MouseButtonDblClick:
                self.toggle_play()          # undo the toggle caused by the first click
                self.toggle_fullscreen()
                return True
        return super().eventFilter(obj, ev)

    # ------------------------------------------------------------ drag & drop
    def dragEnterEvent(self, e):
        if e.mimeData().hasUrls():
            e.acceptProposedAction()

    def dropEvent(self, e):
        md = e.mimeData()
        files = [u.toLocalFile() for u in md.urls() if u.isLocalFile()]
        if files:
            self.add_files(files)
            return
        text = (md.text() or "").strip()
        if not text and md.urls():
            text = md.urls()[0].toString()
        if is_url(text):
            self.add_url(text)


# ----------------------------------------------------------------------------
# Windows: "Open with" / default player (registered per user in HKCU - no admin rights needed)
# ----------------------------------------------------------------------------
ASSOC_PROGID = f"{APP_ID}.Media"
SINGLE_NAME = f"{APP_ID}-single-instance-v1"


def _launch_command():
    """The command Windows runs to open a file: the .exe when built, pythonw + this script otherwise."""
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}"'
    py = sys.executable
    if py.lower().endswith("python.exe"):
        pyw = py[:-len("python.exe")] + "pythonw.exe"
        if os.path.isfile(pyw):
            py = pyw
    return f'"{py}" "{os.path.abspath(__file__)}"'


def register_file_associations():
    """Adds Veyro Player to Windows 'Open with' and to Settings > Default apps for every video / audio type.
    Windows itself decides the default (the user picks Veyro Player in Default apps). Returns True on success."""
    if sys.platform != "win32":
        return False
    try:
        import winreg
        H = winreg.HKEY_CURRENT_USER

        def put(path, value="", name=""):
            with winreg.CreateKeyEx(H, path, 0, winreg.KEY_WRITE) as k:
                winreg.SetValueEx(k, name, 0, winreg.REG_SZ, value)

        cmd = _launch_command() + ' "%1"'
        frozen = getattr(sys, "frozen", False)
        icon = f'"{sys.executable}",0' if frozen else ""
        exts = sorted(MEDIA_EXTS)
        base = "Software\\Classes\\" + ASSOC_PROGID
        put(base, f"{APP_NAME} media file")
        put(base + "\\shell\\open", f"Play with {APP_NAME}")
        put(base + "\\shell\\open\\command", cmd)
        if icon:
            put(base + "\\DefaultIcon", icon)
        if frozen:                                   # also appears under 'Open with > Veyro Player'
            app = "Software\\Classes\\Applications\\" + os.path.basename(sys.executable)
            put(app, APP_NAME, "FriendlyAppName")
            put(app + "\\shell\\open\\command", cmd)
            put(app + "\\DefaultIcon", icon)
            for e in exts:
                put(app + "\\SupportedTypes", "", e)
        cap = "Software\\" + APP_ID + "\\Capabilities"
        put(cap, APP_NAME, "ApplicationName")
        put(cap, "Modern video and music player", "ApplicationDescription")
        for e in exts:
            put(cap + "\\FileAssociations", ASSOC_PROGID, e)
            put("Software\\Classes\\" + e + "\\OpenWithProgids", "", ASSOC_PROGID)
        put("Software\\RegisteredApplications", cap, APP_ID)
        ctypes.windll.shell32.SHChangeNotify(0x08000000, 0, None, None)      # SHCNE_ASSOCCHANGED
        return True
    except Exception:
        return False


def unregister_file_associations():
    """Remove everything register_file_associations() wrote to the registry."""
    if sys.platform != "win32":
        return
    try:
        import winreg
        H = winreg.HKEY_CURRENT_USER

        def drop_tree(path):
            try:
                with winreg.OpenKey(H, path, 0, winreg.KEY_READ | winreg.KEY_WRITE) as k:
                    while True:
                        try:
                            drop_tree(path + "\\" + winreg.EnumKey(k, 0))
                        except OSError:
                            break
                winreg.DeleteKey(H, path)
            except OSError:
                pass

        for e in sorted(MEDIA_EXTS):
            try:
                with winreg.OpenKey(H, "Software\\Classes\\" + e + "\\OpenWithProgids", 0, winreg.KEY_WRITE) as k:
                    winreg.DeleteValue(k, ASSOC_PROGID)
            except OSError:
                pass
        drop_tree("Software\\Classes\\" + ASSOC_PROGID)
        if getattr(sys, "frozen", False):
            drop_tree("Software\\Classes\\Applications\\" + os.path.basename(sys.executable))
        drop_tree("Software\\" + APP_ID)
        try:
            with winreg.OpenKey(H, "Software\\RegisteredApplications", 0, winreg.KEY_WRITE) as k:
                winreg.DeleteValue(k, APP_ID)
        except OSError:
            pass
        ctypes.windll.shell32.SHChangeNotify(0x08000000, 0, None, None)
    except Exception:
        pass


def _clean_args(argv):
    """Files and links from the command line (absolute paths); options like --register are skipped."""
    out = []
    for a in argv:
        if not a or a.startswith("--"):
            continue
        out.append(a if is_url(a) else os.path.abspath(a))
    return out


def main():
    """Program entry: single-instance check, theme, main window, files from the command line."""
    global _BAR_STYLER
    if "--register" in sys.argv:
        register_file_associations()
        return
    if "--unregister" in sys.argv:
        unregister_file_associations()
        return
    args = _clean_args(sys.argv[1:])
    if sys.platform == "win32":
        try:                                          # own taskbar identity + icon (not "python.exe")
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(f"{APP_ID}.Player")
        except Exception:
            pass
    app = QApplication(sys.argv)
    app.setApplicationName(APP_ID)

    # one window only: files opened from Explorer while Veyro Player runs are sent to the running window
    sock = QLocalSocket()
    sock.connectToServer(SINGLE_NAME)
    if sock.waitForConnected(400):
        if sys.platform == "win32":
            try:   # this process was just started by Explorer, so it may hand the foreground right to the running player
                ctypes.windll.user32.AllowSetForegroundWindow(0xFFFFFFFF)       # ASFW_ANY
            except Exception:
                pass
        sock.write(json.dumps(args).encode("utf-8"))
        sock.flush()
        sock.waitForBytesWritten(1500)
        sock.disconnectFromServer()
        return
    server = QLocalServer()
    QLocalServer.removeServer(SINGLE_NAME)
    server.listen(SINGLE_NAME)

    app.setStyle("Fusion")
    st = QSettings(SETTINGS_ORG, SETTINGS_APP)
    set_theme(st.value("theme", "superdark", str), st.value("accent", "", str))
    apply_app_theme(app)
    _BAR_STYLER = _NativeBarStyler(app)
    app.installEventFilter(_BAR_STYLER)
    win = Player()
    win._on_state(QMediaPlayer.PlaybackState.StoppedState)   # set initial play icon
    win._update_vol_icon()
    if not args:
        win.show()                                    # with a file the window shows itself once the video page is ready

    def on_connection():
        while server.hasPendingConnections():
            c = server.nextPendingConnection()

            def read(c=c):
                data = bytes(c.readAll()).decode("utf-8", "ignore")
                if not data:
                    return
                try:
                    got = json.loads(data)
                except ValueError:
                    got = []
                win.open_from_args([a for a in got if isinstance(a, str)])
            c.readyRead.connect(read)
            c.disconnected.connect(c.deleteLater)
            if c.bytesAvailable():
                read()
    server.newConnection.connect(on_connection)

    # the built .exe adds itself to 'Open with' / Default apps the first time it runs (and when it moves)
    if getattr(sys, "frozen", False) and sys.platform == "win32" and st.value("assoc_path", "", str) != sys.executable:
        if register_file_associations():
            st.setValue("assoc_path", sys.executable)
    if args:
        win.open_from_args(args, delay=150)
    sys.exit(app.exec())


if __name__ == "__main__":
    main()

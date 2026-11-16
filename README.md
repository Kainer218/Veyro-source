# Veyro Player

A modern video and music player for Windows (works on any OS that Qt supports), built with **Python + PySide6 (Qt 6)**. It includes a media library, downloads from the internet, a format converter, and a mini music player.

---

## Features

- **Plays most formats**
  - Video: MP4, M4V, MOV, MKV, AVI, WebM, WMV, FLV, MPG/MPEG, TS
  - Audio: MP3, M4A, AAC, WAV, FLAC, OGG/OGA, Opus, WMA, AIF/AIFF, MKA
- **Hardware-accelerated playback** through Qt Multimedia
- **Library** for music and videos with cards, covers and playlists; extra folders can be added for scanning
- **Download from the internet** (YouTube, Instagram, TikTok, X/Twitter, and any link yt-dlp supports, such as Facebook, Vimeo, SoundCloud, Reddit, Dailymotion), with quality and folder options; cover art is saved with downloaded audio files
- **Format converter** powered by ffmpeg: MP4, MKV, WebM, AVI, MOV, GIF, MP3, M4A, OGG, WAV, FLAC, with three quality levels (High / Balanced / Small file)
- **Mini player** for music
- **Queue** and a side panel for video
- **27 colour themes** (dark and light) under Settings > Appearance, plus a custom accent colour
- **Icons drawn in code** and a frameless window with a custom title bar
- **Single instance**: files opened from Explorer are sent to the running window
- **Default player registration** on Windows (no admin rights needed)
- Drag & drop files or links onto the window
- File info for what is playing (name, size, length, resolution, codec ...)

---

## Installation

### Requirements

- Python 3.9+
- Packages:

```bash
pip install PySide6 "yt-dlp[default]" imageio-ffmpeg
```

- For YouTube downloads, installing **Deno** or **Node.js** is recommended.
- `yt-dlp` and `imageio-ffmpeg` are optional and imported lazily. Without them playback still works, but downloading and converting do not.

---

## Usage

```bash
python veyro_player.py                # start the app
python veyro_player.py movie.mp4      # open a file or link directly
```

---

## Keyboard shortcuts

| Key | Action |
|---|---|
| `Space` | Play / pause |
| `Left` / `Right` | -5 s / +5 s |
| `J` / `L` | -10 s / +10 s |
| `Up` / `Down` | Volume up / down |
| `M` | Mute |
| `F` | Fullscreen (`Esc` exits) |
| Double-click video | Fullscreen |
| `N` / `P` | Next / previous |
| `O` | Open files |
| `H` | Back to the library (home screen) |
| `A` / `V` | Switch the library to Music / Videos |
| `Ctrl+M` | Mini player (music) |
| `U` | Download from the internet |
| `Ctrl+V` | Paste a link to download it |
| `I` | Info about the file that is playing |

---

## Building the .exe

On Windows, double-click `build_veyro.bat` (it uses `veyro.ico`). The output is:

```
dist/Veyro/Veyro.exe
```

The first time the built .exe runs, it registers itself under **Open with** and **Settings > Default apps**.

---

## Default player (Windows)

- In the app: **Settings > Default player**
- Or from the command line:

```bash
Veyro.exe --register       # register the app
Veyro.exe --unregister     # remove the registration
```

Registration is per user (`HKCU`) and needs no admin rights. Windows itself decides the default, so pick Veyro Player under Default apps.

---

## Settings

Stored with `QSettings`. They include: download folder, convert folder, default video quality (Best / 1080p / 720p / 480p), cookie browser, autoplay next, remember volume, controls hide delay, extra library folders, theme and accent colour.

---

## Code map

Everything lives in one file on purpose, which makes it easy to build into a single .exe. Search for the class or function name:

| Section | Contents |
|---|---|
| Theme | `THEME_SPECS`, `build_theme`, `get_theme`, `set_theme`, `build_style` |
| Icons | `make_icon`, `make_app_pixmap` |
| Downloads | `LinkInfoThread`, `DownloadThread`, `DownloadDialog` (yt-dlp) |
| Media helpers | `make_thumb`, `make_cover`, `embedded_art_bytes`, `quick_art` |
| Library | `LibraryThread`, `HRow`, `PlaylistDialog` |
| Converter | `ConvertThread`, `ConvertDialog` (ffmpeg) |
| Settings | `default_settings`, `SettingsDialog` |
| Queue widgets | `QueueList`, `QueuePickerDialog`, `PlaylistPicker` |
| Windows glue | `style_main_window`, `enable_native_window_behavior`, `TitleBar` |
| Widgets | `ModeSwitch`, `Veil`, `ControlOverlay`, `MiniPlayer`, `PopOutWindow` |
| Main window | `Player` |
| Entry point | `register_file_associations`, `main` |

### Conventions

- Keep new code inside the matching section of the single file.
- Colours always come from the active theme dict `T`; never hard-code a colour in a widget.
- Slow work (disk scans, yt-dlp, ffmpeg) runs in `QThread` subclasses and reports back with signals.
- Optional packages (`yt_dlp`, `imageio_ffmpeg`) are imported lazily inside the functions that need them.
- Do not change `APP_ID` casually: users' saved covers and file associations live under it.

---

## Data locations

- **Settings:** `QSettings` (organisation and app name `VideoPlayer`, kept from the old name so existing users keep their settings)
- **Custom covers:** `VideoPlayerCovers` folder in AppData
- **Thumbnail cache:** `VeyroPlayerThumbs` folder in the temp directory (safe to delete, rebuilt on demand)

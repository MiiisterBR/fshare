# Fshare

A portable, offline file manager and media player for your local network. Run one Python file on Windows, macOS or Linux, then browse, watch, listen, download and delete files from another computer, phone, tablet or Android TV browser.

**No pip packages, build step, CDN, cloud service or internet connection is required to run the application.** All HTML, CSS, JavaScript and icons are embedded in `server.py`. The shared root is the terminal's current working directory, not the script's location.

## Requirements

- Python **3.9 or newer** on the host computer.
- A modern browser on each receiving device; no receiver installation is needed.
- Devices on the same reachable LAN, with the host firewall allowing the chosen TCP port.
- Free space in the host's system temporary directory for ZIP downloads.

Native decoding, fullscreen, track selection and autoplay permissions depend on the browser, operating system and device. MP4 with H.264 video and AAC audio generally offers the widest compatibility. MKV playback is attempted directly and works when the browser supports its container and codecs.

## Installation and quick start

Download `server.py` from this repository. You can keep the script anywhere:

```bash
cd /path/to/files-to-share
python /path/to/server.py
```

If the script is already inside the folder to share:

```bash
python server.py
```

Use `python3` instead of `python` if that is your system's Python 3 command. The server prints its shared root and addresses such as `http://192.168.1.10:8000`. Open a printed **network address** on your other devices. `127.0.0.1` works only on the host itself. Keep the terminal open; press **Ctrl+C** to stop and clean up temporary ZIPs.

The default port is the first available port from **8000–8019**. There is no separate installation, build or configuration step. Only `server.py` is needed at runtime.

## Configuration

| Option | Effect |
| --- | --- |
| `--port 8080` | Use a specified TCP port; `--port 0` chooses an available port. |
| `--host 127.0.0.1` | Bind only to this computer. The default `0.0.0.0` accepts IPv4 LAN connections. |
| `--password` | Ask for a password in the terminal without echoing it. |
| `--read-only` | Disable all deletion operations. |
| `--self-test` | Run the built-in test suite in temporary folders, then exit. |
| `FSHARE_PASSWORD` | Supply the optional password through the host environment. Avoid saving credentials in committed files. |

Examples:

```bash
python server.py --password --port 8080
python server.py --read-only
python server.py --help
```

## Browsing and file operations

- Navigate with folders, breadcrumbs, the parent button or browser Back.
- Search the **current folder** and sort by name, type, size or modification date.
- Desktop and TV use spacious rows; phones use cards with visible action buttons. TV mode starts enabled and can be toggled. Theme and TV preferences are remembered in that browser.
- **Preview**, **Download file**, **Select** and **Delete** are visible on each file. Folders provide **Open folder** and **Download ZIP**.
- Select multiple items to download one ZIP or delete a group. **Select all** includes matching items on all pages. Large folders render 100 items per page.
- **Download all** archives the current folder's contents, including nested folders. ZIP preparation shows progress and can continue while you browse.
- Deletion requires a confirmation dialog and a separate acknowledgement. Deletion is permanent on the host; folders include their contents.
- Right-click, long press or Shift+F10 provides additional operation shortcuts.

ZIPs use disk-backed temporary files and ZIP64; complete files or archives are not held in server RAM. Temporary ZIPs are removed after transfer, cancellation, expiry, errors or normal shutdown. Symlinks and unavailable entries are excluded. Characters incompatible with portable archive paths are encoded as `%XX` and reported in the ZIP dialog.

## Media player

Native video/audio controls remain available, including seek, volume and fullscreen. The extra transport bar provides Play/Pause, ±10-second seeks, positive speeds from **0.25× to 3×**, fullscreen and **Playback settings**. Speed changes preserve the current source and position.

### Subtitles

Matching SRT/WebVTT sidecars are discovered in the video's folder:

```text
Movie.mkv
Movie.srt
Movie.fa.srt
Movie.en.vtt
Movie.fa.m4a
```

Choose a discovered subtitle or **Load SRT / VTT** from the receiving device. Manual files stay in that browser and are not uploaded to the host. Choose **Off** or use Show/Hide subtitles at any time.

Settings include delay from **−120 to +120 seconds**, color, font size and top/middle/bottom placement. **Positive delay means later subtitles**. Text decoding handles UTF-8, UTF BOMs and legacy Windows-1256; explicit UTF-8, Windows-1256 and Windows-1252 choices are available. Save non-BOM UTF-16 files as UTF-8. Text markup is simplified to safe plain captions; ASS/SSA styling, animations, bitmap subtitles and OCR are not implemented. Each subtitle is limited to **2 MiB / 20,000 cues**; only the currently loaded external cue set is retained.

The browser's exposed embedded text tracks also appear in the selector. A video can contain subtitles that the browser does not expose. This application does not demux MKV/MP4 to extract them. Embedded cue timing/position is adjustable only when the browser exposes mutable cues; external SRT/WebVTT offers more predictable controls. Native cues allow subtitles to accompany native video fullscreen, subject to device support.

### Audio and language

Embedded audio choices appear **only when the browser exposes its `audioTracks` API and actual tracks**. Otherwise, the original soundtrack remains available and the interface explains the limitation. This API has limited cross-browser support; multiple tracks in a file do not guarantee selectable languages in the browser.

For video, select an audio file from the shared folder or **Load audio file** from the receiving device. External audio follows video play/pause, seeks and positive speed changes. Switching sources keeps the video loaded and restores the original soundtrack when you switch back. Unplayable external audio falls back to original audio with an explanation.

External audio delay ranges from **−120 to +120 seconds**; positive delay plays audio later. Separate volume/mute controls apply to external audio. It is synchronized periodically and corrected for drift, rather than providing sample-accurate editing. Browser autoplay restrictions may require pressing Play. External-audio stalls pause the video while audio catches up. Independent delay for embedded audio is unavailable without extracting a separate audio source. iOS native fullscreen, casting, background playback and OS media controls may handle the two media elements differently; inline playback is the most predictable mode.

### Buffering and reverse playback: explicit limits

The player displays the **actual contiguous buffered time ahead** and total buffered coverage. With external audio, the reported playable time ahead considers both sources. Automatic mode requests native background preloading; Lower data use requests metadata first. Playback can start immediately, and normal HTTP Range seeking remains intact.

A plain HTML media element provides **no portable API to enforce a 10-minute buffer or a half-full refill threshold**. `preload` is a hint, and `buffered` is read-only. The browser chooses how much data to retain and can evict it. The application does not duplicate large media in JavaScript arrays or Blob downloads, and does not claim a strict RAM ceiling for the browser's native decoder. At 20 Mb/s, ten minutes of compressed video alone would consume about **1.5 GB**, before decoding overhead. Short files may be fully buffered if the browser allows it; this is not guaranteed.

Precise, bounded buffering would require a container-aware segmented pipeline (for example, compatible fragmented MP4/WebM plus Media Source Extensions), timestamp indexing, eviction logic and substantial compatibility work. Arbitrary byte ranges from MKV/MP4 cannot simply be appended as playable MSE segments.

**True reverse playback is not offered.** Negative native playback rates lack dependable support across the target browsers. Repeated backward seeks are not reverse playback. A prepared reversed copy, or a different demuxing/decoding/frame-cache pipeline, is required. Both have processing and memory costs; this project does not disguise seek buttons as negative-speed playback.

### Optional host-side preparation

FFmpeg is **not a runtime dependency**. If you already use it, it can prepare more compatible files:

```bash
# Remux compatible video/audio into MP4 without re-encoding.
ffmpeg -i "Movie.mkv" -map 0:v:0 -map "0:a:0?" -c copy -movflags +faststart "Movie.mp4"

# Export the first text subtitle; this does not OCR bitmap subtitles.
ffmpeg -i "Movie.mkv" -map 0:s:0 "Movie.en.srt"

# Export a second audio track as an AAC sidecar.
ffmpeg -i "Movie.mkv" -map 0:a:1 -c:a aac "Movie.fa.m4a"
```

Remuxing preserves existing codecs, so incompatible codecs still need transcoding. Text subtitle conversion may lose original styling. Automatic transcoding, live remuxing, universal embedded-track extraction and universal codec decoding are outside the dependency-free implementation.

## Keyboard and remote controls

| Input | Action |
| --- | --- |
| Arrows | Move focus between items and visible controls. Down from an item enters its actions; left/right move between actions. |
| Enter / remote OK | Activate the focused button. Native selects and media controls use browser behavior. |
| Space on a file name | Select/deselect that item. |
| Tab / Shift+Tab | Move focus; dialogs keep focus within their controls. |
| `/` | Focus search outside dialogs. |
| Ctrl/Cmd+A | Select matching items in the current folder outside text inputs. |
| Delete | Request deletion of selected items. |
| Alt+Up | Open the parent folder. |
| Escape / supported Back key | Close a preview or dialog. |

In TV mode, up/down moves focus through form controls and left/right changes the focused select; Enter can open its native picker. Turn off TV mode for ordinary keyboard form behavior. TV remote support depends on which keyboard events its browser sends. Playback settings use native selects, numeric inputs and large buttons so touch, keyboard and remote users can reach the same features.

## LAN troubleshooting and security

- Confirm both devices are on the same LAN. Guest Wi-Fi isolation, VPN routing or firewall rules can prevent access.
- Use the host's printed network IP and port. Addresses can change when reconnecting to Wi-Fi; restart to print current addresses.
- Allow inbound traffic to Python's port in the host firewall. Do not configure public port forwarding for this LAN tool.
- The chosen shared folder and its descendants are accessible, including ordinary hidden files. Share a dedicated media folder rather than a directory containing credentials or private configuration.
- Root-relative paths are validated and symlink/junction traversal is blocked. Deletion uses session-bound, expiring confirmations and checks that selected items have not changed.
- Password protection uses a browser session, CSRF checks and login throttling. **HTTP does not encrypt passwords or file traffic**; use a trusted network. This is not an internet-facing production service.
- Interrupted transfers, inaccessible files and insufficient ZIP disk space produce errors without blocking unrelated downloads. Abrupt process termination or power loss may leave an OS temporary ZIP directory to remove manually.

## Development and verification

The complete application, including its `unittest` suite, lives in `server.py`. No dependencies need installing and no build step is required:

```bash
python server.py --self-test
```

Tests cover Range/HEAD delivery (including a file larger than 4 GiB), Unicode and long paths, root confinement, authentication/CSRF, sidecar discovery and bounded subtitle decoding, safe deletion, concurrent transfers, ZIP64 preparation, cancellation and cleanup/error handling. Test fixtures use temporary directories and do not delete shared user files.

Browser behavior must also be checked with real media: MP4/MKV playback and seek, subtitle visibility/timing/style, external audio play/pause/seek/rate changes, buffer indicators, mobile layout and keyboard focus. Linux Chrome automation is not a substitute for testing Safari/iPhone, Windows, macOS or a physical Android TV. Codec support, embedded tracks and two-element audio synchronization remain device-dependent.

The Git repository intentionally publishes only **`server.py`, `README.md` and `.gitignore`**. The allowlist ignores all other workspace content; do not force-add personal files, credentials, browser profiles, fixtures or generated output. Use concise imperative commit subjects and include verification results in pull requests.

## Technical references

- [Native audio-track API and compatibility](https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/audioTracks)
- [Text tracks and native WebVTT cues](https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/textTracks), [VTTCue](https://developer.mozilla.org/en-US/docs/Web/API/VTTCue)
- [Playback rates and reverse-playback limitations](https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/playbackRate)
- [Preload hints](https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/preload), [read-only buffered ranges](https://developer.mozilla.org/en-US/docs/Web/API/HTMLMediaElement/buffered), [Media Source Extensions](https://developer.mozilla.org/en-US/docs/Web/API/MediaSource)
- [Chromium codec/container support](https://www.chromium.org/audio-video/), [Firefox 145 Matroska support](https://www.firefox.com/en-US/firefox/145.0/releasenotes/)
- [Optional FFmpeg stream-copy/transcoding documentation](https://ffmpeg.org/ffmpeg.html)

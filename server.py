#!/usr/bin/env python3
"""Fshare — an offline, single-file LAN file browser (Python 3.9+).

Run from the directory you want to share:
    python /path/to/server.py
    python server.py --port 8080
    python server.py --password            # hidden password prompt
    python server.py --read-only
    python server.py --self-test

FSHARE_PASSWORD can supply the optional password through the environment.
Only the standard library is used. No files are created in the shared folder;
ZIPs live in the system temporary directory and are removed after transfer,
cancellation, expiry, error, or normal shutdown. HTTP is intended for a trusted
local network; it does not encrypt the password or file traffic.
"""

import argparse
import base64
import contextlib
import errno
import getpass
import hashlib
import hmac
import io
import json
import mimetypes
import os
import re
import secrets
import shutil
import signal
import socket
import stat
import struct
import sys
import tempfile
import threading
import time
import unittest
import unicodedata
import urllib.parse
import zipfile
from concurrent.futures import ThreadPoolExecutor
from http import cookies
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path


CHUNK = 1024 * 1024
MAX_BODY = 4 * 1024 * 1024
MAX_SELECTION = 20000
MAX_SUBTITLE_BYTES = 2 * 1024 * 1024
SESSION_TTL = 12 * 60 * 60
JOB_TTL = 15 * 60
COMPRESSED = {
    '.mp4', '.m4v', '.mkv', '.mov', '.webm', '.avi', '.mp3', '.m4a', '.aac',
    '.flac', '.ogg', '.opus', '.jpg', '.jpeg', '.png', '.gif', '.webp', '.avif',
    '.heic', '.zip', '.gz', '.7z', '.rar', '.pdf', '.woff', '.woff2',
}
MEDIA_TYPES = {
    '.mp4': 'video/mp4', '.m4v': 'video/mp4', '.mov': 'video/quicktime',
    '.webm': 'video/webm', '.mkv': 'video/matroska', '.avi': 'video/x-msvideo',
    '.mp3': 'audio/mpeg', '.m4a': 'audio/mp4', '.aac': 'audio/aac',
    '.wav': 'audio/wav', '.flac': 'audio/flac', '.ogg': 'audio/ogg',
    '.opus': 'audio/ogg', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
    '.png': 'image/png', '.gif': 'image/gif', '.webp': 'image/webp',
    '.avif': 'image/avif', '.svg': 'image/svg+xml', '.bmp': 'image/bmp',
    '.ico': 'image/x-icon', '.heic': 'image/heic', '.tif': 'image/tiff',
    '.tiff': 'image/tiff',
}


class Problem(Exception):
    def __init__(self, status, message):
        super().__init__(message)
        self.status = status


def subtitle_text(raw, encoding='auto'):
    """Decode a bounded sidecar; never interpret its contents as HTML."""
    if len(raw) > MAX_SUBTITLE_BYTES:
        raise Problem(413, 'Subtitles must be no larger than 2 MB.')
    if encoding not in ('auto', 'utf-8', 'windows-1256', 'windows-1252'):
        raise Problem(400, 'Unsupported subtitle encoding.')
    try:
        if encoding == 'auto':
            if raw.startswith((b'\xff\xfe', b'\xfe\xff')):
                text = raw.decode('utf-16')
            else:
                try:
                    text = raw.decode('utf-8-sig')
                except UnicodeDecodeError:
                    text = raw.decode('cp1256')
        else:
            text = raw.decode({'utf-8': 'utf-8-sig', 'windows-1256': 'cp1256',
                               'windows-1252': 'cp1252'}[encoding])
    except UnicodeError:
        raise Problem(422, 'Unable to decode this subtitle. Choose its encoding or save it as UTF-8.')
    if '\x00' in text:
        raise Problem(422, 'This is not a supported text subtitle. Save it as UTF-8 SRT or WebVTT.')
    return text


def media_options(root, relative):
    """Discover sidecars only inside the selected media file's safe parent."""
    with root.open_file(relative):
        _, kind = file_type(relative)
        if kind not in ('video', 'audio'):
            raise Problem(400, 'Select a video or audio file.')
    parent, _, name = relative.rpartition('/')
    stem = unicodedata.normalize('NFKC', os.path.splitext(name)[0]).casefold()
    subtitles, audio = [], []
    for item in root.list(parent):
        if item['blocked'] or item['kind'] == 'folder' or item['path'] == relative:
            continue
        candidate, extension = os.path.splitext(item['name'])
        candidate = unicodedata.normalize('NFKC', candidate).casefold()
        if extension.casefold() in ('.srt', '.vtt') and (candidate == stem or candidate.startswith(stem + '.')):
            subtitles.append(dict(name=item['name'], path=item['path'], size=item['size']))
        if item['kind'] == 'audio':
            audio.append(dict(name=item['name'], path=item['path'], mime=item['mime'], size=item['size']))
    subtitles.sort(key=lambda item: (os.path.splitext(item['name'])[0].casefold() != stem, item['name'].casefold()))
    audio.sort(key=lambda item: (not unicodedata.normalize('NFKC', item['name']).casefold().startswith(stem), item['name'].casefold()))
    return dict(subtitles=subtitles, audio=audio)


def friendly_error(exc):
    if isinstance(exc, Problem):
        return str(exc)
    if isinstance(exc, PermissionError):
        return 'Permission denied. Check the file permissions on the host computer.'
    if isinstance(exc, FileNotFoundError):
        return 'An item no longer exists. Refresh the folder and try again.'
    if isinstance(exc, OSError) and exc.errno in (errno.ENOSPC, errno.EDQUOT):
        return 'Not enough free space in the host computer\'s temporary directory.'
    if isinstance(exc, OSError) and exc.errno in (errno.ELOOP, errno.ENOTDIR):
        return 'This path is unavailable; symbolic links are not accessible.'
    if isinstance(exc, OSError) and exc.errno == errno.ENAMETOOLONG:
        return 'This path exceeds the host filesystem\'s supported length.'
    return 'The operation could not be completed. Refresh and try again.'


def blocked_stat(info):
    return (stat.S_ISLNK(info.st_mode) or
            bool(getattr(info, 'st_file_attributes', 0) & 0x400))


def native_path(path):
    path = os.path.realpath(os.path.abspath(path))
    if os.name == 'nt' and not path.startswith('\\\\?\\'):
        return ('\\\\?\\UNC\\' + path[2:]) if path.startswith('\\\\') else ('\\\\?\\' + path)
    return path


def archive_name(relative):
    """Keep Unicode, escape special names so ZIPs cannot create Windows paths."""
    result = []
    for part in relative.split('/'):
        encoded = ''.join('%%%02X' % ord(c) if c in '%\\:<>"|?*' or ord(c) < 32 else c for c in part)
        if encoded.endswith((' ', '.')):
            encoded = encoded[:-1] + '%%%02X' % ord(encoded[-1])
        base = part.split('.')[0].rstrip(' ').upper()
        if re.fullmatch(r'(CON|PRN|AUX|NUL|COM[1-9¹²³]|LPT[1-9¹²³])', base):
            encoded = '%%%02X' % ord(encoded[0]) + encoded[1:]
        result.append(encoded)
    return '/'.join(result)


def revision(info):
    data = '%s:%s:%s:%s:%s:%s' % (
        info.st_dev, info.st_ino, info.st_size,
        info.st_mtime_ns, info.st_ctime_ns, stat.S_IFMT(info.st_mode))
    return hashlib.sha256(data.encode('ascii')).hexdigest()[:24]


def file_type(name):
    ext = os.path.splitext(name)[1].lower()
    mime = MEDIA_TYPES.get(ext) or mimetypes.guess_type(name)[0] or 'application/octet-stream'
    group = mime.split('/')[0]
    kind = group if group in ('image', 'video', 'audio') else 'file'
    return mime, kind


def byte_label(size):
    value = float(size)
    for unit in ('B', 'KB', 'MB', 'GB', 'TB'):
        if value < 1024 or unit == 'TB':
            return ('%d B' % value) if unit == 'B' else ('%.1f %s' % (value, unit))
        value /= 1024


if os.name == 'nt':
    # Windows directory handles, opened without FILE_SHARE_DELETE, pin every
    # ancestor while we operate. OPEN_REPARSE_POINT prevents junction/symlink
    # traversal, including a concurrent replacement of the final component.
    import ctypes
    import msvcrt
    from ctypes import wintypes

    _kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    _create = _kernel.CreateFileW
    _create.argtypes = [wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD,
                        wintypes.LPVOID, wintypes.DWORD, wintypes.DWORD,
                        wintypes.HANDLE]
    _create.restype = wintypes.HANDLE
    _close = _kernel.CloseHandle
    _close.argtypes = [wintypes.HANDLE]
    _close.restype = wintypes.BOOL

    class _HandleInfo(ctypes.Structure):
        _fields_ = [('attributes', wintypes.DWORD),
                    ('created', wintypes.FILETIME), ('accessed', wintypes.FILETIME),
                    ('modified', wintypes.FILETIME), ('volume', wintypes.DWORD),
                    ('size_high', wintypes.DWORD), ('size_low', wintypes.DWORD),
                    ('links', wintypes.DWORD), ('index_high', wintypes.DWORD),
                    ('index_low', wintypes.DWORD)]

    _getinfo = _kernel.GetFileInformationByHandle
    _getinfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(_HandleInfo)]
    _getinfo.restype = wintypes.BOOL

    def windows_handle(path, directory):
        flags = 0x00200000 | (0x02000000 if directory else 0x08000000)
        handle = _create(path, 0x80000000, 3, None, 3, flags, None)
        if handle == ctypes.c_void_p(-1).value:
            raise ctypes.WinError(ctypes.get_last_error())
        info = _HandleInfo()
        if not _getinfo(handle, ctypes.byref(info)):
            code = ctypes.get_last_error()
            _close(handle)
            raise ctypes.WinError(code)
        if info.attributes & 0x400 or bool(info.attributes & 0x10) != directory:
            _close(handle)
            raise Problem(403, 'Symbolic links, junctions, and special files are not accessible.')
        return handle


class SafeRoot:
    """Root-relative, no-follow operations; POSIX operations use directory FDs."""

    def __init__(self, root):
        original = os.path.realpath(os.path.abspath(root))
        self.name = os.path.basename(original.rstrip(os.sep)) or original
        self.root = native_path(original)
        self.excluded = []

    def parts(self, relative):
        if not isinstance(relative, str) or len(relative) > 32760:
            raise Problem(400, 'Invalid path.')
        if not relative:
            return []
        parts = relative.split('/')
        if any(part in ('', '.', '..') or '\x00' in part for part in parts):
            raise Problem(403, 'Paths must stay inside the shared folder.')
        if os.name == 'nt' and any('\\' in part or ':' in part for part in parts):
            raise Problem(403, 'Windows path separators and device paths are not accessible.')
        if os.name == 'nt' and any(p.endswith((' ', '.')) for p in parts):
            raise Problem(403, 'Ambiguous Windows paths are not accessible.')
        if os.name == 'nt' and any(re.fullmatch(r'(CON|PRN|AUX|NUL|COM[1-9¹²³]|LPT[1-9¹²³])', p.split('.')[0].upper()) for p in parts):
            raise Problem(403, 'Windows device paths are not accessible.')
        full = os.path.normcase(os.path.join(self.root, *parts))
        for excluded in self.excluded:
            try:
                if os.path.commonpath([full, excluded]) == excluded:
                    raise Problem(403, 'Application temporary files are not accessible.')
            except ValueError:
                pass
        return parts

    @contextlib.contextmanager
    def directory(self, relative=''):
        parts = self.parts(relative)
        if os.name == 'nt':
            handles = []
            path = self.root
            try:
                handles.append(windows_handle(path, True))
                for part in parts:
                    path = os.path.join(path, part)
                    handles.append(windows_handle(path, True))
                yield path
            finally:
                for handle in reversed(handles):
                    _close(handle)
        else:
            flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
            fd = os.open(self.root, flags)
            try:
                for part in parts:
                    next_fd = os.open(part, flags, dir_fd=fd)
                    os.close(fd)
                    fd = next_fd
                yield fd
            finally:
                os.close(fd)

    def at_stat(self, directory, name):
        if os.name == 'nt':
            return os.lstat(os.path.join(directory, name))
        return os.stat(name, dir_fd=directory, follow_symlinks=False)

    def checked_stat(self, relative):
        parts = self.parts(relative)
        if not parts:
            raise Problem(403, 'The shared root cannot be selected or deleted.')
        parent = '/'.join(parts[:-1])
        with self.directory(parent) as directory:
            info = self.at_stat(directory, parts[-1])
            if blocked_stat(info) or not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode)):
                raise Problem(403, 'Symbolic links, junctions, and special files are not accessible.')
            return info

    @contextlib.contextmanager
    def open_file(self, relative):
        parts = self.parts(relative)
        if not parts:
            raise Problem(400, 'Select a file.')
        with self.directory('/'.join(parts[:-1])) as directory:
            if os.name == 'nt':
                handle = windows_handle(os.path.join(directory, parts[-1]), False)
                try:
                    fd = msvcrt.open_osfhandle(handle, os.O_RDONLY | os.O_BINARY)
                except Exception:
                    _close(handle)
                    raise
            else:
                fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
            try:
                if not stat.S_ISREG(os.fstat(fd).st_mode):
                    raise Problem(403, 'Only regular files can be opened.')
                with os.fdopen(fd, 'rb', closefd=False) as stream:
                    yield stream
            finally:
                os.close(fd)

    def list(self, relative):
        result = []
        with self.directory(relative) as directory:
            with os.scandir(directory) as scan:
                for entry in scan:
                    path = relative + '/' + entry.name if relative else entry.name
                    try:
                        self.parts(path)
                    except Problem:
                        continue
                    try:
                        # DirEntry.stat() omits inode/device fields on Windows;
                        # use the same full stat as deletion and ZIP validation.
                        info = self.at_stat(directory, entry.name)
                        is_dir = stat.S_ISDIR(info.st_mode) and not blocked_stat(info)
                        blocked = blocked_stat(info) or not (is_dir or stat.S_ISREG(info.st_mode))
                        mime, kind = file_type(entry.name)
                        result.append(dict(name=entry.name, path=path,
                                           kind='folder' if is_dir else kind,
                                           mime=mime, size=None if is_dir else info.st_size,
                                           modified=info.st_mtime, version=revision(info),
                                           blocked=blocked))
                    except OSError:
                        result.append(dict(name=entry.name, path=path, kind='file',
                                           mime='application/octet-stream', size=None,
                                           modified=None, version='', blocked=True))
        return result

    def walk(self, paths, cancelled):
        stack = list(reversed(paths))
        while stack:
            if cancelled.is_set():
                raise Problem(409, 'ZIP preparation cancelled.')
            path = stack.pop()
            info = self.checked_stat(path)
            is_dir = stat.S_ISDIR(info.st_mode)
            yield path, info, is_dir, False
            if is_dir:
                with self.directory(path) as directory:
                    with os.scandir(directory) as scan:
                        children = sorted(list(scan), key=lambda e: e.name.casefold(), reverse=True)
                        for child in children:
                            child_path = path + '/' + child.name
                            child_info = self.at_stat(directory, child.name)
                            try:
                                self.parts(child_path)
                            except Problem:
                                yield child_path, child_info, False, True
                                continue
                            if blocked_stat(child_info) or not (stat.S_ISDIR(child_info.st_mode) or stat.S_ISREG(child_info.st_mode)):
                                yield child_path, child_info, False, True
                            else:
                                stack.append(child_path)

    def delete(self, relative, expected):
        parts = self.parts(relative)
        if not parts:
            raise Problem(403, 'The shared root cannot be deleted.')
        with self.directory('/'.join(parts[:-1])) as parent:
            info = self.at_stat(parent, parts[-1])
            if revision(info) != expected:
                raise Problem(409, 'This item changed since confirmation. Refresh and try again.')
            if blocked_stat(info):
                raise Problem(403, 'Symbolic links and junctions cannot be selected.')
            self._delete_at(parent, parts[-1], expected)

    def _delete_at(self, parent, name, expected=None):
        info = self.at_stat(parent, name)
        if expected is not None and revision(info) != expected:
            raise Problem(409, 'An item changed during deletion. Refresh and try again.')
        is_dir = stat.S_ISDIR(info.st_mode)
        if blocked_stat(info):
            # Remove a nested link itself, never its target. Windows junctions
            # require rmdir rather than unlink; both remove only the link.
            if os.name == 'nt' and is_dir:
                os.rmdir(os.path.join(parent, name))
            elif os.name == 'nt':
                os.unlink(os.path.join(parent, name))
            else:
                os.unlink(name, dir_fd=parent)
        elif is_dir:
            if os.name == 'nt':
                path = os.path.join(parent, name)
                handle = windows_handle(path, True)
                try:
                    if revision(os.lstat(path)) != revision(info):
                        raise Problem(409, 'A folder changed during deletion. Refresh and try again.')
                    with os.scandir(path) as scan:
                        names = [(entry.name, revision(self.at_stat(path, entry.name))) for entry in scan]
                    for child, version in names:
                        self._delete_at(path, child, version)
                finally:
                    _close(handle)
                remaining = os.lstat(path)
                if blocked_stat(remaining) or (remaining.st_dev, remaining.st_ino) != (info.st_dev, info.st_ino):
                    raise Problem(409, 'A folder was replaced during deletion. Refresh and try again.')
                os.rmdir(path)
            else:
                fd = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent)
                try:
                    if revision(os.fstat(fd)) != revision(info):
                        raise Problem(409, 'A folder changed during deletion. Refresh and try again.')
                    with os.scandir(fd) as scan:
                        names = [(entry.name, revision(self.at_stat(fd, entry.name))) for entry in scan]
                    for child, version in names:
                        self._delete_at(fd, child, version)
                finally:
                    os.close(fd)
                remaining = self.at_stat(parent, name)
                if blocked_stat(remaining) or (remaining.st_dev, remaining.st_ino) != (info.st_dev, info.st_ino):
                    raise Problem(409, 'A folder was replaced during deletion. Refresh and try again.')
                os.rmdir(name, dir_fd=parent)
        elif stat.S_ISREG(info.st_mode):
            if os.name == 'nt':
                os.unlink(os.path.join(parent, name))
            else:
                os.unlink(name, dir_fd=parent)
        else:
            raise Problem(403, 'Special files cannot be deleted.')


class ZipJobs:
    def __init__(self, root):
        self.root = root
        self.temp = tempfile.TemporaryDirectory(prefix='fshare-')
        root.excluded.append(os.path.normcase(native_path(self.temp.name)))
        self.lock = threading.RLock()
        self.jobs = {}
        self.pool = ThreadPoolExecutor(max_workers=2, thread_name_prefix='fshare-zip')
        self.stopping = threading.Event()

    def update(self, job, **values):
        with self.lock:
            job.update(values)

    def create(self, owner, base, paths, skipped=0):
        self.root.parts(base)
        paths = sorted(set(paths), key=lambda p: (p.count('/'), p))
        selected = []
        selected_set = set()
        for path in paths:
            if base and not path.startswith(base + '/'):
                raise Problem(403, 'The selection must be inside the current folder.')
            parts = path.split('/')
            if not any('/'.join(parts[:i]) in selected_set for i in range(1, len(parts))):
                self.root.checked_stat(path)
                selected.append(path)
                selected_set.add(path)
        if not selected:
            raise Problem(400, 'There are no downloadable items in this folder.')
        with self.lock:
            if len(self.jobs) >= 32:
                for old_token, old_job in list(self.jobs.items()):
                    if old_job['state'] in ('error', 'cancelled') and not old_job['temp_path']:
                        self.jobs.pop(old_token)
                if len(self.jobs) >= 32:
                    raise Problem(429, 'Too many ZIP jobs. Please try again later.')
            busy = [j for j in self.jobs.values() if j['state'] not in ('error', 'cancelled')]
            if len(busy) >= 8 or sum(j['owner'] == owner for j in busy) >= 2:
                raise Problem(429, 'Finish or cancel an existing ZIP before starting another.')
            token = secrets.token_urlsafe(24)
            label = os.path.basename(selected[0]) if len(selected) == 1 else (os.path.basename(base) or self.root.name)
            job = dict(id=token, owner=owner, base=base, paths=selected,
                       name=label + '.zip', state='queued', bytes=0, total_bytes=0,
                       files=0, total_files=0, skipped=skipped, renamed=0, current='', error='',
                       created=time.monotonic(), touched=time.monotonic(),
                       cancel=threading.Event(), temp_path=None)
            self.jobs[token] = job
            self.pool.submit(self.build, job)
            return self.public(job)

    def public(self, job):
        return {k: job[k] for k in ('id', 'name', 'state', 'bytes', 'total_bytes',
                                    'files', 'total_files', 'skipped', 'renamed', 'current', 'error')}

    def get(self, token, owner):
        with self.lock:
            job = self.jobs.get(token)
            if not job or job['owner'] != owner:
                raise Problem(404, 'This ZIP has expired. Prepare it again.')
            job['touched'] = time.monotonic()
            return job

    def build(self, job):
        try:
            self.update(job, state='scanning')
            total = count = 0
            skipped = job['skipped']
            for path, info, is_dir, blocked in self.root.walk(job['paths'], job['cancel']):
                if blocked:
                    skipped += 1
                elif not is_dir:
                    total += info.st_size
                    count += 1
                self.update(job, total_bytes=total, total_files=count, skipped=skipped, current=path)
            needed = total + (count + 1) * 512 + 65536
            if shutil.disk_usage(self.temp.name).free < needed:
                raise Problem(507, 'ZIP preparation needs about %s of free temporary space.' % byte_label(needed))
            fd, path = tempfile.mkstemp(suffix='.zip', dir=self.temp.name)
            os.close(fd)
            self.update(job, temp_path=path, state='building')
            written = completed = 0
            renamed = 0
            with zipfile.ZipFile(path, 'w', allowZip64=True, compression=zipfile.ZIP_DEFLATED, compresslevel=1) as archive:
                for relative, info, is_dir, blocked in self.root.walk(job['paths'], job['cancel']):
                    if blocked:
                        continue
                    name = relative[len(job['base']) + 1:] if job['base'] else relative
                    compatible_name = archive_name(name)
                    if compatible_name != name:
                        renamed += 1
                        self.update(job, renamed=renamed)
                    name = compatible_name
                    self.update(job, current=relative)
                    stamp = time.localtime(info.st_mtime)[:6]
                    if stamp[0] < 1980:
                        stamp = (1980, 1, 1, 0, 0, 0)
                    elif stamp[0] > 2107:
                        stamp = (2107, 12, 31, 23, 59, 58)
                    zi = zipfile.ZipInfo(name + ('/' if is_dir else ''), date_time=stamp)
                    zi.create_system = 3
                    zi.external_attr = ((0o40755 if is_dir else 0o100644) << 16) | (0x10 if is_dir else 0)
                    if is_dir:
                        archive.writestr(zi, b'')
                        continue
                    zi.compress_type = zipfile.ZIP_STORED if os.path.splitext(name)[1].lower() in COMPRESSED else zipfile.ZIP_DEFLATED
                    zi._compresslevel = 1  # Compatible with Python 3.9's ZipInfo.
                    zi.file_size = info.st_size
                    with self.root.open_file(relative) as source:
                        if revision(os.fstat(source.fileno())) != revision(info):
                            raise Problem(409, 'A file changed during ZIP preparation. Please try again.')
                        with archive.open(zi, 'w', force_zip64=True) as target:
                            while True:
                                if job['cancel'].is_set():
                                    raise Problem(409, 'ZIP preparation cancelled.')
                                chunk = source.read(CHUNK)
                                if not chunk:
                                    break
                                target.write(chunk)
                                written += len(chunk)
                                self.update(job, bytes=written)
                        if revision(os.fstat(source.fileno())) != revision(info):
                            raise Problem(409, 'A file changed during ZIP preparation. Please try again.')
                    completed += 1
                    self.update(job, files=completed)
            with self.lock:
                if job['cancel'].is_set():
                    raise Problem(409, 'ZIP preparation cancelled.')
                self.update(job, state='ready', current='', touched=time.monotonic())
        except Exception as exc:
            self.update(job, state='cancelled' if job['cancel'].is_set() else 'error', error=friendly_error(exc), current='')
            self.remove_file(job)

    def remove_file(self, job):
        with self.lock:
            path = job.get('temp_path')
            if path:
                try:
                    os.unlink(path)
                except FileNotFoundError:
                    pass
                except OSError:
                    return  # Keep the path for the next cleanup pass.
                job['temp_path'] = None

    def cancel(self, job):
        with self.lock:
            job['cancel'].set()
            if job['state'] == 'ready':
                self.remove_file(job)
                job['state'] = 'cancelled'

    def sweep(self):
        with self.lock:
            for token, job in list(self.jobs.items()):
                if time.monotonic() - job['touched'] > JOB_TTL and job['state'] != 'downloading':
                    self.cancel(job)
                    if job['state'] in ('ready', 'cancelled', 'error'):
                        self.remove_file(job)
                        if not job['temp_path']:
                            self.jobs.pop(token, None)

    def close(self):
        self.stopping.set()
        with self.lock:
            for job in self.jobs.values():
                job['cancel'].set()
        self.pool.shutdown(wait=True)
        self.temp.cleanup()


def local_ips():
    addresses = set()
    try:
        for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            addresses.add(info[4][0])
    except OSError:
        pass
    # UDP connect selects a local interface without sending traffic.
    for destination in ('192.168.1.1', '10.255.255.255', '172.16.0.1'):
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as probe:
                probe.connect((destination, 9))
                addresses.add(probe.getsockname()[0])
        except OSError:
            pass
    if sys.platform.startswith('linux') or sys.platform == 'darwin':
        try:
            import fcntl
            for _, name in socket.if_nameindex():
                try:
                    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as probe:
                        request = 0x8915 if sys.platform.startswith('linux') else 0xc0206921
                        data = fcntl.ioctl(probe.fileno(), request, struct.pack('256s', name.encode()[:15]))
                        addresses.add(socket.inet_ntoa(data[20:24]))
                except OSError:
                    continue
        except (OSError, ImportError):
            pass
    return sorted(ip for ip in addresses if not ip.startswith('127.') and ip != '0.0.0.0')


class FileServer(ThreadingHTTPServer):
    daemon_threads = False
    allow_reuse_address = True
    request_queue_size = 128

    def __init__(self, address, root, password='', read_only=False):
        self.root = SafeRoot(root)
        self.read_only = read_only
        self.salt = secrets.token_bytes(16)
        self.password_hash = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), self.salt, 200000) if password else None
        self.sessions = {}
        self.plans = {}
        self.failures = {}
        self.state_lock = threading.RLock()
        self.delete_lock = threading.Lock()
        self.slots = threading.BoundedSemaphore(64)
        self.active_lock = threading.Lock()
        self.active_requests = set()
        self.stop_event = threading.Event()
        ips = local_ips()
        self.hosts = set(ips + ['localhost', '127.0.0.1', socket.gethostname().lower(),
                               socket.gethostname().lower() + '.local'])
        if address[0] not in ('0.0.0.0', ''):
            self.hosts.add(address[0].lower())
        super().__init__(address, Handler)
        self.jobs = ZipJobs(self.root)
        self.cleaner = threading.Thread(target=self.maintenance, daemon=True, name='fshare-cleanup')
        self.cleaner.start()

    def process_request(self, request, client_address):
        if not self.slots.acquire(False):
            try:
                request.sendall(b'HTTP/1.1 503 Service Unavailable\r\nConnection: close\r\nContent-Length: 0\r\nRetry-After: 2\r\n\r\n')
            except OSError:
                pass
            self.shutdown_request(request)
            return
        try:
            with self.active_lock:
                self.active_requests.add(request)
            super().process_request(request, client_address)
        except Exception:
            with self.active_lock:
                self.active_requests.discard(request)
            self.slots.release()
            raise

    def process_request_thread(self, request, client_address):
        try:
            super().process_request_thread(request, client_address)
        finally:
            with self.active_lock:
                self.active_requests.discard(request)
            self.slots.release()

    def maintenance(self):
        while not self.stop_event.wait(15):
            self.jobs.sweep()
            now = time.monotonic()
            with self.state_lock:
                for token, data in list(self.sessions.items()):
                    if now > data['expires']:
                        self.sessions.pop(token, None)
                for token, plan in list(self.plans.items()):
                    if now > plan['expires']:
                        self.plans.pop(token, None)
                for ip, data in list(self.failures.items()):
                    if now - data[1] > 60:
                        self.failures.pop(ip, None)

    def new_session(self):
        token = secrets.token_urlsafe(32)
        data = dict(csrf=secrets.token_urlsafe(32), expires=time.monotonic() + SESSION_TTL)
        with self.state_lock:
            if len(self.sessions) >= 512:
                oldest = min(self.sessions, key=lambda t: self.sessions[t]['expires'])
                self.sessions.pop(oldest)
            self.sessions[token] = data
        return token, data

    def server_close(self):
        self.stop_event.set()
        if hasattr(self, 'jobs'):
            with self.jobs.lock:
                for job in self.jobs.jobs.values():
                    job['cancel'].set()
        with self.active_lock:
            for request in self.active_requests:
                try:
                    request.shutdown(socket.SHUT_RDWR)
                except OSError:
                    pass
        super().server_close()
        if hasattr(self, 'jobs'):
            self.jobs.close()


def attachment(name, disposition='attachment'):
    fallback = ''.join(c if 32 <= ord(c) < 127 and c not in ('"', '\\', ';') else '_' for c in name)
    return '%s; filename="%s"; filename*=UTF-8\'\'%s' % (disposition, fallback, urllib.parse.quote(name, safe=''))


def parse_range(value, size):
    """Single byte ranges; valid multi-range requests are safely ignored."""
    if not value or ',' in value or not value.startswith('bytes='):
        return None
    match = re.fullmatch(r'bytes=(\d*)-(\d*)', value)
    if not match or not any(match.groups()) or size == 0:
        raise Problem(416, 'Requested byte range is not available.')
    first, last = match.groups()
    if len(first) > 20 or len(last) > 20:
        raise Problem(416, 'Requested byte range is not available.')
    if not first:
        length = int(last)
        if length <= 0:
            raise Problem(416, 'Requested byte range is not available.')
        return max(0, size - length), size - 1
    start = int(first)
    end = min(int(last), size - 1) if last else size - 1
    if start >= size or end < start:
        raise Problem(416, 'Requested byte range is not available.')
    return start, end


class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'
    server_version = 'Fshare/1.0'
    sys_version = ''

    def setup(self):
        super().setup()
        self.connection.settimeout(30)
        self.responded = False

    def log_message(self, format, *args):
        # Do not log cookies, passwords, tokens, or user-controlled paths.
        pass

    def end_headers(self):
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('X-Frame-Options', 'DENY')
        self.send_header('Referrer-Policy', 'no-referrer')
        self.send_header('Cross-Origin-Resource-Policy', 'same-origin')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Connection', 'close')
        self.close_connection = True
        self.responded = True
        super().end_headers()

    def json(self, data, status=200, extra=None):
        body = json.dumps(data, ensure_ascii=True, separators=(',', ':')).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        for key, value in (extra or {}).items():
            self.send_header(key, value)
        self.end_headers()
        if self.command != 'HEAD':
            self.wfile.write(body)

    def body(self):
        if self.headers.get('Transfer-Encoding'):
            raise Problem(400, 'Chunked request bodies are not supported.')
        if self.headers.get('Content-Type', '').split(';')[0].strip().lower() != 'application/json':
            raise Problem(415, 'Use an application/json request.')
        try:
            length = int(self.headers.get('Content-Length', '0'))
        except ValueError:
            raise Problem(400, 'Invalid request size.')
        if not 0 < length <= MAX_BODY:
            raise Problem(413, 'The request is too large or empty.')
        raw = self.rfile.read(length)
        if len(raw) != length:
            raise Problem(400, 'Incomplete request body.')
        try:
            result = json.loads(raw)
        except (ValueError, UnicodeDecodeError):
            raise Problem(400, 'Invalid JSON request.')
        if not isinstance(result, dict):
            raise Problem(400, 'Expected a JSON object.')
        return result

    def request_guard(self):
        host = self.headers.get('Host', '')
        try:
            if len(self.headers.get_all('Host', [])) != 1 or not self.path.startswith('/') or self.path.startswith('//'):
                raise ValueError()
            parsed = urllib.parse.urlsplit('//' + host)
            port = parsed.port or 80
            if (parsed.username or parsed.password or parsed.path or
                    (parsed.hostname or '').lower() not in self.server.hosts or
                    port != self.server.server_port):
                raise ValueError()
        except ValueError:
            raise Problem(403, 'Use the local address printed by the server.')
        if self.headers.get('Sec-Fetch-Site') in ('cross-site', 'same-site'):
            raise Problem(403, 'Cross-origin requests are not allowed.')
        origin = self.headers.get('Origin')
        if origin and origin != 'http://' + host:
            raise Problem(403, 'Cross-origin requests are not allowed.')

    def session(self, required=True):
        jar = cookies.SimpleCookie()
        try:
            jar.load(self.headers.get('Cookie', ''))
            token = jar['fshare_session'].value if 'fshare_session' in jar else ''
        except cookies.CookieError:
            token = ''
        with self.server.state_lock:
            data = self.server.sessions.get(token)
            if data and time.monotonic() > data['expires']:
                self.server.sessions.pop(token, None)
                data = None
        if required and not data:
            raise Problem(401, 'Sign in to continue.')
        return token, data

    def csrf(self, data):
        if not hmac.compare_digest(self.headers.get('X-CSRF-Token', '').encode('utf-8'), data['csrf'].encode('ascii')):
            raise Problem(403, 'Session verification failed. Reload the page and try again.')

    def dispatch(self):
        self.request_guard()
        parsed = urllib.parse.urlsplit(self.path)
        route = parsed.path
        query = urllib.parse.parse_qs(parsed.query, keep_blank_values=True)
        relative = query.get('path', [''])[0]
        if self.command in ('GET', 'HEAD'):
            if route == '/':
                nonce = secrets.token_urlsafe(24)
                body = PAGE.replace('__NONCE__', nonce).encode('utf-8')
                self.send_response(200)
                self.send_header('Content-Type', 'text/html; charset=utf-8')
                self.send_header('Content-Length', str(len(body)))
                self.send_header('Content-Security-Policy', "default-src 'none'; script-src 'nonce-%s'; style-src 'nonce-%s'; style-src-attr 'unsafe-inline'; img-src 'self' data:; media-src 'self' blob:; connect-src 'self'; font-src 'none'; object-src 'none'; base-uri 'none'; form-action 'self'; frame-ancestors 'none'" % (nonce, nonce))
                self.end_headers()
                if self.command != 'HEAD':
                    self.wfile.write(body)
                return
            if route == '/favicon.ico':
                self.send_response(204)
                self.send_header('Content-Length', '0')
                self.end_headers()
                return
            if route == '/api/session':
                token, data = self.session(False)
                extra = {}
                if not data and not self.server.password_hash:
                    token, data = self.server.new_session()
                    extra['Set-Cookie'] = self.session_cookie(token)
                self.json(dict(authenticated=bool(data), protected=bool(self.server.password_hash),
                               csrf=data['csrf'] if data else '', read_only=self.server.read_only,
                               root_name=self.server.root.name if data else ''), extra=extra)
                return
            token, data = self.session()
            if route == '/api/list':
                self.json(dict(path=relative, root_name=self.server.root.name, items=self.server.root.list(relative)))
            elif route == '/api/media':
                self.json(media_options(self.server.root, relative))
            elif route == '/api/subtitle':
                if os.path.splitext(relative)[1].casefold() not in ('.srt', '.vtt'):
                    raise Problem(400, 'Select an SRT or WebVTT subtitle.')
                with self.server.root.open_file(relative) as source:
                    if os.fstat(source.fileno()).st_size > MAX_SUBTITLE_BYTES:
                        raise Problem(413, 'Subtitles must be no larger than 2 MB.')
                    raw = source.read(MAX_SUBTITLE_BYTES + 1)
                self.json(dict(text=subtitle_text(raw, query.get('encoding', ['auto'])[0])))
            elif route == '/file':
                self.file(relative, query.get('download', ['0'])[0] == '1')
            elif re.fullmatch(r'/api/zip/[A-Za-z0-9_-]+', route):
                with self.server.jobs.lock:
                    job = self.server.jobs.get(route.rsplit('/', 1)[-1], token)
                    self.json(self.server.jobs.public(job))
            elif re.fullmatch(r'/zip/[A-Za-z0-9_-]+', route):
                self.download_zip(route.rsplit('/', 1)[-1], token)
            else:
                raise Problem(404, 'This address does not exist.')
            return
        if self.command == 'POST':
            if route == '/api/login':
                self.login(self.body())
                return
            token, data = self.session()
            self.csrf(data)
            body = self.body()
            if route == '/api/logout':
                with self.server.state_lock:
                    self.server.sessions.pop(token, None)
                with self.server.jobs.lock:
                    for job in self.server.jobs.jobs.values():
                        if job['owner'] == token:
                            self.server.jobs.cancel(job)
                self.json(dict(ok=True), extra={'Set-Cookie': self.session_cookie('', 0)})
            elif route == '/api/zip':
                base = body.get('path', '')
                skipped = 0
                if body.get('all') is True:
                    items = self.server.root.list(base)
                    paths = [item['path'] for item in items if not item['blocked']]
                    skipped = sum(item['blocked'] for item in items)
                else:
                    paths = self.selection(body.get('paths'))
                self.json(self.server.jobs.create(token, base, paths, skipped), status=202)
            elif re.fullmatch(r'/api/zip/[A-Za-z0-9_-]+/cancel', route):
                job = self.server.jobs.get(route.split('/')[3], token)
                self.server.jobs.cancel(job)
                self.json(dict(ok=True))
            elif route == '/api/delete/plan':
                self.delete_plan(token, body)
            elif route == '/api/delete':
                self.delete_confirm(token, body)
            else:
                raise Problem(404, 'This address does not exist.')
            return
        raise Problem(405, 'Method not allowed.')

    @staticmethod
    def selection(paths):
        if (not isinstance(paths, list) or not paths or len(paths) > MAX_SELECTION or
                any(not isinstance(p, str) for p in paths)):
            raise Problem(400, 'Select between 1 and %d items.' % MAX_SELECTION)
        return paths

    @staticmethod
    def session_cookie(token, max_age=SESSION_TTL):
        return 'fshare_session=%s; Path=/; HttpOnly; SameSite=Strict; Max-Age=%d' % (token, max_age)

    def login(self, body):
        password = body.get('password', '')
        if not isinstance(password, str) or len(password) > 4096:
            raise Problem(400, 'Invalid password.')
        ip = self.client_address[0]
        with self.server.state_lock:
            failures, started = self.server.failures.get(ip, (0, time.monotonic()))
            if time.monotonic() - started > 60:
                failures, started = 0, time.monotonic()
            if failures >= 5:
                raise Problem(429, 'Too many attempts. Try again in a minute.')
            expected = self.server.password_hash
            try:
                candidate = hashlib.pbkdf2_hmac('sha256', password.encode('utf-8'), self.server.salt, 200000) if expected else None
            except UnicodeEncodeError:
                raise Problem(400, 'Invalid password.')
            if expected and not hmac.compare_digest(expected, candidate):
                if len(self.server.failures) >= 1024:
                    self.server.failures.clear()
                self.server.failures[ip] = (failures + 1, started)
                raise Problem(401, 'Incorrect password.')
            self.server.failures.pop(ip, None)
        old, _ = self.session(False)
        with self.server.state_lock:
            self.server.sessions.pop(old, None)
        token, data = self.server.new_session()
        self.json(dict(ok=True, csrf=data['csrf']), extra={'Set-Cookie': self.session_cookie(token)})

    def file(self, relative, download):
        with self.server.root.open_file(relative) as source:
            info = os.fstat(source.fileno())
            size = info.st_size
            tag = '"%s"' % revision(info)
            range_header = self.headers.get('Range') if self.command != 'HEAD' else None
            if self.headers.get('If-Range') and self.headers['If-Range'] not in (tag, self.date_time_string(info.st_mtime)):
                range_header = None
            try:
                segment = parse_range(range_header, size)
            except Problem as exc:
                self.json(dict(error=str(exc)), 416, {'Content-Range': 'bytes */%d' % size, 'Accept-Ranges': 'bytes'})
                return
            start, end = segment if segment else (0, size - 1)
            mime, kind = file_type(relative)
            inline = not download and kind in ('image', 'video', 'audio')
            self.send_response(206 if segment else 200)
            self.send_header('Content-Type', mime if inline else 'application/octet-stream')
            self.send_header('Content-Disposition', attachment(relative.rsplit('/', 1)[-1], 'inline' if inline else 'attachment'))
            self.send_header('Content-Length', str(max(0, end - start + 1)))
            self.send_header('Accept-Ranges', 'bytes')
            self.send_header('ETag', tag)
            self.send_header('Last-Modified', self.date_time_string(info.st_mtime))
            self.send_header('Content-Security-Policy', "default-src 'none'; sandbox; frame-ancestors 'none'")
            if segment:
                self.send_header('Content-Range', 'bytes %d-%d/%d' % (start, end, size))
            self.end_headers()
            if self.command != 'HEAD':
                source.seek(start)
                self.copy_stream(source, max(0, end - start + 1))

    def copy_stream(self, source, length, cancel=None):
        while length:
            if self.server.stop_event.is_set() or (cancel and cancel.is_set()):
                break
            chunk = source.read(min(CHUNK, length))
            if not chunk:
                break
            self.wfile.write(chunk)
            length -= len(chunk)

    def download_zip(self, token, owner):
        jobs = self.server.jobs
        with jobs.lock:
            job = jobs.get(token, owner)
            if job['state'] != 'ready':
                raise Problem(409, 'This ZIP is not ready to download.')
            if self.command == 'HEAD':
                size = os.path.getsize(job['temp_path'])
            else:
                job['state'] = 'downloading'
                size = os.path.getsize(job['temp_path'])
        try:
            self.send_response(200)
            self.send_header('Content-Type', 'application/zip')
            self.send_header('Content-Length', str(size))
            self.send_header('Content-Disposition', attachment(job['name']))
            self.end_headers()
            if self.command != 'HEAD':
                with open(job['temp_path'], 'rb') as source:
                    self.copy_stream(source, size, job['cancel'])
        finally:
            if self.command != 'HEAD':
                jobs.remove_file(job)
                with jobs.lock:
                    jobs.jobs.pop(token, None)

    def delete_plan(self, owner, body):
        if self.server.read_only:
            raise Problem(403, 'Deletion is disabled in read-only mode.')
        items = body.get('items')
        if not isinstance(items, list) or not 0 < len(items) <= MAX_SELECTION:
            raise Problem(400, 'Select items to delete.')
        checked = []
        seen = set()
        for item in items:
            if not isinstance(item, dict):
                raise Problem(400, 'Invalid selection.')
            path = item.get('path')
            info = self.server.root.checked_stat(path)
            if item.get('version') != revision(info):
                raise Problem(409, 'An item changed since the folder was loaded. Refresh and try again.')
            if path not in seen:
                checked.append(dict(path=path, version=revision(info), folder=stat.S_ISDIR(info.st_mode)))
                seen.add(path)
        checked.sort(key=lambda item: (item['path'].count('/'), item['path']))
        checked = [item for item in checked if not any('/'.join(item['path'].split('/')[:i]) in seen for i in range(1, len(item['path'].split('/'))))]
        with self.server.state_lock:
            if len(self.server.plans) >= 128:
                raise Problem(429, 'Too many pending confirmations. Try again shortly.')
            token = secrets.token_urlsafe(24)
            self.server.plans[token] = dict(owner=owner, items=checked, expires=time.monotonic() + 120)
        self.json(dict(id=token, items=checked, expires_in=120))

    def delete_confirm(self, owner, body):
        if self.server.read_only:
            raise Problem(403, 'Deletion is disabled in read-only mode.')
        if body.get('confirm') != 'delete':
            raise Problem(400, 'Explicit confirmation is required.')
        with self.server.state_lock:
            token = body.get('id')
            if not isinstance(token, str):
                raise Problem(400, 'Invalid confirmation.')
            plan = self.server.plans.get(token)
            if not plan or plan['owner'] != owner or time.monotonic() > plan['expires']:
                raise Problem(409, 'Confirmation expired. Select the items again.')
            self.server.plans.pop(token)
        deleted, errors = [], []
        with self.server.delete_lock:
            for item in plan['items']:
                try:
                    self.server.root.delete(item['path'], item['version'])
                    deleted.append(item['path'])
                except Exception as exc:
                    message = friendly_error(exc)
                    if item['folder']:
                        message += ' Some contents may already have been deleted.'
                    errors.append(dict(path=item['path'], error=message))
        self.json(dict(deleted=deleted, errors=errors))

    def handle_method(self):
        try:
            self.dispatch()
        except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, TimeoutError):
            pass
        except Exception as exc:
            if not self.responded:
                status_code = exc.status if isinstance(exc, Problem) else (403 if isinstance(exc, PermissionError) or (isinstance(exc, OSError) and exc.errno in (errno.ELOOP, errno.ENOTDIR)) else 404 if isinstance(exc, FileNotFoundError) else 507 if isinstance(exc, OSError) and exc.errno in (errno.ENOSPC, errno.EDQUOT) else 500)
                try:
                    self.json(dict(error=friendly_error(exc)), status_code)
                except OSError:
                    pass
            else:
                self.close_connection = True

    do_GET = handle_method
    do_HEAD = handle_method
    do_POST = handle_method
    do_OPTIONS = handle_method


PAGE = r'''<!doctype html>
<html lang="en" data-theme="dark">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="color-scheme" content="dark light">
<title>Fshare · Your files, nearby</title>
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 64 64'%3E%3Crect width='64' height='64' rx='16' fill='%23c6ee87'/%3E%3Cpath d='M12 22h17l5 6h18v23H12z' fill='%23212c1d'/%3E%3C/svg%3E">
<style nonce="__NONCE__">
:root{color-scheme:dark;--bg:#111411;--panel:#191d19;--panel2:#202520;--hover:#292f28;--line:#30382f;--text:#f0f3eb;--muted:#9ba597;--accent:#c6ee87;--accent-text:#202e12;--red:#ff9b98;--shadow:0 24px 90px #0007;--folder:#e9c675;--image:#9ae0bb;--video:#c4b1f5;--audio:#eba7cc;--file:#9fc9ed;--radius:16px}
:root[data-theme=light]{color-scheme:light;--bg:#f5f7f1;--panel:#fff;--panel2:#eef1e9;--hover:#e6ecdf;--line:#d9e0d3;--text:#202b20;--muted:#66735f;--accent:#badf7d;--accent-text:#203013;--red:#b83e3c;--shadow:0 24px 90px #24371b22;--folder:#98702a;--image:#2d8260;--video:#7757ad;--audio:#a84981;--file:#367ea9}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font:15px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}button,input,select,a{font:inherit}button,a,input,select{-webkit-tap-highlight-color:transparent}button{cursor:pointer}button,a{touch-action:manipulation}button{border:0}button:disabled{cursor:default;opacity:.42}button:focus-visible,a:focus-visible,input:focus-visible,select:focus-visible,[tabindex]:focus-visible{outline:3px solid var(--accent);outline-offset:4px}button:focus:not(:focus-visible){outline:none}button,a{color:inherit}a{text-decoration:none}button svg,a svg{flex:none}svg{width:21px;height:21px;vertical-align:middle;fill:none;stroke:currentColor;stroke-width:1.8;stroke-linecap:round;stroke-linejoin:round}h1,h2,h3,p{margin:0}button,.btn{min-height:46px;border-radius:11px;display:inline-flex;align-items:center;justify-content:center;gap:9px;padding:10px 16px;background:var(--panel2);color:var(--text);font-weight:600;transition:background .15s}button:hover,.btn:hover{background:var(--hover)}.icon-btn{width:46px;padding:10px;flex:none}.primary{background:var(--accent);color:var(--accent-text)}.primary:hover{background:#d5f3aa}.danger{background:var(--red);color:#301716}.danger:hover{filter:brightness(1.08)}.quiet{background:transparent}.muted{color:var(--muted)}.eyebrow{font-size:11px;font-weight:700;letter-spacing:1.5px;text-transform:uppercase;color:var(--muted)}[hidden]{display:none!important}.layout{min-height:100vh;display:grid;grid-template-columns:238px minmax(0,1fr)}.sidebar{background:var(--panel);border-right:1px solid var(--line);padding:32px 20px;display:flex;flex-direction:column;gap:32px;position:fixed;width:238px;inset:0 auto 0 0;overflow:auto}.brand{display:flex;gap:12px;align-items:center;font-size:24px;font-weight:760;letter-spacing:-1px}.brand-mark{background:var(--accent);color:var(--accent-text);border-radius:14px;width:43px;height:43px;display:grid;place-items:center}.brand-mark svg{width:27px;height:27px}.workspace-card{border:1px solid var(--line);padding:15px;border-radius:12px;margin-top:12px;display:flex;align-items:center;gap:10px}.workspace-card svg{color:var(--folder)}.workspace-card b{font-size:14px;display:block;overflow-wrap:anywhere}.workspace-card small{font-size:11px;color:var(--muted)}.nav{display:flex;flex-direction:column;gap:5px;margin-top:12px}.nav button{justify-content:flex-start;background:transparent;font-weight:500;padding:12px;font-size:14px}.nav button.active{background:var(--hover);color:var(--accent)}.nav .count{margin-left:auto;font-size:12px;color:var(--muted);font-variant-numeric:tabular-nums}.sidebar-bottom{margin-top:auto;border-top:1px solid var(--line);padding-top:24px}.connection{display:flex;align-items:center;gap:8px;font-size:13px;font-weight:600}.dot{width:7px;height:7px;border-radius:50%;background:var(--accent);display:inline-block;box-shadow:0 0 0 4px #b8e77610}.connection-address{margin:8px 0 18px;font-size:11px;overflow-wrap:anywhere}.help-btn{width:100%;justify-content:flex-start;font-size:12px;color:var(--muted);padding-left:0;background:transparent}.main{grid-column:2;padding:32px 42px 120px;min-width:0;max-width:1900px;width:100%;margin:0 auto}.topbar{display:flex;align-items:center;justify-content:space-between;gap:16px;margin-bottom:32px}.topbar h1{font-size:32px;font-weight:650;letter-spacing:-1.1px;margin-top:2px}.top-actions{display:flex;align-items:center;gap:8px}.status-pill{border:1px solid var(--line);border-radius:30px;padding:7px 12px;display:flex;align-items:center;gap:9px;color:var(--muted);font-size:12px;margin-right:8px}.mobile-brand{display:none}.mobile-help{display:none}.toolbar{display:flex;align-items:center;justify-content:space-between;gap:18px;margin:0 0 24px}.path-group{display:flex;gap:12px;align-items:center;min-width:0}.breadcrumbs{display:flex;align-items:center;gap:3px;flex-wrap:wrap;min-width:0}.breadcrumbs button{background:transparent;padding:8px;min-height:44px;font-size:14px;color:var(--muted);font-weight:500;max-width:240px;overflow-wrap:anywhere;text-align:left}.breadcrumbs button:last-of-type{color:var(--text);font-weight:650}.crumb-divider{color:var(--muted);font-size:13px}.toolbar-actions{display:flex;align-items:center;gap:8px;flex:none}.tools{display:flex;align-items:center;justify-content:space-between;gap:16px;margin:0 0 20px}.search-wrap{position:relative;flex:1;max-width:480px}.search-wrap svg{position:absolute;left:16px;top:15px;color:var(--muted);width:19px;height:19px}.search-wrap input{width:100%;height:50px;border:1px solid var(--line);border-radius:12px;background:var(--panel);color:var(--text);padding:12px 42px;font-size:14px}.search-wrap input::placeholder{color:var(--muted)}.search-clear{position:absolute;right:4px;top:4px;min-height:42px;width:38px;padding:5px;background:transparent}.search-clear svg{position:static;width:16px;height:16px}.sort-wrap{display:flex;align-items:center;gap:10px}.sort-wrap label{font-size:12px;color:var(--muted)}select{border:1px solid var(--line);border-radius:11px;min-height:48px;background:var(--panel);color:var(--text);padding:10px 28px 10px 12px;max-width:200px}.summary{display:flex;align-items:center;justify-content:space-between;font-size:12px;color:var(--muted);margin-bottom:12px;gap:10px}.table{border:1px solid var(--line);border-radius:var(--radius);background:var(--panel);overflow:hidden}.table-head,.file-row{display:grid;grid-template-columns:46px minmax(150px,1fr) 105px 95px 145px;align-items:center;gap:12px;padding:0 16px}.table-head{background:var(--panel2);min-height:48px;font-size:11px;color:var(--muted);font-weight:600}.table-head button{padding:6px 0;font-size:11px;color:var(--muted);justify-content:flex-start;background:transparent;min-height:40px}.check-box{display:flex;align-items:center;justify-content:center;min-height:46px;cursor:pointer}.check-box input{accent-color:var(--accent);width:18px;height:18px;cursor:pointer;margin:0}.file-row{min-height:78px;border-top:1px solid var(--line);position:relative}.file-row:hover{background:var(--panel2)}.file-row.selected{background:var(--hover)}.open-item{border-radius:10px;background:transparent;padding:12px 0;justify-content:flex-start;gap:14px;min-width:0;text-align:left;min-height:70px;font-size:14px;font-weight:550}.open-item:hover{background:transparent}.file-icon{width:42px;height:46px;display:grid;place-items:center;border-radius:10px;flex:none;background:var(--panel2);color:var(--file)}.file-icon svg{width:25px;height:25px}.file-icon.folder{color:var(--folder);background:#e3be7412}.file-icon.image{color:var(--image);background:#9ae0bb10}.file-icon.video{color:var(--video);background:#c4b1f512}.file-icon.audio{color:var(--audio);background:#eba7cc10}.file-text{min-width:0}.file-name{display:block;overflow-wrap:anywhere;line-height:1.45;unicode-bidi:plaintext;white-space:pre-wrap}.file-mobile-meta{display:none;color:var(--muted);font-size:11px;font-weight:400;margin-top:4px}.meta-cell{color:var(--muted);font-size:12px;white-space:nowrap}.kind-label{text-transform:capitalize}.row-actions{grid-column:2/-1;display:flex;flex-wrap:wrap;gap:10px;padding:0 0 16px}.row-actions button{font-size:13px;min-height:46px;border:1px solid var(--line)}.row-actions .row-preview{background:var(--accent);color:var(--accent-text);border-color:transparent}.row-actions .row-select[aria-pressed=true]{border-color:var(--accent);color:var(--accent)}.row-actions .row-delete{color:var(--red)}.blocked .open-item{color:var(--muted)}.blocked .file-icon{opacity:.45}.empty{padding:60px 22px;text-align:center}.empty .empty-icon{display:grid;place-items:center;background:var(--panel2);width:64px;height:64px;border-radius:20px;color:var(--accent);margin:0 auto 18px}.empty-icon svg{width:29px;height:29px}.empty h3{font-size:18px;font-weight:600;margin-bottom:6px}.empty p{font-size:13px;color:var(--muted);max-width:390px;margin:0 auto}.empty button{margin-top:18px}.pagination{display:flex;justify-content:space-between;align-items:center;font-size:12px;color:var(--muted);margin-top:18px;gap:12px}.page-actions{display:flex;gap:8px}.page-actions button{font-size:12px;min-height:42px}.footer-note{margin-top:24px;color:var(--muted);font-size:11px;display:flex;align-items:center;gap:7px}.footer-note svg{width:14px;height:14px}.selection-bar{position:fixed;bottom:max(24px,env(safe-area-inset-bottom));left:calc(50% + 119px);transform:translateX(-50%);display:flex;align-items:center;gap:12px;background:var(--panel2);box-shadow:var(--shadow);border:1px solid var(--line);padding:12px 16px;border-radius:17px;z-index:20;white-space:nowrap;max-width:calc(100vw - 270px)}.selection-count{font-size:13px;min-width:94px}.selection-bar .sep{width:1px;height:28px;background:var(--line)}.selection-bar button{font-size:13px}.menu{position:fixed;width:225px;background:var(--panel2);border:1px solid var(--line);border-radius:14px;padding:7px;box-shadow:var(--shadow);z-index:70}.menu-title{padding:8px 10px;font-size:11px;color:var(--muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.menu button{display:flex;width:100%;background:transparent;justify-content:flex-start;font-weight:500;font-size:13px}.menu button:hover{background:var(--hover)}.menu .delete-menu{color:var(--red);border-top:1px solid var(--line);border-radius:0 0 8px 8px;margin-top:5px}.modal{position:fixed;inset:0;z-index:60;background:#070b08bb;backdrop-filter:blur(8px);display:flex;align-items:center;justify-content:center;padding:24px}.dialog{background:var(--panel);border:1px solid var(--line);border-radius:24px;width:100%;max-width:480px;box-shadow:var(--shadow);padding:28px;max-height:calc(100dvh - 48px);overflow:auto}.dialog-header{display:flex;align-items:flex-start;justify-content:space-between;gap:16px;margin-bottom:22px}.dialog-header h2{font-size:21px;letter-spacing:-.4px;line-height:1.4;overflow-wrap:anywhere}.dialog p{font-size:14px;color:var(--muted)}.dialog-symbol{width:54px;height:54px;display:grid;place-items:center;background:var(--panel2);color:var(--accent);border-radius:16px;margin-bottom:20px}.dialog-symbol svg{width:26px;height:26px}.dialog-symbol.warn{color:var(--red)}.dialog-actions{display:flex;justify-content:flex-end;gap:10px;margin-top:24px}.dialog-actions button{flex:1}.delete-list{margin:18px 0;padding:12px 16px;background:var(--panel2);border-radius:12px;list-style:none;max-height:180px;overflow:auto;font-size:13px}.delete-list li{padding:5px 0;overflow-wrap:anywhere;unicode-bidi:plaintext;white-space:pre-wrap}.confirm-label{display:flex;align-items:flex-start;gap:12px;font-size:13px;cursor:pointer;padding-top:7px}.confirm-label input{width:19px;height:19px;accent-color:var(--red);flex:none}.error-text{color:var(--red)!important;margin-top:12px;overflow-wrap:anywhere}.preview-dialog{max-width:1100px;padding:20px}.preview-header{display:flex;align-items:center;justify-content:space-between;gap:16px;margin-bottom:16px}.preview-title{min-width:0}.preview-title h2{font-size:16px;overflow-wrap:anywhere;unicode-bidi:plaintext}.preview-title p{font-size:12px;margin-top:2px}.preview-actions{display:flex;gap:8px;flex:none}.preview-body{min-height:260px;background:#0c0e0c;border-radius:16px;display:flex;align-items:center;justify-content:center;position:relative;overflow:hidden}.preview-body img{display:block;max-width:100%;max-height:70vh;object-fit:contain}.preview-body video{width:100%;max-height:70vh;min-height:200px}.preview-body audio{width:min(90%,600px);margin:90px 0}.media-fallback{text-align:center;padding:40px 20px;color:#a9b2a4}.media-fallback svg{width:40px;height:40px;margin-bottom:16px}.media-fallback h3{color:#f0f3eb;margin-bottom:8px}.media-fallback p{max-width:400px;margin:0 auto 24px;color:#a9b2a4}.preview-note{font-size:11px;margin-top:12px;color:var(--muted);text-align:center}.zip-heading{margin-bottom:6px}.zip-status{font-size:13px!important;min-height:24px;overflow-wrap:anywhere}.zip-track{height:8px;border-radius:12px;background:var(--panel2);overflow:hidden;margin:22px 0 10px}.zip-track progress{appearance:none;-webkit-appearance:none;width:100%;height:8px;border:0;background:transparent}.zip-track progress::-webkit-progress-bar{background:var(--panel2)}.zip-track progress::-webkit-progress-value{background:var(--accent);border-radius:12px}.zip-track progress::-moz-progress-bar{background:var(--accent);border-radius:12px}.zip-numbers{display:flex;justify-content:space-between;font-size:12px;color:var(--muted)}.zip-current{font-size:11px!important;margin-top:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;min-height:19px}.zip-note{font-size:12px!important;margin-top:14px}.login-field{display:block;width:100%;border:1px solid var(--line);border-radius:12px;background:var(--panel2);color:var(--text);height:52px;padding:12px 14px;margin:10px 0}.login-dialog label{display:block;font-size:13px;margin-top:24px}.login-dialog .primary{width:100%;margin-top:14px}.help-grid{display:grid;grid-template-columns:1fr auto;gap:12px;font-size:13px;margin-top:22px}.help-grid kbd{background:var(--panel2);border:1px solid var(--line);border-radius:6px;padding:3px 7px;font:11px/1.5 inherit;color:var(--muted)}.help-tip{margin-top:22px;font-size:12px!important}.toast-stack{position:fixed;bottom:24px;right:24px;z-index:100;display:flex;flex-direction:column;gap:10px;max-width:min(420px,calc(100vw - 32px));pointer-events:none}.toast{background:var(--panel2);box-shadow:var(--shadow);border:1px solid var(--line);border-radius:14px;padding:14px 18px;font-size:13px;overflow-wrap:anywhere;pointer-events:auto}.toast.error{border-color:var(--red)}#zipReopen{position:fixed;bottom:max(24px,env(safe-area-inset-bottom));right:24px;z-index:21}body.has-selection #zipReopen{bottom:112px}body.has-selection .toast-stack{bottom:112px}.spinner{width:25px;height:25px;border:2px solid var(--line);border-top-color:var(--accent);border-radius:50%;animation:spin .8s linear infinite}@keyframes spin{to{transform:rotate(360deg)}}.loading{display:flex;gap:14px;justify-content:center;align-items:center;padding:70px;color:var(--muted);font-size:13px}.tv button,.tv .btn{min-height:60px;font-size:17px}.tv .file-row{min-height:100px}.tv .open-item{min-height:90px;font-size:19px}.tv .file-icon{width:52px;height:56px}.tv .icon-btn{width:60px}.tv .row-actions button{min-height:60px;font-size:17px;padding:12px 20px}.tv .row-actions{padding-bottom:20px;gap:12px}.tv .meta-cell{font-size:15px}.tv .table-head,.tv .file-row{grid-template-columns:46px minmax(150px,1fr) 110px 100px 160px}.tv .main{padding-bottom:140px}.tv .sidebar{font-size:17px}.tv .help-btn{font-size:14px}.tv .breadcrumbs button{font-size:17px}.tv .table-head button{font-size:13px}.tv .menu{width:270px}.tv .dialog{max-width:600px}.tv .preview-dialog{max-width:1200px}
@media(min-width:1600px){.main{padding:42px 64px}.file-row{min-height:86px}}
@media(max-width:1150px){.main{padding:28px 25px 120px}.sidebar{width:210px;padding:28px 16px}.layout{grid-template-columns:210px minmax(0,1fr)}.table-head,.file-row{grid-template-columns:38px minmax(130px,1fr) 80px 80px 110px;gap:8px;padding:0 12px}.selection-bar{left:calc(50% + 105px);max-width:calc(100vw - 240px)}.toolbar{align-items:flex-start;flex-wrap:wrap}.toolbar-actions{margin-left:auto}.topbar h1{font-size:29px}.status-pill{display:none}}
@media(max-width:850px){.sidebar{display:none}.layout{display:block}.main{padding:24px 22px 120px}.topbar{margin-bottom:24px}.topbar .eyebrow{display:none}.mobile-brand{display:flex;margin-right:12px}.top-title{display:flex;align-items:center}.topbar h1{font-size:26px}.selection-bar{left:50%;max-width:calc(100vw - 32px)}.table-head,.file-row{grid-template-columns:36px minmax(140px,1fr) 85px 105px}.type-col{display:none}.tv .table-head,.tv .file-row{grid-template-columns:36px minmax(140px,1fr) 95px 115px}.mobile-help{display:inline-flex!important}.footer-note{line-height:1.6}}
@media(max-width:600px){.main{padding:20px 14px 145px}.topbar{gap:8px}.top-actions{gap:3px}.topbar h1{font-size:23px}.top-actions button{width:40px;min-height:44px;padding:9px}.brand-mark{width:37px;height:37px;border-radius:12px}.mobile-brand{margin-right:9px}.toolbar{gap:12px;margin-bottom:18px}.path-group{width:100%;gap:5px}.breadcrumbs{gap:0}.breadcrumbs button{font-size:13px;max-width:200px}.toolbar-actions{width:100%;margin:0;justify-content:space-between}.toolbar-actions .primary{flex:1}.tools{gap:10px;align-items:stretch;margin-bottom:17px}.sort-wrap label{display:none}.sort-wrap select{width:132px;font-size:12px;max-width:132px;padding-left:9px}.search-wrap{min-width:0}.search-wrap input{font-size:13px;padding-left:38px}.search-wrap svg{left:12px}.summary{font-size:11px}.summary span:last-child{max-width:45%;text-align:right}.table-head,.file-row,.tv .table-head,.tv .file-row{grid-template-columns:28px minmax(0,1fr) 38px;gap:8px;padding:0 10px}.size-col,.date-col{display:none}.table-head{min-height:44px}.file-row{min-height:86px}.open-item{gap:11px;font-size:13px}.file-icon{width:35px;height:42px}.file-mobile-meta{display:block}.selection-bar{flex-wrap:wrap;gap:7px;justify-content:center;border-radius:16px;bottom:max(14px,env(safe-area-inset-bottom));padding:10px 12px;width:calc(100vw - 28px)}.selection-count{flex:1;margin-left:6px}.selection-bar .sep{display:none}.selection-bar .primary,.selection-bar .delete-selected{flex:1}.selection-bar .clear-selection{font-size:12px}.selection-bar button{min-height:44px}.pagination{font-size:11px}.page-actions button{font-size:11px;padding:9px 12px}.modal{padding:14px}.dialog{padding:22px;border-radius:19px;max-height:calc(100dvh - 28px)}.preview-dialog{padding:14px}.preview-header{gap:9px}.preview-actions .btn{width:44px;padding:10px}.preview-actions .btn span:not([data-icon]){display:none}.preview-body{min-height:230px}.preview-title h2{font-size:13px}.preview-title p{font-size:11px}.footer-note{font-size:10px}.toast-stack{right:14px;bottom:14px}.tv .open-item{font-size:17px}.tv .file-mobile-meta{font-size:12px}.tv .file-icon{width:41px;height:48px}}
@media(max-width:600px){#zipReopen{right:14px;bottom:14px}body.has-selection #zipReopen,body.has-selection .toast-stack{bottom:170px}}

#tvBtn[aria-pressed=true]{background:var(--panel2);color:var(--accent);box-shadow:inset 0 0 0 1px var(--line)}
.card-selection-label{display:none}
@media(max-width:1150px) and (min-width:851px){.tv .table-head,.tv .file-row{grid-template-columns:36px minmax(120px,1fr) 85px 85px 120px}.tv .meta-cell{font-size:13px}}
@media(max-width:760px){
.main,.tv .main{padding:20px 14px 155px}.sidebar{display:none}.layout{display:block}.topbar{gap:8px}.topbar h1{font-size:23px}.top-actions{gap:4px}.top-actions button,.tv .top-actions button{width:44px;min-height:48px;padding:10px}.status-pill{display:none}
.toolbar{gap:12px;flex-wrap:wrap;margin-bottom:18px}.path-group{width:100%;gap:5px}.breadcrumbs button,.tv .breadcrumbs button{font-size:14px;min-height:48px}.toolbar-actions{width:100%;margin:0;gap:8px}.toolbar-actions .primary{flex:1}.toolbar-actions button,.tv .toolbar-actions button{font-size:14px;min-height:52px;padding:10px 12px}.toolbar-actions .icon-btn{width:48px}
.tools{gap:10px;align-items:stretch}.sort-wrap label{display:none}.sort-wrap select{width:132px;font-size:12px;max-width:132px;padding-left:9px}.search-wrap{min-width:0}.search-wrap input{font-size:14px;padding-left:38px}.search-wrap svg{left:12px}
.table{border:0;border-radius:0;background:transparent;overflow:visible}.table-head,.tv .table-head{display:flex;gap:10px;padding:0 4px;min-height:48px;background:transparent;margin-bottom:10px}.table-head>button{display:none}.card-selection-label{display:block;font-size:12px}.table-head .check-box{width:28px}#rows{display:grid;gap:12px}
.file-row,.tv .file-row{grid-template-columns:28px minmax(0,1fr);gap:0 10px;padding:12px;border:1px solid var(--line);border-radius:18px;min-height:0;background:var(--panel)}.file-row:hover{background:var(--panel)}.file-row.selected{background:var(--hover);border-color:var(--accent)}.file-row .check-box{align-self:start;min-height:64px}.file-row .meta-cell{display:none}
.open-item,.tv .open-item{font-size:16px;min-height:64px;padding:0 0 12px;gap:12px}.file-icon,.tv .file-icon{width:42px;height:48px}.file-mobile-meta,.tv .file-mobile-meta{display:block;font-size:12px;line-height:1.6}.row-actions,.tv .row-actions{grid-column:1/-1;display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px;padding:6px 0 0}.row-actions button,.tv .row-actions button{min-height:52px;padding:10px 8px;gap:8px;font-size:14px}.row-actions button svg{width:19px;height:19px}
.selection-bar{left:50%;max-width:calc(100vw - 28px);width:calc(100vw - 28px);flex-wrap:wrap;gap:7px;justify-content:center;padding:10px 12px;bottom:max(14px,env(safe-area-inset-bottom))}.selection-count{flex:1;margin-left:6px}.selection-bar .sep{display:none}.selection-bar .primary,.selection-bar .delete-selected{flex:1}.selection-bar button,.tv .selection-bar button{min-height:48px;font-size:14px}.selection-bar .clear-selection{font-size:12px}.pagination{flex-wrap:wrap}.page-actions button,.tv .page-actions button{font-size:13px;min-height:48px}.summary{font-size:11px}
.modal{padding:14px}.dialog{padding:22px;max-height:calc(100dvh - 28px)}.preview-dialog{padding:14px}.preview-header{gap:9px}.preview-actions .btn{width:48px;padding:10px}.preview-actions .btn span:not([data-icon]){display:none}.preview-actions .icon-btn,.tv .preview-actions .icon-btn{width:48px;min-height:48px}.preview-title h2{font-size:14px}
body.has-selection #zipReopen,body.has-selection .toast-stack{bottom:170px}
}
@media(prefers-reduced-motion:reduce){*{animation:none!important;transition:none!important;scroll-behavior:auto!important}}
.tv-nav-hint{display:none}.tv .tv-nav-hint{display:block}.player-stage{min-width:0}.preview-dialog:has(.playback-settings[open]) .preview-body video{max-height:42vh}.player-tools{padding-top:14px}.transport-bar{display:flex;flex-wrap:wrap;gap:10px;align-items:center}.transport-bar .speed-label{display:flex;align-items:center;gap:10px;font-size:13px;color:var(--muted)}.transport-bar select{min-height:50px}.buffer-status{display:flex;align-items:center;justify-content:space-between;gap:16px;margin:14px 2px;font-size:12px;color:var(--muted)}.buffer-status progress{width:120px;height:6px;accent-color:var(--accent);flex:none}.player-message{font-size:13px!important;margin:12px 0!important;color:var(--accent)!important;overflow-wrap:anywhere}.player-message.error{color:var(--red)!important}.playback-settings{border:1px solid var(--line);border-radius:14px;margin-top:10px;background:var(--panel)}.playback-settings summary{cursor:pointer;padding:14px 18px;min-height:52px;font-weight:600;touch-action:manipulation}.playback-settings summary:focus-visible{outline:3px solid var(--accent);outline-offset:3px;border-radius:12px}.settings-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:16px;padding:0 18px 18px}.settings-grid fieldset{min-width:0;margin:0;border:1px solid var(--line);border-radius:12px;padding:16px}.settings-grid legend{padding:0 8px;font-weight:650}.settings-grid label{display:block;font-size:12px;color:var(--muted);margin:12px 0 6px}.settings-grid select{max-width:100%;width:100%;font-size:13px;min-height:48px}.setting-actions{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}.setting-actions button{font-size:13px;flex:1}.setting-hint{font-size:12px!important;line-height:1.7;margin-top:10px!important;overflow-wrap:anywhere}.sync-control{display:flex;gap:6px;align-items:center;flex-wrap:wrap}.sync-control button{font-size:12px;padding:10px;flex:1;white-space:nowrap}.sync-control input{background:var(--panel2);border:1px solid var(--line);border-radius:10px;width:83px;min-height:48px;color:var(--text);text-align:center;padding:8px}.sync-control input:disabled{opacity:.42}.appearance-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}.appearance-grid select{padding:10px 4px;font-size:12px}.buffer-settings{grid-column:1/-1}.external-volume{display:flex;gap:14px;align-items:center;flex-wrap:wrap;margin-top:14px}.external-volume label{flex:1;min-width:130px}.external-volume input{width:100%;accent-color:var(--accent);min-height:36px}.external-volume button{font-size:13px}.preview-body .external-audio{display:none}.tv .playback-settings summary{min-height:60px;font-size:17px}.tv .settings-grid select{font-size:15px;min-height:56px}.tv .setting-actions button,.tv .sync-control button{font-size:14px;min-height:54px}.tv .sync-control input{min-height:54px;font-size:16px}.tv .settings-grid label{font-size:14px}.player-stage:fullscreen{background:var(--bg);width:100%;height:100%;padding:20px;overflow:auto}.player-stage:fullscreen .preview-body{min-height:0}.player-stage:fullscreen video{max-height:calc(100vh - 155px);width:100%}.player-stage:fullscreen .player-tools{max-width:1400px;width:100%;margin:auto}.player-stage:fullscreen:has(.playback-settings[open]) video{max-height:55vh}.player-stage:fullscreen .preview-body audio{margin:20vh 0}#previewBody video::cue{color:white;background-color:rgba(0,0,0,.8);font-size:24px;text-shadow:0 1px 2px #000}
@media(max-width:760px){.settings-grid{grid-template-columns:minmax(0,1fr);padding:0 12px 12px;gap:12px}.settings-grid fieldset{padding:12px}.transport-bar{gap:8px}.transport-bar button,.tv .transport-bar button{font-size:14px;min-height:48px;padding:10px 12px}.transport-bar .speed-label{font-size:12px}.transport-bar select,.tv .transport-bar select{font-size:14px;min-height:48px}.buffer-status{font-size:11px;gap:8px;align-items:flex-start}.buffer-status progress{width:65px;margin-top:5px}.appearance-grid{grid-template-columns:repeat(2,minmax(0,1fr))}.appearance-grid label:last-child{grid-column:1/-1}.tv .settings-grid label{font-size:12px}.tv .settings-grid select{font-size:13px;min-height:48px}.tv .playback-settings summary{font-size:15px;min-height:52px}.setting-actions button,.tv .setting-actions button,.sync-control button,.tv .sync-control button{font-size:12px;min-height:48px}.sync-control input,.tv .sync-control input{min-height:48px;font-size:14px}.player-stage:fullscreen{padding:10px}}

</style>
<style nonce="__NONCE__" id="subtitleStyles"></style>
</head>
<body>
<div class="layout" id="app">
 <aside class="sidebar" aria-label="Workspace navigation">
  <div class="brand"><span class="brand-mark" data-icon="folder"></span>fshare<span class="muted" style="font-size:20px">.</span></div>
  <section><div class="eyebrow">Your workspace</div><div class="workspace-card"><span data-icon="folder"></span><div><b id="rootName">Shared folder</b><small>LOCAL DIRECTORY</small></div></div></section>
  <section><div class="eyebrow">In this folder</div><nav class="nav" id="categories" aria-label="Filter files">
   <button class="active" data-kind="all"><span data-icon="files"></span>All files<span class="count">0</span></button>
   <button data-kind="folder"><span data-icon="folder"></span>Folders<span class="count">0</span></button>
   <button data-kind="video"><span data-icon="video"></span>Videos<span class="count">0</span></button>
   <button data-kind="image"><span data-icon="image"></span>Images<span class="count">0</span></button>
   <button data-kind="audio"><span data-icon="audio"></span>Audio<span class="count">0</span></button>
   <button data-kind="file"><span data-icon="file"></span>Other files<span class="count">0</span></button>
  </nav></section>
  <div class="sidebar-bottom"><div class="connection"><span class="dot"></span>Connected locally</div><p class="connection-address muted" id="address"></p><button class="help-btn" id="helpBtn"><span data-icon="keyboard"></span>Keyboard &amp; connection help</button></div>
 </aside>
 <main class="main">
  <header class="topbar"><div class="top-title"><span class="brand-mark mobile-brand" data-icon="folder"></span><div><div class="eyebrow">Your files, nearby</div><h1>Files</h1></div></div><div class="top-actions"><span class="status-pill"><span class="dot"></span>Local network</span><button class="icon-btn quiet mobile-help" id="mobileHelp" aria-label="Help" title="Help"><span data-icon="help"></span></button><button class="icon-btn quiet" id="tvBtn" aria-label="Enable TV mode" title="TV mode" aria-pressed="false"><span data-icon="tv"></span></button><button class="icon-btn quiet" id="themeBtn" aria-label="Switch to light mode" title="Change theme"><span data-icon="sun"></span></button><button class="icon-btn quiet" id="logoutBtn" aria-label="Sign out" title="Sign out" hidden><span data-icon="logout"></span></button></div></header>
  <div class="toolbar"><div class="path-group"><button class="icon-btn" id="upBtn" aria-label="Go to parent folder" title="Parent folder (Alt + Up)" disabled><span data-icon="up"></span></button><nav class="breadcrumbs" id="breadcrumbs" aria-label="Folder path"></nav></div><div class="toolbar-actions"><button class="icon-btn" id="refreshBtn" aria-label="Refresh folder" title="Refresh"><span data-icon="refresh"></span></button><button id="selectBtn" aria-pressed="false"><span data-icon="check"></span>Select</button><button class="primary" id="downloadAll"><span data-icon="download"></span>Download all</button></div></div>
  <div class="tools"><div class="search-wrap"><span data-icon="search"></span><input id="search" type="search" placeholder="Search this folder…" aria-label="Search files and folders" autocomplete="off"><button class="search-clear" id="clearSearch" aria-label="Clear search" hidden><span data-icon="close"></span></button></div><div class="sort-wrap"><label for="sort">Sort by</label><select id="sort"><option value="name-asc">Name · A to Z</option><option value="name-desc">Name · Z to A</option><option value="modified-desc">Newest first</option><option value="modified-asc">Oldest first</option><option value="size-desc">Largest first</option><option value="size-asc">Smallest first</option><option value="kind-asc">File type</option></select></div></div>
  <div class="summary"><span id="summary" role="status" aria-live="polite">Connecting to your folder…</span><span id="folderSize"></span></div>
  <section class="table" aria-label="Files and folders" aria-busy="true" id="table"><div class="table-head"><label class="check-box" title="Select all matching items"><input id="selectAll" type="checkbox" aria-label="Select all matching files and folders"></label><button id="sortName">Name<span data-icon="down"></span></button><button class="type-col" id="sortType">Type</button><button class="size-col" id="sortSize">Size</button><button class="date-col" id="sortDate">Last modified</button><span class="card-selection-label">Select all matching items</span></div><div id="rows" role="list"></div><div class="empty" id="empty" hidden><div class="empty-icon" data-icon="folder"></div><h3 id="emptyTitle">This folder is empty</h3><p id="emptyMessage">Files added on the host computer will appear here after you refresh.</p><button id="emptyAction" hidden>Go to shared folder</button></div><div class="loading" id="loading"><div class="spinner"></div>Loading your files…</div></section>
  <div class="pagination" id="pagination" hidden><span id="pageLabel"></span><div class="page-actions"><button id="prevPage"><span data-icon="left"></span>Previous</button><button id="nextPage">Next<span data-icon="right"></span></button></div></div>
  <p class="footer-note"><span data-icon="shield"></span><span id="accessNote">Shared on your local network. Files stay on the host computer.</span></p>
 </main>
</div>
<div class="selection-bar" id="selectionBar" hidden><b class="selection-count" id="selectionCount">0 selected</b><button class="quiet clear-selection" id="clearSelection">Clear</button><span class="sep"></span><button class="primary" id="downloadSelected"><span data-icon="download"></span>Download ZIP</button><button class="delete-selected" id="deleteSelected"><span data-icon="trash"></span>Delete</button></div>
<div class="menu" id="menu" role="menu" aria-label="File actions" hidden><div class="menu-title" id="menuTitle"></div><button id="menuOpen" role="menuitem"><span data-icon="open"></span><span id="menuOpenText">Open</span></button><button id="menuDownload" role="menuitem"><span data-icon="download"></span><span id="menuDownloadText">Download</span></button><button id="menuSelect" role="menuitem"><span data-icon="check"></span><span id="menuSelectText">Select</span></button><button id="menuDelete" class="delete-menu" role="menuitem"><span data-icon="trash"></span>Delete</button></div>
<div class="modal" id="previewModal" hidden><section class="dialog preview-dialog" role="dialog" aria-modal="true" aria-labelledby="previewTitle"><header class="preview-header"><div class="preview-title"><h2 id="previewTitle"></h2><p id="previewMeta"></p></div><div class="preview-actions"><a class="btn primary" id="previewDownload" download><span data-icon="download"></span><span>Download</span></a><button class="icon-btn quiet" data-close="previewModal" aria-label="Close preview"><span data-icon="close"></span></button></div></header><div class="player-stage" id="previewStage"><div class="preview-body" id="previewBody"></div><div class="player-tools" id="playerTools" hidden>
 <div class="transport-bar" aria-label="Playback controls">
  <button class="primary" id="playerPlay">Play</button>
  <button id="playerBack" aria-label="Seek backward 10 seconds">−10 s</button>
  <button id="playerForward" aria-label="Seek forward 10 seconds">+10 s</button>
  <label class="speed-label" for="playerRate">Speed<select id="playerRate"><option value="0.25">0.25×</option><option value="0.5">0.5×</option><option value="0.75">0.75×</option><option value="1">1×</option><option value="1.25">1.25×</option><option value="1.5">1.5×</option><option value="2">2×</option><option value="2.5">2.5×</option><option value="3">3×</option></select></label>
  <button id="playerFullscreen">Fullscreen</button>
 </div>
 <div class="buffer-status"><span id="playerBuffer" role="status">Reading media information…</span><progress id="playerBufferMeter" max="1" value="0" aria-label="Buffered fraction of the file"></progress></div>
 <p class="player-message" id="playerMessage" role="status" hidden></p>
 <details class="playback-settings" id="playerSettings"><summary>Playback settings</summary>
  <div class="settings-grid">
   <fieldset id="subtitleSettings"><legend>Subtitles</legend>
    <label for="subtitleTrack">Subtitle track</label><select id="subtitleTrack"><option value="off">Off</option></select>
    <div class="setting-actions"><button id="subtitleToggle" aria-pressed="false" disabled>Show subtitles</button><button id="subtitleLoad">Load SRT / VTT</button><input id="subtitleFile" type="file" accept=".srt,.vtt" hidden></div>
    <p class="setting-hint" id="subtitleHint">Checking for nearby subtitles…</p>
    <label for="subtitleEncoding">Text encoding</label><select id="subtitleEncoding"><option value="auto">Auto (UTF / Persian legacy)</option><option value="utf-8">UTF-8</option><option value="windows-1256">Windows-1256 (Persian / Arabic)</option><option value="windows-1252">Windows-1252 (Western)</option></select>
    <label for="subtitleOffset">Subtitle delay · positive = later</label><div class="sync-control"><button id="subtitleEarlier" aria-label="Show subtitles 0.25 seconds earlier">−0.25 s</button><input id="subtitleOffset" type="number" min="-120" max="120" step="0.25" value="0" aria-label="Subtitle delay in seconds"><button id="subtitleLater" aria-label="Show subtitles 0.25 seconds later">+0.25 s</button><button id="subtitleReset">Reset</button></div>
    <div class="appearance-grid"><label for="subtitleColor">Color<select id="subtitleColor"><option value="#ffffff">White</option><option value="#ffed70">Yellow</option><option value="#b8f79a">Green</option><option value="#90e8ff">Cyan</option></select></label><label for="subtitleSize">Font size<select id="subtitleSize"><option value="18">Small</option><option value="24">Medium</option><option value="32">Large</option><option value="40">Extra large</option></select></label><label for="subtitlePosition">Position<select id="subtitlePosition"><option value="bottom">Bottom</option><option value="middle">Middle</option><option value="top">Top</option></select></label></div>
   </fieldset>
   <fieldset id="audioSettings"><legend>Audio &amp; language</legend>
    <label for="audioTrack">Audio source</label><select id="audioTrack"><option value="original">Original audio (browser default)</option></select>
    <div class="setting-actions"><button id="audioLoad">Load audio file</button><input id="audioFile" type="file" accept="audio/*,.mp3,.m4a,.aac,.wav,.flac,.ogg,.opus" hidden></div>
    <p class="setting-hint" id="audioTrackHint">Checking browser audio-track support…</p>
    <label for="audioOffset">External audio delay · positive = later</label><div class="sync-control"><button id="audioEarlier" aria-label="Play external audio 0.1 seconds earlier" disabled>−0.1 s</button><input id="audioOffset" type="number" min="-120" max="120" step="0.1" value="0" aria-label="External audio delay in seconds" disabled><button id="audioLater" aria-label="Play external audio 0.1 seconds later" disabled>+0.1 s</button><button id="audioReset" disabled>Reset</button></div>
    <p class="setting-hint" id="audioSyncHint">Independent timing is available for external audio. Embedded audio remains aligned by the browser.</p>
    <div class="external-volume" id="externalVolume" hidden><button id="externalMute" aria-pressed="false">Mute external audio</button><label for="externalVolumeLevel">External volume<input id="externalVolumeLevel" type="range" min="0" max="1" step="0.05" value="1"></label></div>
   </fieldset>
   <fieldset class="buffer-settings"><legend>Streaming</legend><label for="playerPreload">Buffer preference</label><select id="playerPreload"><option value="auto">Automatic (browser-managed)</option><option value="metadata">Lower data use (metadata first)</option></select><p class="setting-hint">Playback starts without waiting for a large buffer. The browser controls memory, prefetching and refill after seeks; a fixed 10-minute buffer cannot be guaranteed. Changing this preference does not reload the file.</p><p class="setting-hint">Speed controls support forward playback from 0.25× to 3×. True reverse playback requires a different decoding pipeline; the −10 s button is a seek.</p><p class="setting-hint tv-nav-hint">TV controls: up/down moves focus; left/right changes a selected option. Enter opens native pickers.</p></fieldset>
  </div>
 </details>
</div>
</div><p class="preview-note" id="previewNote">Playback support depends on your browser and the file format.</p></section></div>
<div class="modal" id="deleteModal" hidden><section class="dialog" role="dialog" aria-modal="true" aria-labelledby="deleteTitle"><div class="dialog-symbol warn" data-icon="trash"></div><h2 id="deleteTitle">Delete these items?</h2><p style="margin-top:10px">This permanently deletes items from the host computer. Folders include everything inside them.</p><ul class="delete-list" id="deleteList"></ul><label class="confirm-label"><input type="checkbox" id="deleteAgree">I understand this cannot be undone.</label><p class="error-text" id="deleteError" role="alert" hidden></p><div class="dialog-actions"><button id="deleteCancel" data-close="deleteModal">Cancel</button><button class="danger" id="deleteConfirm" disabled>Delete permanently</button></div></section></div>
<div class="modal" id="zipModal" hidden><section class="dialog" role="dialog" aria-modal="true" aria-labelledby="zipTitle"><div class="dialog-symbol" data-icon="archive"></div><h2 class="zip-heading" id="zipTitle">Preparing your ZIP</h2><p class="zip-status" id="zipStatus" role="status" aria-live="polite">Getting started…</p><div class="zip-track"><progress id="zipProgress" max="100" value="0" aria-label="ZIP preparation progress"></progress></div><div class="zip-numbers"><span id="zipFiles">0 files</span><span id="zipBytes">0 B</span></div><p class="zip-current" id="zipCurrent"></p><p class="zip-note" id="zipNote">You can browse other folders while this runs.</p><div class="dialog-actions"><button id="zipCancel">Cancel ZIP</button><button id="zipBrowse">Keep browsing</button><a class="btn primary" id="zipDownload" hidden>Download ZIP</a></div></section></div>
<div class="modal" id="loginModal" hidden><form class="dialog login-dialog" id="loginForm" role="dialog" aria-modal="true" aria-labelledby="loginTitle"><div class="brand" style="margin-bottom:30px"><span class="brand-mark" data-icon="folder"></span>fshare.</div><h2 id="loginTitle">Your files are protected</h2><p style="margin-top:10px">Enter the password set on the host computer to access this shared folder.</p><label for="password">Access password</label><input class="login-field" id="password" type="password" autocomplete="current-password" required><p class="error-text" id="loginError" role="alert" hidden></p><button type="submit" class="primary" id="loginSubmit"><span data-icon="unlock"></span>Unlock workspace</button></form></div>
<div class="modal" id="helpModal" hidden><section class="dialog" role="dialog" aria-modal="true" aria-labelledby="helpTitle"><header class="dialog-header"><div><div class="eyebrow">Made for nearby devices</div><h2 id="helpTitle" style="margin-top:6px">A few handy shortcuts</h2></div><button class="icon-btn quiet" data-close="helpModal" aria-label="Close help"><span data-icon="close"></span></button></header><div class="help-grid"><span>Move between items</span><kbd>↑ ↓ ← →</kbd><span>Open folder or preview</span><kbd>Enter</kbd><span>Select focused item</span><kbd>Space</kbd><span>Actions for focused item</span><kbd>Shift + F10</kbd><span>Go to parent folder</span><kbd>Alt + ↑</kbd><span>Search this folder</span><kbd>/</kbd><span>Close preview or menu</span><kbd>Esc / Back</kbd></div><p class="help-tip">Every item has visible action buttons. TV mode starts on with larger controls; use the TV button to change it. On phones, items appear as touch-friendly cards. Arrow down enters an item’s actions; left and right move between them. Holding an item or right-clicking also opens shortcuts. Search and Select all apply to the current folder, including items on other pages.</p><p class="help-tip">Use a network address printed in the host terminal on your other devices. Both devices must be on the same LAN. Allow Python through the host firewall; guest Wi-Fi isolation can block access.</p><p class="help-tip">MKV playback is attempted directly and depends on the browser and the video/audio codecs inside it. An incompatible file can be downloaded, or converted to MP4 on the host using an optional media tool. HTTP traffic is intended for a trusted local network.</p></section></div>
<div class="toast-stack" id="toasts" role="status" aria-live="polite"></div>
<button class="btn primary" id="zipReopen" hidden><span data-icon="archive"></span><span id="zipReopenLabel">Preparing ZIP…</span></button>
<script nonce="__NONCE__">
(()=>{
'use strict';
const $=id=>document.getElementById(id);
const paths={folder:['M3 7a2 2 0 0 1 2-2h5l2 3h7a2 2 0 0 1 2 2v9a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2Z'],file:['M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8Z','M14 2v6h6','M8 13h8M8 17h5'],files:['M8 3h10a2 2 0 0 1 2 2v12','M4 7h10a2 2 0 0 1 2 2v11H4Z'],video:['M4 4h16v16H4Z','m10 8 6 4-6 4Z'],image:['M3 3h18v18H3Z','m3 16 6-6 5 5 3-3 4 4','M15 7h.01'],audio:['M9 18V5l12-2v13','M9 5v4l12-2','M6 16a3 3 0 1 0 0 6 3 3 0 0 0 0-6Z','M18 14a3 3 0 1 0 0 6 3 3 0 0 0 0-6Z'],download:['M12 3v12m-5-5 5 5 5-5','M4 16v5h16v-5'],archive:['M4 3h16v18H4Z','M10 3v3h4v3h-4v3h4v3h-4v4h4v-4'],trash:['M3 6h18M9 6V3h6v3M5 6l1 15h12l1-15M10 10v7M14 10v7'],more:['M12 5h.01M12 12h.01M12 19h.01'],up:['m6 11 6-6 6 6M12 5v15'],down:['m8 10 4 4 4-4'],left:['m14 6-6 6 6 6'],right:['m10 6 6 6-6 6'],refresh:['M20 8a8 8 0 1 0 0 8M20 3v5h-5'],search:['M10 3a7 7 0 1 0 0 14 7 7 0 0 0 0-14Z','m15 15 6 6'],check:['m5 12 4 4L19 6'],close:['m6 6 12 12M18 6 6 18'],sun:['M12 8a4 4 0 1 0 0 8 4 4 0 0 0 0-8Z','M12 2v2M12 20v2M2 12h2M20 12h2M5 5l1 1M18 18l1 1M5 19l1-1M18 6l1-1'],moon:['M21 13A9 9 0 0 1 11 3a9 9 0 1 0 10 10Z'],keyboard:['M2 5h20v14H2Z','M6 9h.01M10 9h.01M14 9h.01M18 9h.01M6 13h.01M10 13h.01M14 13h.01M18 13h.01M7 16h10'],tv:['M3 7h18v14H3Z','m8 2 4 5 4-5'],shield:['m12 2 8 3v6c0 5-4 8-8 11-4-3-8-6-8-11V5Z','m8 11 3 3 5-5'],unlock:['M6 10h12v11H6Z','M8 10V6a4 4 0 0 1 7-3'],logout:['M9 3H4v18h5','M10 12h11m-4-4 4 4-4 4'],open:['M14 3h7v7m0-7-11 11','M10 3H3v18h18v-7'],help:['M12 2a10 10 0 1 0 0 20 10 10 0 0 0 0-20Z','M9 8a3 3 0 0 1 6 0c0 2-3 2-3 5M12 17h.01']};
function icon(name){const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.setAttribute('viewBox','0 0 24 24');svg.setAttribute('aria-hidden','true');for(const d of paths[name]||paths.file){const p=document.createElementNS(svg.namespaceURI,'path');p.setAttribute('d',d);svg.append(p)}return svg}
document.querySelectorAll('[data-icon]').forEach(el=>el.replaceChildren(icon(el.dataset.icon)));
function el(tag,cls,text){const n=document.createElement(tag);if(cls)n.className=cls;if(text!==undefined)n.textContent=text;return n}
const state={path:'',items:[],filtered:[],selected:new Map(),kind:'all',page:0,pageSize:100,selectMode:false,session:null,modal:null,lastFocus:null,menuItem:null,request:null,navId:0,zip:null,zipTimer:null,plan:null,loading:false,error:false,player:null};
const collator=new Intl.Collator('en',{numeric:true,sensitivity:'base'});
const dateFormat=new Intl.DateTimeFormat('en',{year:'numeric',month:'short',day:'numeric'});
function bytes(n){if(n==null)return '—';if(n===0)return '0 B';const i=Math.min(4,Math.floor(Math.log(n)/Math.log(1024)));return (i?(n/Math.pow(1024,i)).toFixed(1):n)+' '+['B','KB','MB','GB','TB'][i]}
function date(n){return n==null?'Unavailable':dateFormat.format(new Date(n*1000))}
function toast(text,error=false){const node=el('div','toast'+(error?' error':''),text);$('toasts').append(node);setTimeout(()=>node.remove(),error?9000:4500)}
function preference(key,value){try{if(value!==undefined)localStorage.setItem('fshare-'+key,value);return localStorage.getItem('fshare-'+key)}catch{return null}}
function theme(value){document.documentElement.dataset.theme=value;$('themeBtn').replaceChildren(icon(value==='dark'?'sun':'moon'));$('themeBtn').setAttribute('aria-label','Switch to '+(value==='dark'?'light':'dark')+' mode');preference('theme',value)}
theme(preference('theme')==='light'?'light':'dark');
function tv(on){document.body.classList.toggle('tv',on);$('tvBtn').setAttribute('aria-pressed',String(on));$('tvBtn').setAttribute('aria-label',(on?'Disable':'Enable')+' TV mode');preference('tv-v2',on?'1':'0')}
// Start with TV controls; remember a user's explicit choice from this version onward.
tv(preference('tv-v2')!=='0');
$('themeBtn').addEventListener('click',()=>theme(document.documentElement.dataset.theme==='dark'?'light':'dark'));
$('tvBtn').addEventListener('click',()=>tv(!document.body.classList.contains('tv')));
function focusable(root){return [...root.querySelectorAll('button,a[href],input,select,[tabindex],video[controls],audio[controls],summary')].filter(n=>!n.disabled&&n.tabIndex>=0&&n.getClientRects().length)}
function openModal(id){hideMenu();if(!state.modal)state.lastFocus=document.activeElement;if(state.modal)$(state.modal).hidden=true;state.modal=id;$(id).hidden=false;$('app').inert=true;$('app').setAttribute('aria-hidden','true');$('selectionBar').inert=true;$('zipReopen').inert=true;requestAnimationFrame(()=>{const target=id==='loginModal'?$('password'):id==='deleteModal'?$('deleteCancel'):focusable($(id))[0];if(target)target.focus()})}
function closeModal(){if(!state.modal||state.modal==='loginModal')return;const id=state.modal;if(id==='deleteModal'&&$('deleteConfirm').dataset.busy==='1')return;$(id).hidden=true;if(id==='previewModal'){destroyPlayer();$('previewBody').querySelectorAll('video,audio').forEach(m=>{m.pause();m.removeAttribute('src');m.load()});$('previewBody').replaceChildren()}state.modal=null;if(id==='zipModal'&&state.zip)$('zipReopen').hidden=false;$('app').inert=false;$('app').removeAttribute('aria-hidden');$('selectionBar').inert=false;$('zipReopen').inert=false;if(state.lastFocus&&state.lastFocus.isConnected)state.lastFocus.focus()}
document.querySelectorAll('[data-close]').forEach(b=>b.addEventListener('click',closeModal));
document.querySelectorAll('.modal').forEach(m=>m.addEventListener('click',e=>{if(e.target===m&&m.id!=='loginModal')closeModal()}));
$('helpBtn').addEventListener('click',()=>openModal('helpModal'));$('mobileHelp').addEventListener('click',()=>openModal('helpModal'));
async function api(url,body,signal,retried=false){const opts={credentials:'same-origin',signal,headers:{}};if(body!==undefined){opts.method='POST';opts.headers={'Content-Type':'application/json','X-CSRF-Token':state.session?.csrf||''};opts.body=JSON.stringify(body)}let response;try{response=await fetch(url,opts)}catch(e){if(e.name==='AbortError')throw e;throw new Error('Connection lost. Check that the host is still running, then try again.')}let data;try{data=await response.json()}catch{throw new Error('Unable to read the server response. Reload the page and try again.')}if(!response.ok){if(response.status===401&&url!=='/api/login'){if(state.session?.protected===false&&!retried){const fresh=await api('/api/session');if(fresh.authenticated){state.session=fresh;return api(url,body,signal,true)}}state.session=null;openModal('loginModal')}throw new Error(data.error||'The operation could not be completed.')}return data}
function locationPath(){return new URLSearchParams(location.search).get('path')||''}
async function connect(){try{state.session=await api('/api/session');if(!state.session.authenticated){openModal('loginModal');return}if(state.modal==='loginModal'){state.modal=null;$('loginModal').hidden=true;$('app').inert=false;$('app').removeAttribute('aria-hidden');$('selectionBar').inert=false;$('zipReopen').inert=false}configure();await navigate(locationPath(),false)}catch(e){showLoadError(e.message)}}
function configure(){$('rootName').textContent=state.session.root_name;$('address').textContent=location.host;$('logoutBtn').hidden=!state.session.protected;$('deleteSelected').hidden=state.session.read_only;$('menuDelete').hidden=state.session.read_only;$('accessNote').textContent=(state.session.protected?'Password protected. ':'Shared with devices on this network. ')+(state.session.read_only?'Read-only mode. ':'')+'Files stay on the host computer.'}
$('loginForm').addEventListener('submit',async e=>{e.preventDefault();$('loginError').hidden=true;$('loginSubmit').disabled=true;try{await api('/api/login',{password:$('password').value});$('password').value='';await connect()}catch(err){$('loginError').textContent=err.message;$('loginError').hidden=false;$('password').focus()}finally{$('loginSubmit').disabled=false}});
$('logoutBtn').addEventListener('click',async()=>{try{await api('/api/logout',{});location.reload()}catch(e){toast(e.message,true)}});
function breadcrumb(){const nav=$('breadcrumbs');nav.replaceChildren();const root=el('button','');root.append(icon('folder'),document.createTextNode('Shared folder'));root.addEventListener('click',()=>navigate(''));nav.append(root);let current='';for(const part of state.path.split('/').filter(Boolean)){current=current?current+'/'+part:part;const target=current;nav.append(el('span','crumb-divider','/'));const b=el('button','',part);b.addEventListener('click',()=>navigate(target));nav.append(b)}nav.lastElementChild.setAttribute('aria-current','location');$('upBtn').disabled=!state.path}
async function navigate(path,push=true){if(state.request)state.request.abort();const request=new AbortController();state.request=request;const id=++state.navId;state.loading=true;state.error=false;hideMenu();$('loading').hidden=false;$('empty').hidden=true;$('rows').replaceChildren();$('table').setAttribute('aria-busy','true');$('summary').textContent='Loading your files…';$('pagination').hidden=true;setActionsDisabled(true);try{const data=await api('/api/list?path='+encodeURIComponent(path),undefined,request.signal);if(id!==state.navId)return;const moved=state.path!==data.path;state.path=data.path;state.items=data.items;if(moved){state.selected.clear();state.selectMode=false;$('search').value='';state.kind='all';state.page=0;closeModal()}else{const versions=new Map(state.items.map(i=>[i.path,i.version]));for(const [p,v] of state.selected)if(versions.get(p)!==v)state.selected.delete(p)}if(push&&locationPath()!==path)history.pushState({path},'',path?'/?path='+encodeURIComponent(path):'/');breadcrumb();state.loading=false;$('loading').hidden=true;$('table').setAttribute('aria-busy','false');setActionsDisabled(false);updateCategories();render();document.title=(path?path.split('/').pop()+' · ':'')+'Fshare';if(moved){$('upBtn').focus();window.scrollTo(0,0)}}catch(e){if(e.name!=='AbortError'&&id===state.navId)showLoadError(e.message)}finally{if(id===state.navId)state.loading=false}}
function setActionsDisabled(on){for(const id of ['downloadAll','selectBtn','selectAll','downloadSelected','deleteSelected'])$(id).disabled=on;$('search').disabled=on;$('sort').disabled=on}
function showLoadError(message){state.error=true;state.items=[];state.selected.clear();$('loading').hidden=true;$('rows').replaceChildren();$('empty').hidden=false;$('emptyTitle').textContent='Unable to open this folder';$('emptyMessage').textContent=message;$('emptyAction').hidden=false;$('table').setAttribute('aria-busy','false');$('summary').textContent='Folder unavailable';$('folderSize').textContent='';setActionsDisabled(true);updateSelection()}
$('emptyAction').addEventListener('click',()=>navigate(''));
function updateCategories(){for(const b of $('categories').querySelectorAll('[data-kind]')){b.classList.toggle('active',b.dataset.kind===state.kind);b.setAttribute('aria-pressed',String(b.dataset.kind===state.kind));b.querySelector('.count').textContent=state.items.filter(i=>b.dataset.kind==='all'||i.kind===b.dataset.kind).length.toLocaleString('en')}}
$('categories').addEventListener('click',e=>{const b=e.target.closest('[data-kind]');if(b){state.kind=b.dataset.kind;state.page=0;updateCategories();render()}});
function filtered(){const q=$('search').value.trim().normalize('NFKC').toLocaleLowerCase();let list=state.items.filter(i=>(state.kind==='all'||i.kind===state.kind)&&(!q||i.name.normalize('NFKC').toLocaleLowerCase().includes(q)));const [key,dir]=$('sort').value.split('-');const direction=dir==='desc'?-1:1;list.sort((a,b)=>{if(a.kind==='folder'&&b.kind!=='folder')return -1;if(b.kind==='folder'&&a.kind!=='folder')return 1;let c=key==='name'?collator.compare(a.name,b.name):key==='kind'?collator.compare(a.kind,b.kind):(a[key]||0)-(b[key]||0);return c*direction||collator.compare(a.name,b.name)});return list}
function typeLabel(item){if(item.blocked)return 'Unavailable';if(item.kind==='folder')return 'Folder';if(item.kind!=='file')return item.kind;const dot=item.name.lastIndexOf('.');return dot>0?item.name.slice(dot+1).toUpperCase().slice(0,12)+' file':'File'}
function render(){
 if(state.loading||state.error)return;
 state.filtered=filtered();const count=state.filtered.length;
 const pages=Math.max(1,Math.ceil(count/state.pageSize));state.page=Math.min(state.page,pages-1);
 const start=state.page*state.pageSize,rows=$('rows'),fragment=document.createDocumentFragment();
 for(const item of state.filtered.slice(start,start+state.pageSize)){
  const row=el('div','file-row'+(item.blocked?' blocked':''));row.setAttribute('role','listitem');row.dataset.path=item.path;
  const label=el('label','check-box'),check=el('input');check.type='checkbox';check.tabIndex=-1;check.disabled=item.blocked;
  check.setAttribute('aria-label','Select '+item.name);check.addEventListener('change',()=>toggle(item));label.append(check);
  const open=el('button','open-item');open.type='button';open.setAttribute('aria-label',(item.kind==='folder'?'Open folder ':'Open ')+item.name);open.disabled=item.blocked;
  const image=el('span','file-icon '+item.kind);image.append(icon(item.kind));const text=el('span','file-text');
  text.append(el('span','file-name',item.name));
  text.append(el('span','file-mobile-meta',item.blocked?'Link or unavailable item':typeLabel(item)+(item.kind==='folder'?'':' · '+bytes(item.size))+' · '+date(item.modified)));
  open.append(image,text);open.addEventListener('click',e=>{if(suppressClick){e.preventDefault();return}if(state.selectMode||e.ctrlKey||e.metaKey||e.shiftKey)toggle(item);else activate(item)});
  const kind=el('span','meta-cell type-col kind-label',typeLabel(item)),size=el('span','meta-cell size-col',bytes(item.size)),modified=el('span','meta-cell date-col',date(item.modified));
  modified.title=item.modified?new Date(item.modified*1000).toLocaleString('en'):'';
  const actions=el('div','row-actions');actions.setAttribute('role','group');actions.setAttribute('aria-label','Actions for '+item.name);
  const addAction=(className,label,iconName,run)=>{const b=el('button',className);b.type='button';b.append(icon(iconName),el('span','',label));b.setAttribute('aria-label',label+' '+item.name);b.disabled=item.blocked;b.addEventListener('click',()=>run(item));actions.append(b);return b};
  addAction('row-preview',item.kind==='folder'?'Open folder':'Preview','open',i=>i.kind==='folder'?navigate(i.path):preview(i));
  addAction('row-download',item.kind==='folder'?'Download ZIP':'Download file','download',i=>i.kind==='folder'?startZip([i.path]):downloadFile(i));
  const select=addAction('row-select','Select','check',toggle);select.setAttribute('aria-pressed','false');
  const remove=addAction('row-delete','Delete','trash',i=>requestDelete([i]));remove.disabled=item.blocked||state.session.read_only;
  if(state.session.read_only)remove.title='Deletion is disabled in read-only mode';
  row.append(label,open,kind,size,modified,actions);
  row.addEventListener('contextmenu',e=>{if(item.blocked)return;e.preventDefault();showMenu(item,e.clientX,e.clientY,open)});
  setupLongPress(row,item,open);fragment.append(row);
 }
 rows.replaceChildren(fragment);$('empty').hidden=!!count;$('emptyAction').hidden=true;$('emptyTitle').textContent=state.items.length?'No matching items':'This folder is empty';$('emptyMessage').textContent=state.items.length?'Try another search or choose a different file type.':'Files added on the host computer will appear here after you refresh.';$('pagination').hidden=count<=state.pageSize;$('pageLabel').textContent=(start+1).toLocaleString('en')+'–'+Math.min(start+state.pageSize,count).toLocaleString('en')+' of '+count.toLocaleString('en');$('prevPage').disabled=state.page===0;$('nextPage').disabled=state.page>=pages-1;const folders=state.items.filter(i=>i.kind==='folder').length;$('summary').textContent=(count===state.items.length?count.toLocaleString('en')+' items':count.toLocaleString('en')+' of '+state.items.length.toLocaleString('en')+' items')+' · '+folders.toLocaleString('en')+' folders';$('folderSize').textContent=bytes(state.items.reduce((s,i)=>s+(i.kind!=='folder'?i.size||0:0),0))+' in files';$('clearSearch').hidden=!$('search').value;$('downloadAll').disabled=!state.items.some(i=>!i.blocked);updateSelection()}
function toggle(item){if(item.blocked)return;if(state.selected.has(item.path))state.selected.delete(item.path);else state.selected.set(item.path,item.version);updateSelection()}
function updateSelection(){document.body.classList.toggle('has-selection',state.selected.size>0);for(const row of $('rows').children){const on=state.selected.has(row.dataset.path);row.classList.toggle('selected',on);row.querySelector('input').checked=on;row.querySelector('.open-item').setAttribute('aria-pressed',String(on));const select=row.querySelector('.row-select');select.setAttribute('aria-pressed',String(on));select.querySelector('span').textContent=on?'Deselect':'Select';select.setAttribute('aria-label',(on?'Deselect ':'Select ')+row.querySelector('.file-name').textContent)}const valid=state.filtered.filter(i=>!i.blocked);const n=valid.filter(i=>state.selected.has(i.path)).length;$('selectAll').checked=valid.length>0&&n===valid.length;$('selectAll').indeterminate=n>0&&n<valid.length;$('selectAll').disabled=state.loading||state.error||!valid.length;$('selectionBar').hidden=!state.selected.size;$('selectionCount').textContent=state.selected.size.toLocaleString('en')+' selected';$('selectBtn').setAttribute('aria-pressed',String(state.selectMode));$('selectBtn').classList.toggle('primary',state.selectMode)}
$('selectBtn').addEventListener('click',()=>{state.selectMode=!state.selectMode;updateSelection();if(state.selectMode)toast('Tap items to select them. Space selects the focused item.');else if(!state.selected.size)toast('Selection mode off.')});
$('selectAll').addEventListener('change',()=>{for(const item of state.filtered.filter(i=>!i.blocked)){if($('selectAll').checked)state.selected.set(item.path,item.version);else state.selected.delete(item.path)}updateSelection()});
$('clearSelection').addEventListener('click',()=>{state.selected.clear();state.selectMode=false;updateSelection()});
let searchTimer;$('search').addEventListener('input',()=>{clearTimeout(searchTimer);searchTimer=setTimeout(()=>{state.page=0;render()},100)});$('clearSearch').addEventListener('click',()=>{$('search').value='';state.page=0;render();$('search').focus()});
$('sort').addEventListener('change',()=>{state.page=0;render()});function sortBy(key){const current=$('sort').value;$('sort').value=key+'-'+(current===key+'-asc'?'desc':'asc');if(!$('sort').value)$('sort').value=key+'-asc';render()}
$('sortName').addEventListener('click',()=>sortBy('name'));$('sortType').addEventListener('click',()=>sortBy('kind'));$('sortSize').addEventListener('click',()=>sortBy('size'));$('sortDate').addEventListener('click',()=>sortBy('modified'));
function changePage(delta){state.page+=delta;render();$('table').scrollIntoView({block:'start'});$('rows').querySelector('.open-item:not(:disabled)')?.focus()}
$('prevPage').addEventListener('click',()=>changePage(-1));$('nextPage').addEventListener('click',()=>changePage(1));$('refreshBtn').addEventListener('click',()=>state.session?.authenticated?navigate(state.path,false):connect());
function parent(){if(state.path)navigate(state.path.split('/').slice(0,-1).join('/'))}$('upBtn').addEventListener('click',parent);
window.addEventListener('popstate',()=>{if(state.modal){closeModal();if(locationPath()===state.path)return}navigate(locationPath(),false)});
function fileURL(item,download=true){return '/file?path='+encodeURIComponent(item.path)+(download?'&download=1':'')}
function downloadFile(item){const a=el('a');a.href=fileURL(item);a.download=item.name;document.body.append(a);a.click();a.remove()}
function activate(item){if(item.blocked)return;if(item.kind==='folder'){navigate(item.path);return}if(['image','video','audio'].includes(item.kind)){preview(item);return}downloadFile(item)}
function fallback(item,message){
 destroyPlayer();
 const box=el('div','media-fallback');
 box.append(icon(item.kind),el('h3','','Download to open this file'),el('p','',message||'A preview is not available here. Download the file to open it with a compatible app.'));
 const a=el('a','btn primary','Download file');a.prepend(icon('download'));a.href=fileURL(item);a.download=item.name;box.append(a);$('previewBody').replaceChildren(box);
}
function preview(item){
 destroyPlayer();
 $('previewTitle').textContent=item.name;$('previewMeta').textContent=bytes(item.size)+' · '+date(item.modified);
 $('previewDownload').href=fileURL(item);$('previewDownload').download=item.name;$('previewDownload').setAttribute('aria-label','Download '+item.name);
 const body=$('previewBody'),mkv=/\.mkv$/i.test(item.name);body.replaceChildren();
 $('previewNote').textContent=mkv?'Trying direct MKV playback. Your browser must support both the container and its video/audio codecs.':'Playback support depends on your browser and the file format.';
 openModal('previewModal');
 if(item.kind==='image'){
  const img=el('img');img.alt=item.name;img.addEventListener('error',()=>{if(body.contains(img))fallback(item)},{once:true});img.src=fileURL(item,false);body.append(img);
 }else if(item.kind==='video'||item.kind==='audio'){
  const media=el(item.kind);media.controls=true;media.tabIndex=0;media.preload='metadata';media.setAttribute('playsinline','');
  // MIME capability hints can reject playable MKV files. Let the native decoder inspect the stream.
  media.addEventListener('loadedmetadata',()=>{if(body.contains(media))$('previewNote').textContent=mkv?'Direct MKV playback · seek with the player controls. Browser support also depends on the audio/video codecs.':'Streamed from the host · seek with the player controls.'},{once:true});
  media.addEventListener('error',()=>{if(!body.contains(media))return;const network=media.error?.code===2;media.pause();media.removeAttribute('src');media.load();
   fallback(item,network?'The media connection was interrupted. Check the host and network, then try Preview again.':mkv?'This browser could not decode this MKV container or one of its codecs. Download it, or remux compatible video/audio to MP4 on the host. Unsupported codecs need conversion with an optional tool such as FFmpeg.':'Your browser could not play this file format or its codecs. Download it to open with a compatible app.');
   $('previewNote').textContent=network?'Playback stopped because of a network error.':mkv?'HTTP Range streaming is available; it cannot add missing container or codec support.':'Playback support depends on your browser and the file format.';
  },{once:true});
  body.append(media);startPlayer(media,item);media.src=fileURL(item,false);
 }else fallback(item);
}
// Native streaming stays the source of truth. No media blobs are fetched into JS RAM.
const SUBTITLE_LIMIT=2*1024*1024,MAX_CUES=20000;
function timeLabel(seconds){seconds=Math.max(0,Math.floor(seconds||0));const h=Math.floor(seconds/3600),m=Math.floor(seconds%3600/60),s=seconds%60;return(h?h+':':'')+(h?String(m).padStart(2,'0'):m)+':'+String(s).padStart(2,'0')}
function decodeSubtitle(data,encoding='auto'){
 if(data.byteLength>SUBTITLE_LIMIT)throw Error('Subtitles must be no larger than 2 MB.');
 const raw=new Uint8Array(data);let result;
 if(encoding==='auto'){
  if(raw[0]===255&&raw[1]===254)result=new TextDecoder('utf-16le',{fatal:true}).decode(raw);
  else if(raw[0]===254&&raw[1]===255)result=new TextDecoder('utf-16be',{fatal:true}).decode(raw);
  else{try{result=new TextDecoder('utf-8',{fatal:true}).decode(raw)}catch{result=new TextDecoder('windows-1256',{fatal:true}).decode(raw)}}
 }else result=new TextDecoder(encoding,{fatal:true}).decode(raw);
 if(result.includes('\0'))throw Error('This is not a text subtitle. Save it as UTF-8 SRT or WebVTT.');
 return result;
}
function parseSubtitles(text){
 if(text.length>SUBTITLE_LIMIT)throw Error('Subtitles must be no larger than 2 MB.');
 const timestamp=s=>{const m=/^(?:(\d{1,6}):)?(\d{1,2}):(\d{2})[,.](\d{1,3})$/.exec(s);if(!m||+m[2]>59||+m[3]>59)return NaN;return +(m[1]||0)*3600 + +m[2]*60 + +m[3] + +m[4].padEnd(3,'0')/1000};
 const entities={amp:'&',lt:'<',gt:'>',quot:'"',apos:"'",nbsp:' '};
 const plain=s=>s.replace(/<[^>]*>/g,'').replace(/\{\\[^}]*\}/g,'').replace(/&(#x[\da-f]+|#\d+|amp|lt|gt|quot|apos|nbsp);/gi,(all,key)=>{if(key[0]!=='#')return entities[key.toLowerCase()]||all;const n=key[1].toLowerCase()==='x'?parseInt(key.slice(2),16):parseInt(key.slice(1),10);return n>0&&n<=0x10ffff&&!(n>=0xd800&&n<=0xdfff)?String.fromCodePoint(n):''});
 const cues=[];let skipped=0;
 for(const block of text.replace(/^\uFEFF/,'').replace(/\r\n?/g,'\n').trim().split(/\n[ \t]*\n/)){
  if(!block.trim()||/^(WEBVTT(?:\s|$)|NOTE(?:\s|$)|STYLE(?:\s|$)|REGION(?:\s|$))/.test(block))continue;
  const lines=block.split('\n'),i=lines.findIndex((line,index)=>index<2&&line.includes('-->'));
  if(i<0){skipped++;continue}
  const timing=/^\s*(\S+)\s+-->\s+(\S+)(?:\s+.*)?$/.exec(lines[i]);
  if(!timing){skipped++;continue}
  const start=timestamp(timing[1]),end=timestamp(timing[2]),content=plain(lines.slice(i+1).join('\n')).trim();
  if(!Number.isFinite(start)||!Number.isFinite(end)||end<=start||!content){skipped++;continue}
  if(content.length>5000)throw Error('A subtitle cue is too long.');
  cues.push({start,end,text:content});if(cues.length>MAX_CUES)throw Error('A subtitle may contain at most 20,000 cues.');
 }
 if(!cues.length)throw Error('No valid cues were found. Use a text SRT or WebVTT subtitle.');
 cues.sort((a,b)=>a.start-b.start||a.end-b.end);return{cues,skipped};
}
function playerMessage(text,error=false){const n=$('playerMessage');n.textContent=text;n.hidden=!text;n.classList.toggle('error',error)}
function isPlayer(p){return state.player===p&&!p.destroyed}
function destroyPlayer(){
 const p=state.player;state.player=null;$('playerTools').hidden=true;if(!p)return;
 p.destroyed=true;p.events.abort();p.discovery.abort();p.subtitleRequest?.abort();clearInterval(p.timer);
 stopExternalAudio(p);p.media.pause();p.media.removeAttribute('src');p.media.load();
 for(const track of Array.from(p.media.textTracks))track.mode='disabled';
 if(document.fullscreenElement&&$('previewStage').contains(document.fullscreenElement))document.exitFullscreen?.().catch(()=>{});
 $('subtitleFile').value='';$('audioFile').value='';
}
function playerListen(p,target,type,fn){if(target?.addEventListener)target.addEventListener(type,e=>{if(isPlayer(p))fn(e)},{signal:p.events.signal})}
function subtitleAppearance(){
 const color=$('subtitleColor').value,size=$('subtitleSize').value;
 $('subtitleStyles').textContent='#previewBody video::cue{color:'+color+';font-size:'+size+'px;background-color:rgba(0,0,0,.8);text-shadow:0 1px 2px #000}';
 for(const key of ['Color','Size','Position'])preference('subtitle-'+key.toLowerCase(),$('subtitle'+key).value);
}
function positionCue(cue){
 const position=$('subtitlePosition').value;
 if('snapToLines' in cue){cue.region=null;cue.align='center';cue.size=90;cue.position=50;cue.snapToLines=position==='bottom';cue.line=position==='bottom'?'auto':position==='top'?10:45}
}
function updateSubtitleToggle(p){const active=$('subtitleTrack').value!=='off';$('subtitleToggle').setAttribute('aria-pressed',String(active));$('subtitleToggle').textContent=active?'Hide subtitles':'Show subtitles';$('subtitleToggle').disabled=$('subtitleTrack').options.length<2;if(active)p.lastSubtitle=$('subtitleTrack').value}
function refreshSubtitleOptions(p){
 const select=$('subtitleTrack'),value=select.value;select.replaceChildren(new Option('Off','off'));p.nativeSubs.clear();
 for(const track of Array.from(p.media.textTracks)){
  if(track===p.externalText||!['subtitles','captions'].includes(track.kind))continue;
  if(!p.trackIds.has(track))p.trackIds.set(track,'embedded-sub:'+ ++p.nextTrack);
  const key=p.trackIds.get(track);p.nativeSubs.set(key,track);select.add(new Option('Embedded: '+(track.label||track.language||'Track '+p.nativeSubs.size),key));
 }
 for(const sub of p.sidecars)select.add(new Option(sub.name,'sidecar:'+sub.path));
 if(p.manualSubtitle)select.add(new Option('Local: '+p.manualSubtitle.name,'local'));
 select.value=[...select.options].some(o=>o.value===value)?value:'off';
 $('subtitleHint').textContent=(p.nativeSubs.size?p.nativeSubs.size+' embedded text track(s) exposed by this browser. ':'No embedded text subtitles were exposed by this browser. ')+(p.sidecars.length?p.sidecars.length+' nearby SRT/VTT file(s) detected.':'Load an external SRT/VTT subtitle to add captions.');
 updateSubtitleToggle(p);
}
function applyNativeSubtitles(p){
 const track=p.nativeSubs.get($('subtitleTrack').value);if(!track?.cues)return;
 const signature=$('subtitleOffset').value+'|'+$('subtitlePosition').value,offset=Number($('subtitleOffset').value)||0;
 let unavailable=false;
 for(const cue of Array.from(track.cues)){
  let original=p.cueBases.get(cue);if(!original){original={start:cue.startTime,end:cue.endTime,signature:null};p.cueBases.set(cue,original)}
  if(original.signature===signature)continue;
  try{cue.startTime=Math.max(0,original.start+offset);cue.endTime=Math.max(0,original.end+offset);positionCue(cue);original.signature=signature}catch{unavailable=true}
 }
 if(unavailable)$('subtitleHint').textContent='This browser exposes the track but cannot adjust some embedded cues. Use external SRT/VTT for timing and position controls.';
}
function rebuildExternalSubtitles(p){
 if(!p.externalText||!p.externalCues)return;
 const offset=Number($('subtitleOffset').value)||0,track=p.externalText;
 const previousMode=track.mode;track.mode='hidden';
 // Disabled tracks hide their cue list. Make it readable before removing
 // old cues so switching or re-enabling subtitles never accumulates them.
 for(const cue of Array.from(track.cues||[]))track.removeCue(cue);
 for(const source of p.externalCues){const end=source.end+offset;if(end<=0)continue;
  const safeText=source.text.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
  const cue=new VTTCue(Math.max(0,source.start+offset),end,safeText);positionCue(cue);track.addCue(cue);
 }
 track.mode=previousMode;
}
async function selectSubtitle(key){
 const p=state.player;if(!p||p.media.tagName!=='VIDEO')return;
 p.subtitleRequest?.abort();const serial=++p.subtitleSerial;p.subtitleLoading=key!=='off'&&!p.nativeSubs.has(key);
 $('subtitleTrack').value=key;for(const track of Array.from(p.media.textTracks))track.mode='disabled';updateSubtitleToggle(p);
 if(key==='off')return;
 if(p.nativeSubs.has(key)){const track=p.nativeSubs.get(key);track.mode='showing';applyNativeSubtitles(p);return}
 if(typeof VTTCue!=='function'){p.subtitleLoading=false;playerMessage('This browser cannot create subtitle cues. Use a newer browser.',true);$('subtitleTrack').value='off';updateSubtitleToggle(p);return}
 try{
  $('subtitleHint').textContent='Loading subtitle…';let text;
  if(key==='local')text=decodeSubtitle(await p.manualSubtitle.arrayBuffer(),$('subtitleEncoding').value);
  else{const path=key.slice(8);p.subtitleRequest=new AbortController();const result=await api('/api/subtitle?path='+encodeURIComponent(path)+'&encoding='+encodeURIComponent($('subtitleEncoding').value),undefined,p.subtitleRequest.signal);text=result.text}
  if(!isPlayer(p)||p.subtitleSerial!==serial)return;
  const parsed=parseSubtitles(text);p.externalCues=parsed.cues;
  if(!p.externalText)p.externalText=p.media.addTextTrack('subtitles','External subtitles');
  rebuildExternalSubtitles(p);p.externalText.mode='showing';p.subtitleLoading=false;
  $('subtitleHint').textContent=parsed.cues.length.toLocaleString('en')+' cues loaded'+(parsed.skipped?' · '+parsed.skipped+' malformed block(s) skipped.':'.');
  playerMessage('');updateSubtitleToggle(p);
 }catch(e){if(!isPlayer(p)||p.subtitleSerial!==serial||e.name==='AbortError')return;p.subtitleLoading=false;$('subtitleTrack').value='off';updateSubtitleToggle(p);$('subtitleHint').textContent=e.message;playerMessage('Subtitle could not be loaded: '+e.message,true)}
}
function refreshAudioOptions(p){
 const select=$('audioTrack'),value=select.value;select.replaceChildren(new Option('Original audio (browser default)','original'));p.nativeAudio.clear();
 const tracks=p.media.audioTracks;
 if(tracks)for(let i=0;i<tracks.length;i++){p.nativeAudio.set('embedded-audio:'+i,tracks[i]);select.add(new Option('Embedded: '+(tracks[i].label||tracks[i].language||'Track '+(i+1)),'embedded-audio:'+i))}
 for(const audio of p.nearbyAudio)select.add(new Option(audio.name,'audio-file:'+audio.path));
 if(p.manualAudio)select.add(new Option('Local: '+p.manualAudio.name,'local-audio'));
 select.value=[...select.options].some(o=>o.value===value)?value:'original';
 $('audioTrackHint').textContent=tracks?.length?tracks.length+' embedded audio track(s) available.':'This browser does not expose selectable embedded audio tracks. Original audio and external files are available.';
}
function stopExternalAudio(p){
 p.audioSerial++;const a=p.external;if(a){p.external=null;a.pause();a.removeAttribute('src');a.load();a.remove()}
 if(p.audioObjectURL){URL.revokeObjectURL(p.audioObjectURL);p.audioObjectURL=null}
 if(p.savedMuted!==null){p.media.muted=p.savedMuted;p.savedMuted=null}
 p.audioPlaying=false;p.holding=false;p.audioBoundary=null;$('externalVolume').hidden=true;
 for(const id of ['audioOffset','audioEarlier','audioLater','audioReset'])$(id).disabled=true;
}
function playExternal(p){
 const a=p.external;if(!a||p.audioPlaying||!a.paused)return;
 p.audioPlaying=true;const serial=p.audioSerial;
 a.play().catch(e=>{if(!isPlayer(p)||p.audioSerial!==serial||e.name==='AbortError')return;p.wantPlay=false;p.holding=false;p.media.pause();playerMessage(e.name==='NotAllowedError'?'Press Play to allow both video and external audio.':'External audio could not play. Choose another audio source.',true)}).finally(()=>{if(isPlayer(p)&&p.audioSerial===serial)p.audioPlaying=false});
}
function audioTarget(p){return p.media.currentTime-(Number($('audioOffset').value)||0)}
function syncExternal(p,force=false){
 const a=p.external,v=p.media;if(!a||a.readyState<1)return;
 const target=audioTarget(p);
 if(target<0||Number.isFinite(a.duration)&&target>=a.duration){p.audioBoundary=target<0?'delayed':'ended';a.pause();if(p.holding&&p.wantPlay){p.holding=false;v.play().catch(()=>{})}return}
 p.audioBoundary=null;
 if((force&&Math.abs(a.currentTime-target)>.03)||Math.abs(a.currentTime-target)>.2){try{a.currentTime=target}catch{}}
 const drift=target-a.currentTime;
 a.playbackRate=v.playbackRate*(Math.abs(drift)>.04&&Math.abs(drift)<=.2?1+Math.sign(drift)*.03:1);
 if(!p.wantPlay||v.seeking||p.videoWaiting){a.pause();return}
 if(p.holding){if(a.readyState>=3&&!a.seeking){p.holding=false;v.play().catch(e=>{if(isPlayer(p)){p.wantPlay=false;playerMessage('Press Play to resume playback.',true)}})}return}
 if(!v.paused){if(a.readyState<2||a.seeking){p.holding=true;v.pause();a.pause();return}playExternal(p)}
}
function selectAudio(key){
 const p=state.player;if(!p||p.media.tagName!=='VIDEO')return;
 const wanted=p.wantPlay;stopExternalAudio(p);p.wantPlay=wanted;$('audioTrack').value=key;
 if(key==='original'||p.nativeAudio.has(key)){
  const tracks=p.media.audioTracks;
  if(tracks){const chosen=p.nativeAudio.get(key);for(let i=0;i<tracks.length;i++)tracks[i].enabled=chosen?tracks[i]===chosen:p.originalAudio[i]===true}
  $('audioSyncHint').textContent='Independent timing is available for external audio. Embedded audio remains aligned by the browser.';
  playerMessage('');if(wanted&&p.media.paused)p.media.play().catch(()=>{});return;
 }
 const a=el('audio','external-audio');a.preload=p.media.preload;a.setAttribute('aria-hidden','true');a.tabIndex=-1;
 p.external=a;p.savedMuted=p.media.muted;p.media.muted=true;a.playbackRate=p.media.playbackRate;a.volume=Number($('externalVolumeLevel').value);a.muted=false;
 $('externalMute').setAttribute('aria-pressed','false');$('externalMute').textContent='Mute external audio';
 for(const id of ['audioOffset','audioEarlier','audioLater','audioReset'])$(id).disabled=false;
 $('externalVolume').hidden=false;$('audioSyncHint').textContent='External audio follows video play, pause, seek and speed. Positive delay plays the audio later.';
 playerMessage('Loading external audio…');const serial=p.audioSerial;
 const listen=(type,fn)=>a.addEventListener(type,()=>{if(isPlayer(p)&&p.external===a&&p.audioSerial===serial)fn()},{signal:p.events.signal});
 listen('loadedmetadata',()=>{syncExternal(p,true);playerMessage('External audio active. The original soundtrack is muted.')});
 listen('canplay',()=>syncExternal(p));listen('seeked',()=>syncExternal(p));
 listen('waiting',()=>{if(p.wantPlay&&!p.media.paused){p.holding=true;p.media.pause();a.pause();playerMessage('Buffering external audio…')}});
 listen('playing',()=>{if(!p.wantPlay||p.media.seeking||p.videoWaiting)a.pause();else if($('playerMessage').textContent==='Buffering external audio…')playerMessage('External audio active. The original soundtrack is muted.')});
 listen('error',()=>{const code=a.error?.code;selectAudio('original');playerMessage(code===2?'External audio connection interrupted; original audio restored.':'This browser cannot decode the external audio; original audio restored.',true)});
 if(wanted){p.holding=true;p.media.pause()}
 if(key==='local-audio'){p.audioObjectURL=URL.createObjectURL(p.manualAudio);a.src=p.audioObjectURL}
 else a.src='/file?path='+encodeURIComponent(key.slice(11));
 $('previewBody').append(a);
 // Call play within the source-selection gesture; this also allows iOS to unlock the audio element.
 if(wanted&&audioTarget(p)>=0)playExternal(p);
 syncExternal(p,true);
}
function bufferAhead(media){const t=media.currentTime,r=media.buffered;for(let i=0;i<r.length;i++)if(r.start(i)<=t+.05&&r.end(i)>t)return r.end(i)-t;return 0}
function updatePlayer(p){
 const v=p.media;syncExternal(p);applyNativeSubtitles(p);
 $('playerPlay').textContent=p.wantPlay?'Pause':'Play';
 const ahead=p.external&&!p.audioBoundary?Math.min(bufferAhead(v),audioTarget(p)>=0?bufferAhead(p.external):bufferAhead(v)):bufferAhead(v);
 const status=p.holding?'buffering audio':p.videoWaiting?'buffering':v.paused?'paused':v.networkState===2?'receiving':'playing';
 const audioNote=p.audioBoundary==='ended'?' · external audio ended':p.audioBoundary==='delayed'?' · audio starts after its delay':'';
 $('playerBuffer').textContent='Buffered ahead '+timeLabel(ahead)+' · '+status+audioNote+' · browser-managed';
 let total=0;for(let i=0;i<v.buffered.length;i++)total+=v.buffered.end(i)-v.buffered.start(i);
 $('playerBufferMeter').value=Number.isFinite(v.duration)&&v.duration>0?Math.min(1,total/v.duration):0;
 for(const id of ['playerBack','playerForward'])$(id).disabled=!Number.isFinite(v.duration)||v.duration<=0;
}
async function startPlayer(media,item){
 const p={media,item,events:new AbortController(),discovery:new AbortController(),nativeSubs:new Map(),nativeAudio:new Map(),trackIds:new WeakMap(),cueBases:new WeakMap(),nextTrack:0,sidecars:[],nearbyAudio:[],subtitleSerial:0,audioSerial:0,external:null,savedMuted:null,originalAudio:[],wantPlay:false,videoWaiting:false,holding:false,destroyed:false};
 state.player=p;$('playerTools').hidden=false;playerMessage('');$('subtitleSettings').hidden=item.kind!=='video';$('audioSettings').hidden=item.kind!=='video';
 $('playerSettings').open=false;$('subtitleOffset').value='0';$('audioOffset').value='0';$('subtitleEncoding').value='auto';$('subtitleTrack').value='off';$('audioTrack').value='original';$('externalVolume').hidden=true;
 for(const id of ['audioOffset','audioEarlier','audioLater','audioReset'])$(id).disabled=true;
 for(const key of ['Color','Size','Position']){const select=$('subtitle'+key),value=preference('subtitle-'+key.toLowerCase());select.value=[...select.options].some(o=>o.value===value)?value:key==='Color'?'#ffffff':key==='Size'?'24':'bottom'}
 subtitleAppearance();
 const rate=preference('player-rate');$('playerRate').value=[...$('playerRate').options].some(o=>o.value===rate)?rate:'1';
 try{media.playbackRate=Number($('playerRate').value)}catch{$('playerRate').value='1'}
 const preload=preference('player-preload')||((navigator.connection?.saveData||navigator.deviceMemory<=2)?'metadata':'auto');$('playerPreload').value=preload==='metadata'?'metadata':'auto';media.preload=$('playerPreload').value;
 // Native events are queued. Ignore stale events after rapid play/pause or
 // an audio-source switch, and preserve the intent to resume after buffering.
 playerListen(p,media,'play',()=>{if(media.paused)return;p.wantPlay=true;p.holding=false;syncExternal(p,true);updatePlayer(p)});
 playerListen(p,media,'pause',()=>{if(!media.paused)return;if(!p.holding)p.wantPlay=false;p.external?.pause();updatePlayer(p)});
 playerListen(p,media,'waiting',()=>{if(media.readyState>=3)return;p.videoWaiting=true;p.external?.pause();updatePlayer(p)});
 playerListen(p,media,'playing',()=>{if(media.paused)return;p.videoWaiting=false;syncExternal(p,true);updatePlayer(p)});
 playerListen(p,media,'canplay',()=>{p.videoWaiting=false;updatePlayer(p)});
 playerListen(p,media,'seeking',()=>{p.videoWaiting=false;p.external?.pause()});
 playerListen(p,media,'seeked',()=>{syncExternal(p,true);updatePlayer(p)});
 playerListen(p,media,'ended',()=>{if(!media.ended)return;p.wantPlay=false;p.holding=false;p.external?.pause();updatePlayer(p)});
 playerListen(p,media,'ratechange',()=>{if(p.external)p.external.playbackRate=media.playbackRate;updatePlayer(p)});
 playerListen(p,media,'volumechange',()=>{if(p.external&&!media.muted)media.muted=true});
 playerListen(p,media,'loadedmetadata',()=>{p.originalAudio=media.audioTracks?Array.from(media.audioTracks).map(t=>t.enabled):[];refreshAudioOptions(p);refreshSubtitleOptions(p);updatePlayer(p)});
 playerListen(p,media,'progress',()=>updatePlayer(p));playerListen(p,document,'visibilitychange',()=>syncExternal(p,true));
 playerListen(p,media.textTracks,'addtrack',()=>refreshSubtitleOptions(p));playerListen(p,media.textTracks,'removetrack',()=>refreshSubtitleOptions(p));
 playerListen(p,media.textTracks,'change',()=>{if(p.subtitleLoading)return;const showing=Array.from(media.textTracks).find(t=>t.mode==='showing'&&['subtitles','captions'].includes(t.kind));if(showing===p.externalText)return;const key=showing?p.trackIds.get(showing):'off';if(key&&$('subtitleTrack').value!==key){$('subtitleTrack').value=key;updateSubtitleToggle(p)}applyNativeSubtitles(p)});
 playerListen(p,media.audioTracks,'addtrack',()=>refreshAudioOptions(p));playerListen(p,media.audioTracks,'removetrack',()=>refreshAudioOptions(p));
 refreshSubtitleOptions(p);refreshAudioOptions(p);updatePlayer(p);p.timer=setInterval(()=>{if(isPlayer(p))updatePlayer(p)},250);
 if(item.kind!=='video')return;
 try{const options=await api('/api/media?path='+encodeURIComponent(item.path),undefined,p.discovery.signal);if(!isPlayer(p))return;p.sidecars=options.subtitles;p.nearbyAudio=options.audio;refreshSubtitleOptions(p);refreshAudioOptions(p)}catch(e){if(isPlayer(p)&&e.name!=='AbortError')playerMessage('Sidecar discovery failed: '+e.message+'. Local files can still be loaded.',true)}
}
function togglePlayback(){const p=state.player;if(!p)return;if(p.wantPlay){p.wantPlay=false;p.holding=false;p.media.pause();p.external?.pause();updatePlayer(p)}else{p.wantPlay=true;p.videoWaiting=false;if(p.media.ended)p.media.currentTime=0;
 if(p.external&&audioTarget(p)>=0)playExternal(p);
 p.media.play().catch(e=>{if(isPlayer(p)){p.wantPlay=false;playerMessage('Could not start playback: '+e.message,true);updatePlayer(p)}})}}
$('playerPlay').addEventListener('click',togglePlayback);
function seekPlayer(delta){const p=state.player;if(p&&Number.isFinite(p.media.duration))p.media.currentTime=Math.max(0,Math.min(p.media.duration,p.media.currentTime+delta))}
$('playerBack').addEventListener('click',()=>seekPlayer(-10));$('playerForward').addEventListener('click',()=>seekPlayer(10));
$('playerRate').addEventListener('change',()=>{const p=state.player;if(!p)return;try{p.media.playbackRate=Number($('playerRate').value);preference('player-rate',$('playerRate').value)}catch{playerMessage('This browser does not support that playback speed.',true);$('playerRate').value=String(p.media.playbackRate)}});
$('playerPreload').addEventListener('change',()=>{const p=state.player;if(p){p.media.preload=$('playerPreload').value;if(p.external)p.external.preload=p.media.preload;preference('player-preload',p.media.preload)}});
$('playerFullscreen').addEventListener('click',async()=>{const p=state.player;if(!p)return;try{if(document.fullscreenElement)await document.exitFullscreen();else if($('previewStage').requestFullscreen)await $('previewStage').requestFullscreen();else if(p.media.webkitEnterFullscreen)p.media.webkitEnterFullscreen();else playerMessage('Fullscreen is unavailable in this browser.',true)}catch{playerMessage('Fullscreen was not allowed. Use the native player fullscreen control.',true)}});
$('subtitleTrack').addEventListener('change',()=>selectSubtitle($('subtitleTrack').value));
$('subtitleToggle').addEventListener('click',()=>{const p=state.player;if(p)selectSubtitle($('subtitleTrack').value==='off'?(p.lastSubtitle||$('subtitleTrack').options[1]?.value||'off'):'off')});
$('subtitleLoad').addEventListener('click',()=>$('subtitleFile').click());
$('subtitleFile').addEventListener('change',()=>{const p=state.player,file=$('subtitleFile').files[0];if(!p||!file)return;if(!/\.(srt|vtt)$/i.test(file.name)||file.size>SUBTITLE_LIMIT){playerMessage('Choose an SRT or WebVTT file no larger than 2 MB.',true);return}p.manualSubtitle=file;refreshSubtitleOptions(p);selectSubtitle('local')});
$('subtitleEncoding').addEventListener('change',()=>{const key=$('subtitleTrack').value;if(key==='local'||key.startsWith('sidecar:'))selectSubtitle(key)});
function changeOffset(kind,delta=null){const p=state.player;if(!p)return;const input=$(kind+'Offset');const previous=Number(input.value);const n=delta===null?previous:previous+delta;input.value=String(Math.max(-120,Math.min(120,Number.isFinite(n)?Math.round(n*100)/100:0)));if(kind==='subtitle'){if(p.externalText?.mode==='showing')rebuildExternalSubtitles(p);applyNativeSubtitles(p)}else syncExternal(p,true)}
for(const kind of ['subtitle','audio']){const step=kind==='subtitle'?.25:.1;$(kind+'Earlier').addEventListener('click',()=>changeOffset(kind,-step));$(kind+'Later').addEventListener('click',()=>changeOffset(kind,step));$(kind+'Reset').addEventListener('click',()=>{$(kind+'Offset').value='0';changeOffset(kind)});$(kind+'Offset').addEventListener('change',()=>changeOffset(kind))}
for(const id of ['subtitleColor','subtitleSize','subtitlePosition'])$(id).addEventListener('change',()=>{subtitleAppearance();const p=state.player;if(p){if(p.externalText?.mode==='showing')rebuildExternalSubtitles(p);applyNativeSubtitles(p)}});
$('audioTrack').addEventListener('change',()=>selectAudio($('audioTrack').value));$('audioLoad').addEventListener('click',()=>$('audioFile').click());
$('audioFile').addEventListener('change',()=>{const p=state.player,file=$('audioFile').files[0];if(!p||!file)return;p.manualAudio=file;refreshAudioOptions(p);selectAudio('local-audio')});
$('externalMute').addEventListener('click',()=>{const a=state.player?.external;if(a){a.muted=!a.muted;$('externalMute').setAttribute('aria-pressed',String(a.muted));$('externalMute').textContent=a.muted?'Unmute external audio':'Mute external audio'}});
$('externalVolumeLevel').addEventListener('input',()=>{const a=state.player?.external;if(a){try{a.volume=Number($('externalVolumeLevel').value)}catch{playerMessage('Use your device volume buttons on this browser.')}}});

let menuFocus=null;function showMenu(item,x,y,focus){hideMenu(false);state.menuItem=item;menuFocus=focus;$('menuTitle').textContent=item.name;$('menuOpenText').textContent=item.kind==='folder'?'Open folder':['image','video','audio'].includes(item.kind)?'Preview':'Download file';$('menuDownloadText').textContent=item.kind==='folder'?'Download folder ZIP':'Download file';$('menuSelectText').textContent=state.selected.has(item.path)?'Deselect':'Select';$('menu').hidden=false;const r=$('menu').getBoundingClientRect();$('menu').style.left=Math.max(8,Math.min(x,innerWidth-r.width-8))+'px';$('menu').style.top=Math.max(8,Math.min(y,innerHeight-r.height-8))+'px';$('menuOpen').focus()}
function hideMenu(restore=true){if(!$('menu').hidden){$('menu').hidden=true;if(restore&&menuFocus?.isConnected)menuFocus.focus()}state.menuItem=null}
document.addEventListener('click',e=>{if(!$('menu').hidden&&!$('menu').contains(e.target))hideMenu(false)});window.addEventListener('scroll',()=>hideMenu(false),{passive:true});window.addEventListener('resize',()=>hideMenu(false));
function menuAction(fn){const item=state.menuItem;hideMenu();if(item)fn(item)}
$('menuOpen').addEventListener('click',()=>menuAction(activate));$('menuDownload').addEventListener('click',()=>menuAction(item=>item.kind==='folder'?startZip([item.path]):downloadFile(item)));$('menuSelect').addEventListener('click',()=>menuAction(toggle));$('menuDelete').addEventListener('click',()=>menuAction(item=>requestDelete([item])));
let suppressClick=false;function setupLongPress(row,item,focus){let timer=null,point=null;function stop(){clearTimeout(timer);timer=null}row.addEventListener('pointerdown',e=>{if(e.pointerType==='mouse'||item.blocked||e.target.closest('.check-box,.row-actions'))return;point={x:e.clientX,y:e.clientY};timer=setTimeout(()=>{suppressClick=true;showMenu(item,point.x,point.y,focus);setTimeout(()=>suppressClick=false,900)},600)});row.addEventListener('pointermove',e=>{if(point&&(Math.abs(e.clientX-point.x)>12||Math.abs(e.clientY-point.y)>12))stop()});for(const type of ['pointerup','pointercancel','pointerleave'])row.addEventListener(type,stop)}
async function requestDelete(items){if(state.session.read_only)return;hideMenu();$('deleteSelected').disabled=true;try{state.plan=await api('/api/delete/plan',{items:items.map(i=>({path:i.path,version:i.version}))});$('deleteList').replaceChildren();for(const item of state.plan.items.slice(0,30))$('deleteList').append(el('li','',(item.folder?'Folder: ':'File: ')+item.path.split('/').pop()));if(state.plan.items.length>30)$('deleteList').append(el('li','muted','And '+(state.plan.items.length-30)+' more items'));$('deleteTitle').textContent='Delete '+state.plan.items.length+' item'+(state.plan.items.length===1?'':'s')+'?';$('deleteAgree').checked=false;$('deleteConfirm').disabled=true;$('deleteError').hidden=true;openModal('deleteModal')}catch(e){toast(e.message,true)}finally{$('deleteSelected').disabled=false}}
$('deleteSelected').addEventListener('click',()=>requestDelete(state.items.filter(i=>state.selected.has(i.path))));$('deleteAgree').addEventListener('change',()=>{$('deleteConfirm').disabled=!$('deleteAgree').checked});
$('deleteConfirm').addEventListener('click',async()=>{if(!state.plan||!$('deleteAgree').checked)return;const b=$('deleteConfirm');b.disabled=true;b.dataset.busy='1';b.textContent='Deleting…';$('deleteCancel').disabled=true;$('deleteAgree').disabled=true;try{const result=await api('/api/delete',{id:state.plan.id,confirm:'delete'});for(const path of result.deleted)state.selected.delete(path);if(result.errors.length){$('deleteError').textContent=result.errors.slice(0,5).map(i=>i.path+': '+i.error).join('\n');$('deleteError').hidden=false;toast(result.deleted.length+' deleted; '+result.errors.length+' could not be deleted.',true)}else{b.dataset.busy='0';closeModal();toast(result.deleted.length+' item'+(result.deleted.length===1?'':'s')+' deleted.')}await navigate(state.path,false)}catch(e){$('deleteError').textContent=e.message;$('deleteError').hidden=false}finally{b.dataset.busy='0';b.disabled=true;b.textContent='Delete permanently';$('deleteCancel').disabled=false;$('deleteAgree').disabled=false;state.plan=null}});
async function startZip(paths,all=false){hideMenu();if(state.zip){openModal('zipModal');toast('Finish or cancel the current ZIP first.');return}$('zipTitle').textContent='Preparing your ZIP';$('zipStatus').textContent='Getting started…';$('zipCurrent').textContent='';$('zipFiles').textContent='0 files';$('zipBytes').textContent='0 B';$('zipProgress').value=0;$('zipDownload').hidden=true;$('zipCancel').hidden=false;$('zipCancel').textContent='Cancel ZIP';$('zipBrowse').hidden=false;$('zipNote').textContent='You can browse other folders while this runs.';openModal('zipModal');try{state.zip=await api('/api/zip',all?{path:state.path,all:true}:{path:state.path,paths});updateZip(state.zip);pollZip()}catch(e){$('zipTitle').textContent='Could not prepare ZIP';$('zipStatus').textContent=e.message;$('zipCancel').textContent='Close';$('zipBrowse').hidden=true}}
function updateZip(job){const ready=job.state==='ready',failed=['error','cancelled'].includes(job.state);$('zipProgress').value=ready?100:job.total_bytes?Math.min(99,job.bytes/job.total_bytes*100):0;$('zipFiles').textContent=job.files.toLocaleString('en')+' / '+job.total_files.toLocaleString('en')+' files';$('zipBytes').textContent=bytes(job.bytes)+' / '+bytes(job.total_bytes);$('zipCurrent').textContent=job.current;$('zipTitle').textContent=ready?'Your ZIP is ready':failed?'ZIP '+(job.state==='cancelled'?'cancelled':'could not be prepared'):'Preparing your ZIP';$('zipStatus').textContent=ready?job.name:failed?job.error:job.state==='scanning'?'Counting files and checking space…':job.state==='queued'?'Waiting for an available ZIP worker…':'Adding files to your archive…';$('zipDownload').hidden=!ready;$('zipDownload').href='/zip/'+job.id;$('zipDownload').download=job.name;$('zipCancel').textContent=failed?'Close':ready?'Discard ZIP':'Cancel ZIP';$('zipNote').textContent=[job.skipped?job.skipped+' symbolic links or unavailable entries were excluded.':'',job.renamed?'Special filename characters in '+job.renamed+' archive paths were encoded as %XX for compatibility.':''].filter(Boolean).join(' ')||'You can browse other folders while this runs.';$('zipBrowse').hidden=failed;$('zipReopenLabel').textContent=ready?'ZIP ready':failed?'ZIP status':'Preparing ZIP…';$('zipReopen').hidden=state.modal==='zipModal';if(ready&&state.modal!=='zipModal')toast('Your ZIP is ready. Choose “ZIP ready” to download it.');if(failed&&state.modal!=='zipModal')toast(job.error||'ZIP preparation stopped.',true)}
async function pollZip(){clearTimeout(state.zipTimer);if(!state.zip)return;try{const job=await api('/api/zip/'+state.zip.id);state.zip=job;updateZip(job);if(!['ready','error','cancelled'].includes(job.state))state.zipTimer=setTimeout(pollZip,800)}catch(e){$('zipStatus').textContent=e.message;$('zipCancel').textContent='Close';$('zipBrowse').hidden=true;$('zipReopenLabel').textContent='ZIP connection lost'}}
$('downloadAll').addEventListener('click',()=>startZip([],true));$('downloadSelected').addEventListener('click',()=>startZip([...state.selected.keys()]));
$('zipBrowse').addEventListener('click',()=>{closeModal();$('zipReopen').hidden=!state.zip});$('zipReopen').addEventListener('click',()=>{openModal('zipModal');$('zipReopen').hidden=true;if(state.zip)pollZip()});
$('zipCancel').addEventListener('click',async()=>{clearTimeout(state.zipTimer);if(state.zip){try{await api('/api/zip/'+state.zip.id+'/cancel',{})}catch(e){toast(e.message,true)}}state.zip=null;$('zipReopen').hidden=true;closeModal()});
$('zipDownload').addEventListener('click',()=>{clearTimeout(state.zipTimer);state.zip=null;$('zipReopen').hidden=true;closeModal();toast('Download handed to your browser. Keep the host running until it finishes.')});
document.addEventListener('keydown',e=>{const target=e.target;const tvMode=document.body.classList.contains('tv');const tvArrow=tvMode&&target.matches('select,input')&&['ArrowUp','ArrowDown'].includes(e.key);if(tvMode&&target.matches('select')&&['ArrowLeft','ArrowRight'].includes(e.key)){e.preventDefault();target.selectedIndex=Math.max(0,Math.min(target.options.length-1,target.selectedIndex+(e.key==='ArrowRight'?1:-1)));target.dispatchEvent(new Event('change'));return}if(tvMode&&state.modal==='previewModal'&&$('playerTools').contains(target)&&['ArrowUp','ArrowDown'].includes(e.key)){const controls=focusable($('previewModal')).filter(n=>!n.matches('video,audio'));const next=controls[controls.indexOf(target)+(e.key==='ArrowDown'?1:-1)];e.preventDefault();if(next){next.focus();next.scrollIntoView({block:'nearest'})}return}const typing=target.matches('input:not([type=checkbox]),textarea,select');if(state.modal){if(e.key==='Escape'||e.key==='BrowserBack'||e.key==='GoBack'){e.preventDefault();closeModal();if(state.zip&&state.modal!=='zipModal')$('zipReopen').hidden=false;return}if(e.key==='Tab'){const items=focusable($(state.modal));const first=items[0],last=items[items.length-1];if(e.shiftKey&&(target===first||!$(state.modal).contains(target))){e.preventDefault();last?.focus()}else if(!e.shiftKey&&target===last){e.preventDefault();first?.focus()}}if((typing&&!tvArrow)||target.matches('video,audio'))return}else if(!typing){if(e.key==='/'&&!e.ctrlKey&&!e.metaKey){e.preventDefault();$('search').focus();return}if(e.altKey&&e.key==='ArrowUp'){e.preventDefault();parent();return}if((e.key==='a')&&(e.ctrlKey||e.metaKey)){e.preventDefault();$('selectAll').checked=true;$('selectAll').dispatchEvent(new Event('change'));return}if(e.key==='Delete'&&state.selected.size){e.preventDefault();requestDelete(state.items.filter(i=>state.selected.has(i.path)));return}}
if(!$('menu').hidden){if(e.key==='Escape'){e.preventDefault();hideMenu();return}if(e.key==='ArrowDown'||e.key==='ArrowUp'){const buttons=focusable($('menu'));const index=buttons.indexOf(target);e.preventDefault();buttons[(index+(e.key==='ArrowDown'?1:-1)+buttons.length)%buttons.length]?.focus();return}}
const row=target.closest('.file-row');const item=row?state.items.find(i=>i.path===row.dataset.path):null;if(item&&!typing){if(e.key===' '&&target.classList.contains('open-item')){e.preventDefault();toggle(item);return}if((e.shiftKey&&e.key==='F10')||e.key==='ContextMenu'){e.preventDefault();const r=target.getBoundingClientRect();showMenu(item,r.left+30,r.bottom,target);return}}
if(e.key==='Escape'&&!state.modal){hideMenu();if(state.selected.size){state.selected.clear();updateSelection()}return}if((typing&&!tvArrow)||target.matches('video,audio')||target.matches('input[type=checkbox]')&&!tvArrow)return;if(row&&['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.key)){
 const title=row.querySelector('.open-item'),actions=[...row.querySelectorAll('.row-actions button:not(:disabled)')];
 const titles=[...$('rows').querySelectorAll('.open-item:not(:disabled)')],index=titles.indexOf(title);let next=null;
 if(target===title){if(e.key==='ArrowDown'||e.key==='ArrowRight')next=actions[0];else if(e.key==='ArrowUp')next=titles[index-1]}
 else if(actions.includes(target)){const i=actions.indexOf(target);if(e.key==='ArrowLeft')next=actions[i-1]||title;else if(e.key==='ArrowRight')next=actions[i+1];else if(e.key==='ArrowUp')next=title;else if(e.key==='ArrowDown')next=titles[index+1]}
 if(next){e.preventDefault();next.focus();next.scrollIntoView({block:'nearest'});return}
}
if(['ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.key)){if(target===document.body||target===document.documentElement){const first=$('rows').querySelector('.open-item:not(:disabled)')||$('breadcrumbs').querySelector('button');if(first){e.preventDefault();first.focus();return}}const root=state.modal?$(state.modal):$('app');const candidates=focusable(root).concat(!state.modal&&!$('selectionBar').hidden?focusable($('selectionBar')):[]);const r=target.getBoundingClientRect();const x=r.left+r.width/2,y=r.top+r.height/2;let best=null,score=Infinity;for(const n of candidates){if(n===target)continue;const b=n.getBoundingClientRect();const dx=b.left+b.width/2-x,dy=b.top+b.height/2-y;const vertical=e.key==='ArrowUp'||e.key==='ArrowDown';const forward=e.key==='ArrowDown'?dy:e.key==='ArrowUp'?-dy:e.key==='ArrowRight'?dx:-dx;if(forward<5)continue;const sideways=Math.abs(vertical?dx:dy);const distance=forward+sideways*3;if(distance<score){score=distance;best=n}}if(best){e.preventDefault();best.focus();best.scrollIntoView({block:'nearest'})}}
});
connect();
})();
</script>
</body>
</html>'''


def main():
    parser = argparse.ArgumentParser(description='Share the current directory over your local network. Python standard library only.', epilog='Example: cd Movies && python /path/to/server.py --password')
    parser.add_argument('--port', type=int, default=None, help='TCP port (default: first available port from 8000 to 8019)')
    parser.add_argument('--host', default='0.0.0.0', help='IPv4 bind address (default: all interfaces)')
    parser.add_argument('--password', action='store_true', help='Prompt for an optional password without echoing it')
    parser.add_argument('--read-only', action='store_true', help='Disable all deletion operations')
    parser.add_argument('--self-test', action='store_true', help='Run built-in HTTP, ZIP, path-security, and deletion tests in temporary folders')
    args = parser.parse_args()
    if args.self_test:
        run_tests()
        return
    def interrupted(signum, frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    if args.port is not None and not 0 <= args.port <= 65535:
        parser.error('--port must be between 0 and 65535 (0 chooses an available port).')
    password = os.environ.get('FSHARE_PASSWORD', '')
    if args.password:
        password = getpass.getpass('Access password: ')
        if not password:
            parser.error('The password must not be empty.')
    root = os.getcwd()
    server = None
    try:
        for port in ([args.port] if args.port is not None else range(8000, 8020)):
            try:
                server = FileServer((args.host, port), root, password, args.read_only)
                break
            except OSError as exc:
                if exc.errno != errno.EADDRINUSE or args.port is not None:
                    raise
        if server is None:
            raise OSError('Ports 8000–8019 are busy; choose a port with --port.')
        port = server.server_port
        print('\n  Fshare · Local network file manager')
        print('  Shared folder: %s' % root)
        print('  This computer: http://127.0.0.1:%d' % port)
        if args.host in ('0.0.0.0', ''):
            addresses = local_ips()
        else:
            addresses = [args.host]
        for address in addresses:
            print('  Network:       http://%s:%d' % (address, port))
        if not addresses:
            print('  No LAN IPv4 address detected. Connect to a local network and restart.')
        print('  Access: %s · Delete: %s' % ('Password protected' if password else 'Anyone on this network', 'disabled' if args.read_only else 'requires confirmation'))
        print('  Allow Python through your firewall if another device cannot connect.')
        print('  Keep this terminal open. Press Ctrl+C to stop.\n', flush=True)
        server.serve_forever(poll_interval=0.3)
    except KeyboardInterrupt:
        print('\nStopping Fshare and removing temporary ZIPs…', flush=True)
    except (OSError, ValueError) as exc:
        print('Could not start Fshare: %s' % exc, file=sys.stderr)
        sys.exit(1)
    finally:
        if server:
            server.server_close()


def run_tests():
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ServerTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        sys.exit(1)


# Built-in tests are defined below so the distributed application stays one file.
class ServerTests(unittest.TestCase):
    def setUp(self):
        import http.client
        self.http = http.client
        self.temp = tempfile.TemporaryDirectory(prefix='fshare-test-')
        self.outside = tempfile.TemporaryDirectory(prefix='fshare-outside-')
        self.root = Path(self.temp.name)
        (self.root / 'hello.txt').write_text('Hello, local network!\n', encoding='utf-8')
        (self.root / 'یادداشت فارسی.txt').write_text('سلام دنیا', encoding='utf-8')
        (self.root / 'empty.txt').touch()
        (self.root / 'folder' / 'empty').mkdir(parents=True)
        (self.root / 'folder' / 'nested.txt').write_bytes(b'nested content')
        (Path(self.outside.name) / 'secret.txt').write_bytes(b'OUTSIDE SECRET')
        self.media = bytes(range(256)) * 8192
        (self.root / 'movie.mp4').write_bytes(self.media)
        self.server = FileServer(('127.0.0.1', 0), self.temp.name)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.cookie = ''
        self.csrf = ''
        status, headers, body = self.request('/api/session')
        self.assertEqual(status, 200)
        self.cookie = headers['Set-Cookie'].split(';')[0]
        self.csrf = json.loads(body)['csrf']

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()
        if os.name == 'nt':
            shutil.rmtree(native_path(self.temp.name))
        self.temp.cleanup()
        self.outside.cleanup()

    def request(self, path, body=None, headers=None, method=None):
        connection = self.http.HTTPConnection('127.0.0.1', self.server.server_port, timeout=10)
        fields = {'Cookie': self.cookie}
        payload = None
        if body is not None:
            payload = json.dumps(body).encode('utf-8')
            fields.update({'Content-Type': 'application/json', 'X-CSRF-Token': self.csrf})
        fields.update(headers or {})
        connection.request(method or ('POST' if body is not None else 'GET'), path, payload, fields)
        response = connection.getresponse()
        result = response.status, dict(response.getheaders()), response.read()
        connection.close()
        return result

    def listing(self, path=''):
        status, _, body = self.request('/api/list?path=' + urllib.parse.quote(path))
        self.assertEqual(status, 200, body)
        return json.loads(body)['items']

    def ready_zip(self, body):
        status, _, raw = self.request('/api/zip', body)
        self.assertEqual(status, 202, raw)
        token = json.loads(raw)['id']
        for _ in range(200):
            status, _, raw = self.request('/api/zip/' + token)
            job = json.loads(raw)
            if job['state'] in ('ready', 'error', 'cancelled'):
                self.assertEqual(job['state'], 'ready', raw)
                return token, job
            time.sleep(.025)
        self.fail('ZIP preparation timed out')

    def plan(self, paths):
        items = {i['path']: i for i in self.listing()}
        status, _, raw = self.request('/api/delete/plan', {'items': [items[p] for p in paths]})
        self.assertEqual(status, 200, raw)
        return json.loads(raw)['id']

    def test_unicode_listing_and_download(self):
        items = self.listing()
        self.assertTrue(any(i['name'] == 'یادداشت فارسی.txt' for i in items))
        path = urllib.parse.quote('یادداشت فارسی.txt')
        status, headers, content = self.request('/file?path=' + path + '&download=1')
        self.assertEqual(status, 200)
        self.assertEqual(content.decode('utf-8'), 'سلام دنیا')
        self.assertIn("filename*=UTF-8''%", headers['Content-Disposition'])
        self.assertEqual(headers['X-Content-Type-Options'], 'nosniff')

    def test_html_and_csp(self):
        status, headers, raw = self.request('/')
        self.assertEqual(status, 200)
        self.assertIn(b'Fshare', raw)
        self.assertNotIn(b'__NONCE__', raw)
        self.assertIn("script-src 'nonce-", headers['Content-Security-Policy'])
        self.assertNotIn(b'<script src=', raw)
        self.assertNotIn(b'onclick=', raw)

    def test_matroska_uses_registered_mime_and_partial_delivery(self):
        name = 'فیلم sample.mkv'
        (self.root / name).write_bytes(self.media)
        item = next(i for i in self.listing() if i['name'] == name)
        self.assertEqual(item['kind'], 'video')
        self.assertEqual(item['mime'], 'video/matroska')
        status, headers, raw = self.request('/file?path=' + urllib.parse.quote(name),
                                            headers={'Range': 'bytes=512-1023'})
        self.assertEqual(status, 206)
        self.assertEqual(headers['Content-Type'], 'video/matroska')
        self.assertEqual(headers['Accept-Ranges'], 'bytes')
        self.assertEqual(raw, self.media[512:1024])
        self.assertEqual(headers['Content-Length'], '512')

    def test_media_discovery_matches_unicode_and_language_sidecars(self):
        movie = 'فیلم.mp4'
        (self.root / movie).write_bytes(b'media')
        for name in ['فیلم.srt', 'فیلم.fa.SRT', 'فیلم.en.vtt', 'فیلم2.srt', 'other.srt']:
            (self.root / name).write_text('1\n00:00:00,000 --> 00:00:01,000\nسلام\n', encoding='utf-8')
        (self.root / 'dub.wav').write_bytes(b'audio')
        (self.root / 'فیلم.ja.srt').mkdir()
        try:
            (self.root / 'فیلم.link.srt').symlink_to(Path(self.outside.name) / 'secret.txt')
        except (OSError, NotImplementedError):
            pass
        status, _, raw = self.request('/api/media?path=' + urllib.parse.quote(movie))
        self.assertEqual(status, 200)
        options = json.loads(raw)
        self.assertEqual({i['name'] for i in options['subtitles']}, {'فیلم.srt', 'فیلم.fa.SRT', 'فیلم.en.vtt'})
        self.assertEqual([i['path'] for i in options['audio']], ['dub.wav'])
        status, _, _ = self.request('/api/media?path=hello.txt')
        self.assertEqual(status, 400)
        status, _, _ = self.request('/api/media?path=../movie.mp4')
        self.assertEqual(status, 403)

    def test_subtitle_decoding_limits_and_safe_paths(self):
        text = '1\n00:00:00,000 --> 00:00:01,000\nسلام & <b>world</b>\n'
        for encoding in ['utf-8-sig', 'utf-16', 'cp1256']:
            (self.root / 'captions.srt').write_bytes(text.encode(encoding))
            status, _, raw = self.request('/api/subtitle?path=captions.srt')
            self.assertEqual(status, 200)
            self.assertEqual(json.loads(raw)['text'], text)
        status, _, _ = self.request('/api/subtitle?path=captions.srt&encoding=invalid')
        self.assertEqual(status, 400)
        status, _, _ = self.request('/api/subtitle?path=hello.txt')
        self.assertEqual(status, 400)
        status, _, _ = self.request('/api/subtitle?path=../captions.srt')
        self.assertEqual(status, 403)
        (self.root / 'captions.srt').write_bytes(b'\x00binary')
        status, _, _ = self.request('/api/subtitle?path=captions.srt')
        self.assertEqual(status, 422)
        with (self.root / 'captions.srt').open('wb') as source:
            source.truncate(MAX_SUBTITLE_BYTES + 1)
        status, _, _ = self.request('/api/subtitle?path=captions.srt')
        self.assertEqual(status, 413)
        try:
            (self.root / 'link.srt').symlink_to(Path(self.outside.name) / 'secret.txt')
        except (OSError, NotImplementedError):
            pass
        else:
            status, _, _ = self.request('/api/subtitle?path=link.srt')
            self.assertIn(status, (400, 403))

    def test_media_sidecars_require_authentication(self):
        self.server.password_hash = hashlib.pbkdf2_hmac('sha256', b'test-only', self.server.salt, 200000)
        (self.root / 'captions.srt').write_text('private subtitles', encoding='utf-8')
        self.cookie = ''
        for route in ['/api/media?path=movie.mp4', '/api/subtitle?path=captions.srt']:
            status, _, _ = self.request(route)
            self.assertEqual(status, 401)

    def test_ranges_and_head(self):
        for value, expected in [('bytes=100-199', self.media[100:200]),
                                ('bytes=-123', self.media[-123:]),
                                ('bytes=2097140-', self.media[2097140:]),
                                ('bytes=0-999999999999', self.media)]:
            status, headers, raw = self.request('/file?path=movie.mp4', headers={'Range': value})
            self.assertEqual(status, 206)
            self.assertEqual(raw, expected)
            self.assertEqual(int(headers['Content-Length']), len(expected))
            self.assertTrue(headers['Content-Range'].endswith('/' + str(len(self.media))))
            self.assertEqual(headers['Content-Type'], 'video/mp4')
        for value in ['bytes=9000000-', 'bytes=9-2', 'bytes=-0', 'bytes=-', 'bytes=a-b']:
            status, headers, _ = self.request('/file?path=movie.mp4', headers={'Range': value})
            self.assertEqual(status, 416)
            self.assertEqual(headers['Content-Range'], 'bytes */%d' % len(self.media))
        status, headers, body = self.request('/file?path=movie.mp4', method='HEAD', headers={'Range': 'bytes=0-1'})
        self.assertEqual(status, 200)
        self.assertEqual(int(headers['Content-Length']), len(self.media))
        self.assertFalse(body)
        status, _, raw = self.request('/file?path=movie.mp4', headers={'Range': 'bytes=0-1', 'If-Range': '"outdated"'})
        self.assertEqual(status, 200)
        self.assertEqual(raw, self.media)
        status, _, raw = self.request('/file?path=movie.mp4', headers={'Range': 'bytes=0-1,5-6'})
        self.assertEqual(status, 200)
        self.assertEqual(raw, self.media)

    def test_empty_file(self):
        status, headers, raw = self.request('/file?path=empty.txt')
        self.assertEqual((status, raw), (200, b''))
        self.assertEqual(headers['Content-Length'], '0')
        self.assertEqual(self.request('/file?path=empty.txt', headers={'Range': 'bytes=0-'})[0], 416)

    def test_path_traversal_and_root_deletion(self):
        for path in ['../secret.txt', '/etc/passwd', 'folder/../../secret.txt',
                     '..\\secret.txt', 'C:/Windows/win.ini', 'folder//nested.txt', '\x00']:
            query = urllib.parse.quote(path, safe='')
            status, _, raw = self.request('/file?path=' + query)
            self.assertIn(status, (400, 403, 404), raw)
            self.assertNotIn(b'OUTSIDE SECRET', raw)
        self.assertEqual(self.request('/api/delete/plan', {'items': [{'path': '', 'version': ''}]})[0], 403)
        self.assertTrue(self.root.exists())

    def test_symlinks_and_junction_policy(self):
        try:
            (self.root / 'outside-link').symlink_to(self.outside.name, target_is_directory=True)
            (self.root / 'inside-link').symlink_to(self.root / 'hello.txt')
        except (OSError, NotImplementedError):
            self.skipTest('This host does not allow creating symbolic links')
        items = {i['name']: i for i in self.listing()}
        self.assertTrue(items['outside-link']['blocked'])
        for path in ['outside-link/secret.txt', 'inside-link']:
            status, _, raw = self.request('/file?path=' + path)
            self.assertEqual(status, 403)
            self.assertNotIn(b'OUTSIDE SECRET', raw)
        self.assertNotEqual(self.request('/api/list?path=outside-link')[0], 200)
        self.assertEqual(self.request('/api/zip', {'path': '', 'paths': ['outside-link']})[0], 403)

    def test_csrf_origin_host_and_auth_guards(self):
        self.assertEqual(self.request('/api/list', headers={'Cookie': ''})[0], 401)
        self.assertEqual(self.request('/api/zip', {'path': '', 'paths': ['hello.txt']}, headers={'X-CSRF-Token': ''})[0], 403)
        self.assertEqual(self.request('/api/session', headers={'Origin': 'https://attacker.example'})[0], 403)
        self.assertEqual(self.request('/api/session', headers={'Sec-Fetch-Site': 'cross-site'})[0], 403)
        self.assertEqual(self.request('/api/list', headers={'Host': 'attacker.example:%d' % self.server.server_port})[0], 403)

    def test_password_login_and_logout(self):
        self.server.password_hash = hashlib.pbkdf2_hmac('sha256', 'test-pass'.encode(), self.server.salt, 200000)
        self.cookie = ''
        status, _, raw = self.request('/api/session')
        self.assertFalse(json.loads(raw)['authenticated'])
        self.assertEqual(self.request('/api/login', {'password': 'wrong'})[0], 401)
        status, headers, raw = self.request('/api/login', {'password': 'test-pass'})
        self.assertEqual(status, 200)
        self.assertIn('HttpOnly', headers['Set-Cookie'])
        self.assertIn('SameSite=Strict', headers['Set-Cookie'])
        self.cookie = headers['Set-Cookie'].split(';')[0]
        self.csrf = json.loads(raw)['csrf']
        self.assertEqual(self.request('/api/list')[0], 200)
        self.assertEqual(self.request('/api/logout', {})[0], 200)
        self.assertEqual(self.request('/api/list')[0], 401)

    def test_password_rate_limit(self):
        self.server.password_hash = hashlib.pbkdf2_hmac('sha256', b'correct', self.server.salt, 200000)
        for _ in range(5):
            self.assertEqual(self.request('/api/login', {'password': 'wrong'})[0], 401)
        self.assertEqual(self.request('/api/login', {'password': 'correct'})[0], 429)

    def test_zip_unicode_empty_folders_and_cleanup(self):
        token, job = self.ready_zip({'path': '', 'paths': ['folder', 'یادداشت فارسی.txt']})
        temp_path = self.server.jobs.jobs[token]['temp_path']
        self.assertTrue(os.path.isfile(temp_path))
        self.assertEqual(job['files'], 2)
        status, headers, raw = self.request('/zip/' + token)
        self.assertEqual(status, 200)
        self.assertEqual(headers['Content-Type'], 'application/zip')
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            self.assertIn('folder/empty/', archive.namelist())
            self.assertEqual(archive.read('folder/nested.txt'), b'nested content')
            self.assertEqual(archive.read('یادداشت فارسی.txt').decode(), 'سلام دنیا')
            self.assertGreaterEqual(archive.getinfo('folder/nested.txt').extract_version, 45)
            self.assertIsNone(archive.testzip())
        # The client can receive the last bytes before the worker's finally
        # block runs. Verify cleanup completes, rather than racing that block.
        for _ in range(100):
            with self.server.jobs.lock:
                removed = token not in self.server.jobs.jobs
            if removed and not os.path.exists(temp_path):
                break
            time.sleep(.01)
        self.assertFalse(os.path.exists(temp_path))
        self.assertEqual(self.request('/api/zip/' + token)[0], 404)

    def test_zip_all_and_link_exclusion(self):
        linked = False
        try:
            (self.root / 'folder' / 'secret-link').symlink_to(Path(self.outside.name) / 'secret.txt')
            linked = True
        except (OSError, NotImplementedError):
            pass
        token, job = self.ready_zip({'path': 'folder', 'all': True})
        raw = self.request('/zip/' + token)[2]
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            self.assertEqual(set(archive.namelist()), {'empty/', 'nested.txt'})
            self.assertNotIn(b'OUTSIDE SECRET', raw)
        self.assertEqual(job['skipped'], 1 if linked else 0)
        if linked:
            token, job = self.ready_zip({'path': '', 'paths': ['folder']})
            self.assertEqual(job['skipped'], 1)
            self.request('/api/zip/' + token + '/cancel', {})

    def test_zip_session_isolation_and_cancel(self):
        token, _ = self.ready_zip({'path': '', 'paths': ['hello.txt']})
        path = self.server.jobs.jobs[token]['temp_path']
        other_token, _ = self.server.new_session()
        self.assertEqual(self.request('/api/zip/' + token, headers={'Cookie': 'fshare_session=' + other_token})[0], 404)
        self.assertEqual(self.request('/zip/' + token, headers={'Cookie': 'fshare_session=' + other_token})[0], 404)
        self.assertEqual(self.request('/api/zip/' + token + '/cancel', {})[0], 200)
        self.assertFalse(os.path.exists(path))

    def test_disk_full_error_and_expiry(self):
        from unittest.mock import patch
        fake_usage = shutil._ntuple_diskusage(100, 99, 1)
        with patch.object(shutil, 'disk_usage', return_value=fake_usage):
            status, _, raw = self.request('/api/zip', {'path': '', 'paths': ['movie.mp4']})
            self.assertEqual(status, 202)
            token = json.loads(raw)['id']
            for _ in range(100):
                job = self.server.jobs.get(token, self.cookie.split('=', 1)[1])
                if job['state'] == 'error':
                    break
                time.sleep(.01)
            self.assertEqual(job['state'], 'error')
            self.assertIn('free temporary space', job['error'])
            self.assertIsNone(job['temp_path'])
        token, _ = self.ready_zip({'path': '', 'paths': ['hello.txt']})
        job = self.server.jobs.jobs[token]
        path = job['temp_path']
        job['touched'] -= JOB_TTL + 1
        self.server.jobs.sweep()
        self.assertFalse(os.path.exists(path))
        self.assertNotIn(token, self.server.jobs.jobs)

    def test_confirmed_deletion_and_stale_confirmation(self):
        token = self.plan(['hello.txt'])
        self.assertEqual(self.request('/api/delete', {'id': token})[0], 400)
        self.assertTrue((self.root / 'hello.txt').exists())
        (self.root / 'hello.txt').write_bytes(b'changed after preview')
        status, _, raw = self.request('/api/delete', {'id': token, 'confirm': 'delete'})
        self.assertEqual(status, 200)
        self.assertTrue(json.loads(raw)['errors'])
        self.assertTrue((self.root / 'hello.txt').exists())
        token = self.plan(['hello.txt', 'folder'])
        status, _, raw = self.request('/api/delete', {'id': token, 'confirm': 'delete'})
        self.assertEqual(status, 200)
        self.assertEqual(len(json.loads(raw)['deleted']), 2)
        self.assertFalse((self.root / 'folder').exists())
        self.assertEqual(self.request('/api/delete', {'id': token, 'confirm': 'delete'})[0], 409)

    def test_read_only_mode(self):
        self.server.read_only = True
        items = self.listing()
        self.assertEqual(self.request('/api/delete/plan', {'items': [items[0]]})[0], 403)
        self.assertEqual(self.request('/api/delete', {'id': 'x', 'confirm': 'delete'})[0], 403)
        self.assertEqual(self.request('/file?path=hello.txt')[0], 200)

    def test_recursive_delete_never_follows_nested_link(self):
        try:
            (self.root / 'folder' / 'outside').symlink_to(self.outside.name, target_is_directory=True)
        except (OSError, NotImplementedError):
            self.skipTest('This host does not allow symbolic links')
        token = self.plan(['folder'])
        _, _, raw = self.request('/api/delete', {'id': token, 'confirm': 'delete'})
        self.assertFalse(json.loads(raw)['errors'])
        self.assertEqual((Path(self.outside.name) / 'secret.txt').read_bytes(), b'OUTSIDE SECRET')

    def test_thousands_of_files_and_long_paths(self):
        many = self.root / 'many'
        many.mkdir()
        for index in range(3000):
            (many / ('item-%04d.txt' % index)).touch()
        self.assertEqual(len(self.listing('many')), 3000)
        relative = '/'.join(['long-directory-name-%02d' % i for i in range(18)]) + '/فارسی.txt'
        full = native_path(self.root / relative)
        os.makedirs(os.path.dirname(full))
        with open(full, 'wb') as stream:
            stream.write(b'long path works')
        status, _, raw = self.request('/file?path=' + urllib.parse.quote(relative))
        self.assertEqual(status, 200)
        self.assertEqual(raw, b'long path works')

    def test_concurrent_download_and_interrupted_zip_cleanup(self):
        large = self.root / 'large.mp4'
        with large.open('wb') as stream:
            stream.truncate(32 * 1024 * 1024)
        connection = self.http.HTTPConnection('127.0.0.1', self.server.server_port, timeout=10)
        connection.request('GET', '/file?path=large.mp4', headers={'Cookie': self.cookie})
        response = connection.getresponse()
        self.assertEqual(response.status, 200)
        started = time.monotonic()
        self.assertEqual(self.request('/api/list')[0], 200)
        self.assertLess(time.monotonic() - started, 2)
        response.close()
        connection.close()
        token, _ = self.ready_zip({'path': '', 'paths': ['large.mp4']})
        temp_path = self.server.jobs.jobs[token]['temp_path']
        connection = self.http.HTTPConnection('127.0.0.1', self.server.server_port, timeout=10)
        connection.request('GET', '/zip/' + token, headers={'Cookie': self.cookie})
        response = connection.getresponse()
        self.assertEqual(response.status, 200)
        response.read(100)
        response.close()
        connection.close()
        for _ in range(100):
            if not os.path.exists(temp_path):
                break
            time.sleep(.02)
        self.assertFalse(os.path.exists(temp_path))

    @unittest.skipIf(os.name == 'nt', 'This test uses POSIX sparse files to avoid allocating 6 GB')
    def test_range_in_file_larger_than_four_gigabytes(self):
        size = 6 * 1024 ** 3
        with (self.root / 'huge.mp4').open('wb') as stream:
            stream.seek(size - 4)
            stream.write(b'TAIL')
        status, headers, raw = self.request('/file?path=huge.mp4', headers={'Range': 'bytes=%d-' % (size - 4)})
        self.assertEqual(status, 206)
        self.assertEqual(raw, b'TAIL')
        self.assertEqual(headers['Content-Range'], 'bytes %d-%d/%d' % (size - 4, size - 1, size))

    def test_cancel_during_zip_build_removes_temporary_file(self):
        from unittest.mock import patch
        entered, release = threading.Event(), threading.Event()
        original = self.server.root.open_file

        @contextlib.contextmanager
        def delayed(path):
            with original(path) as stream:
                entered.set()
                release.wait(5)
                yield stream

        with patch.object(self.server.root, 'open_file', delayed):
            try:
                status, _, raw = self.request('/api/zip', {'path': '', 'paths': ['movie.mp4']})
                self.assertEqual(status, 202)
                token = json.loads(raw)['id']
                self.assertTrue(entered.wait(5))
                self.assertEqual(self.request('/api/zip/' + token + '/cancel', {})[0], 200)
            finally:
                release.set()
            for _ in range(100):
                job = self.server.jobs.jobs[token]
                if job['state'] == 'cancelled' and job['temp_path'] is None:
                    break
                time.sleep(.01)
            self.assertEqual(job['state'], 'cancelled')
            self.assertIsNone(job['temp_path'])

    def test_zip_error_after_temporary_file_created_is_cleaned_up(self):
        from unittest.mock import patch

        @contextlib.contextmanager
        def out_of_space(path):
            raise OSError(errno.ENOSPC, 'simulated disk exhaustion')
            yield  # Make this a context manager without creating a real stream.

        with patch.object(self.server.root, 'open_file', out_of_space):
            status, _, raw = self.request('/api/zip', {'path': '', 'paths': ['hello.txt']})
            self.assertEqual(status, 202)
            token = json.loads(raw)['id']
            for _ in range(100):
                job = self.server.jobs.jobs[token]
                if job['state'] == 'error' and job['temp_path'] is None:
                    break
                time.sleep(.01)
            self.assertEqual(job['state'], 'error')
            self.assertIn('Not enough free space', job['error'])
            self.assertIsNone(job['temp_path'])
        self.assertFalse(list(Path(self.server.jobs.temp.name).iterdir()))

    def test_delete_confirmation_expiry_and_session_ownership(self):
        token = self.plan(['hello.txt'])
        other, other_data = self.server.new_session()
        self.assertEqual(self.request('/api/delete', {'id': token, 'confirm': 'delete'}, headers={
            'Cookie': 'fshare_session=' + other, 'X-CSRF-Token': other_data['csrf']})[0], 409)
        self.server.plans[token]['expires'] = time.monotonic() - 1
        self.assertEqual(self.request('/api/delete', {'id': token, 'confirm': 'delete'})[0], 409)
        self.assertTrue((self.root / 'hello.txt').exists())

    @unittest.skipIf(os.name == 'nt', 'Windows does not support these native filenames')
    def test_native_filenames_and_safe_portable_zip_names(self):
        names = ['movie:part.txt', '..\\outside.txt', 'CON.txt', 'literal%5C.txt', 'trailing.']
        for name in names:
            (self.root / name).write_bytes(name.encode('utf-8'))
            status, _, raw = self.request('/file?path=' + urllib.parse.quote(name, safe=''))
            self.assertEqual(status, 200)
            self.assertEqual(raw, name.encode('utf-8'))
        self.assertTrue(set(names).issubset({item['name'] for item in self.listing()}))
        token, job = self.ready_zip({'path': '', 'paths': names})
        self.assertEqual(job['renamed'], len(names))
        raw = self.request('/zip/' + token)[2]
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            expected = ['movie%3Apart.txt', '..%5Coutside.txt', '%43ON.txt', 'literal%255C.txt', 'trailing%2E']
            self.assertEqual(set(archive.namelist()), set(expected))
            for name, safe in zip(names, expected):
                self.assertEqual(archive.read(safe), name.encode('utf-8'))

    @unittest.skipUnless(sys.platform.startswith('linux') or sys.platform == 'darwin', 'POSIX interface enumeration')
    def test_ip_discovery_continues_after_interface_without_ipv4(self):
        import fcntl
        from unittest.mock import patch
        data = bytearray(256)
        data[20:24] = socket.inet_aton('192.168.42.123')
        with patch.object(socket, 'if_nameindex', return_value=[(1, 'empty'), (2, 'lan')]), patch.object(fcntl, 'ioctl', side_effect=[OSError('No IPv4 address'), bytes(data)]):
            self.assertIn('192.168.42.123', local_ips())


if __name__ == '__main__':
    main()

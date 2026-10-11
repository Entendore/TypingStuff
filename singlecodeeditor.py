#!/usr/bin/env python3
"""
Unified Typing Video Studio — Code Editor Mode (Preview Optimized)
==================================================================
"""

from __future__ import annotations

import bisect, copy, gc, io, json, logging, math, os, platform, random, re, shutil
import subprocess, sys, tempfile, threading, time as _time, unicodedata, wave
import queue
from collections import OrderedDict, deque
from concurrent.futures import ThreadPoolExecutor, Future
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Any, Callable, Dict, List, Literal, Optional, Protocol, Tuple, TypeAlias, Union

import numpy as np

from PySide6.QtCore import (QEvent, QPoint, QPointF, QRect, Qt, QThread, QTimer,
                            QUrl, Signal, QBuffer, QIODevice, QSize, QElapsedTimer)
from PySide6.QtGui import (QColor, QFont, QFontDatabase, QFontMetrics, QImage,
                           QLinearGradient, QPainter, QPainterPath, QPalette,
                           QPen, QPixmap, QPolygonF, QKeySequence, QShortcut,
                           QTransform, QAction)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (QApplication, QCheckBox, QComboBox, QDialog,
                               QDoubleSpinBox, QFileDialog, QFormLayout,
                               QFrame, QGraphicsDropShadowEffect, QGridLayout,
                               QGroupBox, QHBoxLayout, QHeaderView, QLabel,
                               QLineEdit, QMainWindow, QMessageBox,
                               QPlainTextEdit, QProgressBar, QPushButton,
                               QScrollArea, QSizePolicy, QSlider, QSpinBox,
                               QSplitter, QStatusBar, QTableWidget,
                               QTableWidgetItem, QVBoxLayout, QWidget,
                               QMenu, QStyle)

# Optional dependencies
try:
    from numba import njit
    _HAS_NUMBA: bool = True
except ImportError:
    _HAS_NUMBA = False

try:
    from pygments import lex
    from pygments.lexers import get_lexer_by_name
    _HAS_PYGMENTS: bool = True
except ImportError:
    _HAS_PYGMENTS = False

# Python 3.10 compatibility for StrEnum
try:
    from enum import StrEnum
except ImportError:
    from enum import Enum
    class StrEnum(str, Enum):
        pass

# ============================================================================
# 1. EXCEPTIONS & LOGGING
# ============================================================================

class StudioError(Exception):
    """Base exception for Typing Studio."""

class ExportError(StudioError):
    """Raised during video/audio export failures."""

class RendererError(StudioError):
    """Raised during frame rendering failures."""

logger = logging.getLogger("TypingStudio")
logger.setLevel(logging.DEBUG)
_fh = logging.FileHandler("studio.log", mode='w', encoding='utf-8')
_fh.setLevel(logging.DEBUG)
_fh.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
logger.addHandler(_fh)
_ch = logging.StreamHandler(sys.stderr)
_ch.setLevel(logging.ERROR)
_ch.setFormatter(logging.Formatter("[!] %(levelname)s: %(message)s"))
logger.addHandler(_ch)

# ============================================================================
# 2. TYPES & ENUMS
# ============================================================================

class CursorStyle(StrEnum):
    BLOCK = "Block"
    BEAM = "Beam"
    UNDERLINE = "Underline"

class EncoderType(StrEnum):
    YOUTUBE = "YouTube Optimised (H.264/AAC)"
    NVENC = "NVENC (NVIDIA)"
    QSV = "QSV (Intel)"
    AMF = "AMF (AMD)"
    VIDEOTOOLBOX = "Apple VideoToolbox"

class StatusColor(StrEnum):
    PENDING = "#a6adc8"
    RUNNING = "#89b4fa"
    DONE = "#a6e3a1"
    FAILED = "#f38ba8"
    CANCELLED = "#f9e2af"
    SKIPPED = "#f9e2af"

# Type Aliases
RGB: TypeAlias = Tuple[int, int, int]
Point: TypeAlias = Tuple[int, int]
Rect: TypeAlias = Tuple[int, int, int, int]
ThemeDict: TypeAlias = Dict[str, str]

# ============================================================================
# 3. CONFIGURATION & CONSTANTS
# ============================================================================

CWD = Path.cwd()
INPUT_DIR = CWD / "input"
OUTPUT_DIR = CWD / "output"
TEMP_DIR = CWD / "temp"
SETTINGS_FILE = CWD / "settings.json"
RECENT_FILE = CWD / "recent.json"

for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR):
    _d.mkdir(parents=True, exist_ok=True)

SUPPORTED_EXTENSIONS = frozenset({
    ".py", ".js", ".ts", ".jsx", ".tsx", ".java", ".c", ".cpp", ".h", ".hpp",
    ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt", ".sh", ".bash", ".zsh",
    ".sql", ".html", ".htm", ".css", ".scss", ".json", ".yaml", ".yml", ".toml",
    ".ini", ".cfg", ".txt", ".md", ".lua", ".dart", ".r", ".m",
})

EXT_TO_LANGUAGE: Dict[str, str] = {
    ".py": "python", ".js": "javascript", ".ts": "typescript", ".jsx": "typescript",
    ".tsx": "typescript", ".java": "java", ".c": "c", ".cpp": "cpp", ".h": "c",
    ".hpp": "cpp", ".cs": "csharp", ".go": "go", ".rs": "rust", ".rb": "ruby",
    ".php": "php", ".swift": "swift", ".kt": "kotlin", ".sh": "bash",
    ".bash": "bash", ".zsh": "bash", ".sql": "sql", ".html": "html",
    ".htm": "html", ".css": "css", ".scss": "scss", ".json": "json",
    ".yaml": "yaml", ".yml": "yaml", ".toml": "ini", ".ini": "ini",
    ".cfg": "ini", ".txt": "text", ".md": "markdown", ".lua": "lua",
    ".dart": "dart", ".r": "r", ".m": "objc",
}

RESOLUTIONS: Dict[str, Point] = {
    "1920x1080 (16:9)": (1920, 1080),
    "1280x720 (16:9)":  (1280, 720),
    "3840x2160 (4K)":   (3840, 2160),
    "1080x1920 (9:16)": (1080, 1920),
    "720x1280 (9:16)":  (720, 1280),
    "1080x1080 (1:1)":  (1080, 1080),
    "1440x1080 (4:3)":  (1440, 1080),
}

THEMES: Dict[str, ThemeDict] = {
    "Dracula": {
        "background":"#282a36","foreground":"#f8f8f2","comment":"#6272a4",
        "keyword":"#ff79c6","string":"#f1fa8c","number":"#bd93f9",
        "function":"#50fa7b","builtin":"#8be9fd","decorator":"#50fa7b",
        "operator":"#ff79c6","class_name":"#8be9fd","line_number":"#6272a4",
        "current_line":"#44475a","cursor":"#f8f8f2","title_bar":"#21222c",
        "title_text":"#8be9fd","window_border":"#191a21","selection":"#44475a",
        "accent":"#bd93f9",
    },
    "One Dark": {
        "background":"#282c34","foreground":"#abb2bf","comment":"#5c6370",
        "keyword":"#c678dd","string":"#98c379","number":"#d19a66",
        "function":"#61afef","builtin":"#e5c07b","decorator":"#56b6c2",
        "operator":"#c678dd","class_name":"#e5c07b","line_number":"#4b5263",
        "current_line":"#2c313c","cursor":"#528bff","title_bar":"#21252b",
        "title_text":"#61afef","window_border":"#181a1f","selection":"#3e4451",
        "accent":"#61afef",
    },
    "Monokai Pro": {
        "background":"#2D2A2E","foreground":"#FCFCFA","comment":"#727072",
        "keyword":"#FF6188","string":"#FFD866","number":"#AB9DF2",
        "function":"#A9DC76","builtin":"#78DCE8","decorator":"#A9DC76",
        "operator":"#FF6188","class_name":"#78DCE8","line_number":"#727072",
        "current_line":"#41393C","cursor":"#FCFCFA","title_bar":"#221F22",
        "title_text":"#FF6188","window_border":"#1B181A","selection":"#403841",
        "accent":"#AB9DF2",
    },
    "Tokyo Night": {
        "background":"#1a1b26","foreground":"#a9b1d6","comment":"#565f89",
        "keyword":"#bb9af7","string":"#9ece6a","number":"#ff9e64",
        "function":"#7aa2f7","builtin":"#7dcfff","decorator":"#7aa2f7",
        "operator":"#89ddff","class_name":"#7aa2f7","line_number":"#3b4261",
        "current_line":"#1f2335","cursor":"#c0caf5","title_bar":"#16161e",
        "title_text":"#7aa2f7","window_border":"#15161e","selection":"#33467c",
        "accent":"#7aa2f7",
    },
    "Catppuccin Mocha": {
        "background":"#1e1e2e","foreground":"#cdd6f4","comment":"#6c7086",
        "keyword":"#cba6f7","string":"#a6e3a1","number":"#fab387",
        "function":"#89b4fa","builtin":"#89dceb","decorator":"#f9e2af",
        "operator":"#94e2d5","class_name":"#f9e2af","line_number":"#585b70",
        "current_line":"#313244","cursor":"#f5e0dc","title_bar":"#181825",
        "title_text":"#89b4fa","window_border":"#11111b","selection":"#45475a",
        "accent":"#cba6f7",
    },
    "GitHub Dark": {
        "background":"#0d1117","foreground":"#c9d1d9","comment":"#8b949e",
        "keyword":"#ff7b72","string":"#a5d6ff","number":"#79c0ff",
        "function":"#d2a8ff","builtin":"#ffa657","decorator":"#d2a8ff",
        "operator":"#ff7b72","class_name":"#ffa657","line_number":"#484f58",
        "current_line":"#161b22","cursor":"#58a6ff","title_bar":"#010409",
        "title_text":"#58a6ff","window_border":"#30363d","selection":"#1f6feb",
        "accent":"#58a6ff",
    },
    "Solarized Dark": {
        "background":"#002b36","foreground":"#93a1a1","comment":"#586e75",
        "keyword":"#859900","string":"#2aa198","number":"#d33682",
        "function":"#268bd2","builtin":"#b58900","decorator":"#cb4b16",
        "operator":"#859900","class_name":"#b58900","line_number":"#073642",
        "current_line":"#073642","cursor":"#eee8d5","title_bar":"#003747",
        "title_text":"#268bd2","window_border":"#073642","selection":"#073642",
        "accent":"#268bd2",
    },
}

def get_system_fonts() -> List[str]:
    """Safely retrieves monospace fonts available on the system."""
    try:
        families = QFontDatabase.families()
        preferred = ["JetBrains Mono", "Fira Code", "Cascadia Code", "Consolas",
                     "IBM Plex Mono", "SF Mono", "Menlo", "Monaco",
                     "DejaVu Sans Mono", "Courier New", "monospace"]
        sys_fams = [f for f in families if f not in preferred and not f.startswith("@")]
        return preferred + sys_fams
    except Exception:
        return ["JetBrains Mono", "Consolas", "monospace"]

FONT_FAMILIES: List[str] = get_system_fonts()

# ============================================================================
# 4. DATA MODELS (slots-optimized)
# ============================================================================

@dataclass(slots=True)
class StudioConfig:
    theme: str = "Dracula"
    resolution: str = "1920x1080 (16:9)"
    fps: int = 30
    encoder: str = EncoderType.YOUTUBE.value
    output_template: str = "{name}_{date}"
    yt_extras: bool = True

    sound_enabled: bool = True
    sound_preset: str = "Mechanical"
    stereo: bool = False
    volume: int = 60
    bgm_path: str = ""
    bgm_volume: int = 25
    bgm_duck: bool = True

    kb_enabled: bool = False
    kb_layout: str = "QWERTY"
    kb_position: str = "Bottom Center"
    kb_opacity: float = 0.82

    font_family: str = "JetBrains Mono"
    font_size_auto: bool = True
    font_size: int = 22
    tab_size: int = 4
    show_line_numbers: bool = True
    show_window_chrome: bool = True
    cursor_style: str = CursorStyle.BLOCK.value
    wpm: int = 100
    typo_rate: float = 0.0
    auto_shorts: bool = False
    cinematic_zoom: bool = False
    focus_dimming: bool = False
    smooth_scroll: bool = True

    intro_card: bool = True
    intro_duration: float = 2.5
    outro_card: bool = True
    outro_duration: float = 2.5
    progress_bar_overlay: bool = False
    watermark_text: str = ""
    watermark_opacity: float = 0.25
    window_title: str = ""

    use_custom: bool = False
    custom_code: str = ""

    recursive_scan: bool = True
    scan_depth: int = 10

@dataclass(slots=True)
class FileItem:
    path: str
    checked: bool = False
    status: str = "Pending"
    size_mb: float = 0.0

@dataclass(slots=True)
class TypingProfile:
    wpm: int = 100
    start_pause: float = 0.5
    end_pause: float = 1.5
    typo_rate: float = 0.0
    burst_mode: bool = False

@dataclass(slots=True)
class VoiceSpec:
    osc: str = "sine"
    freq: float = 440.0
    fm_ratio: float = 1.0
    fm_index: float = 0.0
    attack: float = 0.001
    decay_rate: float = 30.0
    attack_curve: float = 2.0
    filt: str = "none"
    f_cutoff: float = 8000.0
    f_high: float = 12000.0
    f_q: float = 1.0
    drive: float = 0.0
    gain: float = 0.5
    delay: float = 0.0
    modes: Optional[List[Tuple[float, float, float]]] = None
    inharmonicity: float = 0.0

@dataclass(slots=True)
class SoundSpec:
    duration: float = 0.12
    layers: List[VoiceSpec] = field(default_factory=list)

# ============================================================================
# 5. UTILITIES & THREAD-SAFE LEXER
# ============================================================================

ZWJ = '\u200d'
VS16 = '\ufe0f'

def split_graphemes(text: str) -> List[str]:
    graphemes, i, n = [], 0, len(text)
    while i < n:
        c, i = text[i], i + 1
        while i < n:
            nxt = text[i]
            if nxt == ZWJ or nxt == VS16 or unicodedata.combining(nxt) != 0:
                c += nxt; i += 1
                if c[-1] == ZWJ and i < n:
                    c += text[i]; i += 1
            else:
                break
        graphemes.append(c)
    return graphemes

def convert_shortcodes(text: str) -> str:
    shortcodes = {":rocket:": "🚀", ":fire:": "🔥", ":sparkles:": "✨",
                  ":heart:": "❤️", ":check:": "✅", ":x:": "❌",
                  ":warning:": "⚠️", ":star:": "⭐", ":tada:": "🎉"}
    for code, emoji in shortcodes.items():
        text = text.replace(code, emoji)
    return text

def read_text_file(path: str) -> str:
    try:
        with open(path, "r", encoding="utf-8") as f:
            text = f.read()
    except UnicodeDecodeError:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            text = f.read()
    text = convert_shortcodes(text)
    text = text.replace("\xa0", " ").replace("\xad", "")
    text = re.sub(r'[ \t]+\n', '\n', text)
    text = "\n".join(line.rstrip() for line in text.splitlines())
    return text

class LexerFactory:
    """Thread-safe lexer instantiation. Pygments lexers maintain internal state
    and are strictly NOT thread-safe. We must instantiate per-call."""
    @staticmethod
    def get_lexer(lang: str):
        if not _HAS_PYGMENTS:
            return None
        try:
            return get_lexer_by_name(lang, stripall=False)
        except Exception:
            return get_lexer_by_name("text", stripall=False)

# ============================================================================
# 6. DSP AUDIO ENGINE (Numba Accelerated)
# ============================================================================

AUDIO_SAMPLE_RATE = 48000

if _HAS_NUMBA:
    @njit(cache=True)
    def _nb_k_weight(x: np.ndarray, sr: int) -> np.ndarray:
        n = len(x); y = np.empty(n, dtype=np.float64)
        if sr == 48000:
            s1_b0=1.53512485958624; s1_b1=-2.61187896900947; s1_b2=1.23925952524423
            s1_a1=-1.69019851598276; s1_a2=0.732626261909496
            s2_b0=1.0; s2_b1=-2.0; s2_b2=1.0
            s2_a1=-1.99004745481143; s2_a2=0.990072500365666
        else:
            for i in range(n): y[i] = x[i]
            return y
        z1 = z2 = 0.0
        for i in range(n):
            xn = x[i]; yn = s1_b0 * xn + z1
            z1 = s1_b1 * xn - s1_a1 * yn + z2; z2 = s1_b2 * xn - s1_a2 * yn; y[i] = yn
        z1 = z2 = 0.0
        for i in range(n):
            xn = y[i]; yn = s2_b0 * xn + z1
            z1 = s2_b1 * xn - s2_a1 * yn + z2; z2 = s2_b2 * xn - s2_a2 * yn; y[i] = yn
        return y

    @njit(cache=True)
    def _nb_compute_loudness(x_k: np.ndarray) -> float:
        n = len(x_k)
        if n == 0: return -70.0
        s = 0.0
        for i in range(n):
            v = x_k[i]; s += v * v
        ms = s / n
        if ms < 1e-20: return -70.0
        return -0.691 + 10.0 * np.log10(ms)

    @njit(cache=True)
    def _nb_apply_gain(x: np.ndarray, gain: float) -> np.ndarray:
        n = len(x); out = np.empty(n, dtype=np.float64)
        for i in range(n): out[i] = x[i] * gain
        return out

def _normalize_to_lufs(x: np.ndarray, sr: int, target_lufs: float = -16.0) -> np.ndarray:
    if len(x) < sr // 2: return x
    if _HAS_NUMBA:
        xk = _nb_k_weight(x.astype(np.float64), sr)
        cl = _nb_compute_loudness(xk)
        if not np.isfinite(cl) or cl <= -70.0: return x
        gdb = target_lufs - cl
        gl = 10.0 ** (gdb / 20.0)
        return _nb_apply_gain(x.astype(np.float64), gl).astype(np.float32)
    return x

class DSP:
    SR = AUDIO_SAMPLE_RATE

    @staticmethod
    def env_exp(n: int, sr: int, attack: float = 0.001, decay_rate: float = 30.0, attack_curve: float = 2.0) -> np.ndarray:
        t = np.arange(n, dtype=np.float64) / sr
        env = np.exp(-t * decay_rate)
        a_samp = max(1, int(attack * sr))
        if a_samp < n:
            a_env = np.linspace(0, 1, a_samp) ** attack_curve
            env[:a_samp] = a_env * np.exp(-np.arange(a_samp, dtype=np.float64) / sr * decay_rate)
        return env

    @staticmethod
    def fir_lowpass(cutoff: float, sr: int = AUDIO_SAMPLE_RATE, n_taps: int = 127) -> np.ndarray:
        if n_taps % 2 == 0: n_taps += 1
        fc = min(max(1.0, cutoff), sr / 2.0 - 1.0) / sr
        n = np.arange(n_taps, dtype=np.float64)
        center = (n_taps - 1) / 2.0
        h = np.sinc(2 * fc * (n - center))
        w = 0.42 - 0.5*np.cos(2*np.pi*n/(n_taps-1)) + 0.08*np.cos(4*np.pi*n/(n_taps-1))
        h *= w; s = np.sum(h)
        if s > 0: h /= s
        return h

    @staticmethod
    def convolve(x: np.ndarray, h: np.ndarray) -> np.ndarray:
        n, nh = len(x), len(h)
        if nh <= 1: return x * h[0] if nh == 1 else x
        n_fft = 1 << ((n + nh - 1).bit_length())
        return np.fft.irfft(np.fft.rfft(x, n_fft) * np.fft.rfft(h, n_fft), n_fft)[:n]

    @staticmethod
    def filt_lp(x: np.ndarray, c: float, sr: int = AUDIO_SAMPLE_RATE, n_taps: int = 127) -> np.ndarray:
        return DSP.convolve(x, DSP.fir_lowpass(c, sr, n_taps))

    @staticmethod
    def filt_hp(x: np.ndarray, c: float, sr: int = AUDIO_SAMPLE_RATE, n_taps: int = 63) -> np.ndarray:
        hlp = DSP.fir_lowpass(c, sr, n_taps); h = -hlp; h[len(h)//2] += 1.0
        return DSP.convolve(x, h)

    @staticmethod
    def filt_bp(x: np.ndarray, l: float, h: float, sr: int = AUDIO_SAMPLE_RATE) -> np.ndarray:
        return DSP.filt_lp(x, h, sr) - DSP.filt_lp(x, l, sr)

    @staticmethod
    def filt_resonator(x: np.ndarray, freq: float, q: float, sr: int = AUDIO_SAMPLE_RATE, gain: float = 1.0) -> np.ndarray:
        w0 = 2 * np.pi * freq / sr
        r = np.exp(-w0 / (2 * max(0.5, q)))
        wd = w0 * np.sqrt(max(0.0, 1.0 - 1.0/(4*q*q))) if q > 0.5 else w0
        n_ir = min(len(x), max(16, int(sr * max(0.005, 6.0 * q / max(1.0, freq)))))
        t = np.arange(n_ir, dtype=np.float64)
        ir = (r ** t) * np.sin(wd * t)
        pk = np.max(np.abs(ir))
        if pk > 1e-10: ir = ir / pk * gain
        return DSP.convolve(x, ir)

    @staticmethod
    def osc_sine(f: float, n: int, sr: int) -> np.ndarray:
        return np.sin(2*np.pi*f*(np.arange(n, dtype=np.float64)/sr))

    @staticmethod
    def osc_fm(c: float, mr: float, mi: float, n: int, sr: int) -> np.ndarray:
        t = np.arange(n, dtype=np.float64) / sr
        return np.sin(2*np.pi*c*t + mi*np.sin(2*np.pi*c*mr*t))

    @staticmethod
    def osc_saw(f: float, n: int, sr: int) -> np.ndarray:
        t = np.arange(n, dtype=np.float64) / sr
        sig = np.zeros(n)
        for h in range(1, 17):
            fh = f * h
            if fh >= sr * 0.45: break
            sig += np.sin(2*np.pi*fh*t) / h
        return sig * 0.5

    @staticmethod
    def noise_white(n: int, rng: np.random.RandomState) -> np.ndarray:
        return rng.randn(n).astype(np.float64)

    @staticmethod
    def noise_pink(n: int, rng: np.random.RandomState) -> np.ndarray:
        white = rng.randn(n).astype(np.float64)
        fft = np.fft.rfft(white)
        freqs = np.fft.rfftfreq(n, 1.0/AUDIO_SAMPLE_RATE)
        freqs[0] = max(freqs[1] if len(freqs) > 1 else 1.0, 1.0)
        fft[1:] /= np.sqrt(np.abs(freqs[1:])); fft[0] = 0
        return np.fft.irfft(fft, n=n)

    @staticmethod
    def noise_brown(n: int, rng: np.random.RandomState) -> np.ndarray:
        white = rng.randn(n).astype(np.float64)
        brown = np.cumsum(white); brown -= np.mean(brown)
        pk = np.max(np.abs(brown))
        if pk > 0: brown = brown / pk
        return brown * 0.5

    @staticmethod
    def modal(modes: List[Tuple[float, float, float]], n: int, sr: int, inharmonicity: float = 0.0) -> np.ndarray:
        t = np.arange(n, dtype=np.float64) / sr
        out = np.zeros(n, dtype=np.float64)
        f0 = modes[0][0] if modes else 440.0
        for freq, decay, amp in modes:
            af = freq
            if inharmonicity > 0:
                nh = freq / f0
                af = freq * np.sqrt(1 + inharmonicity * nh * nh)
            out += np.sin(2*np.pi*af*t) * np.exp(-decay*t) * amp
        return out

    @staticmethod
    def sat_tanh(x: np.ndarray, drive: float = 1.0) -> np.ndarray:
        if drive <= 0: return x
        return np.tanh(x * drive) / max(0.001, np.tanh(drive))

    @staticmethod
    def to_int16(x: np.ndarray, target_db: float = -1.0) -> np.ndarray:
        pk = np.max(np.abs(x)) if len(x) > 0 else 0.0
        if pk < 1e-10: return np.zeros_like(x, dtype=np.int16)
        return np.clip(x * (10**(target_db/20) / pk) * 32767, -32768, 32767).astype(np.int16)

MODULAR_SOUND_PRESETS: Dict[str, SoundSpec] = {
    "Mechanical": SoundSpec(duration=0.12, layers=[
        VoiceSpec(osc="noise_white", attack=0.0001, decay_rate=400.0, filt="bp", f_cutoff=3000, f_high=6000, drive=1.5, gain=0.5),
        VoiceSpec(osc="fm", freq=1200, fm_ratio=2.0, fm_index=0.4, attack=0.0003, decay_rate=80.0, filt="lp", f_cutoff=3500, gain=0.35),
        VoiceSpec(osc="sine", freq=150, attack=0.0015, decay_rate=50.0, filt="lp", f_cutoff=500, gain=0.45, delay=0.002)
    ]),
    "Cherry MX Red": SoundSpec(duration=0.10, layers=[
        VoiceSpec(osc="noise_white", attack=0.0003, decay_rate=250.0, filt="bp", f_cutoff=1500, f_high=4000, gain=0.15),
        VoiceSpec(osc="sine", freq=140, attack=0.0012, decay_rate=40.0, filt="lp", f_cutoff=500, gain=0.55),
        VoiceSpec(osc="sine", freq=70, attack=0.0015, decay_rate=30.0, filt="lp", f_cutoff=250, gain=0.5, delay=0.001)
    ]),
    "Cherry MX Blue": SoundSpec(duration=0.18, layers=[
        VoiceSpec(osc="noise_white", attack=0.0002, decay_rate=350.0, filt="bp", f_cutoff=2000, f_high=6000, drive=1.2, gain=0.45),
        VoiceSpec(osc="fm", freq=1800, fm_ratio=3.0, fm_index=0.8, attack=0.0004, decay_rate=60.0, filt="lp", f_cutoff=4500, gain=0.3),
        VoiceSpec(osc="sine", freq=110, attack=0.001, decay_rate=35.0, filt="lp", f_cutoff=400, gain=0.55, delay=0.0015)
    ]),
    "IBM Model M": SoundSpec(duration=0.25, layers=[
        VoiceSpec(osc="fm", freq=5200, fm_ratio=3.5, fm_index=1.2, attack=0.0002, decay_rate=12.0, filt="lp", f_cutoff=12000, gain=0.4),
        VoiceSpec(osc="noise_white", attack=0.0003, decay_rate=200.0, filt="bp", f_cutoff=1500, f_high=4500, gain=0.3, delay=0.0005),
        VoiceSpec(osc="sine", freq=120, attack=0.001, decay_rate=25.0, filt="lp", f_cutoff=300, gain=0.45, delay=0.002)
    ]),
    "ASMR Deep Thock": SoundSpec(duration=0.15, layers=[
        VoiceSpec(osc="sine", freq=110, attack=0.003, decay_rate=25.0, filt="lp", f_cutoff=400, gain=0.75),
        VoiceSpec(osc="sine", freq=60, attack=0.004, decay_rate=20.0, filt="lp", f_cutoff=200, gain=0.6, delay=0.001),
        VoiceSpec(osc="noise_pink", attack=0.006, decay_rate=45.0, filt="lp", f_cutoff=900, gain=0.2)
    ]),
    "Studio ASMR": SoundSpec(duration=0.12, layers=[
        VoiceSpec(osc="noise_white", attack=0.0003, decay_rate=250.0, filt="bp", f_cutoff=2500, f_high=5000, gain=0.18),
        VoiceSpec(osc="fm", freq=1000, fm_ratio=2.0, fm_index=0.3, attack=0.0005, decay_rate=80.0, filt="lp", f_cutoff=4000, gain=0.3),
        VoiceSpec(osc="sine", freq=150, attack=0.0015, decay_rate=50.0, filt="lp", f_cutoff=600, gain=0.5, delay=0.002)
    ]),
    "Typewriter": SoundSpec(duration=0.18, layers=[
        VoiceSpec(osc="sine", freq=2000, attack=0.001, decay_rate=15.0, filt="lp", f_cutoff=3000, gain=0.6),
        VoiceSpec(osc="noise_white", attack=0.0005, decay_rate=100.0, filt="bp", f_cutoff=1000, f_high=3000, gain=0.3, delay=0.005)
    ]),
    "Cyberpunk Hacker": SoundSpec(duration=0.10, layers=[
        VoiceSpec(osc="fm", freq=800, fm_ratio=3.5, fm_index=1.5, attack=0.0005, decay_rate=40.0, filt="lp", f_cutoff=4000, gain=0.4),
        VoiceSpec(osc="sine", freq=80, attack=0.002, decay_rate=30.0, filt="lp", f_cutoff=200, gain=0.5, delay=0.001)
    ]),
    "Heavenly ASMR": SoundSpec(duration=0.40, layers=[
        VoiceSpec(osc="modal", modes=[(800, 4.0, 1.0), (1600, 2.5, 0.5), (2800, 1.5, 0.25)], attack=0.002, decay_rate=8.0, filt="lp", f_cutoff=8000, gain=0.5),
        VoiceSpec(osc="sine", freq=100, attack=0.003, decay_rate=20.0, filt="lp", f_cutoff=250, gain=0.4, delay=0.001)
    ]),
    "Lo-Fi Chill": SoundSpec(duration=0.15, layers=[
        VoiceSpec(osc="sine", freq=150, attack=0.004, decay_rate=25.0, filt="lp", f_cutoff=400, gain=0.55),
        VoiceSpec(osc="noise_pink", attack=0.005, decay_rate=15.0, filt="lp", f_cutoff=500, gain=0.25, delay=0.001)
    ]),
    "Crystal Chime": SoundSpec(duration=0.40, layers=[
        VoiceSpec(osc="modal", modes=[(1500, 7.0, 1.0), (3150, 5.0, 0.5), (4950, 3.0, 0.3), (7050, 2.0, 0.2)], inharmonicity=0.0002, attack=0.0001, decay_rate=7.0, filt="lp", f_cutoff=16000, gain=0.5)
    ]),
}

class ModularSoundEngine:
    def __init__(self, sr: int = AUDIO_SAMPLE_RATE):
        self.sr = sr

    def _render_voice(self, spec: VoiceSpec, n: int, rng: np.random.RandomState) -> np.ndarray:
        sig = np.zeros(n, dtype=np.float64)
        if spec.osc == "sine": sig = DSP.osc_sine(spec.freq, n, self.sr)
        elif spec.osc == "fm": sig = DSP.osc_fm(spec.freq, spec.fm_ratio, spec.fm_index, n, self.sr)
        elif spec.osc == "saw": sig = DSP.osc_saw(spec.freq, n, self.sr)
        elif spec.osc == "noise_white": sig = DSP.noise_white(n, rng)
        elif spec.osc == "noise_pink": sig = DSP.noise_pink(n, rng)
        elif spec.osc == "noise_brown": sig = DSP.noise_brown(n, rng)
        elif spec.osc == "modal" and spec.modes: sig = DSP.modal(spec.modes, n, self.sr, spec.inharmonicity)

        sig *= DSP.env_exp(n, self.sr, attack=spec.attack, decay_rate=spec.decay_rate, attack_curve=spec.attack_curve)
        if spec.filt == "lp": sig = DSP.filt_lp(sig, spec.f_cutoff, self.sr)
        elif spec.filt == "hp": sig = DSP.filt_hp(sig, spec.f_cutoff, self.sr)
        elif spec.filt == "bp": sig = DSP.filt_bp(sig, spec.f_cutoff, spec.f_high, self.sr)
        elif spec.filt == "resonator": sig = DSP.filt_resonator(sig, spec.f_cutoff, spec.f_q, self.sr)
        if spec.drive > 0: sig = DSP.sat_tanh(sig, spec.drive)
        d = int(spec.delay * self.sr)
        if d > 0 and d < n:
            return np.concatenate([np.zeros(d, dtype=np.float64), sig[:n-d]]) * spec.gain
        return sig * spec.gain

    def render(self, spec: SoundSpec, seed: int) -> np.ndarray:
        rng = np.random.RandomState(seed)
        n = int(self.sr * spec.duration)
        mix = np.zeros(n, dtype=np.float64)
        for v in spec.layers:
            mix += self._render_voice(v, n, rng)
        return DSP.to_int16(DSP.filt_hp(mix, 20.0, self.sr, n_taps=63))

class SimpleSoundGen:
    _QWERTY_ROWS = ("`1234567890-=", "qwertyuiop[]\\", "asdfghjkl;'", "zxcvbnm,./")
    _ROW_PITCH_SHIFT = [1.5, 0.5, -0.5, -2.0]

    def __init__(self, sr: int = AUDIO_SAMPLE_RATE, preset: str = "Mechanical", stereo: bool = False):
        self.sr = sr; self.preset = preset; self.stereo = stereo
        self.engine = ModularSoundEngine(sr)
        spec = MODULAR_SOUND_PRESETS.get(preset, MODULAR_SOUND_PRESETS["Mechanical"])
        self.clicks = [self.engine.render(spec, i) for i in range(32)]
        self.spaces = [self.engine.render(spec, 100+i) for i in range(16)]
        self.enters = [self.engine.render(spec, 200+i) for i in range(8)]

    @staticmethod
    def _pitch_shift(sound: np.ndarray, semitones: float) -> np.ndarray:
        if semitones == 0 or len(sound) < 8: return sound
        factor = 2 ** (semitones / 12)
        n_orig = len(sound); n_new = max(1, int(n_orig / factor))
        if n_new == n_orig: return sound
        indices = np.linspace(0, n_orig - 1, n_new)
        i0 = indices.astype(np.int32); frac = indices - i0
        i1 = np.minimum(i0 + 1, n_orig - 1)
        s = sound.astype(np.float64)
        shifted = s[i0] * (1 - frac) + s[i1] * frac
        return shifted.astype(np.int16)

    def _get_pitch_shift(self, char: str) -> float:
        if char in (' ', '\n', '\t'): return -3.0
        c = char.lower()
        for r, row in enumerate(self._QWERTY_ROWS):
            if c in row: return self._ROW_PITCH_SHIFT[r]
        return 0.0

    def generate_pcm(self, timestamps: List[Tuple[float, str]], volume: float = 0.5) -> np.ndarray:
        if not timestamps: return np.zeros(0, dtype=np.int16)
        sr = self.sr
        total = max(ts for ts, _ in timestamps) + 0.3
        n = int(sr * total)
        rng = random.Random(98765)
        raw, starts_i, pans = [], [], []
        for ts, ch in timestamps:
            if ch == "\n":
                snd, vm, pan = rng.choice(self.enters), rng.uniform(1.05, 1.20), 0.2
            elif ch == " ":
                snd, vm, pan = rng.choice(self.spaces), rng.uniform(1.00, 1.15), 0.0
            else:
                base_snd = rng.choice(self.clicks)
                shift = self._get_pitch_shift(ch)
                snd = self._pitch_shift(base_snd, shift) if shift != 0 else base_snd
                vm, pan = rng.uniform(0.95, 1.10), rng.uniform(-0.3, 0.3)
            s = int(ts * sr); e = min(s + len(snd), n)
            if s < n:
                raw.append(snd[:e-s].astype(np.float32) * volume * vm)
                starts_i.append(s)
                if self.stereo: pans.append(pan)
        if not raw: return np.zeros(n, dtype=np.int16)
        if self.stereo:
            ml, mr = np.zeros(n, dtype=np.float32), np.zeros(n, dtype=np.float32)
            for i, snd in enumerate(raw):
                s = starts_i[i]; pan = pans[i]
                lg = np.cos((pan + 1.0) * np.pi / 4.0)
                rg = np.sin((pan + 1.0) * np.pi / 4.0)
                e = min(s + len(snd), n)
                ml[s:e] += snd[:e-s] * lg
                mr[s:e] += snd[:e-s] * rg
            ml = _normalize_to_lufs(ml, sr); mr = _normalize_to_lufs(mr, sr)
            out = np.empty(n*2, dtype=np.int16)
            out[0::2] = np.clip(ml * 32767, -32768, 32767).astype(np.int16)
            out[1::2] = np.clip(mr * 32767, -32768, 32767).astype(np.int16)
            return out
        starts = np.array(starts_i, dtype=np.int64)
        lengths = np.array([len(s) for s in raw], dtype=np.int64)
        flat = np.concatenate(raw)
        mix = np.zeros(n, dtype=np.float32)
        offset = 0
        for i in range(len(starts)):
            mix[int(starts[i]):int(starts[i]+lengths[i])] += flat[offset:offset+lengths[i]]
            offset += lengths[i]
        mix = _normalize_to_lufs(mix, sr)
        return np.clip(mix * 32767, -32768, 32767).astype(np.int16)

# ============================================================================
# 7. TYPING ANIMATOR
# ============================================================================

class TypingAnimator:
    def __init__(self, code: str, profile: TypingProfile, seed: int = 42):
        self.code = code
        self.profile = profile
        self.error_count = 0
        rng = random.Random(seed)
        chars = list(code)
        base_delay = 1.0 / ((profile.wpm * 5) / 60)
        t = profile.start_pause
        self.display_chars: List[str] = []
        self._timestamps: List[float] = []
        self.timeline: List[Tuple[float, str]] = []

        for char in chars:
            if char not in ('\n', ' ', '\t') and rng.random() < profile.typo_rate:
                self.error_count += 1
                t += base_delay * rng.uniform(0.4, 0.9)
                typo_char = rng.choice("abcdefghijklmnopqrstuvwxyz")
                self.timeline.append((t, typo_char))
                self.display_chars.append(typo_char)
                self._timestamps.append(t)
                t += base_delay * rng.uniform(0.3, 0.6)
                self.timeline.append((t, '\b'))
                self.display_chars.append('\b')
                self._timestamps.append(t)

            self.timeline.append((t, char))
            self.display_chars.append(char)
            self._timestamps.append(t)

            if char in ".!?": t += base_delay * rng.uniform(5.0, 8.0)
            elif char in ",;:": t += base_delay * rng.uniform(2.5, 4.0)
            elif char == '\n': t += base_delay * rng.uniform(3.5, 6.0)
            elif char == ' ': t += base_delay * rng.uniform(0.9, 1.4)
            elif profile.burst_mode and rng.random() < 0.05:
                t += base_delay * rng.uniform(8.0, 15.0)
            else:
                t += base_delay * rng.uniform(0.7, 1.3)

        self._duration = t + profile.end_pause

    def duration(self) -> float:
        return self._duration

    def visible_at(self, t: float) -> int:
        return bisect.bisect_right(self._timestamps, t) if t > 0 else 0

    def char_timestamps(self) -> List[Tuple[float, str]]:
        return self.timeline

    def active_key_at(self, t: float, fd: float = 0.18) -> Tuple[Optional[str], float]:
        if not self._timestamps or t < self._timestamps[0]:
            return None, 0.0
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0: return None, 0.0
        last_ts, last_char = self.timeline[idx - 1]
        elapsed = t - last_ts
        if elapsed < fd:
            return (last_char, max(0.0, (1.0 - elapsed / fd) ** 1.5))
        return None, 0.0

    @staticmethod
    def find_wpm_for_target(text: str, target_dur: float, sp: float = 0.5, ep: float = 1.5) -> int:
        available = target_dur - sp - ep
        if available <= 0: return 300
        count = len(text)
        return max(30, min(300, int(60.0 / max(0.01, available / max(1, count * 1.2)) / 5.0)))

# ============================================================================
# 8. KEYBOARD OVERLAY & RENDERER
# ============================================================================

KEYBOARD_LAYOUTS: Dict[str, List[List[Tuple[str, float]]]] = {
    "QWERTY": [
        [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],
        [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],
        [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "AZERTY": [
        [("²",1),("&",1),("é",1),("\"",1),("'",1),("(",1),("-",1),("è",1),("_",1),("ç",1),("à",1),(")",1),("=",1),("Bksp",2)],
        [("Tab",1.5),("A",1),("Z",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("^",1),("$",1),("Enter",1.5)],
        [("Caps",1.75),("Q",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("M",1),("ù",1),("*",1),("Enter",2.25)],
        [("Shift",1.25),("<",1),("W",1),("X",1),("C",1),("V",1),("B",1),("N",1),(",",1),(";",1),(":",1),("!",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "QWERTZ": [
        [("^",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("ß",1),("´",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Z",1),("U",1),("I",1),("O",1),("P",1),("Ü",1),("+",1),("Enter",1.5)],
        [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("Ö",1),("Ä",1),("#",1),("Enter",2.25)],
        [("Shift",1.25),("<",1),("Y",1),("X",1),("C",1),("V",1),("B",1),("N",1),(",",1),(".",1),("-",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "Dvorak": [
        [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("[",1),("]",1),("Bksp",2)],
        [("Tab",1.5),("'",1),(",",1),(".",1),("P",1),("Y",1),("F",1),("G",1),("C",1),("R",1),("L",1),("/",1),("=",1),("\\",1.5)],
        [("Caps",1.75),("A",1),("O",1),("E",1),("U",1),("I",1),("D",1),("H",1),("T",1),("N",1),("S",1),("-",1),("Enter",2.25)],
        [("Shift",2.25),(";",1),("Q",1),("J",1),("K",1),("X",1),("B",1),("M",1),("W",1),("V",1),("Z",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "Colemak": [
        [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("F",1),("P",1),("G",1),("J",1),("L",1),("U",1),("Y",1),(";",1),("[",1),("]",1),("\\",1.5)],
        [("Bksp",1.75),("A",1),("R",1),("S",1),("T",1),("D",1),("H",1),("N",1),("E",1),("I",1),("O",1),("'",1),("Enter",2.25)],
        [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("K",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "JIS (Japanese)": [
        [("半",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("^",1),("¥",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("@",1),("[",1),("]",1),("\\",1.5)],
        [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),(":",1),("Enter",2.25)],
        [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("_",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("無",1),("",4.25),("變",1.25),("Alt",1.25),("Fn",1.25),("Ctrl",1.25)],
    ],
    "Pinyin (Chinese)": [
        [("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],
        [("中",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],
        [("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
    "Turkish Q": [
        [("\"",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("*",1),("-",1),("Bksp",2)],
        [("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("Ğ",1),("Ü",1),(";",1.5)],
        [("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("Ş",1),("İ",1),("Enter",2.25)],
        [("Shift",2.25),("<",1),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),("Ö",1),("Ç",1),(".",1),("Shift",2.75)],
        [("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)],
    ],
}

class KeyboardOverlay:
    def __init__(self, video_w: int, video_h: int, layout_name: str = "QWERTY", 
                 theme: Optional[ThemeDict] = None, opacity: float = 0.82, 
                 position: str = "bottom_center"):
        self.video_w, self.video_h = video_w, video_h
        self.theme = theme or THEMES["Dracula"]
        self.opacity = opacity
        self.rows = KEYBOARD_LAYOUTS.get(layout_name, KEYBOARD_LAYOUTS["QWERTY"])
        self.char_map: Dict[str, Point] = {}
        for ri, row in enumerate(self.rows):
            for ci, (label, _) in enumerate(row):
                if len(label) == 1:
                    self.char_map[label] = self.char_map[label.lower()] = (ri, ci)
                if label == "": self.char_map[" "] = (ri, ci)
                elif "enter" in label.lower(): self.char_map["\n"] = (ri, ci)
                elif "tab" in label.lower(): self.char_map["\t"] = (ri, ci)
                elif "bksp" in label.lower(): self.char_map["\b"] = (ri, ci)
        for s, b in {"~":"`","!":"1","@":"2","#":"3","$":"4","%":"5","^":"6","&":"7",
                     "*":"8","(":"9",")":"0","_":"-","+=":"=","{":"[","}":"]","|":"\\",
                     ":":";",'"':"'","<":",",">":".","?":"/"}.items():
            if b in self.char_map: self.char_map[s] = self.char_map[b]

        target_kb_w = int(video_w * 0.65)
        required_unit = target_kb_w / 15.0
        self.key_unit = max(14, min(55, int(required_unit)))
        self.key_gap = max(2, self.key_unit // 14)
        self.key_h = int(self.key_unit * 0.82)
        self._kb_w = int(max(sum(w for _, w in r) for r in self.rows) * self.key_unit
                         + (max(len(r) for r in self.rows) - 1) * self.key_gap)
        self._kb_h = int(len(self.rows) * self.key_h + (len(self.rows) - 1) * self.key_gap)

        self.position = position
        self._kb_x, self._kb_y = 0, 0
        self.key_rects: Dict[Point, QRect] = {}
        self._rebuild_key_rects()

    def height_needed(self) -> int:
        return self._kb_h + max(16, self.video_h // 30)

    def _apply_position(self, y_target: Optional[int] = None) -> None:
        m_x = max(8, self.video_w // 60)
        m_y = max(8, self.video_h // 60)
        if "center" in self.position: self._kb_x = (self.video_w - self._kb_w) // 2
        elif "right" in self.position: self._kb_x = self.video_w - self._kb_w - m_x
        elif "left" in self.position: self._kb_x = m_x
        if "top" in self.position: self._kb_y = m_y
        else:
            if y_target is not None:
                self._kb_y = y_target
                max_y = self.video_h - self._kb_h - m_y
                min_y = m_y
                if self._kb_y > max_y: self._kb_y = max_y
                if self._kb_y < min_y: self._kb_y = min_y
            else:
                self._kb_y = self.video_h - self._kb_h - m_y

    def _rebuild_key_rects(self) -> None:
        self.key_rects = {}
        for ri, row in enumerate(self.rows):
            x = self._kb_x
            for ci, (_, w) in enumerate(row):
                kw = int(w * self.key_unit) - self.key_gap
                y = self._kb_y + ri * (self.key_h + self.key_gap)
                self.key_rects[(ri, ci)] = QRect(x, y, kw, self.key_h)
                x += int(w * self.key_unit)

    def reposition(self, y_target: Optional[int] = None) -> None:
        self._apply_position(y_target)
        self._rebuild_key_rects()

    def resolve_key(self, ch: str) -> Optional[Point]:
        return self.char_map.get(ch)

    def draw(self, p: QPainter, active_key: Optional[Point] = None, flash: float = 0.0) -> None:
        p.save()
        p.setOpacity(self.opacity)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        th = self.theme
        radius = max(3, self.key_unit // 8)

        pad = max(6, self.key_unit // 4)
        p.setPen(QPen(QColor(th["window_border"]), max(1, self.key_unit // 20)))
        p.setBrush(QColor(th["title_bar"]))
        p.drawRoundedRect(self._kb_x-pad, self._kb_y-pad,
                          self._kb_w+2*pad, self._kb_h+2*pad, radius*2, radius*2)

        kbg = QColor(th["background"])
        kbr = QColor(th["window_border"])
        lc = QColor(th["foreground"])
        mc = QColor(th["line_number"])
        hlb = QColor(th["cursor"])

        hkf = hlg = None
        hle = 0
        if flash > 0 and active_key is not None:
            hkf = QColor(
                int(kbg.red()+(hlb.red()-kbg.red())*flash),
                int(kbg.green()+(hlb.green()-kbg.green())*flash),
                int(kbg.blue()+(hlb.blue()-kbg.blue())*flash),
            )
            hlg = QColor(hlb); hlg.setAlpha(int(80*flash))
            hle = max(3, int(self.key_unit*0.12*flash))

        for (ri, ci), rect in self.key_rects.items():
            label = self.rows[ri][ci][0]
            ia = (active_key is not None and active_key == (ri, ci))
            if ia and hkf is not None:
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(hlg)
                p.drawRoundedRect(rect.adjusted(-hle, -hle, hle, hle), radius, radius)
                p.setBrush(hkf); p.setPen(QPen(kbr, 1))
            else:
                p.setPen(Qt.PenStyle.NoPen); p.setBrush(kbr.darker(150))
                p.drawRoundedRect(rect.adjusted(0, 3, 0, 3), radius, radius)
                p.setBrush(kbg); p.setPen(QPen(kbr, 1))
            p.drawRoundedRect(rect, radius, radius)
            if label:
                p.setPen(mc if len(label) > 1 else lc)
                p.setFont(QFont("Segoe UI", max(7, int(self.key_unit * 0.30))))
                p.drawText(rect, Qt.AlignmentFlag.AlignCenter, label)
        p.restore()

class CodeRenderer:
    def __init__(self, width: int, height: int, config: StudioConfig,
                 code: str, title: str, language: str,
                 kb_overlay: Optional[KeyboardOverlay] = None):
        self.width = width
        self.height = height
        self.config = config
        self.code = code
        self.title = title
        self.language = language
        self.theme = THEMES.get(config.theme, THEMES["Dracula"])
        self.kb_overlay = kb_overlay
        self.padding = min(24, max(8, min(width, height) // 30))
        self.tab_size = config.tab_size
        self._code_rect = QRect(0, 0, 1, 1)

        fams = [config.font_family, "JetBrains Mono", "Cascadia Code",
                "DejaVu Sans Mono", "Consolas", "monospace"]
        self.font = QFont(config.font_family, config.font_size)
        self.font.setFamilies(list(dict.fromkeys(fams)))
        self.font.setFixedPitch(True)
        self.fm = QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance("M")
        self.line_h = self.fm.height()
        self._tab_adv = self.char_w * self.tab_size

        self._qcolors = {k: QColor(v) for k, v in self.theme.items()
                         if isinstance(v, str) and v.startswith("#")}
        self._qc_fg = self._qcolors.get("foreground", QColor("#f8f8f2"))
        self._qc_ln = self._qcolors.get("line_number", QColor("#6272a4"))
        self._qc_cursor = self._qcolors.get("cursor", QColor("#f8f8f2"))
        self._qc_current = self._qcolors.get("current_line", QColor("#44475a"))
        self._qc_accent = self._qcolors.get("accent", QColor("#bd93f9"))

        self._token_cache: OrderedDict[str, list] = OrderedDict()
        self._token_lock = threading.Lock()
        self._build_bg_cache()

    def _tokenize(self, text: str) -> List[Tuple[QColor, str]]:
        if not _HAS_PYGMENTS or self.language == "text":
            return [(self._qc_fg, text)]
        with self._token_lock:
            if text in self._token_cache:
                self._token_cache.move_to_end(text)
                return self._token_cache[text]
            lexer = LexerFactory.get_lexer(self.language)
            if not lexer: return [(self._qc_fg, text)]
            tokens = []
            for ttype, val in lex(text, lexer):
                if val in ('\n', ' ', '\t'):
                    tokens.append((self._qc_fg, val)); continue
                color = self._qc_fg
                s = str(ttype)
                if s.startswith('Token.Comment'): color = self._qcolors.get("comment", self._qc_fg)
                elif s.startswith('Token.Keyword'): color = self._qcolors.get("keyword", self._qc_fg)
                elif s.startswith('Token.String'): color = self._qcolors.get("string", self._qc_fg)
                elif s.startswith('Token.Number'): color = self._qcolors.get("number", self._qc_fg)
                elif s.startswith('Token.Name.Function'): color = self._qcolors.get("function", self._qc_fg)
                elif s.startswith('Token.Name.Class'): color = self._qcolors.get("class_name", self._qc_fg)
                elif s.startswith('Token.Name.Builtin'): color = self._qcolors.get("builtin", self._qc_fg)
                elif s.startswith('Token.Name.Decorator'): color = self._qcolors.get("decorator", self._qc_fg)
                elif s.startswith('Token.Operator'): color = self._qcolors.get("operator", self._qc_fg)
                tokens.append((color, val))
            
            self._token_cache[text] = tokens
            if len(self._token_cache) > 1000:
                self._token_cache.popitem(last=False)
            return tokens

    def _build_bg_cache(self) -> None:
        self._bg = QImage(self.width, self.height, QImage.Format.Format_RGB32)
        self._bg.fill(QColor(self.theme["background"]))
        p = QPainter(self._bg)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        bg = self._qcolors.get("background", QColor("#282a36"))
        g = QLinearGradient(0, 0, 0, self.height)
        g.setColorAt(0, bg.lighter(105)); g.setColorAt(1, bg)
        p.fillRect(0, 0, self.width, self.height, g)

        pad = self.padding
        chrome_h = 42 if self.config.show_window_chrome else 0
        ww = self.width - 2 * pad

        kb_h = self.kb_overlay.height_needed() if self.kb_overlay else 0
        kb_top = self.kb_overlay and "top" in self.kb_overlay.position

        avail_h = self.height - 2 * pad
        target_wh = avail_h - kb_h
        max_ratio = 1.2
        if target_wh > ww * max_ratio: target_wh = int(ww * max_ratio)

        total_block_h = target_wh + kb_h
        start_y = pad + (avail_h - total_block_h) // 2

        wy = start_y + (kb_h if kb_top else 0)
        wh = target_wh
        wx, ww = pad, self.width - 2*pad

        p.setPen(Qt.PenStyle.NoPen); p.setBrush(QColor(0, 0, 0, 80))
        p.drawRoundedRect(wx+4, wy+4, ww, wh, 12, 12)
        p.setPen(QColor(self.theme["window_border"]))
        p.setBrush(QColor(self.theme["background"]))
        p.drawRoundedRect(wx, wy, ww, wh, 12, 12)

        if self.config.show_window_chrome:
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(self.theme["title_bar"]))
            p.drawRoundedRect(wx, wy, ww, chrome_h, 12, 12)
            p.drawRect(wx, wy+chrome_h-12, ww, 12)
            for i, color in enumerate(["#ff5f56", "#ffbd2e", "#27c93f"]):
                p.setBrush(QColor(color)); p.setPen(Qt.PenStyle.NoPen)
                p.drawEllipse(QPoint(wx+20+i*24, wy+19), 7, 7)
            self._code_rect = QRect(wx+4, wy+chrome_h, ww-8, wh-chrome_h)
        else:
            self._code_rect = QRect(wx+4, wy, ww-8, wh)

        if self.kb_overlay:
            if not kb_top: self.kb_overlay.reposition(wy + wh + max(8, self.height // 60))
            else: self.kb_overlay.reposition(start_y)
        p.end()

    @staticmethod
    def auto_font_size(lines_count: int, width: int, height: int,
                      padding: int = 24, show_chrome: bool = True,
                      show_ln: bool = True, text: str = "",
                      font_family: str = "JetBrains Mono",
                      keyboard_h: int = 0) -> int:
        chrome_h = 42 if show_chrome else 0
        max_ratio = 1.2
        avail_h = height - 2*padding - keyboard_h
        if avail_h > width * max_ratio: avail_h = int(width * max_ratio)
        rh, rw = avail_h - chrome_h, width - 2*padding - 8
        if rh < 20 or rw < 40 or lines_count < 1: return 14
        max_chars = max(max(len(l.replace("\t", "    ")) for l in text.split("\n")), 1) if text else 80

        def lnw(cw: int) -> int:
            return (len(str(lines_count))*cw + 32 + int(cw * 1.5)) if show_ln else 0

        lo, hi, best = 8, max(14, min(128, int(width/40))), 14
        while lo <= hi:
            mid = (lo+hi)//2
            fm = QFontMetrics(QFont(font_family, mid))
            if min(lines_count, 40) * fm.height() <= rh:
                cw = fm.horizontalAdvance("M")
                if min(max_chars, 120) * cw + lnw(cw) <= rw:
                    best = mid; lo = mid + 1
                else:
                    hi = mid - 1
            else:
                hi = mid - 1
        return max(8, best)

    def render_frame(self, display_chars: List[str], num_visible: int,
                     cursor_visible: bool = True, target: Optional[QImage] = None,
                     active_char: Optional[str] = None, key_flash: float = 0.0,
                     title_text: str = "", t: float = 0.0, duration: float = 0.0,
                     animator: Optional[TypingAnimator] = None,
                     draw_guides: bool = False, phase: str = "main") -> QImage:
        img = target if target is not None else QImage(self.width, self.height, QImage.Format.Format_RGB32)
        if target is None: img.fill(QColor(self.theme["background"]))
        
        with QPainter(img) as p:
            p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
            p.drawImage(0, 0, self._bg)

            cr = self._code_rect
            if self.config.show_window_chrome:
                p.setPen(QColor(self.theme["title_text"]))
                p.setFont(QFont(self.config.font_family, max(8, min(12, self.width // 80))))
                p.drawText(QRect(self.padding, cr.top() - 42, cr.width(), 42),
                           Qt.AlignmentFlag.AlignCenter, title_text)

            out: List[str] = []
            for ch in display_chars[:num_visible]:
                if ch == "\b":
                    if out: out.pop()
                else:
                    out.append(ch)
            visible_text = "".join(out)

            tokens = self._tokenize(visible_text)
            lines: List[List[Tuple[QColor, str]]] = []
            current_line: List[Tuple[QColor, str]] = []
            for color, val in tokens:
                if '\n' in val:
                    parts = val.split('\n')
                    for i, part in enumerate(parts):
                        if part: current_line.append((color, part))
                        if i < len(parts) - 1:
                            lines.append(current_line); current_line = []
                else:
                    current_line.append((color, val))
            lines.append(current_line)

            cursor_line = len(lines) - 1
            total_lines = len(lines)
            max_vis = max(1, -(-cr.height() // self.line_h))

            if self.config.smooth_scroll:
                target_scroll = max(0, min(cursor_line - max_vis + 5, total_lines - max_vis)) \
                    if cursor_line >= max_vis - 5 else max(0, cursor_line - 3)
                if not hasattr(self, '_current_scroll'):
                    self._current_scroll = float(target_scroll)
                self._current_scroll += (target_scroll - self._current_scroll) * 0.35
                scroll = int(self._current_scroll)
            else:
                scroll = max(0, min(cursor_line - max_vis + 5, total_lines - max_vis)) \
                    if cursor_line >= max_vis - 5 else max(0, cursor_line - 3)

            ln_gap = max(12, int(self.char_w * 1.5))
            ln_width = (len(str(total_lines + scroll)) * self.char_w + 32 + ln_gap) \
                if self.config.show_line_numbers else 0
            x0, y_acc = cr.left() + ln_width, cr.top()

            focus_start, focus_end = -1, -1
            if self.config.focus_dimming and self.language in ("python", "javascript", "typescript", "go", "rust", "ruby"):
                for i, line in enumerate(lines):
                    line_str = "".join(v for _, v in line)
                    if re.match(r'^\s*(def|class|func|fn)\s', line_str):
                        if i <= cursor_line: focus_start = i
                        elif i > cursor_line and focus_start != -1:
                            focus_end = i; break
                if focus_start != -1 and focus_end == -1: focus_end = total_lines

            p.setClipRect(cr)
            p.setFont(self.font)

            for si in range(max_vis):
                li = scroll + si
                if li >= total_lines: break
                y = y_acc; y_acc += self.line_h

                bg_color = None
                if li == cursor_line: bg_color = self._qc_current
                if bg_color: p.fillRect(cr.left(), y, cr.width(), self.line_h, bg_color)

                if self.config.show_line_numbers and ln_width > 0:
                    p.setPen(self._qc_ln)
                    p.drawText(QRect(cr.left(), y, ln_width - ln_gap, self.line_h),
                               Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, str(li + 1))

                line_tokens = lines[li]
                if not line_tokens:
                    if cursor_visible and li == cursor_line: self._draw_caret(p, int(x0), int(y))
                    continue

                x = x0
                opacity = 1.0
                if focus_start != -1 and not (focus_start <= li < focus_end): opacity = 0.35

                for color, val in line_tokens:
                    if opacity < 1.0:
                        dim = QColor(color); dim.setAlpha(int(255 * opacity))
                        p.setPen(dim)
                    else:
                        p.setPen(color)
                    p.setFont(self.font)
                    for ch in val:
                        if ch == "\t":
                            x += self._tab_adv
                        else:
                            ch_w = self.fm.horizontalAdvance(ch)
                            p.drawText(QRect(int(x), int(y), int(ch_w), int(self.line_h)),
                                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, ch)
                            x += ch_w
                if cursor_visible and li == cursor_line: self._draw_caret(p, int(x), int(y))

            p.setClipping(False)

            if self.kb_overlay and active_char and key_flash > 0:
                ak = self.kb_overlay.resolve_key(active_char)
                if ak: self.kb_overlay.draw(p, active_key=ak, flash=key_flash)

            if self.config.progress_bar_overlay and duration > 0:
                prog = min(1.0, t / duration)
                bar_h = 4
                bar_y = self.height - bar_h - 8
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(QColor(0, 0, 0, 120))
                p.drawRect(0, bar_y, self.width, bar_h)
                p.setBrush(self._qc_accent)
                p.drawRect(0, bar_y, int(self.width * prog), bar_h)

            if self.config.watermark_text:
                p.setPen(QColor(255, 255, 255, int(255 * self.config.watermark_opacity)))
                p.setFont(QFont(self.config.font_family, max(10, self.width // 80)))
                p.drawText(QRect(self.padding, self.height - 40, self.width - 2*self.padding, 30),
                           Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, self.config.watermark_text)

            if phase == "intro" and self.config.intro_card:
                self._draw_card(p, title_text, t, self.config.intro_duration, fade_in=True)
            elif phase == "outro" and self.config.outro_card:
                self._draw_card(p, title_text, t, self.config.outro_duration, fade_in=False)

            if draw_guides:
                p.setRenderHint(QPainter.RenderHint.Antialiasing)
                p.setPen(QPen(QColor(255, 0, 0, 150), 2, Qt.PenStyle.DashLine))
                p.setBrush(Qt.BrushStyle.NoBrush)
                p.drawRect(24, 24, self.width - 48, self.height - 48)
                if self.config.show_window_chrome:
                    p.setPen(QPen(QColor(0, 255, 0, 150), 2, Qt.PenStyle.DashLine))
                    p.drawRect(self._code_rect.left()-4, self._code_rect.top()-42, self._code_rect.width()+8, 42)
                p.setPen(QPen(QColor(0, 150, 255, 150), 2, Qt.PenStyle.DashLine))
                p.drawRect(self._code_rect)

        return img

    def _draw_card(self, p: QPainter, title: str, t: float, dur: float, fade_in: bool) -> None:
        if fade_in:
            alpha = min(1.0, t / 0.5)
            if t > dur - 0.5: alpha = max(0.0, (dur - t) / 0.5)
        else:
            alpha = min(1.0, t / 0.5)
            if t > dur - 0.5: alpha = max(0.0, (dur - t) / 0.5)

        p.save()
        p.setOpacity(alpha)
        p.fillRect(0, 0, self.width, self.height, QColor(self.theme["background"]))

        p.setPen(QColor(self.theme["title_text"]))
        title_font = QFont(self.config.font_family, max(28, self.width // 30))
        title_font.setBold(True)
        p.setFont(title_font)
        p.drawText(QRect(0, self.height//2 - 60, self.width, 80), Qt.AlignmentFlag.AlignCenter, title)

        p.setPen(QColor(self.theme["comment"]))
        p.setFont(QFont(self.config.font_family, max(12, self.width // 80)))
        p.drawText(QRect(0, self.height//2 + 20, self.width, 40), Qt.AlignmentFlag.AlignCenter, "Typing Video Studio")
        p.restore()

    def _draw_caret(self, p: QPainter, x: int, y: int) -> None:
        pad = (self.line_h - self.fm.height()) // 2
        caret_y = y + pad + 1
        caret_h = self.fm.height() - 2
        style = self.config.cursor_style
        if style == CursorStyle.BLOCK.value:
            w = max(self.char_w, 2)
            gc = QColor(self._qc_cursor); gc.setAlpha(120)
            p.fillRect(x, caret_y, w, caret_h, gc)
        elif style == CursorStyle.BEAM.value:
            w = max(2, self.config.font_size // 10)
            p.fillRect(x, caret_y, w, caret_h, self._qc_cursor)
        elif style == CursorStyle.UNDERLINE.value:
            w = max(self.char_w, 2)
            p.fillRect(x, caret_y + caret_h - 3, w, 3, self._qc_cursor)

class PaneBundle:
    def __init__(self, renderer: CodeRenderer, animator: TypingAnimator,
                 title: str, config: StudioConfig):
        self.renderer = renderer
        self.animator = animator
        self.title = title
        self.config = config
        self.frame_w = renderer.width
        self.frame_h = renderer.height

    def duration(self) -> float:
        d = self.animator.duration()
        if self.config.intro_card: d += self.config.intro_duration
        if self.config.outro_card: d += self.config.outro_duration
        return d

    def char_timestamps_all(self) -> List[Tuple[float, str]]:
        offset = self.config.intro_duration if self.config.intro_card else 0.0
        return [(ts + offset, ch) for ts, ch in self.animator.char_timestamps()]

    def render_frame(self, t: float, target: Optional[QImage] = None,
                     draw_guides: bool = False) -> QImage:
        intro_dur = self.config.intro_duration if self.config.intro_card else 0.0
        outro_dur = self.config.outro_duration if self.config.outro_card else 0.0
        main_dur = self.animator.duration()

        if self.config.intro_card and t < intro_dur:
            img = target if target is not None else QImage(self.frame_w, self.frame_h, QImage.Format.Format_RGB32)
            img.fill(QColor(self.renderer.theme["background"]))
            with QPainter(img) as p: p.drawImage(0, 0, self.renderer._bg)
            return self.renderer.render_frame([], 0, False, target=img,
                                              title_text=self.title, t=t,
                                              duration=self.duration(),
                                              animator=self.animator,
                                              draw_guides=draw_guides, phase="intro")

        if self.config.outro_card and t > intro_dur + main_dur:
            outro_t = t - intro_dur - main_dur
            img = target if target is not None else QImage(self.frame_w, self.frame_h, QImage.Format.Format_RGB32)
            img.fill(QColor(self.renderer.theme["background"]))
            with QPainter(img) as p: p.drawImage(0, 0, self.renderer._bg)
            return self.renderer.render_frame(self.animator.display_chars,
                                              len(self.animator.display_chars),
                                              False, target=img,
                                              title_text=self.title, t=outro_t,
                                              duration=self.duration(),
                                              animator=self.animator,
                                              draw_guides=draw_guides, phase="outro")

        main_t = t - intro_dur
        nv = self.animator.visible_at(main_t)
        ac, kf = self.animator.active_key_at(main_t)

        scale = 1.0
        if self.config.cinematic_zoom and main_t < main_dur:
            progress = main_t / max(0.1, main_dur)
            scale = 1.0 + 0.08 * progress

        img = self.renderer.render_frame(
            self.animator.display_chars, nv, True,
            active_char=ac, key_flash=kf,
            title_text=self.title, target=target,
            t=main_t, duration=main_dur,
            animator=self.animator,
            draw_guides=draw_guides, phase="main"
        )

        if scale > 1.0:
            scaled = img.scaled(int(self.frame_w * scale), int(self.frame_h * scale),
                                Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                Qt.TransformationMode.SmoothTransformation)
            canvas = QImage(self.frame_w, self.frame_h, QImage.Format.Format_RGB32)
            canvas.fill(QColor(self.renderer.theme["background"]))
            with QPainter(canvas) as p:
                x = (self.frame_w - scaled.width()) // 2
                y = (self.frame_h - scaled.height()) // 2
                p.drawImage(x, y, scaled)
            return canvas
        return img

# ============================================================================
# 9. EXPORT PIPELINE & COMMAND BUILDER
# ============================================================================

class FFmpegCommandBuilder:
    """Pure functional FFmpeg command builder. Stateless and testable."""
    @staticmethod
    def build(w: int, h: int, fps: int, output: str, config: StudioConfig,
              has_audio: bool, has_bgm: bool) -> List[str]:
        cmd = ["ffmpeg", "-y", "-f", "rawvideo", "-pix_fmt", "bgra",
               "-s", f"{w}x{h}", "-r", str(fps), "-i", "pipe:0"]
        
        if has_bgm: cmd += ["-i", config.bgm_path]

        if has_audio and has_bgm:
            if config.bgm_duck:
                cmd += ["-filter_complex",
                        f"[2:a]volume={config.bgm_volume/100.0}[bgm];"
                        f"[bgm][1:a]sidechaincompress=threshold=0.05:ratio=8:attack=5:release=200[bgm_duck];"
                        f"[1:a][bgm_duck]amix=inputs=2:duration=longest[aout]"]
            else:
                cmd += ["-filter_complex",
                        f"[2:a]volume={config.bgm_volume/100.0}[bgm];"
                        f"[1:a][bgm]amix=inputs=2:duration=longest[aout]"]
            cmd += ["-map", "0:v", "-map", "[aout]"]
        elif has_audio:
            cmd += ["-map", "0:v", "-map", "1:a"]
        elif has_bgm:
            cmd += ["-map", "0:v", "-map", "1:a"]
        else:
            cmd += ["-map", "0:v"]

        pixels = w * h
        if config.encoder == EncoderType.YOUTUBE.value:
            maxrate = int((pixels / 2073600.0) * 12000000)
            bufsize = maxrate * 2
            cmd += ["-c:v", "libx264", "-preset", "slow", "-crf", "17",
                    "-maxrate", f"{maxrate}", "-bufsize", f"{bufsize}",
                    "-pix_fmt", "yuv420p", "-profile:v", "high",
                    "-g", str(fps*2), "-keyint_min", str(fps*2),
                    "-sc_threshold", "0",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]
        elif config.encoder == EncoderType.NVENC.value:
            cmd += ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr",
                    "-cq", "19", "-b:v", "0", "-pix_fmt", "yuv420p",
                    "-profile:v", "high",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]
        elif config.encoder == EncoderType.QSV.value:
            cmd += ["-c:v", "h264_qsv", "-preset", "slow", "-global_quality", "19",
                    "-pix_fmt", "yuv420p", "-profile:v", "high",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]
        elif config.encoder == EncoderType.AMF.value:
            cmd += ["-c:v", "h264_amf", "-preset", "quality", "-rc", "cqp",
                    "-qp_i", "19", "-qp_p", "19", "-pix_fmt", "yuv420p",
                    "-profile:v", "high",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]
        elif config.encoder == EncoderType.VIDEOTOOLBOX.value:
            cmd += ["-c:v", "h264_videotoolbox", "-q:v", "50",
                    "-pix_fmt", "yuv420p", "-profile:v", "high",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]
        else:
            cmd += ["-c:v", "libx264", "-preset", "slow", "-crf", "17",
                    "-pix_fmt", "yuv420p", "-profile:v", "high",
                    "-color_primaries", "bt709", "-color_trc", "bt709",
                    "-colorspace", "bt709", "-color_range", "tv"]

        if has_audio or has_bgm:
            cmd += ["-c:a", "aac", "-b:a", "256k"]
        cmd += ["-movflags", "+faststart", output]
        return cmd

@dataclass
class ExportCommand:
    item: FileItem
    output_path: str
    config: StudioConfig
    bundle: Optional[PaneBundle] = None
    status: str = "Pending"
    _lock: threading.Lock = field(default_factory=threading.Lock)

    def get_bundle(self, strategy: 'CodeEditorStrategy') -> Optional[PaneBundle]:
        """Thread-safe lazy initialization of the bundle."""
        with self._lock:
            if self.bundle is None:
                try:
                    self.bundle = strategy.build(self.config, [self.item], self.config.custom_code)
                except Exception as e:
                    logger.error(f"Failed to build bundle for {self.output_path}", exc_info=True)
                    return None
            return self.bundle

class VideoExporter(QThread):
    progress = Signal(int)
    status = Signal(str)
    finished_ok = Signal(str, int)
    error = Signal(str)

    def __init__(self, command: ExportCommand, strategy: 'CodeEditorStrategy'):
        super().__init__()
        self.command = command
        self.strategy = strategy
        self.output = command.output_path
        self.fps = command.config.fps
        self.config = command.config
        self._cancel = threading.Event()
        self.w, self.h = 0, 0

    def cancel(self) -> None: 
        self._cancel.set()

    def _generate_audio(self, tmp_dir: str) -> Optional[str]:
        if not self.config.sound_enabled: return None
        try:
            sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo)
            pcm = sg.generate_pcm(self.bundle.char_timestamps_all(),
                                  self.config.volume / 100.0)
            audio_path = os.path.join(tmp_dir, "audio.wav")
            with wave.open(audio_path, "w") as wf:
                wf.setnchannels(2 if sg.stereo else 1)
                wf.setsampwidth(2)
                wf.setframerate(sg.sr)
                wf.writeframes(pcm.tobytes())
            del pcm, sg
            gc.collect()
            return audio_path
        except Exception:
            logger.error("Audio generation failed", exc_info=True)
            return None

    def run(self) -> None:
        tmp = tempfile.mkdtemp(dir=str(TEMP_DIR), prefix="export_")
        try:
            self.bundle = self.command.get_bundle(self.strategy)
            if not self.bundle:
                self.error.emit("Failed to build renderer bundle")
                return

            self.w, self.h = self.bundle.frame_w, self.bundle.frame_h
            total_dur = self.bundle.duration()
            n_frames = int(total_dur * self.fps)

            max_workers = max(2, (os.cpu_count() or 4) - 1)
            frame_ram = self.w * self.h * 4
            max_window_by_ram = max(2, int(512 * 1024 * 1024 / frame_ram))
            window_size = min(max_workers * 2, max_window_by_ram)
            
            def render_worker(fi: int) -> Optional[QImage]:
                try:
                    if self._cancel.is_set(): return None
                    t = fi / self.fps
                    img = QImage(self.w, self.h, QImage.Format.Format_RGB32)
                    return self.bundle.render_frame(t, img)
                except Exception:
                    logger.error(f"Error rendering frame {fi}", exc_info=True)
                    return None

            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                audio_future = executor.submit(self._generate_audio, tmp) if self.config.sound_enabled else None
                
                futures: OrderedDict[int, Future] = OrderedDict()
                for fi in range(min(window_size, n_frames)):
                    futures[fi] = executor.submit(render_worker, fi)
                
                audio_path = audio_future.result() if audio_future else None
                has_audio = audio_path is not None
                has_bgm = bool(self.config.bgm_path and os.path.exists(self.config.bgm_path))

                cmd = FFmpegCommandBuilder.build(self.w, self.h, self.fps, self.output, self.config, has_audio, has_bgm)

                si = subprocess.STARTUPINFO()
                if platform.system() == "Windows":
                    si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                    si.wShowWindow = subprocess.SW_HIDE
                
                with subprocess.Popen(cmd, stdin=subprocess.PIPE,
                                      stdout=subprocess.DEVNULL,
                                      stderr=subprocess.PIPE, startupinfo=si) as proc:
                    
                    thumb_pcts = [0.25, 0.50, 0.75] if self.config.yt_extras else []
                    thumb_idx = 0

                    for fi in range(n_frames):
                        if self._cancel.is_set(): break
                        
                        try:
                            img = futures[fi].result()
                        except Exception:
                            self.error.emit("Frame rendering failed.")
                            self._cancel.set()
                            break
                        finally:
                            del futures[fi]
                        
                        next_fi = fi + window_size
                        if next_fi < n_frames:
                            futures[next_fi] = executor.submit(render_worker, next_fi)
                        
                        if img is None:
                            self.error.emit("Frame rendering failed.")
                            self._cancel.set()
                            break
                            
                        try:
                            ptr = img.constBits()
                            ptr.setsize(img.sizeInBytes())
                            proc.stdin.write(memoryview(ptr))
                        except BrokenPipeError:
                            stderr_output = proc.stderr.read().decode('utf-8', errors='ignore') if proc.stderr else ""
                            self.error.emit(f"FFmpeg crashed:\n{stderr_output[:500]}")
                            self._cancel.set()
                            break
                        finally:
                            del img
                            
                        if thumb_idx < len(thumb_pcts) and fi == int(n_frames * thumb_pcts[thumb_idx]):
                            thumb_path = os.path.splitext(self.output)[0] + f"_thumb_{thumb_idx+1}.jpg"
                            self.bundle.render_frame(fi / self.fps,
                                QImage(self.w, self.h, QImage.Format.Format_RGB32)
                            ).save(thumb_path, "JPG", 95)
                            thumb_idx += 1
                            
                        if fi % 30 == 0:
                            self.progress.emit(int(fi / n_frames * 100))
                            self.status.emit(f"Rendering frame {fi}/{n_frames}...")

                if proc.stdin:
                    try: proc.stdin.close()
                    except Exception: pass
                if self._cancel.is_set():
                    proc.kill()
                try:
                    proc.wait(timeout=30)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait()

            if not self._cancel.is_set() and os.path.exists(self.output):
                self.progress.emit(100)
                file_size = os.path.getsize(self.output)
                self.finished_ok.emit(self.output, file_size)
            else:
                self.error.emit("Cancelled")
        except Exception as e:
            logger.error(f"Export failed for {self.output}", exc_info=True)
            self.error.emit(str(e))
        finally:
            self.bundle = None
            self.command.bundle = None
            gc.collect()
            shutil.rmtree(tmp, ignore_errors=True)

# ============================================================================
# 10. MAIN WINDOW (UI & STATE)
# ============================================================================

class BatchTableWidget(QTableWidget):
    def __init__(self, rows: int = 0, columns: int = 0, parent: Optional[QWidget] = None):
        super().__init__(rows, columns, parent)
        self._checkbox_anchor: Optional[int] = None
        self.setAcceptDrops(True)

    def dragEnterEvent(self, e: Any) -> None:
        if e.mimeData().hasUrls(): e.acceptProposedAction()

    def dropEvent(self, e: Any) -> None:
        urls = e.mimeData().urls()
        paths = []
        for u in urls:
            p = u.toLocalFile()
            if os.path.isfile(p) and os.path.splitext(p)[1].lower() in SUPPORTED_EXTENSIONS:
                paths.append(p)
            elif os.path.isdir(p):
                for dirpath, _, fnames in os.walk(p):
                    for fn in fnames:
                        if os.path.splitext(fn)[1].lower() in SUPPORTED_EXTENSIONS:
                            paths.append(os.path.join(dirpath, fn))
        if paths and self.window(): self.window()._add_paths(paths)
        e.acceptProposedAction()

    def mousePressEvent(self, event: Any) -> None:
        if event.button() != Qt.MouseButton.LeftButton:
            super().mousePressEvent(event); return
        pos = event.position().toPoint() if hasattr(event, 'position') else event.pos()
        item = self.itemAt(pos)
        if not item:
            super().mousePressEvent(event); return
        row = item.row()
        chk_item = self.item(row, 0)
        if chk_item is None:
            super().mousePressEvent(event); return
        new_state = (chk_item.checkState() == Qt.CheckState.Unchecked)
        modifiers = QApplication.keyboardModifiers()
        if (modifiers & Qt.KeyboardModifier.ShiftModifier) and self._checkbox_anchor is not None and self._checkbox_anchor != row:
            anchor = self._checkbox_anchor
            lo, hi = min(anchor, row), max(anchor, row)
            self.blockSignals(True)
            for i in range(lo, hi + 1):
                ci = self.item(i, 0)
                if ci is not None: ci.setCheckState(Qt.CheckState.Checked if new_state else Qt.CheckState.Unchecked)
            self.blockSignals(False)
            self.itemChanged.emit(chk_item)
        else:
            if item.column() != 0:
                chk_item.setCheckState(Qt.CheckState.Checked if new_state else Qt.CheckState.Unchecked)
            self._checkbox_anchor = row
            self.itemChanged.emit(chk_item)
        if item.column() != 0: super().mousePressEvent(event)

class CodeEditorStrategy:
    def get_code(self, config: StudioConfig, files: List[FileItem], custom_code: str) -> Tuple[str, str, str]:
        if config.use_custom:
            code = convert_shortcodes(custom_code)
            return (code if code.strip() else "# Custom code empty", "python", "custom_code.py")
        checked = [f for f in files if f.checked]
        if not checked:
            return ("import numpy as np\n\ndef hello():\n    print('Add files to begin!')", "python", "preview.py")
        it = checked[0]
        return (read_text_file(it.path), EXT_TO_LANGUAGE.get(os.path.splitext(it.path)[1].lower(), "text"), os.path.basename(it.path))

    def build(self, config: StudioConfig, files: List[FileItem], custom_code: str) -> Optional[PaneBundle]:
        w, h = RESOLUTIONS.get(config.resolution, (1920, 1080))
        code, lang, title = self.get_code(config, files, custom_code)

        wpm = config.wpm
        if config.auto_shorts:
            test_anim = TypingAnimator(code, TypingProfile(wpm=wpm))
            if test_anim.duration() > 180:
                wpm = TypingAnimator.find_wpm_for_target(code, 179.0, 0.5, 1.5)

        animator = TypingAnimator(code, TypingProfile(wpm=wpm, typo_rate=config.typo_rate))

        kb_h = 0
        kb = None
        if config.kb_enabled:
            kb = KeyboardOverlay(w, h, config.kb_layout, THEMES.get(config.theme, THEMES["Dracula"]),
                                 config.kb_opacity, config.kb_position.lower().replace(" ", "_"))
            kb_h = kb.height_needed()

        fsz = config.font_size
        if config.font_size_auto:
            fsz = CodeRenderer.auto_font_size(
                code.count("\n") + 1, w, h, text=code,
                font_family=config.font_family, keyboard_h=kb_h,
                show_chrome=config.show_window_chrome, show_ln=config.show_line_numbers,
            )

        config_copy = copy.deepcopy(config)
        config_copy.font_size = fsz
        renderer = CodeRenderer(w, h, config_copy, code, title, lang, kb_overlay=kb)
        title_text = config.window_title if config.window_title else title
        return PaneBundle(renderer, animator, title_text, config_copy)

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Typing Video Studio — Code Editor Mode (Expert)")
        self.resize(1400, 900)
        self.setAcceptDrops(True)

        self.config = StudioConfig()
        self.strategy = CodeEditorStrategy()
        self.export_commands: deque[ExportCommand] = deque()
        self.current_command: Optional[ExportCommand] = None
        self._items: List[FileItem] = []
        self._item_paths: set = set()
        self._exporter: Optional[VideoExporter] = None
        self._batch_cancelled = False
        self.batch_total = 0; self.batch_done = 0; self.batch_start_time = 0
        self.batch_total_size = 0
        self.completed_times: List[float] = []

        self._prep_executor = ThreadPoolExecutor(max_workers=1)

        self._preview_animating = False
        self._preview_anim_t = 0.0
        self._preview_progress = 0.3
        
        # Real-time sync clocks
        self._timer_start_time: float = 0.0
        self._timer_start_anim_t: float = 0.0
        
        self._debounce_timer = QTimer(self)
        self._debounce_timer.setSingleShot(True)
        self._debounce_timer.setInterval(200)
        self._debounce_timer.timeout.connect(self._invalidate_preview)
        self._preview_timer = QTimer(self)
        self._preview_timer.setInterval(16) # ~60fps UI refresh
        self._preview_timer.timeout.connect(self._advance_preview)
        self._cached_bundle: Optional[PaneBundle] = None
        self._preview_scratch: Optional[QImage] = None

        self._audio_player = QMediaPlayer()
        self._audio_out = QAudioOutput()
        self._audio_player.setAudioOutput(self._audio_out)
        self._audio_buf: Optional[QBuffer] = None

        self._build_ui()
        self._connect_signals()
        self._load_settings()
        self._load_recent()
        self._scan_dir(str(INPUT_DIR))
        QTimer.singleShot(500, self._update_preview)

    def _build_ui(self) -> None:
        root = QSplitter(Qt.Orientation.Horizontal)
        self.setCentralWidget(root)

        left = QWidget(); left.setMinimumWidth(320)
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(0, 0, 0, 0); left_layout.setSpacing(0)

        header = QFrame(); header.setFixedHeight(40)
        header.setStyleSheet("QFrame { background: #1e1e2e; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header); hl.setContentsMargins(12, 0, 8, 0)
        hdr_lbl = QLabel("📂 FILE BATCH & SETTINGS")
        hdr_lbl.setStyleSheet("font-weight: bold; color: #cdd6f4;")
        hl.addWidget(hdr_lbl); hl.addStretch()
        left_layout.addWidget(header)

        left_splitter = QSplitter(Qt.Orientation.Vertical)
        left_splitter.setHandleWidth(6)
        left_layout.addWidget(left_splitter, 1)

        file_widget = QWidget()
        fl = QVBoxLayout(file_widget); fl.setContentsMargins(8, 8, 8, 8); fl.setSpacing(8)

        br1 = QHBoxLayout(); br1.setContentsMargins(0, 0, 0, 0)
        self.scan_btn = QPushButton("🔄 Scan"); self.scan_btn.clicked.connect(lambda: self._scan_dir(str(INPUT_DIR)))
        self.add_btn = QPushButton("➕ Add"); self.add_btn.clicked.connect(self._add_files)
        self.clear_btn = QPushButton("✖ Clear"); self.clear_btn.clicked.connect(self._clear_list)
        br1.addWidget(self.scan_btn); br1.addWidget(self.add_btn); br1.addWidget(self.clear_btn)
        br1.addStretch()
        self.recursive_chk = QCheckBox("Sub"); self.recursive_chk.setChecked(True)
        br1.addWidget(self.recursive_chk)
        br1.addWidget(QLabel("Depth:"))
        self.depth_sp = QSpinBox(); self.depth_sp.setRange(1, 99); self.depth_sp.setValue(10)
        self.depth_sp.setFixedWidth(50); br1.addWidget(self.depth_sp)
        fl.addLayout(br1)

        sel_row = QHBoxLayout(); sel_row.setContentsMargins(0, 0, 0, 0)
        self.select_all_btn = QPushButton("☑ All"); self.select_all_btn.clicked.connect(self._select_all)
        self.deselect_all_btn = QPushButton("☐ None"); self.deselect_all_btn.clicked.connect(self._deselect_all)
        self.retry_btn = QPushButton("🔁 Retry Failed"); self.retry_btn.clicked.connect(self._retry_failed)
        self.clear_done_btn = QPushButton("🧹 Clear Done"); self.clear_done_btn.clicked.connect(self._clear_done)
        
        sel_row.addWidget(self.select_all_btn); sel_row.addWidget(self.deselect_all_btn)
        sel_row.addWidget(self.retry_btn); sel_row.addWidget(self.clear_done_btn)
        sel_row.addStretch()
        self._sel_count_lbl = QLabel("0 selected")
        self._sel_count_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        sel_row.addWidget(self._sel_count_lbl)
        fl.addLayout(sel_row)

        self.table = BatchTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["", "File", "Size", "Status"])
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        self.table.verticalHeader().setVisible(False)
        self.table.itemChanged.connect(self._on_item_changed)
        self.table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._on_table_context_menu)
        hdr = self.table.horizontalHeader()
        hdr.setSectionResizeMode(0, QHeaderView.ResizeMode.Fixed); hdr.resizeSection(0, 36)
        hdr.setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        hdr.setSectionResizeMode(2, QHeaderView.ResizeMode.Fixed); hdr.resizeSection(2, 70)
        hdr.setSectionResizeMode(3, QHeaderView.ResizeMode.Fixed); hdr.resizeSection(3, 100)
        fl.addWidget(self.table)
        left_splitter.addWidget(file_widget)

        self.common_tabs = QTabWidget(); self.common_tabs.setDocumentMode(True)

        v_tab_content = QWidget()
        vfl = QFormLayout(v_tab_content); vfl.setSpacing(6)
        vfl.setContentsMargins(8, 8, 8, 8)
        vfl.setFormAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.theme_cb = QComboBox(); self.theme_cb.addItems(list(THEMES.keys()))
        vfl.addRow("Theme:", self.theme_cb)
        self.res_cb = QComboBox(); self.res_cb.addItems(list(RESOLUTIONS.keys()))
        vfl.addRow("Resolution:", self.res_cb)
        self.fps_sp = QSpinBox(); self.fps_sp.setRange(30, 60)
        self.fps_sp.setSingleStep(30); self.fps_sp.setValue(30)
        vfl.addRow("FPS:", self.fps_sp)
        self.encoder_cb = QComboBox(); self.encoder_cb.addItems(list(EncoderType))
        vfl.addRow("Encoder:", self.encoder_cb)
        self.yt_extras_chk = QCheckBox("Generate YT Thumbnails")
        self.yt_extras_chk.setChecked(True); vfl.addRow(self.yt_extras_chk)
        self.output_template_edit = QLineEdit(); self.output_template_edit.setText("{name}_{date}")
        self.output_template_edit.setToolTip("Placeholders: {name}, {date}, {lang}")
        vfl.addRow("Output Name:", self.output_template_edit)

        qt_row = QHBoxLayout(); qt_row.setContentsMargins(0, 0, 0, 0)
        for txt, secs in [("30s", 30), ("1m", 60), ("2m", 120), ("3m", 180), ("5m", 300)]:
            btn = QPushButton(txt); btn.setFixedWidth(40)
            btn.clicked.connect(lambda checked=False, s=secs: self._apply_target_duration(s))
            qt_row.addWidget(btn)
        qt_row.addStretch()
        vfl.addRow("Quick Target:", qt_row)
        dur_row = QHBoxLayout(); dur_row.setContentsMargins(0, 0, 0, 0)
        self.target_dur_sp = QSpinBox(); self.target_dur_sp.setRange(5, 7200)
        self.target_dur_sp.setValue(60); self.target_dur_sp.setSuffix("s")
        self.target_dur_lbl = QLabel("0h 1m 0s")
        self.target_dur_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-family: monospace;")
        self.target_dur_lbl.setMinimumWidth(70)
        def update_dur_label(secs: int) -> None:
            h, m, s = secs // 3600, (secs % 3600) // 60, secs % 60
            self.target_dur_lbl.setText(f"{h}h {m}m {s}s")
        self.target_dur_sp.valueChanged.connect(update_dur_label)
        update_dur_label(self.target_dur_sp.value())
        dur_apply_btn = QPushButton("Set WPM")
        dur_apply_btn.clicked.connect(lambda: self._apply_target_duration(self.target_dur_sp.value()))
        dur_row.addWidget(self.target_dur_sp, 1)
        dur_row.addWidget(self.target_dur_lbl); dur_row.addWidget(dur_apply_btn)
        vfl.addRow("Target Dur:", dur_row)

        v_tab = QScrollArea(); v_tab.setWidgetResizable(True); v_tab.setWidget(v_tab_content)
        v_tab.setFrameShape(QFrame.Shape.NoFrame)
        self.common_tabs.addTab(v_tab, "Video")

        a_tab_content = QWidget()
        afl = QFormLayout(a_tab_content); afl.setSpacing(6)
        afl.setContentsMargins(8, 8, 8, 8)
        afl.setFormAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.sound_chk = QCheckBox("Enable Audio"); self.sound_chk.setChecked(True)
        afl.addRow(self.sound_chk)
        self.preset_cb = QComboBox(); self.preset_cb.addItems(list(MODULAR_SOUND_PRESETS.keys()))
        afl.addRow("Preset:", self.preset_cb)
        self.stereo_chk = QCheckBox("Binaural ASMR"); afl.addRow(self.stereo_chk)
        self.vol_sp = QSpinBox(); self.vol_sp.setRange(0, 100); self.vol_sp.setValue(60)
        self.vol_sp.setSuffix("%"); afl.addRow("Volume:", self.vol_sp)
        test_row = QHBoxLayout(); test_row.setContentsMargins(0, 0, 0, 0)
        self.test_sound_btn = QPushButton("🔊 Test Sound")
        self.test_sound_btn.setStyleSheet(
            "QPushButton { background: #89b4fa; color: #1e1e2e; font-weight: bold; border: none; border-radius: 4px; padding: 6px; }")
        self.test_sound_btn.clicked.connect(self._test_sound)
        test_row.addWidget(self.test_sound_btn)
        afl.addRow("Preview:", test_row)
        bgm_row = QHBoxLayout(); bgm_row.setContentsMargins(0, 0, 0, 0)
        self.bgm_edit = QLineEdit(); self.bgm_edit.setPlaceholderText("BGM MP3 path")
        bgm_btn = QPushButton("..."); bgm_btn.setFixedWidth(30)
        bgm_btn.clicked.connect(self._browse_bgm)
        bgm_row.addWidget(self.bgm_edit); bgm_row.addWidget(bgm_btn)
        afl.addRow("BGM:", bgm_row)
        self.bgm_vol_sp = QSpinBox(); self.bgm_vol_sp.setRange(0, 100); self.bgm_vol_sp.setValue(25)
        self.bgm_vol_sp.setSuffix("%"); afl.addRow("BGM Vol:", self.bgm_vol_sp)
        self.bgm_duck_chk = QCheckBox("Sidechain Ducking"); self.bgm_duck_chk.setChecked(True)
        afl.addRow(self.bgm_duck_chk)
        a_tab = QScrollArea(); a_tab.setWidgetResizable(True); a_tab.setWidget(a_tab_content)
        a_tab.setFrameShape(QFrame.Shape.NoFrame)
        self.common_tabs.addTab(a_tab, "Audio")

        e_tab_content = QWidget()
        efl = QFormLayout(e_tab_content); efl.setSpacing(6)
        efl.setContentsMargins(8, 8, 8, 8)
        efl.setFormAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.font_cb = QComboBox(); self.font_cb.addItems(FONT_FAMILIES)
        efl.addRow("Font:", self.font_cb)
        fs_row = QHBoxLayout(); fs_row.setContentsMargins(0, 0, 0, 0)
        self.font_sz_auto = QCheckBox("Auto"); fs_row.addWidget(self.font_sz_auto)
        self.font_sz_sp = QSpinBox(); self.font_sz_sp.setRange(8, 72); self.font_sz_sp.setValue(22)
        self.font_sz_sp.setEnabled(False); fs_row.addWidget(self.font_sz_sp)
        self.font_sz_auto.toggled.connect(self.font_sz_sp.setEnabled)
        efl.addRow("Size:", fs_row)
        self.cursor_style_cb = QComboBox(); self.cursor_style_cb.addItems(list(CursorStyle))
        efl.addRow("Cursor:", self.cursor_style_cb)
        self.tab_size_sp = QSpinBox(); self.tab_size_sp.setRange(1, 8); self.tab_size_sp.setValue(4)
        efl.addRow("Tab Size:", self.tab_size_sp)
        self.show_ln_chk = QCheckBox("Line Numbers"); self.show_ln_chk.setChecked(True)
        efl.addRow(self.show_ln_chk)
        self.show_chrome_chk = QCheckBox("Window Chrome"); self.show_chrome_chk.setChecked(True)
        efl.addRow(self.show_chrome_chk)
        self.smooth_scroll_chk = QCheckBox("Smooth Scroll"); self.smooth_scroll_chk.setChecked(True)
        efl.addRow(self.smooth_scroll_chk)
        self.wpm_sp = QSpinBox(); self.wpm_sp.setRange(30, 300); self.wpm_sp.setValue(100)
        efl.addRow("WPM:", self.wpm_sp)
        self.typo_sp = QDoubleSpinBox(); self.typo_sp.setRange(0.0, 0.2)
        self.typo_sp.setSingleStep(0.01); efl.addRow("Typo Rate:", self.typo_sp)
        self.auto_shorts_chk = QCheckBox("Auto-adjust for Shorts (<3 min)")
        efl.addRow(self.auto_shorts_chk)
        self.zoom_chk = QCheckBox("Cinematic Ken Burns Zoom"); efl.addRow(self.zoom_chk)
        self.focus_chk = QCheckBox("Code Block Focus (Dimming)"); efl.addRow(self.focus_chk)
        self.intro_chk = QCheckBox("Intro Title Card"); self.intro_chk.setChecked(True)
        efl.addRow(self.intro_chk)
        self.intro_dur_sp = QDoubleSpinBox(); self.intro_dur_sp.setRange(0.5, 10.0)
        self.intro_dur_sp.setValue(2.5); self.intro_dur_sp.setSingleStep(0.5)
        self.intro_dur_sp.setSuffix("s"); efl.addRow("Intro Dur:", self.intro_dur_sp)
        self.outro_chk = QCheckBox("Outro Title Card"); self.outro_chk.setChecked=True
        efl.addRow(self.outro_chk)
        self.outro_dur_sp = QDoubleSpinBox(); self.outro_dur_sp.setRange(0.5, 10.0)
        self.outro_dur_sp.setValue(2.5); self.outro_dur_sp.setSingleStep(0.5)
        self.outro_dur_sp.setSuffix("s"); efl.addRow("Outro Dur:", self.outro_dur_sp)
        self.progress_overlay_chk = QCheckBox("Progress Bar Overlay")
        efl.addRow(self.progress_overlay_chk)
        self.watermark_edit = QLineEdit(); self.watermark_edit.setPlaceholderText("Watermark text")
        efl.addRow("Watermark:", self.watermark_edit)
        self.window_title_edit = QLineEdit(); self.window_title_edit.setPlaceholderText("Auto from filename")
        efl.addRow("Custom Title:", self.window_title_edit)
        e_tab = QScrollArea(); e_tab.setWidgetResizable(True); e_tab.setWidget(e_tab_content)
        e_tab.setFrameShape(QFrame.Shape.NoFrame)
        self.common_tabs.addTab(e_tab, "Editor")

        k_tab_content = QWidget()
        kfl = QFormLayout(k_tab_content); kfl.setSpacing(6)
        kfl.setContentsMargins(8, 8, 8, 8)
        kfl.setFormAlignment(Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignLeft)
        self.kb_enabled_chk = QCheckBox("Show Keyboard Overlay")
        kfl.addRow(self.kb_enabled_chk)
        self.kb_layout_cb = QComboBox(); self.kb_layout_cb.addItems(list(KEYBOARD_LAYOUTS.keys()))
        kfl.addRow("KB Layout:", self.kb_layout_cb)
        self.kb_position_cb = QComboBox()
        self.kb_position_cb.addItems(["Bottom Center", "Bottom Right", "Bottom Left",
                                       "Top Center", "Top Right", "Top Left"])
        kfl.addRow("KB Position:", self.kb_position_cb)
        self.kb_opacity_sp = QDoubleSpinBox(); self.kb_opacity_sp.setRange(0.1, 1.0)
        self.kb_opacity_sp.setSingleStep(0.05); self.kb_opacity_sp.setValue(0.82)
        kfl.addRow("KB Opacity:", self.kb_opacity_sp)
        k_tab = QScrollArea(); k_tab.setWidgetResizable(True); k_tab.setWidget(k_tab_content)
        k_tab.setFrameShape(QFrame.Shape.NoFrame)
        self.common_tabs.addTab(k_tab, "Keyboard")

        c_tab_content = QWidget()
        cvl = QVBoxLayout(c_tab_content); cvl.setSpacing(6)
        cvl.setContentsMargins(8, 8, 8, 8)
        self.use_custom_chk = QCheckBox("Use Custom Code (ignores file list)")
        cvl.addWidget(self.use_custom_chk)
        self.custom_editor = QPlainTextEdit()
        self.custom_editor.setPlaceholderText("Type or paste code here. Shortcodes: :rocket: -> 🚀")
        cvl.addWidget(self.custom_editor)
        c_tab = QScrollArea(); c_tab.setWidgetResizable(True); c_tab.setWidget(c_tab_content)
        c_tab.setFrameShape(QFrame.Shape.NoFrame)
        self.common_tabs.addTab(c_tab, "Custom")

        left_splitter.addWidget(self.common_tabs)
        left_splitter.setSizes([250, 450])
        left_splitter.setStretchFactor(0, 0); left_splitter.setStretchFactor(1, 1)

        bottom_bar = QVBoxLayout(); bottom_bar.setContentsMargins(8, 4, 8, 8); bottom_bar.setSpacing(4)
        
        self.batch_prog_lbl = QLabel("Overall Batch: 0%")
        self.batch_prog_lbl.setStyleSheet("color: #a6adc8; font-size: 10px; font-weight: bold;")
        bottom_bar.addWidget(self.batch_prog_lbl)
        self.batch_progress_bar = QProgressBar(); self.batch_progress_bar.setVisible(False)
        self.batch_progress_bar.setFormat("%v / %m  (%p%)")
        bottom_bar.addWidget(self.batch_progress_bar)

        self.file_prog_lbl = QLabel("Current File: Idle")
        self.file_prog_lbl.setStyleSheet("color: #a6adc8; font-size: 10px;")
        bottom_bar.addWidget(self.file_prog_lbl)
        self.file_progress_bar = QProgressBar(); self.file_progress_bar.setVisible(False)
        self.file_progress_bar.setFormat("%p%")
        bottom_bar.addWidget(self.file_progress_bar)

        br2 = QHBoxLayout(); br2.setContentsMargins(0, 0, 0, 0)
        self.export_btn = QPushButton("🎬 Export")
        self.export_btn.setStyleSheet(
            "QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 8px; }")
        self.export_btn.clicked.connect(self._start_export)
        br2.addWidget(self.export_btn, 1)
        self.skip_btn = QPushButton("⏭ Skip"); self.skip_btn.setFixedWidth(60)
        self.skip_btn.setEnabled(False); self.skip_btn.clicked.connect(self._skip_current)
        br2.addWidget(self.skip_btn)
        self.cancel_btn = QPushButton("✖"); self.cancel_btn.setFixedWidth(36)
        self.cancel_btn.setEnabled(False); self.cancel_btn.clicked.connect(self._cancel_export)
        br2.addWidget(self.cancel_btn)
        bottom_bar.addLayout(br2)
        
        br3 = QHBoxLayout(); br3.setContentsMargins(0, 0, 0, 0)
        self.save_proj_btn = QPushButton("💾 Save"); self.save_proj_btn.clicked.connect(self._save_project)
        br3.addWidget(self.save_proj_btn)
        self.load_proj_btn = QPushButton("📂 Load"); self.load_proj_btn.clicked.connect(self._load_project)
        br3.addWidget(self.load_proj_btn)
        bottom_bar.addLayout(br3)
        
        info_row = QHBoxLayout(); info_row.setContentsMargins(0, 0, 0, 0)
        self.batch_info_lbl = QLabel("Ready to export.")
        self.batch_info_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-weight: bold;")
        info_row.addWidget(self.batch_info_lbl, 1)
        self.shutdown_chk = QCheckBox("Shutdown PC when done")
        self.shutdown_chk.setStyleSheet("color: #a6adc8; font-size: 11px;")
        info_row.addWidget(self.shutdown_chk)
        bottom_bar.addLayout(info_row)
        
        left_layout.addLayout(bottom_bar)
        root.addWidget(left)

        preview_widget = QWidget()
        p_layout = QVBoxLayout(preview_widget); p_layout.setContentsMargins(8, 8, 8, 8); p_layout.setSpacing(8)
        self.preview_lbl = QLabel(); self.preview_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_lbl.setStyleSheet("background: #11111b; border-radius: 8px;")
        self.preview_lbl.setMinimumSize(640, 360)
        self.preview_lbl.setAcceptDrops(True)
        p_layout.addWidget(self.preview_lbl, 1)
        
        stats_row = QHBoxLayout(); stats_row.setContentsMargins(0, 0, 0, 0)
        self.stats_lbl = QLabel("Render: 0ms | WPM: 0 | Chars: 0/0")
        self.stats_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-family: monospace;")
        stats_row.addWidget(self.stats_lbl); stats_row.addStretch()
        self.g_pad_chk = QCheckBox("Pad"); self.g_pad_chk.toggled.connect(self._debounce_timer.start)
        self.g_chrome_chk = QCheckBox("Chrome"); self.g_chrome_chk.toggled.connect(self._debounce_timer.start)
        self.g_code_chk = QCheckBox("Code"); self.g_code_chk.toggled.connect(self._debounce_timer.start)
        stats_row.addWidget(self.g_pad_chk); stats_row.addWidget(self.g_chrome_chk); stats_row.addWidget(self.g_code_chk)
        p_layout.addLayout(stats_row)
        
        ctrls = QHBoxLayout(); ctrls.setContentsMargins(0, 0, 0, 0)
        
        # Added Restart Button
        self.restart_btn = QPushButton("⏮"); self.restart_btn.setFixedWidth(40)
        self.restart_btn.setToolTip("Restart Preview")
        self.restart_btn.clicked.connect(self._restart_preview)
        ctrls.addWidget(self.restart_btn)
        
        self.prev_btn = QPushButton("◀"); self.prev_btn.setFixedWidth(40)
        self.prev_btn.setToolTip("Previous Frame")
        self.prev_btn.clicked.connect(lambda: self._step_frame(-1)); ctrls.addWidget(self.prev_btn)
        
        self.play_btn = QPushButton("▶ Animate"); self.play_btn.setFixedWidth(110)
        self.play_btn.setStyleSheet(
            "QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 6px; }")
        self.play_btn.clicked.connect(lambda: self._toggle_preview())
        ctrls.addWidget(self.play_btn)
        
        self.next_btn = QPushButton("▶"); self.next_btn.setFixedWidth(40)
        self.next_btn.setToolTip("Next Frame")
        self.next_btn.clicked.connect(lambda: self._step_frame(1)); ctrls.addWidget(self.next_btn)
        
        # Added Loop Checkbox
        self.loop_chk = QCheckBox("🔄 Loop")
        self.loop_chk.setStyleSheet("color: #a6e3a1; font-size: 11px;")
        ctrls.addWidget(self.loop_chk)
        
        self.slider = QSlider(Qt.Orientation.Horizontal); self.slider.setRange(0, 1000)
        ctrls.addWidget(self.slider, 1)
        
        self.time_lbl = QLabel("0:00.00 / 0:00.00")
        self.time_lbl.setStyleSheet("color: #a6e3a1; font-family: monospace;")
        self.time_lbl.setMinimumWidth(130)
        ctrls.addWidget(self.time_lbl)
        
        p_layout.addLayout(ctrls)
        root.addWidget(preview_widget)
        root.setSizes([400, 1000])
        root.setStretchFactor(0, 0); root.setStretchFactor(1, 1)

    def _connect_signals(self) -> None:
        def upd(key: str, value: Any) -> None:
            setattr(self.config, key, value)
            self._debounce_timer.start()
        self.theme_cb.currentTextChanged.connect(lambda v: upd('theme', v))
        self.res_cb.currentTextChanged.connect(lambda v: upd('resolution', v))
        self.fps_sp.valueChanged.connect(lambda v: upd('fps', v))
        self.encoder_cb.currentTextChanged.connect(lambda v: upd('encoder', v))
        self.yt_extras_chk.toggled.connect(lambda v: upd('yt_extras', v))
        self.output_template_edit.textChanged.connect(lambda v: upd('output_template', v))
        self.sound_chk.toggled.connect(lambda v: upd('sound_enabled', v))
        self.preset_cb.currentTextChanged.connect(lambda v: upd('sound_preset', v))
        self.stereo_chk.toggled.connect(lambda v: upd('stereo', v))
        self.vol_sp.valueChanged.connect(lambda v: upd('volume', v))
        self.bgm_edit.textChanged.connect(lambda v: upd('bgm_path', v))
        self.bgm_vol_sp.valueChanged.connect(lambda v: upd('bgm_volume', v))
        self.bgm_duck_chk.toggled.connect(lambda v: upd('bgm_duck', v))
        self.kb_enabled_chk.toggled.connect(lambda v: upd('kb_enabled', v))
        self.kb_layout_cb.currentTextChanged.connect(lambda v: upd('kb_layout', v))
        self.kb_position_cb.currentTextChanged.connect(lambda v: upd('kb_position', v))
        self.kb_opacity_sp.valueChanged.connect(lambda v: upd('kb_opacity', v))
        self.font_cb.currentTextChanged.connect(lambda v: upd('font_family', v))
        self.font_sz_auto.toggled.connect(lambda v: upd('font_size_auto', v))
        self.font_sz_sp.valueChanged.connect(lambda v: upd('font_size', v))
        self.cursor_style_cb.currentTextChanged.connect(lambda v: upd('cursor_style', v))
        self.tab_size_sp.valueChanged.connect(lambda v: upd('tab_size', v))
        self.show_ln_chk.toggled.connect(lambda v: upd('show_line_numbers', v))
        self.show_chrome_chk.toggled.connect(lambda v: upd('show_window_chrome', v))
        self.smooth_scroll_chk.toggled.connect(lambda v: upd('smooth_scroll', v))
        self.wpm_sp.valueChanged.connect(lambda v: upd('wpm', v))
        self.typo_sp.valueChanged.connect(lambda v: upd('typo_rate', v))
        self.auto_shorts_chk.toggled.connect(lambda v: upd('auto_shorts', v))
        self.zoom_chk.toggled.connect(lambda v: upd('cinematic_zoom', v))
        self.focus_chk.toggled.connect(lambda v: upd('focus_dimming', v))
        self.intro_chk.toggled.connect(lambda v: upd('intro_card', v))
        self.intro_dur_sp.valueChanged.connect(lambda v: upd('intro_duration', v))
        self.outro_chk.toggled.connect(lambda v: upd('outro_card', v))
        self.outro_dur_sp.valueChanged.connect(lambda v: upd('outro_duration', v))
        self.progress_overlay_chk.toggled.connect(lambda v: upd('progress_bar_overlay', v))
        self.watermark_edit.textChanged.connect(lambda v: upd('watermark_text', v))
        self.window_title_edit.textChanged.connect(lambda v: upd('window_title', v))
        self.use_custom_chk.toggled.connect(lambda v: upd('use_custom', v))
        self.custom_editor.textChanged.connect(lambda: upd('custom_code', self.custom_editor.toPlainText()))
        self.recursive_chk.toggled.connect(lambda v: upd('recursive_scan', v))
        self.depth_sp.valueChanged.connect(lambda v: upd('scan_depth', v))
        self.slider.valueChanged.connect(self._on_slider_changed)

    def _scan_dir(self, path: str) -> None:
        self._items.clear(); self._item_paths.clear()
        if not os.path.isdir(path): return
        max_depth = self.config.scan_depth if self.config.recursive_scan else 1
        skip_dirs = {".git", ".hg", ".svn", "__pycache__", "node_modules",
                     ".venv", "venv", ".env", ".idea", ".vscode", "dist",
                     "build", ".tox", ".mypy_cache", ".pytest_cache"}
        found = []
        for dirpath, dirnames, filenames in os.walk(path):
            rel = os.path.relpath(dirpath, path)
            depth = 1 if rel == "." else rel.count(os.sep) + 2
            if depth > max_depth: dirnames.clear(); continue
            dirnames[:] = [d for d in dirnames if d not in skip_dirs and not d.startswith(".")]
            for fname in sorted(filenames):
                ext = os.path.splitext(fname)[1].lower()
                if ext in SUPPORTED_EXTENSIONS:
                    p = os.path.join(dirpath, fname)
                    try:
                        sz = os.path.getsize(p) / (1024*1024)
                    except:
                        sz = 0.0
                    found.append(FileItem(path=p, checked=True, size_mb=sz))
        self._items = found
        self._item_paths = {it.path for it in found}
        self._refresh_table()
        self._update_sel_count()

    def _add_files(self) -> None:
        paths, _ = QFileDialog.getOpenFileNames(
            self, "Select Files", "",
            "All Supported Files (*.py *.js *.ts *.txt *.md *.json *.go *.rs *.java *.cpp *.c *.h *.cs *.rb *.php *.sh *.sql *.html *.css *.yaml *.yml *.toml *.ini *.lua *.dart *.r *.m);;All Files (*)"
        )
        self._add_paths(paths)

    def _add_paths(self, paths: List[str]) -> None:
        for p in paths:
            if p not in self._item_paths:
                try:
                    sz = os.path.getsize(p) / (1024*1024)
                except:
                    sz = 0.0
                item = FileItem(path=p, checked=True, size_mb=sz)
                self._items.append(item); self._item_paths.add(p)
                self._add_to_recent(p)
        self._refresh_table()
        self._update_sel_count()
        self._debounce_timer.start()

    def _clear_list(self) -> None:
        self._items.clear(); self._item_paths.clear()
        self._refresh_table(); self._update_sel_count()
        self._invalidate_preview()

    def _select_all(self) -> None:
        for it in self._items: it.checked = True
        self._refresh_table(); self._update_sel_count(); self._debounce_timer.start()

    def _deselect_all(self) -> None:
        for it in self._items: it.checked = False
        self._refresh_table(); self._update_sel_count(); self._debounce_timer.start()

    def _update_sel_count(self) -> None:
        count = sum(1 for it in self._items if it.checked)
        total = len(self._items)
        self._sel_count_lbl.setText(f"{count}/{total} selected")

    def _refresh_table(self) -> None:
        self.table.blockSignals(True)
        self.table.setRowCount(len(self._items))
        for i, item in enumerate(self._items):
            chk = QTableWidgetItem()
            chk.setFlags(Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsEnabled)
            chk.setCheckState(Qt.CheckState.Checked if item.checked else Qt.CheckState.Unchecked)
            self.table.setItem(i, 0, chk)
            
            fname_item = QTableWidgetItem(os.path.basename(item.path))
            fname_item.setToolTip(item.path)
            self.table.setItem(i, 1, fname_item)
            
            sz_item = QTableWidgetItem(f"{item.size_mb:.1f} MB")
            sz_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            self.table.setItem(i, 2, sz_item)
            
            status_item = QTableWidgetItem(item.status)
            status_item.setForeground(QColor(str(StatusColor[item.status.upper()] if item.status.upper() in StatusColor.__members__ else StatusColor.PENDING)))
            self.table.setItem(i, 3, status_item)
        self.table.blockSignals(False)

    def _on_item_changed(self, item: QTableWidgetItem) -> None:
        row = item.row()
        if item.column() == 0:
            self._items[row].checked = item.checkState() == Qt.CheckState.Checked
            self._update_sel_count(); self._debounce_timer.start()

    def _on_table_context_menu(self, pos: Any) -> None:
        item = self.table.itemAt(pos)
        if not item: return
        row = item.row()
        if row >= len(self._items): return
        menu = QMenu(self)
        export_action = menu.addAction("Export This File Only")
        menu.addSeparator()
        remove_action = menu.addAction("Remove from List")
        copy_action = menu.addAction("Copy File Path")
        action = menu.exec(self.table.viewport().mapToGlobal(pos))
        if action == export_action:
            for it in self._items: it.checked = False
            self._items[row].checked = True
            self._refresh_table(); self._update_sel_count()
            self._start_export()
        elif action == remove_action:
            self._item_paths.discard(self._items[row].path)
            del self._items[row]
            self._refresh_table(); self._update_sel_count()
        elif action == copy_action:
            QApplication.clipboard().setText(self._items[row].path)

    def _retry_failed(self) -> None:
        for it in self._items:
            if it.status in ("Failed", "Cancelled", "Skipped"):
                it.status = "Pending"
        self._refresh_table()

    def _clear_done(self) -> None:
        self._items = [it for it in self._items if it.status != "Done"]
        self._item_paths = {it.path for it in self._items}
        self._refresh_table(); self._update_sel_count()

    def _load_recent(self) -> None:
        self._recent: List[str] = []
        try:
            if RECENT_FILE.exists():
                with open(RECENT_FILE, "r", encoding="utf-8") as f:
                    self._recent = json.load(f)[:10]
        except Exception:
            self._recent = []

    def _add_to_recent(self, path: str) -> None:
        if path in self._recent: self._recent.remove(path)
        self._recent.insert(0, path)
        self._recent = self._recent[:10]
        try:
            with open(RECENT_FILE, "w", encoding="utf-8") as f:
                json.dump(self._recent, f, indent=2)
        except Exception:
            pass

    def _invalidate_preview(self) -> None:
        self._cached_bundle = None
        self._preview_scratch = None
        self._audio_player.stop()
        self._audio_buf = None
        self._update_preview()

    def _update_preview(self) -> None:
        if self._cached_bundle is None:
            self._cached_bundle = self.strategy.build(self.config, self._items, self.config.custom_code)
            if self._cached_bundle:
                self._preview_scratch = QImage(self._cached_bundle.frame_w, self._cached_bundle.frame_h,
                                                QImage.Format.Format_RGB32)
        if not self._cached_bundle: return
        t_start = _time.perf_counter()
        t = self._cached_bundle.duration() * self._preview_progress
        draw_guides = self.g_pad_chk.isChecked() or self.g_chrome_chk.isChecked() or self.g_code_chk.isChecked()
        img = self._cached_bundle.render_frame(t, self._preview_scratch, draw_guides=draw_guides)
        self.preview_lbl.setPixmap(QPixmap.fromImage(img).scaled(
            self.preview_lbl.size(), Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation))
        render_time = (_time.perf_counter() - t_start) * 1000
        dur = self._cached_bundle.duration()
        
        # High precision time format MM:SS.ms
        m, s = int(t // 60), t % 60
        dm, ds = int(dur // 60), dur % 60
        self.time_lbl.setText(f"{m:02d}:{s:05.2f} / {dm:02d}:{ds:05.2f}")
        
        total_chars = len(self._cached_bundle.animator.display_chars)
        visible_chars = self._cached_bundle.animator.visible_at(t)
        self.stats_lbl.setText(f"Render: {render_time:.1f}ms | WPM: {self.config.wpm} | Chars: {visible_chars}/{total_chars}")
        if not self._preview_animating:
            self.slider.blockSignals(True)
            self.slider.setValue(int(self._preview_progress * 1000))
            self.slider.blockSignals(False)

    def _on_slider_changed(self, val: int) -> None:
        self._preview_progress = val / 1000.0
        if self._cached_bundle:
            dur = self._cached_bundle.duration()
            self._preview_anim_t = self._preview_progress * dur
            
            # If playing, sync real-time clock
            if self._preview_animating:
                self._timer_start_time = _time.perf_counter()
                self._timer_start_anim_t = self._preview_anim_t
            
            # Sync audio if playing
            if self._audio_player.duration() > 0:
                self._audio_player.setPosition(int(self._preview_anim_t * 1000))
                
        self._update_preview()

    def _step_frame(self, direction: int) -> None:
        if not self._cached_bundle: return
        fps = self.config.fps
        dt = direction / fps
        dur = self._cached_bundle.duration()
        self._preview_anim_t = max(0, min(dur, self._preview_anim_t + dt))
        self._preview_progress = self._preview_anim_t / dur if dur > 0 else 0
        
        if self._preview_animating:
            self._timer_start_time = _time.perf_counter()
            self._timer_start_anim_t = self._preview_anim_t
            if self._audio_player.duration() > 0:
                self._audio_player.setPosition(int(self._preview_anim_t * 1000))
                
        self._update_preview()

    def _restart_preview(self) -> None:
        if not self._cached_bundle: return
        self._preview_anim_t = 0.0
        self._preview_progress = 0.0
        if self._preview_animating:
            self._timer_start_time = _time.perf_counter()
            self._timer_start_anim_t = 0.0
            if self._audio_player.duration() > 0:
                self._audio_player.setPosition(0)
                self._audio_player.play()
        self._update_preview()

    def _toggle_preview(self) -> None:
        if not self._cached_bundle: return
        if self._preview_animating:
            self._preview_animating = False
            self._preview_timer.stop()
            self._audio_player.pause()
            self.play_btn.setText("▶ Animate")
        else:
            self._preview_animating = True
            if self._preview_anim_t >= self._cached_bundle.duration():
                self._preview_anim_t = 0
            self.play_btn.setText("⏸ Pause")
            
            # Real-time sync setup
            self._timer_start_time = _time.perf_counter()
            self._timer_start_anim_t = self._preview_anim_t
            
            if self.config.sound_enabled:
                # Generate audio only if buffer is empty
                if self._audio_player.duration() <= 0:
                    self._generate_and_load_audio()
                
                if self._audio_player.duration() > 0:
                    self._audio_player.setPosition(int(self._preview_anim_t * 1000))
                    self._audio_player.play()
            self._preview_timer.start()

    def _generate_and_load_audio(self) -> None:
        try:
            sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo)
            pcm = sg.generate_pcm(self._cached_bundle.char_timestamps_all(),
                                  self.config.volume / 100.0)
            channels = 2 if sg.stereo else 1
            if len(pcm) > 0:
                buf = io.BytesIO()
                with wave.open(buf, "w") as wf:
                    wf.setnchannels(channels); wf.setsampwidth(2)
                    wf.setframerate(sg.sr); wf.writeframes(pcm.tobytes())
                self._audio_buf = QBuffer()
                self._audio_buf.setData(buf.getvalue())
                self._audio_buf.open(QIODevice.OpenModeFlag.ReadOnly)
                self._audio_out.setVolume(self.config.volume / 100.0)
                self._audio_player.setSourceDevice(self._audio_buf, QUrl())
        except Exception:
            logger.error("Failed to generate preview audio", exc_info=True)

    def _advance_preview(self) -> None:
        if not self._cached_bundle: return
        # Use real-time clock for accurate progression
        elapsed = _time.perf_counter() - self._timer_start_time
        self._preview_anim_t = self._timer_start_anim_t + elapsed
        
        dur = self._cached_bundle.duration()
        if self._preview_anim_t >= dur:
            if self.loop_chk.isChecked():
                self._preview_anim_t = 0
                self._timer_start_time = _time.perf_counter()
                self._timer_start_anim_t = 0
                if self._audio_player.duration() > 0:
                    self._audio_player.setPosition(0)
                    self._audio_player.play()
            else:
                self._preview_anim_t = dur
                self._toggle_preview() # This will pause and stop audio
                return
        
        self._preview_progress = self._preview_anim_t / dur if dur > 0 else 0
        self._update_preview()

    def _apply_target_duration(self, secs: int) -> None:
        code, _, _ = self.strategy.get_code(self.config, self._items, self.config.custom_code)
        wpm = TypingAnimator.find_wpm_for_target(code, secs, 0.5, 1.5)
        self.wpm_sp.setValue(wpm)
        self.statusBar().showMessage(f"Adjusted WPM to ~{wpm} for {secs}s target", 3000)

    def _browse_bgm(self) -> None:
        path, _ = QFileDialog.getOpenFileName(
            self, "Select Background Music", "", "Audio Files (*.mp3 *.wav *.m4a *.flac)")
        if path: self.bgm_edit.setText(path)

    def _test_sound(self) -> None:
        try:
            sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo)
            sample_text = "hello world 123"
            timestamps = []
            t = 0.0
            for ch in sample_text:
                timestamps.append((t, ch))
                t += 0.10 if ch == ' ' else 0.06
            pcm = sg.generate_pcm(timestamps, 1.0)
            if len(pcm) > 0:
                buf = io.BytesIO()
                with wave.open(buf, "w") as wf:
                    wf.setnchannels(2 if sg.stereo else 1)
                    wf.setsampwidth(2); wf.setframerate(sg.sr)
                    wf.writeframes(pcm.tobytes())
                self._audio_player.stop()
                self._audio_buf = QBuffer()
                self._audio_buf.setData(buf.getvalue())
                self._audio_buf.open(QIODevice.OpenModeFlag.ReadOnly)
                self._audio_out.setVolume(self.config.volume / 100.0)
                self._audio_player.setSourceDevice(self._audio_buf, QUrl())
                self._audio_player.play()
                self.statusBar().showMessage(
                    f"🔊 Testing: {self.config.sound_preset} | Vol: {self.config.volume}% | Stereo: {self.config.stereo}", 3000)
        except Exception as e:
            logger.error("Audio test failed", exc_info=True)
            self.statusBar().showMessage(f"Audio test failed: {e}", 3000)

    def _start_export(self) -> None:
        if self.config.use_custom:
            items = [FileItem(path="custom_code.py", checked=True)]
        else:
            items = [it for it in self._items if it.checked]
        if not items:
            QMessageBox.information(self, "Nothing selected",
                                    "Check files to export or enable Custom Code.")
            return
        
        for it in self._items:
            if it.checked: it.status = "Pending"
        self._refresh_table()
        
        self.export_commands.clear()
        self._batch_cancelled = False
        self.batch_done = 0
        self.batch_total_size = 0
        self.completed_times.clear()
        self.batch_start_time = _time.time()
        
        for item in items:
            base_name = os.path.splitext(os.path.basename(item.path))[0]
            date_str = datetime.now().strftime("%Y%m%d")
            lang = EXT_TO_LANGUAGE.get(os.path.splitext(item.path)[1].lower(), "text")
            out_name = self.config.output_template.format(name=base_name, date=date_str, lang=lang) + ".mp4"
            out_path = str(OUTPUT_DIR / out_name)
            cmd = ExportCommand(item=item, output_path=out_path, config=copy.deepcopy(self.config))
            cmd.status = "Pending"
            self.export_commands.append(cmd)
            
        self.batch_total = len(self.export_commands)
        self.batch_progress_bar.setVisible(True)
        self.batch_progress_bar.setRange(0, self.batch_total)
        self.batch_progress_bar.setValue(0)
        self.file_progress_bar.setVisible(True)
        self.file_progress_bar.setRange(0, 100)
        self.file_progress_bar.setValue(0)
        
        self.export_btn.setEnabled(False)
        self.skip_btn.setEnabled(True)
        self.cancel_btn.setEnabled(True)
        self.retry_btn.setEnabled=False
        self.clear_done_btn.setEnabled(False)
        
        self.batch_info_lbl.setText(f"Starting batch of {self.batch_total} videos...")
        self._process_export_queue()

    def _process_export_queue(self) -> None:
        if not self.export_commands:
            self._on_batch_finished()
            return
            
        self.current_command = self.export_commands.popleft()
        self.current_command.status = "Running"
        self.current_command.item.status = "Running"
        self._refresh_table()
        
        item_name = os.path.basename(self.current_command.output_path)
        self.file_prog_lbl.setText(f"Current File: {item_name}")
        self.statusBar().showMessage(f"Preparing {item_name}...")
        QApplication.processEvents()
        
        if self.export_commands:
            next_cmd = self.export_commands[0]
            self._prep_executor.submit(next_cmd.get_bundle, self.strategy)
            
        self._exporter = VideoExporter(self.current_command, self.strategy)
        self._exporter.progress.connect(self._on_export_progress)
        self._exporter.status.connect(lambda s: self.statusBar().showMessage(s))
        self._exporter.finished_ok.connect(self._on_item_done)
        self._exporter.error.connect(self._on_item_failed)
        self._exporter.start()

    def _on_export_progress(self, p: int) -> None:
        item_name = os.path.basename(self.current_command.output_path)
        self.statusBar().showMessage(f"Rendering {item_name}: {p}%")
        self.file_progress_bar.setValue(p)
        
        total_progress = self.batch_done + (p / 100.0)
        pct = int((total_progress / self.batch_total) * 100) if self.batch_total > 0 else 0
        self.batch_progress_bar.setValue(int(total_progress))
        self.batch_prog_lbl.setText(f"Overall Batch: {pct}%")
        
        elapsed = _time.time() - self.batch_start_time
        if total_progress > 0:
            eta = (elapsed / total_progress) * (self.batch_total - total_progress)
            eta_str = f"{int(eta // 60)}m {int(eta % 60)}s"
        else:
            eta_str = "..."
            
        size_str = f"{self.batch_total_size / 1024:.1f} GB" if self.batch_total_size > 0 else "0 MB"
        self.batch_info_lbl.setText(f"Item {self.batch_done + 1}/{self.batch_total} | ETA: {eta_str} | Total Size: {size_str}")

    def _on_item_done(self, path: str, file_size: int) -> None:
        self.current_command.item.status = "Done"
        self.current_command.item.size_mb = file_size / (1024*1024)
        self.batch_done += 1
        self.batch_total_size += file_size
        
        time_taken = _time.time() - self.batch_start_time
        self.completed_times.append(time_taken)
        
        self._refresh_table()
        self.batch_progress_bar.setValue(self.batch_done)
        
        self.current_command.bundle = None
        gc.collect()
        
        self._process_export_queue()

    def _on_item_failed(self, err: str) -> None:
        if self._batch_cancelled:
            self.current_command.item.status = "Cancelled"
            self._refresh_table()
            return
            
        self.current_command.item.status = "Skipped" if err == "Cancelled" else "Failed"
        self.batch_done += 1
        self._refresh_table()
        self.batch_progress_bar.setValue(self.batch_done)
        self.statusBar().showMessage(f"Item {os.path.basename(self.current_command.output_path)} {self.current_command.item.status}.", 2000)
        
        self.current_command.bundle = None
        gc.collect()
        
        self._process_export_queue()

    def _on_batch_finished(self) -> None:
        self.export_btn.setEnabled(True)
        self.skip_btn.setEnabled(False)
        self.cancel_btn.setEnabled(False)
        self.retry_btn.setEnabled(True)
        self.clear_done_btn.setEnabled(True)
        self.batch_progress_bar.setVisible(False)
        self.file_progress_bar.setVisible(False)
        self.batch_prog_lbl.setText("Overall Batch: Complete!")
        self.file_prog_lbl.setText("Current File: Idle")
        self.batch_info_lbl.setText("Batch complete!")
        QMessageBox.information(self, "Done", "Batch export complete!")
        if self.shutdown_chk.isChecked():
            self._perform_shutdown()

    def _skip_current(self) -> None:
        if self._exporter:
            self.statusBar().showMessage(f"Skipping {os.path.basename(self.current_command.output_path)}...")
            self._exporter.cancel()

    def _cancel_export(self) -> None:
        self._batch_cancelled = True
        if self._exporter: self._exporter.cancel()
        self.export_commands.clear()
        if self.current_command: self.current_command.item.status = "Cancelled"
        self._refresh_table()
        self.export_btn.setEnabled(True)
        self.skip_btn.setEnabled(False)
        self.cancel_btn.setEnabled(False)
        self.retry_btn.setEnabled(True)
        self.clear_done_btn.setEnabled(True)
        self.batch_progress_bar.setVisible(False)
        self.file_progress_bar.setVisible(False)
        self.batch_info_lbl.setText("Batch cancelled")
        self.statusBar().showMessage("Batch export cancelled", 3000)

    def _perform_shutdown(self) -> None:
        reply = QMessageBox.question(
            self, "Auto Action",
            "Batch export complete. Shutdown PC now?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No)
        if reply == QMessageBox.StandardButton.Yes:
            try:
                if platform.system() == "Windows":
                    subprocess.run(["shutdown", "/s", "/t", "30"])
                elif platform.system() == "Linux":
                    subprocess.run(["shutdown", "-h", "now"])
                elif platform.system() == "Darwin":
                    subprocess.run(["shutdown", "-h", "now"])
            except Exception:
                pass

    def _save_project(self) -> None:
        path, _ = QFileDialog.getSaveFileName(self, "Save Project", "", "Studio Project (*.studio)")
        if not path: return
        config_dict = self.config.__dict__.copy()
        with open(path, "w", encoding="utf-8") as f:
            json.dump(config_dict, f, indent=2)
        self.statusBar().showMessage("Project saved!", 3000)

    def _load_project(self) -> None:
        path, _ = QFileDialog.getOpenFileName(self, "Load Project", "", "Studio Project (*.studio)")
        if not path: return
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.config = StudioConfig(**data)
        except Exception:
            logger.error("Failed to load project file", exc_info=True)
            QMessageBox.warning(self, "Load Error", "Failed to load project. The file might be corrupted.")
            return
        
        self.theme_cb.setCurrentText(self.config.theme)
        self.res_cb.setCurrentText(self.config.resolution)
        self.fps_sp.setValue(self.config.fps)
        self.encoder_cb.setCurrentText(self.config.encoder)
        self.yt_extras_chk.setChecked(self.config.yt_extras)
        self.output_template_edit.setText(self.config.output_template)
        self.sound_chk.setChecked(self.config.sound_enabled)
        self.preset_cb.setCurrentText(self.config.sound_preset)
        self.stereo_chk.setChecked(self.config.stereo)
        self.vol_sp.setValue(self.config.volume)
        self.bgm_edit.setText(self.config.bgm_path)
        self.bgm_vol_sp.setValue(self.config.bgm_volume)
        self.bgm_duck_chk.setChecked(self.config.bgm_duck)
        self.kb_enabled_chk.setChecked(self.config.kb_enabled)
        self.kb_layout_cb.setCurrentText(self.config.kb_layout)
        self.kb_position_cb.setCurrentText(self.config.kb_position)
        self.kb_opacity_sp.setValue(self.config.kb_opacity)
        self.font_cb.setCurrentText(self.config.font_family)
        self.font_sz_auto.setChecked(self.config.font_size_auto)
        self.font_sz_sp.setValue(self.config.font_size)
        self.cursor_style_cb.setCurrentText(self.config.cursor_style)
        self.tab_size_sp.setValue(self.config.tab_size)
        self.show_ln_chk.setChecked(self.config.show_line_numbers)
        self.show_chrome_chk.setChecked(self.config.show_window_chrome)
        self.smooth_scroll_chk.setChecked(self.config.smooth_scroll)
        self.wpm_sp.setValue(self.config.wpm)
        self.typo_sp.setValue(self.config.typo_rate)
        self.auto_shorts_chk.setChecked(self.config.auto_shorts)
        self.zoom_chk.setChecked(self.config.cinematic_zoom)
        self.focus_chk.setChecked(self.config.focus_dimming)
        self.intro_chk.setChecked(self.config.intro_card)
        self.intro_dur_sp.setValue(self.config.intro_duration)
        self.outro_chk.setChecked(self.config.outro_card)
        self.outro_dur_sp.setValue(self.config.outro_duration)
        self.progress_overlay_chk.setChecked(self.config.progress_bar_overlay)
        self.watermark_edit.setText(self.config.watermark_text)
        self.window_title_edit.setText(self.config.window_title)
        self.use_custom_chk.setChecked(self.config.use_custom)
        self.custom_editor.setPlainText(self.config.custom_code)
        self.recursive_chk.setChecked(self.config.recursive_scan)
        self.depth_sp.setValue(self.config.scan_depth)
        self.statusBar().showMessage("Project loaded!", 3000)
        self._invalidate_preview()

    def _load_settings(self) -> None:
        if not SETTINGS_FILE.exists(): return
        try:
            with open(SETTINGS_FILE, "r") as f:
                data = json.load(f)
            self.theme_cb.setCurrentText(data.get("theme", "Dracula"))
            self.shutdown_chk.setChecked(data.get("shutdown_when_done", False))
        except Exception:
            logger.error("Failed to load settings.json", exc_info=True)

    def closeEvent(self, e: Any) -> None:
        try:
            self._prep_executor.shutdown(wait=False)
        except:
            pass
        try:
            with open(SETTINGS_FILE, "w") as f:
                json.dump({
                    "theme": self.config.theme,
                    "shutdown_when_done": self.shutdown_chk.isChecked(),
                }, f)
        except Exception:
            pass
        super().closeEvent(e)

# ============================================================================
# 11. ENTRY POINT
# ============================================================================

STYLE = """
QMainWindow, QDialog { background: #1e1e2e; }
QGroupBox { color: #cdd6f4; font-weight: bold; font-size: 12px;
            border: 1px solid #45475a; border-radius: 8px;
            margin-top: 10px; padding-top: 14px; }
QGroupBox::title { subcontrol-origin: margin; left: 12px; }
QLabel { color: #cdd6f4; }
QCheckBox { color: #cdd6f4; spacing: 6px; }
QCheckBox::indicator { width: 16px; height: 16px; border-radius: 3px;
                       border: 1px solid #45475a; background: #313244; }
QCheckBox::indicator:checked { background: #89b4fa; border-color: #89b4fa; }
QTableWidget { background: #181825; color: #cdd6f4; gridline-color: #313244;
               border: none; outline: none; border-radius: 6px; }
QTableWidget::item { padding: 4px 6px; border-bottom: 1px solid #11111b; }
QTableWidget::item:selected { background: #89b4fa; color: #1e1e2e; }
QHeaderView::section { background: #1e1e2e; color: #a6adc8; border: none;
                       padding: 4px; font-size: 10px; border-radius: 0; }
QComboBox, QSpinBox, QDoubleSpinBox, QLineEdit {
    background: #313244; color: #cdd6f4; border: 1px solid #45475a;
    border-radius: 4px; padding: 4px 8px; min-height: 22px;
}
QComboBox::drop-down { border: none; }
QComboBox QAbstractItemView { background: #313244; color: #cdd6f4;
    selection-background-color: #89b4fa; selection-color: #1e1e2e;
    border: 1px solid #45475a; }
QPushButton { background: #313244; color: #cdd6f4; border: 1px solid #45475a;
              border-radius: 6px; padding: 6px 12px; min-height: 22px; }
QPushButton:hover { background: #45475a; border-color: #89b4fa; }
QProgressBar { background: #313244; border: none; border-radius: 4px;
               text-align: center; color: #cdd6f4; min-height: 20px; }
QProgressBar::chunk { background: #89b4fa; border-radius: 4px; }
QTabWidget::pane { border: 1px solid #45475a; border-radius: 6px;
                   background: #1e1e2e; top: -1px; }
QTabBar::tab { background: #313244; color: #a6adc8; padding: 6px 12px;
               border: 1px solid #45475a; border-bottom: none;
               border-top-left-radius: 6px; border-top-right-radius: 6px;
               font-weight: bold; }
QTabBar::tab:selected { background: #1e1e2e; color: #cdd6f4;
                        border-bottom: 2px solid #89b4fa; }
QTabBar::tab:hover:!selected { background: #45475a; }
QPlainTextEdit { background: #11111b; color: #cdd6f4;
                 border: 1px solid #45475a; border-radius: 4px; }
QSplitter { background: #11111b; }
QSplitter::handle { background: #181825; }
QSplitter::handle:horizontal { width: 8px; border-left: 1px solid #11111b;
                               border-right: 1px solid #11111b; }
QSplitter::handle:horizontal:hover { background: #45475a; }
QSplitter::handle:vertical { height: 8px; border-top: 1px solid #11111b;
                             border-bottom: 1px solid #11111b; }
QSplitter::handle:vertical:hover { background: #45475a; }
QScrollArea { background: transparent; border: none; }
QScrollBar:vertical { background: #181825; width: 8px; border: none; border-radius: 4px; }
QScrollBar::handle:vertical { background: #45475a; border-radius: 4px; min-height: 20px; }
QScrollBar::handle:vertical:hover { background: #585b70; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
QScrollBar:horizontal { background: #181825; height: 8px; border: none; border-radius: 4px; }
QScrollBar::handle:horizontal { background: #45475a; border-radius: 4px; min-width: 20px; }
QScrollBar::handle:horizontal:hover { background: #585b70; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
"""

if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setStyleSheet(STYLE)
    pal = QPalette()
    pal.setColor(QPalette.ColorRole.Window, QColor("#1e1e2e"))
    pal.setColor(QPalette.ColorRole.WindowText, QColor("#cdd6f4"))
    pal.setColor(QPalette.ColorRole.Base, QColor("#313244"))
    pal.setColor(QPalette.ColorRole.Text, QColor("#cdd6f4"))
    pal.setColor(QPalette.ColorRole.Button, QColor("#313244"))
    pal.setColor(QPalette.ColorRole.ButtonText, QColor("#cdd6f4"))
    pal.setColor(QPalette.ColorRole.Highlight, QColor("#89b4fa"))
    pal.setColor(QPalette.ColorRole.HighlightedText, QColor("#1e1e2e"))
    app.setPalette(pal)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())
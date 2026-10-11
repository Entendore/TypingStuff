#!/usr/bin/env python3
"""
Unified Typing Video Studio (Ultimate UI Edition)
=================================================
Fixed visual layout for multi-window rendering and settings panels.
Improved Keyboard Overlay layout, scaling, and positioning (Top/Bottom/Shorts).
Corrected cursor movements and text scaling calculations.
Added per-mode font family and font size controls.
Organized Common Settings into a compact Tab Widget.
Added advanced file filtering (name, ext, category, folder) and mode-sync selection.
Added Markdown, fallback Code, and ANSI/ASCII Art highlighting.
"""
from __future__ import annotations

import bisect, io, json, logging, math, os, platform, random, re, shutil, subprocess, sys, tempfile, threading, time as _time, unicodedata, wave, queue, copy
from collections import OrderedDict, deque
from contextlib import contextmanager
from dataclasses import dataclass, field, asdict
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Callable, Dict, Final, FrozenSet, List, Optional, Sequence, Tuple, Union
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from abc import ABC, abstractmethod
import difflib

import numpy as np

from PySide6.QtCore import (QEvent, QPoint, QPointF, QRect, Qt, QThread, QTimer, QUrl, Signal, QBuffer, QIODevice)
from PySide6.QtGui import (QColor, QFont, QFontDatabase, QFontMetrics, QImage, QLinearGradient, QPainter, QPainterPath, QPalette, QPen, QPixmap, QPolygonF, QKeySequence, QShortcut, QTransform)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (QApplication, QCheckBox, QComboBox, QDialog, QDoubleSpinBox, QFileDialog, QFormLayout, QFrame, QGraphicsDropShadowEffect, QGridLayout, QGroupBox, QHBoxLayout, QHeaderView, QLabel, QLineEdit, QMainWindow, QMessageBox, QPlainTextEdit, QProgressBar, QPushButton, QScrollArea, QSizePolicy, QSlider, QSpinBox, QSplitter, QStatusBar, QTabWidget, QTableWidget, QTableWidgetItem, QTimeEdit, QVBoxLayout, QWidget)

import logging
import sys

try:
    import numba
    from numba import njit, prange
    _HAS_NUMBA = True
except ImportError:
    _HAS_NUMBA = False

try:
    from pygments import lex
    from pygments.lexers import get_lexer_by_name
    _HAS_PYGMENTS = True
except ImportError:
    _HAS_PYGMENTS = False



# Configure logger
logger = logging.getLogger("TypingStudio")
logger.setLevel(logging.DEBUG) # Capture everything

# File handler (mode='w' overwrites the log on each app start)
file_handler = logging.FileHandler("studio.log", mode='w', encoding='utf-8')
file_handler.setLevel(logging.DEBUG)
file_handler.setFormatter(logging.Formatter("%(asctime)s - %(levelname)s - %(message)s"))
logger.addHandler(file_handler)

# Console/Terminal handler (Errors only)
console_handler = logging.StreamHandler(sys.stderr)
console_handler.setLevel(logging.ERROR)
console_handler.setFormatter(logging.Formatter("[!] %(levelname)s: %(message)s"))
logger.addHandler(console_handler)

# =====================================================================
# 1. CONFIGURATION & MODES
# =====================================================================

class StudioMode(Enum):
    MULTI_WINDOW = "Multi-Window Code Comparison"
    JR_VS_SR = "Junior vs Senior Dev"
    CODE_YT = "Single Window Code (YouTube Optimised)"
    TEXT_EMOJI = "Text & Emoji (Single Window)"

CWD = Path.cwd()
INPUT_DIR = CWD / "input"
OUTPUT_DIR = CWD / "output"
TEMP_DIR = CWD / "temp"
SETTINGS_FILE = CWD / "settings.json"

for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR):
    _d.mkdir(parents=True, exist_ok=True)

SUPPORTED_EXTENSIONS = frozenset({
    ".py", ".js", ".ts", ".jsx", ".tsx", ".java", ".c", ".cpp", ".h", ".hpp",
    ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt", ".sh", ".bash", ".zsh",
    ".sql", ".html", ".htm", ".css", ".scss", ".json", ".yaml", ".yml", ".toml",
    ".ini", ".cfg", ".txt", ".md", ".lua", ".dart", ".r", ".m",
    ".csv", ".asc", ".ascii", ".art", ".ans", ".nfo", ".diz", ".emoji", ".emo"
})

EXT_TO_LANGUAGE = {
    ".py": "python", ".js": "javascript", ".ts": "typescript", ".c": "c", ".cpp": "cpp",
    ".cs": "csharp", ".go": "go", ".rs": "rust", ".rb": "ruby", ".php": "php", ".swift": "swift",
    ".kt": "kotlin", ".sh": "bash", ".sql": "sql", ".html": "html", ".css": "css", ".scss": "scss",
    ".json": "json", ".yaml": "yaml", ".yml": "yaml", ".md": "markdown", ".txt": "text",
    ".csv": "text", ".asc": "text", ".ascii": "text", ".art": "text", ".ans": "text",
    ".nfo": "text", ".diz": "text", ".emoji": "text", ".emo": "text"
}

FILE_CATEGORIES = {
    "All": set(SUPPORTED_EXTENSIONS),
    "Code": {".py", ".js", ".ts", ".jsx", ".tsx", ".java", "c", ".cpp", ".h", ".hpp", ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt", ".sh", ".bash", ".zsh", ".lua", ".dart", ".r", ".m"},
    "Markup/Web": {".html", ".htm", ".css", ".scss", ".md"},
    "Config/Data": {".json", ".yaml", ".yml", ".toml", ".ini", ".cfg", ".sql", ".csv"},
    "Text/Art": {".txt", ".asc", ".ascii", ".art", ".ans", ".nfo", ".diz", ".emoji", ".emo"}
}

MULTI_WINDOW_LAYOUTS = {
    "1 Window (Single)": 1, 
    "2 Windows (Split)": 2, 
    "4 Windows (Grid)": 4,
    "Git Conflict (3-Pane)": 3
}
JR_VS_SR_LAYOUTS = ["Side by Side (50/50)", "Stacked (50/50)", "Junior Big (70/30)", "Senior Big (70/30)"]
RESOLUTIONS = {"1920x1080": (1920, 1080), "1280x720": (1280, 720), "3840x2160": (3840, 2160), "1080x1920 (9:16)": (1080, 1920), "720x1280 (9:16)": (720, 1280)}

def _get_system_fonts():
    try:
        db = QFontDatabase
        families = db.families()
        preferred = ["Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code", "IBM Plex Mono", "DejaVu Sans Mono", "Courier New", "monospace"]
        sys_fams = [f for f in families if f not in preferred and not f.startswith("@")]
        return preferred + sys_fams
    except:
        return ["Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code", "IBM Plex Mono", "monospace"]

FONT_FAMILIES = ["Consolas", "JetBrains Mono", "Fira Code", "Cascadia Code", "IBM Plex Mono", "monospace"]


THEMES = {
    "Dracula": {"background":"#282a36","foreground":"#f8f8f2","comment":"#6272a4","keyword":"#ff79c6","string":"#f1fa8c","number":"#bd93f9","function":"#50fa7b","builtin":"#8be9fd","decorator":"#50fa7b","operator":"#ff79c6","class_name":"#8be9fd","line_number":"#6272a4","current_line":"#44475a","cursor":"#f8f8f2","title_bar":"#21222c","title_text":"#8be9fd","window_border":"#191a21","junior_accent":"#8be9fd","senior_accent":"#50fa7b"},
    "One Dark": {"background":"#282c34","foreground":"#abb2bf","comment":"#5c6370","keyword":"#c678dd","string":"#98c379","number":"#d19a66","function":"#61afef","builtin":"#e5c07b","decorator":"#56b6c2","operator":"#c678dd","class_name":"#e5c07b","line_number":"#4b5263","current_line":"#2c313c","cursor":"#528bff","title_bar":"#21252b","title_text":"#61afef","window_border":"#181a1f","junior_accent":"#61afef","senior_accent":"#98c379"},
}

EMOJI_SHORTCODES = {":rocket:": "🚀", ":fire:": "🔥", ":sparkles:": "✨", ":heart:": "❤️", ":check:": "✅"}
ENCODERS = ["YouTube Optimised (H.264/AAC)", "NVENC (NVIDIA)", "QSV (Intel)", "AMF (AMD)"]

# =====================================================================
# 2. PATTERN 1: MVC / STATE MANAGEMENT
# =====================================================================

@dataclass
class StudioConfig:
    mode: StudioMode = StudioMode.CODE_YT
    theme: str = "Dracula"
    resolution: str = "1920x1080"
    fps: int = 30
    sound_enabled: bool = True
    sound_preset: str = "Mechanical"
    stereo: bool = False
    volume: int = 50
    encoder: str = "YouTube Optimised (H.264/AAC)"
    bgm_path: str = ""
    bgm_volume: int = 30
    bgm_duck: bool = True
    use_custom: bool = False
    custom_code: str = ""
    
    kb_enabled: bool = False
    kb_layout: str = "QWERTY"
    kb_position: str = "Bottom Center"
    kb_opacity: float = 0.82
    
    # Multi-Window Settings
    layout_mw: str = "2 Windows (Split)"
    wpm_mw: int = 100
    typo_mw: float = 0.0
    shorts_mw: bool = False
    diff_highlight_mw: bool = True
    sync_mw: bool = True
    mw_ratio: int = 50
    
    # Multi-Window Fonts (Up to 4 panes)
    font_mw: str = "Consolas"
    font_sz_auto_mw: bool = False
    font_sz_mw: int = 22
    font_mw_2: str = "Consolas"
    font_sz_auto_mw_2: bool = False
    font_sz_mw_2: int = 22
    font_mw_3: str = "Consolas"
    font_sz_auto_mw_3: bool = False
    font_sz_mw_3: int = 22
    font_mw_4: str = "Consolas"
    font_sz_auto_mw_4: bool = False
    font_sz_mw_4: int = 22
    
    # Jr vs Sr Settings
    layout_jr: str = "Side by Side (50/50)"
    jr_wpm: int = 90
    sr_wpm: int = 130
    typo_jr: float = 0.03
    jr_custom_code: str = ""
    sr_custom_code: str = ""
    hud_jr: bool = True
    jr_sound: str = "Mechanical"
    sr_sound: str = "ASMR Deep Thock"
    
    # Jr vs Sr Fonts
    font_jr: str = "Consolas"
    font_sz_auto_jr: bool = False
    font_sz_jr: int = 22
    font_sr: str = "Consolas"
    font_sz_auto_sr: bool = False
    font_sz_sr: int = 22
    
    # Code YT Settings
    wpm_yt: int = 100
    typo_yt: float = 0.0
    shorts_yt: bool = False
    yt_zoom: bool = False
    yt_focus: bool = False
    font_yt: str = "Consolas"
    font_sz_auto_yt: bool = False
    font_sz_yt: int = 22
    
    # Text & Emoji Settings
    wpm_txt: int = 100
    typo_txt: float = 0.0
    shorts_txt: bool = False
    ascii_art: bool = False
    ansi_colors: bool = False
    txt_markdown: bool = False
    txt_crt: bool = False
    txt_bubbles: bool = False
    txt_clean: bool = True
    font_txt: str = "Consolas"
    font_sz_auto_txt: bool = False
    font_sz_txt: int = 22
    
    # Global Extras
    yt_extras: bool = True
    recursive_scan: bool = True
    scan_depth: int = 10
    output_template: str = "{name}_{date}"

# =====================================================================
# 3. UTILITIES & PATTERN 5: FLYWEIGHT
# =====================================================================

ZWJ = '\u200d'; VS16 = '\ufe0f'

def split_graphemes(text: str) -> List[str]:
    graphemes, i, n = [], 0, len(text)
    while i < n:
        c, i = text[i], i + 1
        while i < n:
            nxt = text[i]
            if nxt == ZWJ or nxt == VS16 or unicodedata.combining(nxt) != 0:
                c += nxt; i += 1
                if c[-1] == ZWJ and i < n: c += text[i]; i += 1
            else: break
        graphemes.append(c)
    return graphemes

def is_emoji(char: str) -> bool:
    if not char: return False
    if ZWJ in char or VS16 in char: return True
    cat = unicodedata.category(char[0])
    # Only consider 'So' (Symbol, Other) which covers emojis. 
    # Ignore 'Sm' (Math) and 'Sk' (Modifier) so code symbols don't trigger the pop effect.
    return cat == 'So'

def convert_shortcodes(text: str) -> str:
    for code, emoji in EMOJI_SHORTCODES.items(): text = text.replace(code, emoji)
    return text

def read_text_file(path: str, clean: bool = True) -> str:
    ext = os.path.splitext(path)[1].lower()
    enc = "cp437" if ext in (".nfo", ".diz") else "utf-8"
    try:
        with open(path, "r", encoding=enc) as f: text = f.read()
    except UnicodeDecodeError:
        with open(path, "r", encoding="utf-8", errors="replace") as f: text = f.read()
    text = convert_shortcodes(text)
    if clean and ext not in (".asc", ".ascii", ".art", ".ans", ".nfo", ".diz", ".emoji", ".emo"):
        text = text.replace("\xa0", " ").replace("\xad", "")
        text = re.sub(r'[ \t]+\n', '\n', text)
        text = "\n".join(line.rstrip() for line in text.splitlines())
    return text

class LexerFactory:
    @staticmethod
    @lru_cache(maxsize=50)
    def get_lexer(lang: str):
        if not _HAS_PYGMENTS: return None
        try: return get_lexer_by_name(lang, stripall=False)
        except: return get_lexer_by_name("text", stripall=False)

# =====================================================================
# 4. DSP ENGINE & MODULAR SOUND DESIGN
# =====================================================================

AUDIO_SAMPLE_RATE = 48000

if _HAS_NUMBA:
    @njit(cache=True)
    def _nb_k_weight(x, sr):
        n = len(x); y = np.empty(n, dtype=np.float64)
        if sr == 48000:
            s1_b0=1.53512485958624; s1_b1=-2.61187896900947; s1_b2=1.23925952524423; s1_a1=-1.69019851598276; s1_a2=0.732626261909496
            s2_b0=1.0; s2_b1=-2.0; s2_b2=1.0; s2_a1=-1.99004745481143; s2_a2=0.990072500365666
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
    def _nb_compute_loudness(x_k):
        n = len(x_k)
        if n == 0: return -70.0
        s = 0.0
        for i in range(n): v = x_k[i]; s += v * v
        ms = s / n
        if ms < 1e-20: return -70.0
        return -0.691 + 10.0 * np.log10(ms)

    @njit(cache=True)
    def _nb_apply_gain(x, gain):
        n = len(x); out = np.empty(n, dtype=np.float64)
        for i in range(n): out[i] = x[i] * gain
        return out

def _normalize_to_lufs(x, sr, target_lufs=-14.0):
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
    @staticmethod
    def env_exp(n, sr, attack=0.001, decay_rate=30.0, attack_curve=2.0):
        t = np.arange(n, dtype=np.float64) / sr
        env = np.exp(-t * decay_rate)
        a_samp = max(1, int(attack * sr))
        if a_samp < n:
            a_env = np.linspace(0, 1, a_samp) ** attack_curve
            env[:a_samp] = a_env * np.exp(-np.arange(a_samp, dtype=np.float64) / sr * decay_rate)
        return env

    @staticmethod
    def fir_lowpass(cutoff, sr=AUDIO_SAMPLE_RATE, n_taps=127):
        if n_taps % 2 == 0: n_taps += 1
        fc = min(max(1.0, cutoff), sr / 2.0 - 1.0) / sr
        n = np.arange(n_taps, dtype=np.float64); center = (n_taps - 1) / 2.0
        h = np.sinc(2 * fc * (n - center))
        w = 0.42 - 0.5*np.cos(2*np.pi*n/(n_taps-1)) + 0.08*np.cos(4*np.pi*n/(n_taps-1))
        h *= w; s = np.sum(h)
        if s > 0: h /= s
        return h

    @staticmethod
    def convolve(x, h):
        n, nh = len(x), len(h)
        if nh <= 1: return x * h[0] if nh == 1 else x
        n_fft = 1 << ((n + nh - 1).bit_length())
        return np.fft.irfft(np.fft.rfft(x, n_fft) * np.fft.rfft(h, n_fft), n_fft)[:n]

    @staticmethod
    def filt_lp(x, c, sr=AUDIO_SAMPLE_RATE, n_taps=127): return DSP.convolve(x, DSP.fir_lowpass(c, sr, n_taps))
    @staticmethod
    def filt_hp(x, c, sr=AUDIO_SAMPLE_RATE, n_taps=63):
        hlp = DSP.fir_lowpass(c, sr, n_taps); h = -hlp; h[len(h)//2] += 1.0; return DSP.convolve(x, h)
    @staticmethod
    def filt_bp(x, l, h, sr=AUDIO_SAMPLE_RATE): return DSP.filt_lp(x, h, sr) - DSP.filt_lp(x, l, sr)
    @staticmethod
    def filt_resonator(x, freq, q, sr=AUDIO_SAMPLE_RATE, gain=1.0):
        w0 = 2 * np.pi * freq / sr; r = np.exp(-w0 / (2 * max(0.5, q)))
        wd = w0 * np.sqrt(max(0.0, 1.0 - 1.0/(4*q*q))) if q > 0.5 else w0
        n_ir = min(len(x), max(16, int(sr * max(0.005, 6.0 * q / max(1.0, freq)))))
        t = np.arange(n_ir, dtype=np.float64); ir = (r ** t) * np.sin(wd * t)
        pk = np.max(np.abs(ir))
        if pk > 1e-10: ir = ir / pk * gain
        return DSP.convolve(x, ir)

    @staticmethod
    def osc_sine(f, n, sr): return np.sin(2*np.pi*f*(np.arange(n, dtype=np.float64)/sr))
    @staticmethod
    def osc_fm(c, mr, mi, n, sr):
        t = np.arange(n, dtype=np.float64) / sr
        return np.sin(2*np.pi*c*t + mi*np.sin(2*np.pi*c*mr*t))
    @staticmethod
    def osc_saw(f, n, sr):
        t = np.arange(n, dtype=np.float64) / sr; sig = np.zeros(n)
        for h in range(1, 17):
            fh = f * h
            if fh >= sr * 0.45: break
            sig += np.sin(2*np.pi*fh*t) / h
        return sig * 0.5

    @staticmethod
    def noise_white(n, rng): return rng.randn(n).astype(np.float64)
    @staticmethod
    def noise_pink(n, rng):
        white = rng.randn(n).astype(np.float64)
        fft = np.fft.rfft(white)
        freqs = np.fft.rfftfreq(n, 1.0/AUDIO_SAMPLE_RATE)
        freqs[0] = max(freqs[1] if len(freqs) > 1 else 1.0, 1.0)
        fft[1:] /= np.sqrt(np.abs(freqs[1:])); fft[0] = 0
        return np.fft.irfft(fft, n=n)
    @staticmethod
    def noise_brown(n, rng):
        white = rng.randn(n).astype(np.float64); brown = np.cumsum(white); brown -= np.mean(brown)
        pk = np.max(np.abs(brown))
        if pk > 0: brown = brown / pk
        return brown * 0.5
    @staticmethod
    def modal(modes, n, sr, inharmonicity=0.0):
        t = np.arange(n, dtype=np.float64) / sr; out = np.zeros(n, dtype=np.float64)
        f0 = modes[0][0] if modes else 440.0
        for freq, decay, amp in modes:
            af = freq
            if inharmonicity > 0:
                nh = freq / f0; af = freq * np.sqrt(1 + inharmonicity * nh * nh)
            out += np.sin(2*np.pi*af*t) * np.exp(-decay*t) * amp
        return out

    @staticmethod
    def sat_tanh(x, drive=1.0):
        if drive <= 0: return x
        return np.tanh(x * drive) / max(0.001, np.tanh(drive))
    @staticmethod
    def to_int16(x, target_db=-1.0):
        pk = np.max(np.abs(x)) if len(x) > 0 else 0.0
        if pk < 1e-10: return np.zeros_like(x, dtype=np.int16)
        return np.clip(x * (10**(target_db/20) / pk) * 32767, -32768, 32767).astype(np.int16)

# --- MODULAR SOUND ENGINE ---
@dataclass
class VoiceSpec:
    osc: str = "sine"; freq: float = 440.0; fm_ratio: float = 1.0; fm_index: float = 0.0
    attack: float = 0.001; decay_rate: float = 30.0; attack_curve: float = 2.0
    filt: str = "none"; f_cutoff: float = 8000.0; f_high: float = 12000.0; f_q: float = 1.0
    drive: float = 0.0; gain: float = 0.5; delay: float = 0.0
    modes: Optional[List[Tuple[float, float, float]]] = None; inharmonicity: float = 0.0

@dataclass
class SoundSpec:
    duration: float = 0.12
    layers: List[VoiceSpec] = field(default_factory=list)

MODULAR_SOUND_PRESETS = {
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
    ])
}

class ModularSoundEngine:
    def __init__(self, sr=AUDIO_SAMPLE_RATE):
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
        if d > 0 and d < n: return np.concatenate([np.zeros(d, dtype=np.float64), sig[:n-d]]) * spec.gain
        return sig * spec.gain

    def render(self, spec: SoundSpec, seed: int) -> np.ndarray:
        rng = np.random.RandomState(seed)
        n = int(self.sr * spec.duration)
        mix = np.zeros(n, dtype=np.float64)
        for v in spec.layers: mix += self._render_voice(v, n, rng)
        return DSP.to_int16(DSP.filt_hp(mix, 20.0, self.sr, n_taps=63))

class SimpleSoundGen:
    _QWERTY_ROWS = ("`1234567890-=", "qwertyuiop[]\\", "asdfghjkl;'", "zxcvbnm,./")
    _ROW_PITCH_SHIFT = [1.5, 0.5, -0.5, -2.0]

    def __init__(self, sr=AUDIO_SAMPLE_RATE, preset="Mechanical", stereo=False, reverb_amt=0.1):
        self.sr = sr; self.preset = preset; self.stereo = stereo; self.reverb_amt = reverb_amt
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

    def generate_pcm(self, timestamps, volume=0.5):
        if not timestamps: return np.zeros(0, dtype=np.int16)
        sr = self.sr; total = max(ts for ts, _ in timestamps) + 0.3; n = int(sr * total)
        rng = random.Random(98765); raw, starts_i, pans = [], [], []
        for ts, ch in timestamps:
            if ch == "\n": snd, vm, pan = rng.choice(self.enters), rng.uniform(1.05, 1.20), 0.2
            elif ch == " ": snd, vm, pan = rng.choice(self.spaces), rng.uniform(1.00, 1.15), 0.0
            else:
                base_snd = rng.choice(self.clicks)
                shift = self._get_pitch_shift(ch)
                snd = self._pitch_shift(base_snd, shift) if shift != 0 else base_snd
                vm, pan = rng.uniform(0.95, 1.10), rng.uniform(-0.3, 0.3)
            s = int(ts * sr); e = min(s + len(snd), n)
            if s < n:
                raw.append(snd[:e-s].astype(np.float32) * volume * vm); starts_i.append(s)
                if self.stereo: pans.append(pan)
        if not raw: return np.zeros(n, dtype=np.int16)
        if self.stereo:
            ml, mr = np.zeros(n, dtype=np.float32), np.zeros(n, dtype=np.float32)
            for i, snd in enumerate(raw):
                s = starts_i[i]; pan = pans[i]
                lg = np.cos((pan + 1.0) * np.pi / 4.0); rg = np.sin((pan + 1.0) * np.pi / 4.0)
                e = min(s + len(snd), n); ml[s:e] += snd[:e-s] * lg; mr[s:e] += snd[:e-s] * rg
            ml = _normalize_to_lufs(ml, sr); mr = _normalize_to_lufs(mr, sr)
            out = np.empty(n*2, dtype=np.int16)
            out[0::2] = np.clip(ml * 32767, -32768, 32767).astype(np.int16)
            out[1::2] = np.clip(mr * 32767, -32768, 32767).astype(np.int16)
            return out
        starts = np.array(starts_i, dtype=np.int64); lengths = np.array([len(s) for s in raw], dtype=np.int64)
        flat = np.concatenate(raw); offsets = np.zeros(len(raw), dtype=np.int64)
        for i in range(1, len(raw)): offsets[i] = offsets[i-1] + lengths[i-1]
        mix = np.zeros(n, dtype=np.float32)
        for i in range(len(starts)): mix[int(starts[i]):int(starts[i]+lengths[i])] += flat[int(offsets[i]):int(offsets[i]+lengths[i])]
        mix = _normalize_to_lufs(mix, sr)
        return np.clip(mix * 32767, -32768, 32767).astype(np.int16)

# =====================================================================
# 5. TYPING ANIMATOR
# =====================================================================

@dataclass
class TypingProfile:
    name: str = "Default"; wpm: int = 100; start_pause: float = 0.5; end_pause: float = 1.5; typo_rate: float = 0.0; is_text: bool = False

class TypingAnimator:
    def __init__(self, code: str, profile: TypingProfile, seed: int = 42):
        self.code, self.profile = code, profile
        self.error_count = 0
        rng = random.Random(seed)
        chars = split_graphemes(code) if profile.is_text else list(code)
        base_delay = 1.0 / ((profile.wpm * 5) / 60)
        t = profile.start_pause
        self.display_chars, self._timestamps, self.timeline = [], [], []
        for char in chars:
            if char != '\n' and char != ' ' and rng.random() < profile.typo_rate:
                self.error_count += 1
                t += base_delay * rng.uniform(0.5, 1.0)
                self.timeline.append((t, rng.choice("abcdefghijklmnopqrstuvwxyz"))); self.display_chars.append(self.timeline[-1][1]); self._timestamps.append(t)
                t += base_delay * rng.uniform(0.5, 1.0)
                self.timeline.append((t, '\b')); self.display_chars.append('\b'); self._timestamps.append(t)
            self.timeline.append((t, char)); self.display_chars.append(char); self._timestamps.append(t)
            if char in ".!?": t += base_delay * rng.uniform(4.0, 6.0)
            elif char in ",;:": t += base_delay * rng.uniform(2.0, 3.5)
            elif char == '\n': t += base_delay * rng.uniform(3.0, 5.0)
            else: t += base_delay * rng.uniform(0.7, 1.3)
        self._duration = t + profile.end_pause

    def duration(self) -> float: return self._duration
    def visible_at(self, t: float) -> int: return bisect.bisect_right(self._timestamps, t) if t > 0 else 0
    def char_timestamps(self) -> List[Tuple[float, str]]: return self.timeline
    def active_key_at(self, t: float, fd: float = 0.18) -> Tuple[Optional[str], float]:
        if not self._timestamps or t < self._timestamps[0]: return None, 0.0
        idx = bisect.bisect_right(self._timestamps, t)
        if idx == 0: return None, 0.0
        last_ts, last_char = self.timeline[idx - 1]
        elapsed = t - last_ts
        return (last_char, max(0.0, (1.0 - elapsed / fd) ** 1.5)) if elapsed < fd else (None, 0.0)
    @staticmethod
    def find_wpm_for_target(text: str, target_dur: float, sp: float, ep: float) -> int:
        available = target_dur - sp - ep
        if available <= 0: return 300
        count = len(split_graphemes(text))
        return max(30, min(300, int(60.0 / max(0.01, available / max(1, count * 1.2)) / 5.0)))

# =====================================================================
# 6. RENDERING ENGINE
# =====================================================================

KEYBOARD_LAYOUTS = {
    "QWERTY": [[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],[("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],[("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "AZERTY": [[("²",1),("&",1),("é",1),("\"",1),("'",1),("(",1),("-",1),("è",1),("_",1),("ç",1),("à",1),(")",1),("=",1),("Bksp",2)],[("Tab",1.5),("A",1),("Z",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("^",1),("$",1),("Enter",1.5)],[("Caps",1.75),("Q",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("M",1),("ù",1),("*",1),("Enter",2.25)],[("Shift",1.25),("<",1),("W",1),("X",1),("C",1),("V",1),("B",1),("N",1),(",",1),(";",1),(":",1),("!",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "QWERTZ": [[("^",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("ß",1),("´",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Z",1),("U",1),("I",1),("O",1),("P",1),("Ü",1),("+",1),("Enter",1.5)],[("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("Ö",1),("Ä",1),("#",1),("Enter",2.25)],[("Shift",1.25),("<",1),("Y",1),("X",1),("C",1),("V",1),("B",1),("N",1),(",",1),(".",1),("-",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "Dvorak": [[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("[",1),("]",1),("Bksp",2)],[("Tab",1.5),("'",1),(",",1),(".",1),("P",1),("Y",1),("F",1),("G",1),("C",1),("R",1),("L",1),("/",1),("=",1),("\\",1.5)],[("Caps",1.75),("A",1),("O",1),("E",1),("U",1),("I",1),("D",1),("H",1),("T",1),("N",1),("S",1),("-",1),("Enter",2.25)],[("Shift",2.25),(";",1),("Q",1),("J",1),("K",1),("X",1),("B",1),("M",1),("W",1),("V",1),("Z",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "Colemak": [[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("F",1),("P",1),("G",1),("J",1),("L",1),("U",1),("Y",1),(";",1),("[",1),("]",1),("\\",1.5)],[("Bksp",1.75),("A",1),("R",1),("S",1),("T",1),("D",1),("H",1),("N",1),("E",1),("I",1),("O",1),("'",1),("Enter",2.25)],[("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("K",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "JIS (Japanese)": [[("半",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("^",1),("¥",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("@",1),("[",1),("]",1),("\\",1.5)],[("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),(":",1),("Enter",2.25)],[("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("_",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("無",1),("",4.25),("変",1.25),("Alt",1.25),("Fn",1.25),("Ctrl",1.25)]],
    "Pinyin (Chinese)": [[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],[("中",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],[("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)]],
    "Turkish Q": [[("\"",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("*",1),("-",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("Ğ",1),("Ü",1),(";",1.5)],[("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("Ş",1),("İ",1),("Enter",2.25)],[("Shift",2.25),("<",1),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),("Ö",1),("Ç",1),(".",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)]]
}

class KeyboardOverlay:
    def __init__(self, video_w, video_h, layout_name="QWERTY", theme=None, opacity=0.82, max_height=None, position="bottom_center"):
        self.video_w, self.video_h, self.theme, self.opacity = video_w, video_h, theme, opacity
        self.rows = KEYBOARD_LAYOUTS.get(layout_name, KEYBOARD_LAYOUTS["QWERTY"])
        self.char_map = {}
        for ri, row in enumerate(self.rows):
            for ci, (label, w) in enumerate(row):
                if len(label) == 1: self.char_map[label] = self.char_map[label.lower()] = (ri, ci)
                if label == "": self.char_map[" "] = (ri, ci)
                elif "enter" in label.lower(): self.char_map["\n"] = (ri, ci)
                elif "tab" in label.lower(): self.char_map["\t"] = (ri, ci)
                elif "bksp" in label.lower(): self.char_map["\b"] = (ri, ci)
        for s, b in {"~":"`","!":"1","@":"2","#":"3","$":"4","%":"5","^":"6","&":"7","*":"8","(":"9",")":"0","_":"-","+=":"=","{":"[","}":"]","|":"\\",":":";",'"':"'","<":",",">":".","?":"/"}.items():
            if b in self.char_map: self.char_map[s] = self.char_map[b]
            
        target_kb_w = int(video_w * 0.65)
        required_unit = target_kb_w / 15.0
        self.key_unit = max(14, min(55, int(required_unit)))
        self.key_gap = max(2, self.key_unit // 14)
        self.key_h = int(self.key_unit * 0.82)
        self._kb_w = int(max(sum(w for _, w in r) for r in self.rows) * self.key_unit + (max(len(r) for r in self.rows) - 1) * self.key_gap)
        self._kb_h = int(len(self.rows) * self.key_h + (len(self.rows) - 1) * self.key_gap)

        self.position = position
        self._kb_x, self._kb_y = 0, 0
        self.key_rects = {}
        self._rebuild_key_rects()

    def height_needed(self): 
        return self._kb_h + max(16, self.video_h // 30)

    def _apply_position(self, y_target=None):
        m_x = max(8, self.video_w // 60)
        m_y = max(8, self.video_h // 60)
        
        if "center" in self.position: self._kb_x = (self.video_w - self._kb_w) // 2
        elif "right" in self.position: self._kb_x = self.video_w - self._kb_w - m_x
        elif "left" in self.position: self._kb_x = m_x
        
        if "top" in self.position:
            self._kb_y = m_y
        else:
            if y_target is not None:
                self._kb_y = y_target
                max_y = self.video_h - self._kb_h - m_y
                min_y = m_y
                if self._kb_y > max_y: self._kb_y = max_y
                if self._kb_y < min_y: self._kb_y = min_y
            else:
                self._kb_y = self.video_h - self._kb_h - m_y

    def _rebuild_key_rects(self):
        self.key_rects = {}
        for ri, row in enumerate(self.rows):
            x = self._kb_x
            for ci, (_, w) in enumerate(row):
                kw = int(w * self.key_unit) - self.key_gap
                y = self._kb_y + ri * (self.key_h + self.key_gap)
                self.key_rects[(ri, ci)] = QRect(x, y, kw, self.key_h)
                x += int(w * self.key_unit)

    def reposition(self, y_target=None): 
        self._apply_position(y_target)
        self._rebuild_key_rects()
        
    def resolve_key(self, ch): return self.char_map.get(ch)
    
    def draw(self, p, active_key=None, flash=0.0):
        p.save()
        p.setOpacity(self.opacity)
        p.setRenderHint(QPainter.Antialiasing)
        th = self.theme or THEMES["Dracula"]
        radius = max(3, self.key_unit // 8)
        
        pad = max(6, self.key_unit // 4)
        p.setPen(QPen(QColor(th["window_border"]), max(1, self.key_unit // 20)))
        p.setBrush(QColor(th["title_bar"])) 
        p.drawRoundedRect(self._kb_x-pad, self._kb_y-pad, self._kb_w+2*pad, self._kb_h+2*pad, radius*2, radius*2)
        
        kbg = QColor(th["background"])
        kbr = QColor(th["window_border"])
        lc = QColor(th["foreground"])
        mc = QColor(th["line_number"])
        hlb = QColor(th["cursor"])
        
        if flash > 0 and active_key is not None:
            hkf = QColor(int(kbg.red()+(hlb.red()-kbg.red())*flash), int(kbg.green()+(hlb.green()-kbg.green())*flash), int(kbg.blue()+(hlb.blue()-kbg.blue())*flash))
            hlg = QColor(hlb)
            hlg.setAlpha(int(60*flash))
            hle = max(3, int(self.key_unit*0.12*flash))
        else: 
            hkf = None
            
        for (ri, ci), rect in self.key_rects.items():
            label = self.rows[ri][ci][0]
            ia = (active_key is not None and active_key == (ri, ci))
            
            if ia and hkf is not None:
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(hlg)
                p.drawRoundedRect(rect.adjusted(-hle, -hle, hle, hle), radius, radius)
                p.setBrush(hkf)
                p.setPen(QPen(kbr, 1))
            else:
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(kbr.darker(150))
                p.drawRoundedRect(rect.adjusted(0, 3, 0, 3), radius, radius)
                p.setBrush(kbg)
                p.setPen(QPen(kbr, 1))
                
            p.drawRoundedRect(rect, radius, radius)
            
            if label:
                p.setPen(mc if len(label) > 1 else lc)
                p.setFont(QFont("Segoe UI", max(7, int(self.key_unit * 0.30))))
                p.drawText(rect, Qt.AlignCenter, label)
        p.restore()

class StudioRenderer:
    def __init__(self, width, height, theme_name="Dracula", font_family="Consolas", font_size=22,
                 show_line_numbers=True, show_window_chrome=True, padding=24, tab_size=4,
                 language="python", ascii_art_mode=False, config=None, pane_idx=0, line_diffs=None, kb_overlay=None):
        self.width, self.height = width, height
        self.theme = THEMES.get(theme_name, THEMES["Dracula"])
        self.font_family, self.font_size = font_family, font_size
        self.show_line_numbers, self.show_window_chrome = show_line_numbers, show_window_chrome
        self.padding = min(padding, max(8, min(width, height) // 30))
        self.tab_size = tab_size
        self.language, self.ascii_art_mode = language, ascii_art_mode
        self.config = config
        self.pane_idx = pane_idx
        self.line_diffs = line_diffs if line_diffs else {}
        self.kb_overlay = kb_overlay
        self.CURSOR_BLINK = 0.53
        self._code_rect = QRect(0, 0, 1, 1)
        
        _fams = [font_family, "JetBrains Mono", "DejaVu Sans Mono", "Consolas", "monospace", "Noto Color Emoji", "Segoe UI Emoji", "sans-serif"]
        self.font = QFont(self.font_family, self.font_size)
        self.font.setFamilies(list(dict.fromkeys(_fams)))
        self.font.setFixedPitch(True)
        # Force standard grayscale antialiasing for video output
        self.font.setStyleStrategy(QFont.StyleStrategy.NoSubpixelAntialias | QFont.StyleStrategy.PreferAntialias)
        self.fm = QFontMetrics(self.font)
        self.char_w = self.fm.horizontalAdvance("M"); self.line_h = self.fm.height()
        self._tab_adv = self.char_w * tab_size
        
        self._qcolors = {k: QColor(v) for k, v in self.theme.items() if isinstance(v, str) and v.startswith("#")}
        self._qc_fg = self._qcolors.get("foreground", QColor("#f8f8f2"))
        self._qc_ln = self._qcolors.get("line_number", QColor("#6272a4"))
        self._qc_cursor = self._qcolors.get("cursor", QColor("#f8f8f2"))
        self._qc_current_line = self._qcolors.get("current_line", QColor("#44475a"))
        
        self.ansi_colors = {
            '30': QColor("#000000"), '31': QColor("#ff5555"), '32': QColor("#50fa7b"), '33': QColor("#f1fa8c"),
            '34': QColor("#bd93f9"), '35': QColor("#ff79c6"), '36': QColor("#8be9fd"), '37': QColor("#f8f8f2"),
            '90': QColor("#6272a4"), '91': QColor("#ff6e6e"), '92': QColor("#69ff94"), '93': QColor("#ffffa5"),
            '94': QColor("#d6acff"), '95': QColor("#ff92df"), '96': QColor("#a4ffff"), '97': QColor("#ffffff")
        }
        
        self._token_cache = {}
        self._token_lock = threading.Lock()
        self._build_bg_cache()

    def _tokenize_ansi(self, text):
        tokens = []
        parts = re.split(r'(\x1b\[[0-9;]*m)', text)
        current_color = self._qc_fg
        for part in parts:
            if not part: continue
            if part.startswith('\x1b['):
                codes = part[2:-1].split(';')
                if '0' in codes:
                    current_color = self._qc_fg
                else:
                    for code in codes:
                        if code in self.ansi_colors:
                            current_color = self.ansi_colors[code]
            else:
                tokens.append((current_color, part))
        return tokens

    def _tokenize_markdown(self, text):
        tokens = []
        pattern = re.compile(
            r'(^#+\s+.*?$|^[-*+]\s+.*?$|^>\s+.*?$|\*\*.*?\*\*|\*.*?\*|`[^`]*`|\[.*?\]\(.*?\))',
            re.MULTILINE
        )
        last_end = 0
        cmt_color = self._qcolors.get("comment", self._qc_fg)
        kw_color = self._qcolors.get("keyword", self._qc_fg)
        str_color = self._qcolors.get("string", self._qc_fg)
        num_color = self._qcolors.get("number", self._qc_fg)
        fn_color = self._qcolors.get("function", self._qc_fg)
        
        for match in pattern.finditer(text):
            start, end = match.span()
            if start > last_end:
                tokens.append((self._qc_fg, text[last_end:start]))
            match_text = match.group(0)
            if match_text.startswith('#'):
                tokens.append((kw_color, match_text))
            elif match_text.startswith(('-', '*', '+')) and len(match_text) > 1 and match_text[1] == ' ':
                tokens.append((cmt_color, match_text))
            elif match_text.startswith('>'):
                tokens.append((cmt_color, match_text))
            elif match_text.startswith('`'):
                tokens.append((str_color, match_text))
            elif match_text.startswith('['):
                tokens.append((fn_color, match_text))
            elif match_text.startswith('**'):
                tokens.append((kw_color, match_text))
            elif match_text.startswith('*'):
                tokens.append((num_color, match_text))
            else:
                tokens.append((self._qc_fg, match_text))
            last_end = end
        if last_end < len(text):
            tokens.append((self._qc_fg, text[last_end:]))
        return tokens

    def _tokenize_basic_code(self, text):
        tokens = []
        pattern = re.compile(
            r'(\#.*?$|\/\/.*?$|\/\*.*?\*\/)|("(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|`(?:\\.|[^`\\])*`)|(\b\d+\.?\d*\b)|(\b[A-Za-z_][A-Za-z0-9_]*\b)',
            re.MULTILINE
        )
        keywords = {'def', 'class', 'import', 'from', 'return', 'if', 'else', 'elif', 'for', 'while', 'try', 'except', 'finally', 'with', 'as', 'in', 'is', 'not', 'and', 'or', 'True', 'False', 'None', 'public', 'private', 'void', 'int', 'string', 'float', 'bool', 'func', 'fn', 'let', 'const', 'var', 'function', 'new', 'this', 'self'}
        
        cmt_color = self._qcolors.get("comment", self._qc_fg)
        str_color = self._qcolors.get("string", self._qc_fg)
        num_color = self._qcolors.get("number", self._qc_fg)
        kw_color = self._qcolors.get("keyword", self._qc_fg)
        
        last_end = 0
        for match in pattern.finditer(text):
            start, end = match.span()
            if start > last_end:
                tokens.append((self._qc_fg, text[last_end:start]))
            
            match_text = match.group(0)
            if match_text.startswith('#') or match_text.startswith('//') or match_text.startswith('/*'):
                tokens.append((cmt_color, match_text))
            elif match_text.startswith('"') or match_text.startswith("'") or match_text.startswith('`'):
                tokens.append((str_color, match_text))
            elif match_text.isdigit():
                tokens.append((num_color, match_text))
            elif match_text in keywords:
                tokens.append((kw_color, match_text))
            else:
                tokens.append((self._qc_fg, match_text))
            last_end = end
        if last_end < len(text):
            tokens.append((self._qc_fg, text[last_end:]))
        return tokens

    def _tokenize(self, text):
        if '\x1b[' in text:
            if self.config and self.config.ansi_colors:
                return self._tokenize_ansi(text)
            text = re.sub(r'\x1b\[[0-9;]*m', '', text)
            
        if self.ascii_art_mode:
            return [(self._qc_fg, text)]
            
        if self.config and self.config.mode == StudioMode.TEXT_EMOJI and self.config.txt_markdown:
            return self._tokenize_markdown(text)
            
        if self.language in ("text", "markdown"):
            if self.language == "markdown":
                return self._tokenize_markdown(text)
            return [(self._qc_fg, text)]
            
        if not _HAS_PYGMENTS:
            return self._tokenize_basic_code(text)
            
        with self._token_lock:
            cache_key = text
            if cache_key in self._token_cache: return self._token_cache[cache_key]
            lexer = LexerFactory.get_lexer(self.language)
            if not lexer:
                tokens = self._tokenize_basic_code(text)
                self._token_cache[cache_key] = tokens
                return tokens
            tokens = []
            for ttype, val in lex(text, lexer):
                if val in ('\n', ' ', '\t'): tokens.append((self._qc_fg, val)); continue
                color = self._qc_fg; ttype_str = str(ttype)
                if ttype_str.startswith('Token.Comment'): color = self._qcolors.get("comment", self._qc_fg)
                elif ttype_str.startswith('Token.Keyword'): color = self._qcolors.get("keyword", self._qc_fg)
                elif ttype_str.startswith('Token.String'): color = self._qcolors.get("string", self._qc_fg)
                elif ttype_str.startswith('Token.Number'): color = self._qcolors.get("number", self._qc_fg)
                elif ttype_str.startswith('Token.Name.Function'): color = self._qcolors.get("function", self._qc_fg)
                elif ttype_str.startswith('Token.Name.Class'): color = self._qcolors.get("class_name", self._qc_fg)
                tokens.append((color, val))
            self._token_cache[cache_key] = tokens
            return tokens

    def _build_bg_cache(self):
        self._bg = QImage(self.width, self.height, QImage.Format_RGB32)
        self._bg.fill(QColor(self.theme["background"]))
        p = QPainter(self._bg); p.setRenderHint(QPainter.Antialiasing)
        bg = self._qcolors.get("background", QColor("#282a36"))
        g = QLinearGradient(0, 0, 0, self.height); g.setColorAt(0, bg.lighter(105)); g.setColorAt(1, bg)
        p.fillRect(0, 0, self.width, self.height, g)
        pad, chrome_h = self.padding, 42 if self.show_window_chrome else 0
        ww = self.width - 2 * pad
        
        kb_h = self.kb_overlay.height_needed() if self.kb_overlay else 0
        kb_top = self.kb_overlay and "top" in self.kb_overlay.position
        
        avail_h = self.height - 2 * pad
        target_wh = avail_h - kb_h
        
        max_ratio = 1.1 if self.config.mode != StudioMode.TEXT_EMOJI else 2.0
        if self.ascii_art_mode:
            max_ratio = float('inf') # Allow ASCII art to fill the entire vertical space
            
        if target_wh > ww * max_ratio:
            target_wh = int(ww * max_ratio)
            
        total_block_h = target_wh + kb_h
        start_y = pad + (avail_h - total_block_h) // 2
        
        wy = start_y + (kb_h if kb_top else 0)
        wh = target_wh
        wx, ww = pad, self.width - 2*pad
        
        # Draw a soft, expanding drop shadow behind the code window
        for i in range(6, 0, -1):
            alpha = int(40 / i) # Fades out towards the edges
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(0, 0, 0, alpha))
            p.drawRoundedRect(wx - i, wy - i, ww + i*2, wh + i*2, 12 + i, 12 + i)
            
        p.setPen(QColor(self.theme["window_border"])); p.setBrush(QColor(self.theme["background"])); p.drawRoundedRect(wx, wy, ww, wh, 12, 12)
        
        if self.show_window_chrome:
            p.setPen(Qt.PenStyle.NoPen); p.setBrush(QColor(self.theme["title_bar"])); p.drawRoundedRect(wx, wy, ww, chrome_h, 12, 12)
            p.drawRect(wx, wy+chrome_h-12, ww, 12)
            for i, color in enumerate(["#ff5f56", "#ffbd2e", "#27c93f"]):
                p.setBrush(QColor(color)); p.setPen(Qt.PenStyle.NoPen); p.drawEllipse(QPoint(wx+20+i*24, wy+19), 7, 7)
            self._code_rect = QRect(wx+4, wy+chrome_h, ww-8, wh-chrome_h)
        else: 
            self._code_rect = QRect(wx+4, wy, ww-8, wh)
            
        if self.kb_overlay:
            if not kb_top:
                self.kb_overlay.reposition(wy + wh + max(8, self.height // 60))
            else:
                self.kb_overlay.reposition(start_y)
                
        p.end()

    @staticmethod
    def auto_font_size(lines_count, width, height, padding=24, show_chrome=True, show_ln=True, text=None, font_family="Consolas", keyboard_h=0, ascii_art_mode=False):
        chrome_h = 42 if show_chrome else 0
        max_ratio = 1.1 if not ascii_art_mode else float('inf')
        avail_h = height - 2*padding - keyboard_h
        if avail_h > width * max_ratio:
            avail_h = int(width * max_ratio)
            
        rh, rw = avail_h - chrome_h, width - 2*padding - 8
        if rh < 20 or rw < 40 or lines_count < 1: return 14
        max_chars = max(max(len(l.replace("\t", "    ")) for l in text.split("\n")), 1) if text else 80
        
        def lnw(cw): return (len(str(lines_count))*cw + 32 + int(cw * 1.5)) if show_ln else 0
        
        lo, hi, best = 8, max(14, min(128, int(width/40))), 14
        while lo <= hi:
            mid = (lo+hi)//2; fm = QFontMetrics(QFont(font_family, mid))
            if (lines_count if ascii_art_mode else min(lines_count, 35)) * fm.height() <= rh:
                cw = fm.horizontalAdvance("M")
                if (max_chars if ascii_art_mode else min(max_chars, 120)) * cw + lnw(cw) <= rw: best = mid; lo = mid + 1
                else: hi = mid - 1
            else: hi = mid - 1
        return max(8, best)

    def render_frame(self, display_chars, num_visible, cursor_visible=True, target=None, active_char=None, key_flash=0.0, title_text="", t=0.0, duration=0.0, hud_data=None, animator=None, draw_guides=False):
        img = target if target is not None else QImage(self.width, self.height, QImage.Format_RGB32)
        if target is None: img.fill(QColor(self.theme["background"]))
        p = QPainter(img)
        # Enable smooth scaling for zoom/focus, and antialiasing for text and shapes
        p.setRenderHints(QPainter.TextAntialiasing | QPainter.Antialiasing | QPainter.SmoothPixmapTransform)
        p.drawImage(0, 0, self._bg)
        cr = self._code_rect
        if self.show_window_chrome:
            p.setPen(QColor(self.theme["title_text"])); p.setFont(QFont(self.font_family, max(8, min(12, self.width // 80))))
            p.drawText(QRect(self.padding, cr.top() - 42, cr.width(), 42), Qt.AlignCenter, title_text)
            
        out = []
        for ch in display_chars[:num_visible]:
            if ch == "\b":
                if out: out.pop()
            else: out.append(ch)
        visible_text = "".join(out)
        
        is_bold = False; is_italic = False
        if self.config and self.config.mode == StudioMode.TEXT_EMOJI and self.config.txt_markdown:
            new_out = []
            i = 0
            while i < len(out):
                if "".join(out[i:i+2]) == "**": is_bold = not is_bold; i += 2; continue
                if out[i] == "*" and not is_bold: is_italic = not is_italic; i += 1; continue
                new_out.append(out[i]); i += 1
            out = new_out
        
        tokens = self._tokenize("".join(out))
        lines, current_line = [], []
        for color, val in tokens:
            if '\n' in val:
                parts = val.split('\n')
                for i, part in enumerate(parts):
                    if part: current_line.append((color, part))
                    if i < len(parts) - 1: lines.append(current_line); current_line = []
            else: current_line.append((color, val))
        lines.append(current_line)
        
        cursor_line = len(lines) - 1; total_lines = len(lines)
        max_vis = max(1, -(-cr.height() // self.line_h))
        scroll = max(0, min(cursor_line - max_vis + 5, total_lines - max_vis)) if cursor_line >= max_vis - 5 else max(0, cursor_line - 3)
        
        ln_gap = max(12, int(self.char_w * 1.5))
        ln_width = (len(str(total_lines + scroll)) * self.char_w + 32 + ln_gap) if self.show_line_numbers else 0
        x0, y_acc = cr.left() + ln_width, cr.top()
        
        
        focus_block_start, focus_block_end = -1, -1
        if self.config and self.config.mode == StudioMode.CODE_YT and self.config.yt_focus and self.language in ("python", "javascript", "typescript", "go", "rust", "ruby"):
            for i, line in enumerate(lines):
                line_str = "".join(v for _, v in line)
                if re.match(r'^\s*(def|class|func|fn)\s', line_str):
                    if i <= cursor_line: focus_block_start = i
                    elif i > cursor_line and focus_block_start != -1: focus_block_end = i; break
            if focus_block_start != -1 and focus_block_end == -1: focus_block_end = total_lines

        p.setClipRect(cr); p.setFont(self.font)
        
        for si in range(max_vis):
            li = scroll + si
            if li >= total_lines: break
            y = y_acc; y_acc += self.line_h
            
            if self.config and self.config.mode == StudioMode.TEXT_EMOJI and self.config.txt_bubbles:
                line_str = "".join(v for _, v in lines[li])
                line_w = 0
                for _, val in lines[li]:
                    for ch in val:
                        if ch == "\t": line_w += self._tab_adv
                        else: line_w += self.fm.horizontalAdvance(ch)
                bubble_w = min(cr.width() - 30, line_w + 30)
                bubble_rect = QRect(x0, y + 5, bubble_w, self.line_h - 10)
                if line_str.startswith("Me:"):
                    bubble_rect.moveRight(cr.right() - 10)
                    p.setBrush(QColor("#007AFF")); p.setPen(Qt.NoPen)
                else:
                    p.setBrush(QColor("#333333")); p.setPen(Qt.NoPen)
                p.drawRoundedRect(bubble_rect, 10, 10)
                x0_bubble = bubble_rect.left() + 10
            else:
                x0_bubble = x0

            bg_color = None
            if li == cursor_line: bg_color = self._qc_current_line
            if self.line_diffs.get(li) == 'added': bg_color = QColor(50, 200, 50, 40)
            elif self.line_diffs.get(li) == 'removed': bg_color = QColor(255, 50, 50, 40)
            if bg_color and not (self.config and self.config.mode == StudioMode.TEXT_EMOJI and self.config.txt_bubbles): 
                p.fillRect(cr.left(), y, cr.width(), self.line_h, bg_color)
            
            if self.show_line_numbers and ln_width > 0:
                p.setPen(self._qc_ln)
                p.drawText(QRect(cr.left(), y, ln_width - ln_gap, self.line_h), Qt.AlignRight | Qt.AlignVCenter, str(li + 1))

            line_tokens = lines[li]
            if not line_tokens:
                if cursor_visible and li == cursor_line: self._draw_caret(p, int(x0), int(y + self.line_h * 0.15), max(4, self.line_h - 10))
                continue
            
            line_w = 0
            for _, val in line_tokens:
                for ch in val:
                    if ch == "\t": line_w += self._tab_adv
                    else: line_w += self.fm.horizontalAdvance(ch)
                    
            if self.ascii_art_mode:
                x = x0 + (cr.width() - ln_width - line_w) // 2
            else: x = x0_bubble
                
            opacity = 1.0
            if focus_block_start != -1 and not (focus_block_start <= li < focus_block_end):
                opacity = 0.3
                
            for color, val in line_tokens:
                if opacity < 1.0:
                    dim_color = QColor(color); dim_color.setAlpha(int(255 * opacity))
                    p.setPen(dim_color)
                else:
                    p.setPen(color)
                
                if is_bold or is_italic:
                    f = QFont(self.font); f.setBold(is_bold); f.setItalic(is_italic); p.setFont(f)
                else: p.setFont(self.font)
                
                ts_list = animator._timestamps if animator and hasattr(animator, '_timestamps') else []
                char_ts = ts_list[num_visible-1] if num_visible > 0 and num_visible <= len(ts_list) else 0
                is_pop_char = is_emoji(val) and t - char_ts < 0.15 and t - char_ts >= 0
                
                for ch in val:
                    if ch == "\t":
                        x += self._tab_adv
                    else:
                        ch_w = self.fm.horizontalAdvance(ch)
                        if is_pop_char:
                            p.save()
                            progress = max(0, 1.0 - (t - char_ts) / 0.15)
                            pop_scale = 1.0 + 0.5 * progress
                            cx = x + ch_w / 2
                            cy = y + self.line_h * 0.5
                            p.translate(cx, cy); p.scale(pop_scale, pop_scale); p.translate(-cx, -cy)
                            p.drawText(QRect(int(x), int(y), int(ch_w) + 10, int(self.line_h)), Qt.AlignLeft | Qt.AlignVCenter, ch)
                            p.restore()
                        else:
                            p.drawText(QRect(int(x), int(y), int(ch_w) + 10, int(self.line_h)), Qt.AlignLeft | Qt.AlignVCenter, ch)
                        x += ch_w
            if cursor_visible and li == cursor_line: self._draw_caret(p, int(x), int(y))
                
        p.setClipping(False)

        if self.kb_overlay and active_char and key_flash > 0:
            ak = self.kb_overlay.resolve_key(active_char)
            if ak: self.kb_overlay.draw(p, active_key=ak, flash=key_flash)
            
        if draw_guides:
            p.setRenderHint(QPainter.Antialiasing)
            p.setPen(QPen(QColor(255, 0, 0, 150), 2, Qt.DashLine)); p.setBrush(Qt.NoBrush)
            p.drawRect(24, 24, self.width - 48, self.height - 48)
            if self.show_window_chrome:
                p.setPen(QPen(QColor(0, 255, 0, 150), 2, Qt.DashLine)); p.setBrush(Qt.NoBrush)
                p.drawRect(self._code_rect.left()-4, self._code_rect.top()-42, self._code_rect.width()+8, 42)
            p.setPen(QPen(QColor(0, 150, 255, 150), 2, Qt.DashLine)); p.setBrush(Qt.NoBrush)
            p.drawRect(self._code_rect)
        
        p.end()
        return img

    def _draw_caret(self, p, x, y, h=None):
        w = max(2, self.font_size // 10)
        pad = (self.line_h - self.fm.height()) // 2
        caret_y = y + pad + 1
        caret_h = self.fm.height() - 2
        
        # Shift glow to start at 'x' instead of 'x-w' so it doesn't overlap the previous character
        gc = QColor(self._qc_cursor); gc.setAlpha(60); p.fillRect(x, caret_y-2, w*3, caret_h+4, gc)
        gc.setAlpha(100); p.fillRect(x, caret_y-1, w*2, caret_h+2, gc)
        
        p.fillRect(x, caret_y, w, caret_h, self._qc_cursor)


class MultiPaneRenderer:
    @staticmethod
    def compute_pane_rects(frame_w, frame_h, num_panes, layout, gap=20, config=None):
        W, H, g, n = frame_w, frame_h, gap, num_panes
        if n == 1: return [QRect(0, 0, W, H)]
        if n == 2:
            if config and config.mode == StudioMode.MULTI_WINDOW:
                ratio = config.mw_ratio / 100.0
                if W < H: 
                    ph = int((H-g) * ratio)
                    return [QRect(0, 0, W, ph), QRect(0, ph+g, W, H-ph-g)]
                else:
                    pw = int((W-g) * ratio)
                    return [QRect(0, 0, pw, H), QRect(pw+g, 0, W-g-pw, H)]
            if "Stacked" in layout:
                ph = (H-g)//2
                return [QRect(0, (H-(2*ph+g))//2, W, ph), QRect(0, (H-(2*ph+g))//2+ph+g, W, ph)]
            if "Junior Big" in layout:
                pw = int((W-g)*0.7)
                return [QRect(0, 0, pw, H), QRect(pw+g, 0, W-g-pw, H)]
            if "Senior Big" in layout:
                pw = int((W-g)*0.3)
                return [QRect(0, 0, pw, H), QRect(pw+g, 0, W-g-pw, H)]
            pw = (W-g)//2
            return [QRect(0, 0, pw, H), QRect(pw+g, 0, W-pw-g, H)]
        if n == 3:
            if W < H: 
                ph = (H - 2 * g) // 3
                return [QRect(0, 0, W, ph), QRect(0, ph + g, W, ph), QRect(0, 2 * (ph + g), W, H - 2 * (ph + g))]
            pw = (W - 2 * g) // 3
            return [
                QRect(0, 0, pw, H),
                QRect(pw + g, 0, pw, H),
                QRect(2 * (pw + g), 0, W - 2 * (pw + g), H)
            ]
        pw, ph = (W-g)//2, (H-g)//2
        return [QRect(0, 0, pw, ph), QRect(pw+g, 0, W-pw-g, ph), QRect(0, ph+g, pw, H-ph-g), QRect(pw+g, ph+g, W-pw-g, H-ph-g)]

    def __init__(self, panes, frame_w, frame_h, num_panes, layout, gap=20, bg_color="#0d0d12", config=None):
        self.panes = panes
        self.frame_w, self.frame_h = frame_w, frame_h
        self.num_panes, self.layout, self.gap = num_panes, layout, gap
        self.bg_color = bg_color
        self.config = config
        self.pane_rects = self.compute_pane_rects(frame_w, frame_h, num_panes, layout, gap, config)

    def _compute_pane_rects(self):
        return self.compute_pane_rects(self.frame_w, self.frame_h, self.num_panes, self.layout, self.gap, self.config)
    
    def duration(self): return max(a.duration() for _, a, _ in self.panes) if self.panes else 0.0
    def char_timestamps_all(self):
        ts = []
        for _, a, _ in self.panes: ts.extend(a.char_timestamps())
        return ts
    
    def render_frame(self, t, target=None, draw_guides=False):
        img = target if target is not None else QImage(self.frame_w, self.frame_h, QImage.Format_RGB32)
        img.fill(QColor(self.bg_color))
        p = QPainter(img); p.setRenderHint(QPainter.SmoothPixmapTransform)

        for i, (renderer, animator, title) in enumerate(self.panes):
            if i >= len(self.pane_rects): break
            rect = self.pane_rects[i]
            nv = animator.visible_at(t)
            cv = True  
            ac, kf = animator.active_key_at(t)
                        
            scale = 1.0
            if self.config and self.config.mode == StudioMode.CODE_YT and self.config.yt_zoom and t < animator.duration():
                progress = t / animator.duration()
                scale = 1.0 + 0.1 * progress

            pane_img = renderer.render_frame(
                animator.display_chars, nv, cv, active_char=ac, key_flash=kf,
                title_text=title,
                target=QImage(rect.width(), rect.height(), QImage.Format_RGB32),
                t=t, duration=animator.duration(), animator=animator, draw_guides=draw_guides
            )
            
            if scale > 1.0:
                pw, ph = rect.width(), rect.height()
                sw, sh = int(pw * scale), int(ph * scale)
                scaled_img = pane_img.scaled(sw, sh, Qt.KeepAspectRatioByExpanding, Qt.SmoothTransformation)
                x = rect.left() - (sw - pw) // 2
                y = rect.top() - (sh - ph) // 2
                p.drawImage(x, y, scaled_img)
            else:
                p.drawImage(rect.topLeft(), pane_img)
                
        p.end()
        return img

# =====================================================================
# 7. PATTERN 2: STRATEGY PATTERN (Rendering Modes)
# =====================================================================

def get_line_diffs(code1, code2):
    lines1 = code1.splitlines()
    lines2 = code2.splitlines()
    sm = difflib.SequenceMatcher(None, lines1, lines2)
    diffs1, diffs2 = {}, {}
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ('replace', 'delete'):
            for i in range(i1, i2): diffs1[i] = 'removed'
        if tag in ('replace', 'insert'):
            for j in range(j1, j2): diffs2[j] = 'added'
    return diffs1, diffs2

class BaseRenderStrategy(ABC):
    @abstractmethod
    def build_panes(self, config: StudioConfig, files: List['FileItem'], custom_code: str) -> Optional[MultiPaneRenderer]: pass

    def _get_code(self, config, files, custom_code):
        if config.use_custom:
            code = convert_shortcodes(custom_code)
            return (code if code.strip() else "# Custom code empty", "python", "custom_code.py")
        checked = [f for f in files if f.checked]
        if not checked: return ("import numpy as np\n\ndef hello():\n    print('Add files to begin!')", "python", "preview.py")
        it = checked[0]
        code = read_text_file(it.path, config.txt_clean)
        if config.mode == StudioMode.TEXT_EMOJI and not config.ansi_colors:
            code = re.sub(r'\x1b\[[0-9;]*m', '', code)
        return (code, EXT_TO_LANGUAGE.get(os.path.splitext(it.path)[1].lower(), "text"), os.path.basename(it.path))

    def _make_renderer(self, config, w, h, code, title, lang, pane_idx=0, line_diffs=None):
        if config.mode == StudioMode.MULTI_WINDOW:
            suffix = "" if pane_idx == 0 else f"_{pane_idx+1}"
            font_fam = getattr(config, f"font_mw{suffix}")
            f_auto = getattr(config, f"font_sz_auto_mw{suffix}")
            f_sz = getattr(config, f"font_sz_mw{suffix}")
        elif config.mode == StudioMode.JR_VS_SR:
            if pane_idx == 0:
                font_fam = config.font_jr; f_auto = config.font_sz_auto_jr; f_sz = config.font_sz_jr
            else:
                font_fam = config.font_sr; f_auto = config.font_sz_auto_sr; f_sz = config.font_sz_sr
        elif config.mode == StudioMode.CODE_YT:
            font_fam = config.font_yt; f_auto = config.font_sz_auto_yt; f_sz = config.font_sz_yt
        elif config.mode == StudioMode.TEXT_EMOJI:
            font_fam = config.font_txt; f_auto = config.font_sz_auto_txt; f_sz = config.font_sz_txt
        else:
            font_fam = "Consolas"; f_auto = True; f_sz = 22

        kb_h = 0
        if config.kb_enabled:
            kb_h = int(w * 0.65 / 15 * 0.82) * 5 + 20 
            
        fsz = StudioRenderer.auto_font_size(code.count("\n")+1, w, h, text=code, font_family=font_fam, keyboard_h=kb_h, ascii_art_mode=config.ascii_art) if f_auto else f_sz
        kb = None
        if config.kb_enabled:
            pos_str = config.kb_position.lower().replace(" ", "_")
            kb = KeyboardOverlay(w, h, config.kb_layout, THEMES.get(config.theme, THEMES["Dracula"]), config.kb_opacity, (h-2*24)//3, pos_str)
        return StudioRenderer(w, h, config.theme, font_fam, fsz, language=EXT_TO_LANGUAGE.get(os.path.splitext(title)[1].lower(), lang), ascii_art_mode=config.ascii_art, config=config, pane_idx=pane_idx, line_diffs=line_diffs, kb_overlay=kb)
    
    def _make_animator(self, code, wpm, tr=0.0, is_text=False):
        return TypingAnimator(code, TypingProfile(wpm=wpm, typo_rate=tr, is_text=is_text))

class MultiWindowStrategy(BaseRenderStrategy):
    def build_panes(self, config, files, custom_code):
        w, h = RESOLUTIONS.get(config.resolution, (1920, 1080))
        n_panes = MULTI_WINDOW_LAYOUTS[config.layout_mw]
        gap = 20
        pane_rects = MultiPaneRenderer.compute_pane_rects(w, h, n_panes, "Grid", gap, config)
        
        codes = []
        if config.use_custom:
            c, l, t = self._get_code(config, files, custom_code)
            for _ in range(n_panes): codes.append((c, l, t))
        else:
            checked = [f for f in files if f.checked]
            if not checked:
                c, l, t = self._get_code(config, files, custom_code)
                for _ in range(n_panes): codes.append((c, l, t))
            else:
                for i in range(n_panes):
                    if i < len(checked):
                        it = checked[i]
                        codes.append((read_text_file(it.path, config.txt_clean), EXT_TO_LANGUAGE.get(os.path.splitext(it.path)[1].lower(), "text"), os.path.basename(it.path)))
                    else:
                        codes.append(codes[0])

        if config.sync_mw:
            base_dur = max(TypingAnimator(c, TypingProfile(wpm=config.wpm_mw)).duration() for c, _, _ in codes)
            wpms = [TypingAnimator.find_wpm_for_target(c, base_dur, 0.5, 1.5) for c, _, _ in codes]
        else:
            wpms = [config.wpm_mw] * n_panes

        diffs = [None] * n_panes
        if config.diff_highlight_mw and n_panes >= 2:
            d01_0, d01_1 = get_line_diffs(codes[0][0], codes[1][0])
            diffs[0] = d01_0; diffs[1] = d01_1
            if n_panes >= 3:
                d12_1, d12_2 = get_line_diffs(codes[1][0], codes[2][0])
                merged_1 = {}
                for k, v in d01_1.items(): merged_1[k] = v
                for k, v in d12_1.items(): merged_1[k] = v
                diffs[1] = merged_1; diffs[2] = d12_2
            if n_panes >= 4:
                d23_2, d23_3 = get_line_diffs(codes[2][0], codes[3][0])
                merged_2 = {}
                for k, v in (diffs[2] or {}).items(): merged_2[k] = v
                for k, v in d23_2.items(): merged_2[k] = v
                diffs[2] = merged_2; diffs[3] = d23_3

        git_titles = ["Base", "Incoming", "Resolved"]
        panes = []
        for i in range(n_panes):
            code, lang, title = codes[i]
            animator = self._make_animator(code, wpms[i], tr=config.typo_mw)
            if n_panes == 3 and config.layout_mw == "Git Conflict (3-Pane)":
                title_text = f"{git_titles[i]} - {title}"
            else:
                title_text = title
            rect = pane_rects[i]
            renderer = self._make_renderer(config, rect.width(), rect.height(), code, title, lang, i, diffs[i])
            panes.append((renderer, animator, title_text))
        return MultiPaneRenderer(panes, w, h, n_panes, "Grid", gap=gap, config=config)

class JrVsSrStrategy(BaseRenderStrategy):
    def build_panes(self, config, files, custom_code):
        w, h = RESOLUTIONS.get(config.resolution, (1920, 1080))
        gap = 20
        pane_rects = MultiPaneRenderer.compute_pane_rects(w, h, 2, config.layout_jr, gap, config)
        
        if config.use_custom or (config.jr_custom_code and config.sr_custom_code):
            code1 = convert_shortcodes(config.jr_custom_code) if config.jr_custom_code else "def junior():\n    pass"
            code2 = convert_shortcodes(config.sr_custom_code) if config.sr_custom_code else "def senior():\n    pass"
            lang, t1, t2 = "python", "junior.py", "senior.py"
        else:
            checked = [f for f in files if f.checked]
            if not checked:
                c, l, t = self._get_code(config, files, custom_code)
                code1, code2, lang, t1, t2 = c, c, l, t, t
            else:
                it = checked[0]
                ext = os.path.splitext(it.path)[1].lower()
                if ext == ".json":
                    try:
                        with open(it.path, "r", encoding="utf-8") as f: data = json.load(f)
                        code1 = convert_shortcodes(data.get("junior_code", "")); code2 = convert_shortcodes(data.get("senior_code", ""))
                        lang = data.get("language", "python"); title = data.get("title", os.path.basename(it.path))
                        t1, t2 = f"{title} (Junior)", f"{title} (Senior)"
                        if not code1.strip(): code1 = "# Junior code missing in JSON"
                        if not code2.strip(): code2 = "# Senior code missing in JSON"
                    except:
                        c, l, t = self._get_code(config, files, custom_code)
                        code1, code2, lang, t1, t2 = c, c, l, t, t
                else:
                    c, l, t = self._get_code(config, files, custom_code)
                    code1, code2, lang, t1, t2 = c, c, l, t, t
                    
        a1 = self._make_animator(code1, config.jr_wpm, tr=config.typo_jr); a2 = self._make_animator(code2, config.sr_wpm, tr=0.0)
        r1 = self._make_renderer(config, pane_rects[0].width(), pane_rects[0].height(), code1, t1, lang, 0)
        r2 = self._make_renderer(config, pane_rects[1].width(), pane_rects[1].height(), code2, t2, lang, 1)
        return MultiPaneRenderer([(r1, a1, f"👶 Junior - {t1}"), (r2, a2, f"🧓 Senior - {t2}")], w, h, 2, config.layout_jr, gap=gap, config=config)

class CodeYTStrategy(BaseRenderStrategy):
    def build_panes(self, config, files, custom_code):
        w, h = RESOLUTIONS.get(config.resolution, (1920, 1080))
        code, lang, title = self._get_code(config, files, custom_code)
        wpm = config.wpm_yt
        a = self._make_animator(code, wpm, tr=config.typo_yt)
        return MultiPaneRenderer([(self._make_renderer(config, w, h, code, title, lang), a, title)], w, h, 1, "Single", config=config)

class TextEmojiStrategy(BaseRenderStrategy):
    def build_panes(self, config, files, custom_code):
        w, h = RESOLUTIONS.get(config.resolution, (1920, 1080))
        code, lang, title = self._get_code(config, files, custom_code)
        wpm = TypingAnimator.find_wpm_for_target(code, 179.0, 0.5, 1.5) if config.shorts_txt else config.wpm_txt
        a = self._make_animator(code, wpm, is_text=True)
        return MultiPaneRenderer([(self._make_renderer(config, w, h, code, title, lang), a, title)], w, h, 1, "Single", config=config)

# =====================================================================
# 8. PATTERN 6: COMMAND PATTERN (Export Queueing)
# =====================================================================

@dataclass
class ExportCommand:
    item: 'FileItem'; output_path: str; config: StudioConfig
    mp: Optional[MultiPaneRenderer] = None
    status: str = "Pending"

# =====================================================================
# 9. PATTERN 3: PRODUCER-CONSUMER PATTERN (Parallel Rendering)
# =====================================================================

class VideoExporter(QThread):
    progress = Signal(int); status = Signal(str); finished_ok = Signal(str); error = Signal(str)

    def __init__(self, command: ExportCommand):
        super().__init__()
        self.command = command; self.mp = command.mp; self.output = command.output_path; self.fps = command.config.fps
        self.config = command.config; self._cancel = threading.Event(); self.w, self.h = self.mp.frame_w, self.mp.frame_h

    def cancel(self): self._cancel.set()

    def _apply_crt_filter(self, img):
        p = QPainter(img); p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80))
        for y in range(0, self.h, 3): p.drawRect(0, y, self.w, 1)
        p.setBrush(QColor(0, 255, 0, 20)); p.drawRect(0, 0, self.w, self.h); p.end()

    def run(self):
        tmp = tempfile.mkdtemp(dir=str(TEMP_DIR), prefix="export_")
        try:
            total_dur = self.mp.duration()
            n_frames = int(total_dur * self.fps); audio_path = os.path.join(tmp, "audio.wav")
            
            cmd = ["ffmpeg", "-y", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{self.w}x{self.h}", "-r", str(self.fps), "-sws_flags", "lanczos+accurate_rnd+full_chroma_int", "-i", "pipe:0"]
            has_audio = False

            if self.config.sound_enabled:
                if self.config.mode == StudioMode.JR_VS_SR:
                    sg1 = SimpleSoundGen(preset=self.config.jr_sound, stereo=self.config.stereo)
                    pcm1 = sg1.generate_pcm(self.mp.panes[0][1].char_timestamps(), 1.0)
                    sg2 = SimpleSoundGen(preset=self.config.sr_sound, stereo=self.config.stereo)
                    pcm2 = sg2.generate_pcm(self.mp.panes[1][1].char_timestamps(), 1.0)

                    max_len = max(len(pcm1), len(pcm2))
                    mix = np.zeros(max_len, dtype=np.int32)
                    mix[:len(pcm1)] += pcm1
                    mix[:len(pcm2)] += pcm2
                    pcm = np.clip(mix, -32768, 32767).astype(np.int16)

                    with wave.open(audio_path, "w") as wf: wf.setnchannels(2 if self.config.stereo else 1); wf.setsampwidth(2); wf.setframerate(sg1.sr); wf.writeframes(pcm.tobytes())
                else:
                    sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo); pcm = sg.generate_pcm(self.mp.char_timestamps_all(), 1.0)
                    with wave.open(audio_path, "w") as wf: wf.setnchannels(2 if sg.stereo else 1); wf.setsampwidth(2); wf.setframerate(sg.sr); wf.writeframes(pcm.tobytes())
                cmd += ["-i", audio_path]; has_audio = True
            has_bgm = False
            if self.config.bgm_path and os.path.exists(self.config.bgm_path): cmd += ["-i", self.config.bgm_path]; has_bgm = True
                
            if has_audio and has_bgm:
                if self.config.bgm_duck: cmd += ["-filter_complex", f"[2:a]volume={self.config.bgm_volume/100.0}[bgm];[bgm][1:a]sidechaincompress=threshold=0.05:ratio=8:attack=5:release=200[bgm_duck];[1:a][bgm_duck]amix=inputs=2:duration=longest[aout]"]
                else: cmd += ["-filter_complex", f"[2:a]volume={self.config.bgm_volume/100.0}[bgm];[1:a][bgm]amix=inputs=2:duration=longest[aout]"]
                cmd += ["-map", "0:v", "-map", "[aout]"]
            elif has_audio: cmd += ["-map", "0:v", "-map", "1:a"]
            else: cmd += ["-map", "0:v"]
                
            if "YouTube Optimised" in self.config.encoder:
                pixels = self.w * self.h; maxrate = int((pixels / 2073600.0) * 12000000); bufsize = maxrate * 2
                cmd += ["-c:v", "libx264", "-preset", "slow", "-crf", "17", "-maxrate", f"{maxrate}", "-bufsize", f"{bufsize}", "-pix_fmt", "yuv420p", "-profile:v", "high", "-g", str(self.fps*2), "-keyint_min", str(self.fps*2), "-sc_threshold", "0", "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709", "-color_range", "tv"]
            elif "NVENC (NVIDIA)" in self.config.encoder:
                cmd += ["-c:v", "h264_nvenc", "-preset", "p5", "-rc", "vbr", "-cq", "19", "-b:v", "0", "-pix_fmt", "yuv420p", "-profile:v", "high", "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709", "-color_range", "tv"]
            elif "QSV (Intel)" in self.config.encoder:
                cmd += ["-c:v", "h264_qsv", "-preset", "slow", "-global_quality", "19", "-pix_fmt", "yuv420p", "-profile:v", "high", "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709", "-color_range", "tv"]
            elif "AMF (AMD)" in self.config.encoder:
                cmd += ["-c:v", "h264_amf", "-preset", "quality", "-rc", "cqp", "-qp_i", "19", "-qp_p", "19", "-pix_fmt", "yuv420p", "-profile:v", "high", "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709", "-color_range", "tv"]
            else: 
                cmd += ["-c:v", "libx264", "-preset", "slow", "-crf", "17", "-pix_fmt", "yuv420p", "-profile:v", "high", "-color_primaries", "bt709", "-color_trc", "bt709", "-colorspace", "bt709", "-color_range", "tv"]

            if has_audio or has_bgm: cmd += ["-c:a", "aac", "-b:a", "256k"]
            cmd += ["-movflags", "+faststart", self.output]
            
            si = subprocess.STARTUPINFO()
            if platform.system() == "Windows": si.dwFlags |= subprocess.STARTF_USESHOWWINDOW; si.wShowWindow = subprocess.SW_HIDE
            proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, startupinfo=si)
            
            frame_queue = queue.Queue(maxsize=60)
            def render_worker(fi):
                try:
                    if self._cancel.is_set(): return
                    t = fi / self.fps; img = QImage(self.w, self.h, QImage.Format_RGB32); img = self.mp.render_frame(t, img)
                    if self.config.txt_crt: self._apply_crt_filter(img)
                    
                    # PySide6 returns a memoryview directly, so we can pass it straight to numpy
                    ptr = img.constBits()
                    arr = np.frombuffer(ptr, dtype=np.uint8).reshape((self.h, img.bytesPerLine() // 4, 4))
                    frame_queue.put(np.ascontiguousarray(arr[:, :, 2::-1]).tobytes())
                except Exception:
                    logger.error(f"Error rendering frame {fi}", exc_info=True)
                    frame_queue.put(None) # Sentinel for error
                    
            max_workers = max(2, (os.cpu_count() or 4) - 1)
            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                futures = [executor.submit(render_worker, fi) for fi in range(n_frames)]
                thumb_pcts = [0.25, 0.50, 0.75] if self.config.yt_extras else []; thumb_idx = 0
                for fi in range(n_frames):
                    if self._cancel.is_set(): break
                    try: frame_data = frame_queue.get(timeout=10)
                    except queue.Empty:
                        if self._cancel.is_set(): break
                        self.error.emit("Rendering timed out."); break
                        
                    if frame_data is None:
                        self.error.emit("Frame rendering failed.")
                        break
                        
                    try:
                        proc.stdin.write(frame_data)
                    except BrokenPipeError:
                        stderr_output = proc.stderr.read().decode('utf-8', errors='ignore') if proc.stderr else ""
                        self.error.emit(f"FFmpeg crashed:\n{stderr_output[:500]}")
                        self._cancel.set()
                        break
                        
                    if thumb_idx < len(thumb_pcts) and fi == int(n_frames * thumb_pcts[thumb_idx]):
                        thumb_path = os.path.splitext(self.output)[0] + f"_thumb_{thumb_idx+1}.jpg"
                        self.mp.render_frame(fi / self.fps, QImage(self.w, self.h, QImage.Format_RGB32)).save(thumb_path, "JPG", 95); thumb_idx += 1
                    if fi % 30 == 0: self.progress.emit(int(fi / n_frames * 100)); self.status.emit(f"Rendering frame {fi}/{n_frames}...")
                        
            try:
                proc.stdin.close()
                if self._cancel.is_set(): proc.kill()
                proc.wait(timeout=30)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            except Exception:
                pass

            if not self._cancel.is_set(): self.progress.emit(100); self.finished_ok.emit(self.output)
            else: self.error.emit("Cancelled")
        except Exception as e: 
            logger.error(f"Export failed for {self.output}", exc_info=True)
            self.error.emit(str(e))
        finally: shutil.rmtree(tmp, ignore_errors=True)

# =====================================================================
# 10. MAIN WINDOW & GUI (Dedicated Tabs for each Mode)
# =====================================================================

@dataclass
class FileItem:
    path: str; checked: bool = False; status: str = "Pending"

class BatchTableWidget(QTableWidget):
    def __init__(self, rows=0, columns=0, parent=None):
        super().__init__(rows, columns, parent); self._checkbox_anchor = None

    def mousePressEvent(self, event: QEvent) -> None:
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

        if (modifiers & Qt.ShiftModifier) and self._checkbox_anchor is not None and self._checkbox_anchor != row:
            anchor = self._checkbox_anchor
            lo, hi = min(anchor, row), max(anchor, row)
            self.blockSignals(True)
            for i in range(lo, hi + 1):
                ci = self.item(i, 0)
                if ci is not None:
                    ci.setCheckState(Qt.CheckState.Checked if new_state else Qt.CheckState.Unchecked)
            self.blockSignals(False)
            self.itemChanged.emit(chk_item)
        else:
            if item.column() != 0:
                chk_item.setCheckState(Qt.CheckState.Checked if new_state else Qt.CheckState.Unchecked)
            self._checkbox_anchor = row
            self.itemChanged.emit(chk_item)

        if item.column() != 0:
            super().mousePressEvent(event)

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Unified Typing Video Studio (Ultimate UI Edition)"); self.resize(1400, 900)
        self.config = StudioConfig()
        global FONT_FAMILIES
        FONT_FAMILIES = _get_system_fonts()
        self.strategies = {StudioMode.MULTI_WINDOW: MultiWindowStrategy(), StudioMode.JR_VS_SR: JrVsSrStrategy(), StudioMode.CODE_YT: CodeYTStrategy(), StudioMode.TEXT_EMOJI: TextEmojiStrategy()}
        self.export_commands = deque(); self.current_command = None
        self._items, self._item_paths = [], set(); self._exporter = None
        self._batch_cancelled = False
        self.batch_total = 0; self.batch_done = 0; self.batch_start_time = 0
        
        self._preview_animating = False; self._preview_anim_t = 0.0; self._preview_progress = 0.3
        self._debounce_timer = QTimer(self); self._debounce_timer.setSingleShot(True); self._debounce_timer.setInterval(200); self._debounce_timer.timeout.connect(self._invalidate_preview)
        self._preview_timer = QTimer(self); self._preview_timer.setInterval(33); self._preview_timer.timeout.connect(self._advance_preview)
        self._cached_mp = None; self._preview_scratch = None
        self._audio_player = QMediaPlayer(); self._audio_out = QAudioOutput(); self._audio_player.setAudioOutput(self._audio_out); self._audio_buf = None
        self._build_ui(); self._connect_signals(); self._load_settings(); self._scan_dir(str(INPUT_DIR))
        QTimer.singleShot(500, self._update_preview)

    def _build_ui(self):
        root = QSplitter(Qt.Horizontal)
        self.setCentralWidget(root)
        
        left = QWidget()
        left.setMinimumWidth(420)
        left_layout = QVBoxLayout(left); left_layout.setContentsMargins(0, 0, 0, 0); left_layout.setSpacing(0)
        
        header = QFrame(); header.setFixedHeight(40); header.setStyleSheet("QFrame { background: #1e1e2e; border-bottom: 1px solid #11111b; }")
        hl = QHBoxLayout(header); hl.setContentsMargins(12, 0, 8, 0)
        hdr_lbl = QLabel("📂 GLOBAL SETTINGS"); hdr_lbl.setStyleSheet("font-weight: bold; color: #cdd6f4;"); hl.addWidget(hdr_lbl); hl.addStretch()
        left_layout.addWidget(header)
        
        self.common_tabs = QTabWidget(); self.common_tabs.setDocumentMode(True)
        left_layout.addWidget(self.common_tabs, 1)
        
        # ===================== FILES TAB =====================
        file_batch_widget = QWidget()
        ll = QVBoxLayout(file_batch_widget); ll.setContentsMargins(8, 8, 8, 8); ll.setSpacing(8)
        
        br1 = QHBoxLayout(); br1.setContentsMargins(0, 0, 0, 0)
        self.scan_btn = QPushButton("🔄 Scan"); self.scan_btn.clicked.connect(lambda: self._scan_dir(str(INPUT_DIR))); br1.addWidget(self.scan_btn)
        self.add_btn = QPushButton("➕ Add"); self.add_btn.clicked.connect(self._add_files); br1.addWidget(self.add_btn)
        self.clear_btn = QPushButton("✖ Clear"); self.clear_btn.clicked.connect(self._clear_list); br1.addWidget(self.clear_btn)
        br1.addStretch()
        self.recursive_chk = QCheckBox("Sub"); self.recursive_chk.setChecked(True); br1.addWidget(self.recursive_chk)
        br1.addWidget(QLabel("Depth:"))
        self.depth_sp = QSpinBox(); self.depth_sp.setRange(1, 99); self.depth_sp.setValue(10); self.depth_sp.setFixedWidth(50); br1.addWidget(self.depth_sp)
        ll.addLayout(br1)

        sel_row = QHBoxLayout(); sel_row.setContentsMargins(0, 0, 0, 0)
        self.select_all_btn = QPushButton("☑ All"); self.select_all_btn.clicked.connect(self._select_all); sel_row.addWidget(self.select_all_btn)
        self.deselect_all_btn = QPushButton("☐ None"); self.deselect_all_btn.clicked.connect(self._deselect_all); sel_row.addWidget(self.deselect_all_btn)
        self.select_visible_btn = QPushButton("☑ Vis"); self.select_visible_btn.setToolTip("Select all files matching current filter")
        self.select_visible_btn.clicked.connect(self._select_visible); sel_row.addWidget(self.select_visible_btn)
        self.deselect_visible_btn = QPushButton("☐ Vis"); self.deselect_visible_btn.setToolTip("Deselect all files matching current filter")
        self.deselect_visible_btn.clicked.connect(self._deselect_visible); sel_row.addWidget(self.deselect_visible_btn)
        sel_row.addStretch()
        sel_count_lbl = QLabel("0 selected"); sel_count_lbl.setStyleSheet("color: #a6adc8; font-size: 11px;")
        sel_row.addWidget(sel_count_lbl); self._sel_count_lbl = sel_count_lbl
        ll.addLayout(sel_row)
        
        filter_row = QHBoxLayout(); filter_row.setContentsMargins(0, 0, 0, 0); filter_row.setSpacing(4)
        filter_row.addWidget(QLabel("Filter:"))
        self.filter_edit = QLineEdit(); self.filter_edit.setPlaceholderText("Name/path contains...")
        self.filter_edit.setClearButtonEnabled(True)
        self.filter_edit.textChanged.connect(self._apply_filter)
        filter_row.addWidget(self.filter_edit, 1)

        self.type_filter_cb = QComboBox(); self.type_filter_cb.setToolTip("Filter by file category/type")
        self.type_filter_cb.addItems(list(FILE_CATEGORIES.keys()))
        self.type_filter_cb.currentIndexChanged.connect(self._apply_filter)
        self.type_filter_cb.setMaximumWidth(120)
        filter_row.addWidget(self.type_filter_cb)

        self.ext_filter_cb = QComboBox(); self.ext_filter_cb.setToolTip("Filter by extension")
        self.ext_filter_cb.addItem("📂 All")
        _common_exts = [".py", ".js", ".ts", ".tsx", ".jsx", ".java", ".cpp", ".c", ".h", ".cs", ".go", ".rs", ".rb", ".php", ".swift", ".kt", ".sh", ".html", ".css", ".json", ".yaml", ".yml", ".toml", ".md", ".txt", ".csv", ".asc", ".ascii", ".art", ".ans", ".nfo", ".diz", ".emoji", ".emo"]
        _other_exts = sorted([e for e in SUPPORTED_EXTENSIONS if e not in _common_exts])
        for ext in _common_exts + _other_exts:
            self.ext_filter_cb.addItem(ext)
        self.ext_filter_cb.currentIndexChanged.connect(self._apply_filter)
        self.ext_filter_cb.setMaximumWidth(100)
        filter_row.addWidget(self.ext_filter_cb)

        self.case_chk = QCheckBox("Aa"); self.case_chk.setToolTip("Case-sensitive filter")
        self.case_chk.toggled.connect(self._apply_filter)
        filter_row.addWidget(self.case_chk)

        self.clear_filter_btn = QPushButton("✖"); self.clear_filter_btn.setFixedWidth(28)
        self.clear_filter_btn.setToolTip("Clear filter")
        self.clear_filter_btn.clicked.connect(self._clear_filter)
        filter_row.addWidget(self.clear_filter_btn)
        ll.addLayout(filter_row)

        folder_row = QHBoxLayout(); folder_row.setContentsMargins(0, 0, 0, 0); folder_row.setSpacing(4)
        folder_row.addWidget(QLabel("Folder:"))
        self.folder_filter_cb = QComboBox(); self.folder_filter_cb.setToolTip("Filter by subfolder")
        self.folder_filter_cb.addItem("📁 All Folders")
        self.folder_filter_cb.currentIndexChanged.connect(self._apply_filter)
        folder_row.addWidget(self.folder_filter_cb, 1)

        self.sync_mode_btn = QPushButton("🪄 Sync to Mode")
        self.sync_mode_btn.setToolTip("Set Type filter based on the current rendering mode (Code vs Text)")
        self.sync_mode_btn.clicked.connect(self._sync_filter_to_mode)
        folder_row.addWidget(self.sync_mode_btn)
        ll.addLayout(folder_row)
        
        self.table = BatchTableWidget(0, 3); self.table.setHorizontalHeaderLabels(["", "File", "Status"])
        self.table.setSelectionBehavior(QTableWidget.SelectRows); self.table.setEditTriggers(QTableWidget.NoEditTriggers)
        self.table.verticalHeader().setVisible(False); self.table.itemChanged.connect(self._on_item_changed)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu); self.table.customContextMenuRequested.connect(self._on_table_context_menu)
        hdr = self.table.horizontalHeader()
        hdr.setSectionResizeMode(0, QHeaderView.Fixed); hdr.resizeSection(0, 36)
        hdr.setSectionResizeMode(1, QHeaderView.Stretch); hdr.setSectionResizeMode(2, QHeaderView.Fixed); hdr.resizeSection(2, 100)
        ll.addWidget(self.table)
        
        self.common_tabs.addTab(file_batch_widget, "Files")
        
        # ===================== VIDEO TAB =====================
        v_tab_content = QWidget(); vfl = QFormLayout(v_tab_content); vfl.setSpacing(6); vfl.setContentsMargins(8, 8, 8, 8); vfl.setFormAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.theme_cb = QComboBox(); self.theme_cb.addItems(list(THEMES.keys())); vfl.addRow("Theme:", self.theme_cb)
        self.res_cb = QComboBox(); self.res_cb.addItems(list(RESOLUTIONS.keys())); vfl.addRow("Resolution:", self.res_cb)
        self.fps_sp = QSpinBox(); self.fps_sp.setRange(30, 60); self.fps_sp.setSingleStep(30); self.fps_sp.setValue(30); vfl.addRow("FPS:", self.fps_sp)
        self.encoder_cb = QComboBox(); self.encoder_cb.addItems(ENCODERS); vfl.addRow("Encoder:", self.encoder_cb)
        self.yt_extras_chk = QCheckBox("Generate YT Extras"); self.yt_extras_chk.setChecked(True); vfl.addRow(self.yt_extras_chk)
        self.output_template_edit = QLineEdit(); self.output_template_edit.setText("{name}_{date}"); self.output_template_edit.setToolTip("Placeholders: {name}, {date}, {lang}"); vfl.addRow("Output Name:", self.output_template_edit)

        qt_row = QHBoxLayout(); qt_row.setContentsMargins(0,0,0,0)
        for txt, secs in [("30s", 30), ("1m", 60), ("2m", 120), ("3m", 180), ("5m", 300)]:
            btn = QPushButton(txt); btn.setFixedWidth(40)
            btn.clicked.connect(lambda checked=False, s=secs: self._apply_target_duration(s))
            qt_row.addWidget(btn)
        qt_row.addStretch()
        vfl.addRow("Quick Target:", qt_row)

        dur_row = QHBoxLayout(); dur_row.setContentsMargins(0,0,0,0)
        self.target_dur_sp = QSpinBox(); self.target_dur_sp.setRange(5, 7200); self.target_dur_sp.setValue(60); self.target_dur_sp.setSuffix("s")
        self.target_dur_lbl = QLabel("0h 0m 0s")
        self.target_dur_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-family: monospace;")
        self.target_dur_lbl.setMinimumWidth(70)
        
        def update_dur_label(secs):
            h = secs // 3600
            m = (secs % 3600) // 60
            s = secs % 60
            self.target_dur_lbl.setText(f"{h}h {m}m {s}s")
            
        self.target_dur_sp.valueChanged.connect(update_dur_label)
        update_dur_label(self.target_dur_sp.value())
        
        dur_apply_btn = QPushButton("Set WPM"); dur_apply_btn.clicked.connect(lambda: self._apply_target_duration(self.target_dur_sp.value()))
        dur_row.addWidget(self.target_dur_sp, 1); dur_row.addWidget(self.target_dur_lbl); dur_row.addWidget(dur_apply_btn)
        vfl.addRow("Target Dur:", dur_row)
        
        v_tab = QScrollArea(); v_tab.setWidgetResizable(True); v_tab.setWidget(v_tab_content); v_tab.setFrameShape(QFrame.NoFrame)
        self.common_tabs.addTab(v_tab, "Video")

        # ===================== AUDIO TAB =====================
        a_tab_content = QWidget(); afl = QFormLayout(a_tab_content); afl.setSpacing(6); afl.setContentsMargins(8, 8, 8, 8); afl.setFormAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.sound_chk = QCheckBox("Enable Audio"); self.sound_chk.setChecked(True); afl.addRow(self.sound_chk)
        self.preset_cb = QComboBox(); self.preset_cb.addItems(list(MODULAR_SOUND_PRESETS.keys())); afl.addRow("Preset:", self.preset_cb)
        self.stereo_chk = QCheckBox("Binaural ASMR"); afl.addRow(self.stereo_chk)
        self.vol_sp = QSpinBox(); self.vol_sp.setRange(0, 100); self.vol_sp.setValue(50); self.vol_sp.setSuffix("%"); afl.addRow("Volume:", self.vol_sp)
        test_row = QHBoxLayout(); test_row.setContentsMargins(0, 0, 0, 0)
        self.test_sound_btn = QPushButton("🔊 Test Sound")
        self.test_sound_btn.setStyleSheet("QPushButton { background: #89b4fa; color: #1e1e2e; font-weight: bold; border: none; border-radius: 4px; padding: 6px; }")
        self.test_sound_btn.clicked.connect(self._test_sound)
        test_row.addWidget(self.test_sound_btn)
        afl.addRow("Preview:", test_row)
        bgm_row = QHBoxLayout(); bgm_row.setContentsMargins(0,0,0,0)
        self.bgm_edit = QLineEdit(); self.bgm_edit.setPlaceholderText("BGM MP3 path")
        bgm_btn = QPushButton("..."); bgm_btn.setFixedWidth(30); bgm_btn.clicked.connect(self._browse_bgm)
        bgm_row.addWidget(self.bgm_edit); bgm_row.addWidget(bgm_btn); afl.addRow("BGM:", bgm_row)
        self.bgm_vol_sp = QSpinBox(); self.bgm_vol_sp.setRange(0, 100); self.bgm_vol_sp.setValue(30); self.bgm_vol_sp.setSuffix("%"); afl.addRow("BGM Vol:", self.bgm_vol_sp)
        self.bgm_duck_chk = QCheckBox("Sidechain Ducking"); self.bgm_duck_chk.setChecked(True); afl.addRow(self.bgm_duck_chk)
        
        a_tab = QScrollArea(); a_tab.setWidgetResizable(True); a_tab.setWidget(a_tab_content); a_tab.setFrameShape(QFrame.NoFrame)
        self.common_tabs.addTab(a_tab, "Audio")
        
        # ===================== KEYBOARD TAB =====================
        k_tab_content = QWidget(); kfl = QFormLayout(k_tab_content); kfl.setSpacing(6); kfl.setContentsMargins(8, 8, 8, 8); kfl.setFormAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.kb_enabled_chk = QCheckBox("Show Keyboard Overlay"); kfl.addRow(self.kb_enabled_chk)
        self.kb_layout_cb = QComboBox(); self.kb_layout_cb.addItems(list(KEYBOARD_LAYOUTS.keys())); kfl.addRow("KB Layout:", self.kb_layout_cb)
        self.kb_position_cb = QComboBox(); self.kb_position_cb.addItems(["Bottom Center", "Bottom Right", "Bottom Left", "Top Center", "Top Right", "Top Left"])
        kfl.addRow("KB Position:", self.kb_position_cb)
        self.kb_opacity_sp = QDoubleSpinBox(); self.kb_opacity_sp.setRange(0.1, 1.0); self.kb_opacity_sp.setSingleStep(0.05); self.kb_opacity_sp.setValue(0.82); kfl.addRow("KB Opacity:", self.kb_opacity_sp)
        
        k_tab = QScrollArea(); k_tab.setWidgetResizable(True); k_tab.setWidget(k_tab_content); k_tab.setFrameShape(QFrame.NoFrame)
        self.common_tabs.addTab(k_tab, "Keyboard")
        
        # ===================== CUSTOM TAB =====================
        c_tab_content = QWidget(); cvl = QVBoxLayout(c_tab_content); cvl.setSpacing(6); cvl.setContentsMargins(8, 8, 8, 8)
        self.use_custom_chk = QCheckBox("Use Custom Code (ignores file list)"); cvl.addWidget(self.use_custom_chk)
        self.custom_editor = QPlainTextEdit(); self.custom_editor.setPlaceholderText("Supports shortcodes: :rocket: -> 🚀")
        cvl.addWidget(self.custom_editor)
        
        c_tab = QScrollArea(); c_tab.setWidgetResizable(True); c_tab.setWidget(c_tab_content); c_tab.setFrameShape(QFrame.NoFrame)
        self.common_tabs.addTab(c_tab, "Custom")
        
        # ===================== BOTTOM BAR =====================
        bottom_bar = QVBoxLayout(); bottom_bar.setContentsMargins(8, 4, 8, 8); bottom_bar.setSpacing(6)
        self.progress_bar = QProgressBar(); self.progress_bar.setVisible(False); self.progress_bar.setFormat("%v / %m  (%p%)"); bottom_bar.addWidget(self.progress_bar)
        
        br2 = QHBoxLayout(); br2.setContentsMargins(0, 0, 0, 0)
        self.export_btn = QPushButton("🎬 Export"); self.export_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 8px; }")
        self.export_btn.clicked.connect(self._start_export); br2.addWidget(self.export_btn, 1)
        self.skip_btn = QPushButton("⏭ Skip"); self.skip_btn.setFixedWidth(60); self.skip_btn.setEnabled(False); self.skip_btn.clicked.connect(self._skip_current); br2.addWidget(self.skip_btn)
        self.cancel_btn = QPushButton("✖"); self.cancel_btn.setFixedWidth(36); self.cancel_btn.setEnabled(False); self.cancel_btn.clicked.connect(self._cancel_export); br2.addWidget(self.cancel_btn)
        bottom_bar.addLayout(br2)
        
        br3 = QHBoxLayout(); br3.setContentsMargins(0, 0, 0, 0)
        self.save_proj_btn = QPushButton("💾 Save"); self.save_proj_btn.clicked.connect(self._save_project); br3.addWidget(self.save_proj_btn)
        self.load_proj_btn = QPushButton("📂 Load"); self.load_proj_btn.clicked.connect(self._load_project); br3.addWidget(self.load_proj_btn)
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
        
        # ===================== RIGHT PANE (Mode Tabs) =====================
        self.mode_tabs = QTabWidget()
        root.addWidget(self.mode_tabs)
        root.setSizes([420, 1000])
        root.setStretchFactor(0, 0)
        root.setStretchFactor(1, 1)
        
        self._build_multi_window_tab()
        self._build_jr_vs_sr_tab()
        self._build_code_yt_tab()
        self._build_text_emoji_tab()
        
        self.mode_tabs.currentChanged.connect(lambda idx: (self._on_mode_changed(idx), self._debounce_timer.start()))
        
        # Default to Files tab so users land on their file list first
        self.common_tabs.setCurrentIndex(0)

    def _create_font_controls(self, prefix):
        font_cb = QComboBox(); font_cb.addItems(FONT_FAMILIES)
        font_sz_auto = QCheckBox("Auto")
        fs_row = QHBoxLayout(); fs_row.setContentsMargins(0,0,0,0); fs_row.addWidget(font_sz_auto)
        font_sz_sp = QSpinBox(); font_sz_sp.setRange(8, 72); font_sz_sp.setValue(22); font_sz_sp.setEnabled(False); fs_row.addWidget(font_sz_sp)
        font_sz_auto.toggled.connect(font_sz_sp.setEnabled)
        setattr(self, f"{prefix}_font_cb", font_cb); setattr(self, f"{prefix}_font_sz_auto", font_sz_auto); setattr(self, f"{prefix}_font_sz_sp", font_sz_sp)
        return font_cb, fs_row

    def _create_font_group(self, prefix, label_text):
        widget = QWidget()
        layout = QFormLayout(widget)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(4)
        
        font_cb = QComboBox(); font_cb.addItems(FONT_FAMILIES)
        font_sz_auto = QCheckBox("Auto")
        font_sz_sp = QSpinBox(); font_sz_sp.setRange(8, 72); font_sz_sp.setValue(22); font_sz_sp.setEnabled(False)
        
        fs_row = QHBoxLayout(); fs_row.setContentsMargins(0,0,0,0); fs_row.addWidget(font_sz_auto); fs_row.addWidget(font_sz_sp)
        font_sz_auto.toggled.connect(font_sz_sp.setEnabled)
        
        setattr(self, f"{prefix}_font_cb", font_cb)
        setattr(self, f"{prefix}_font_sz_auto", font_sz_auto)
        setattr(self, f"{prefix}_font_sz_sp", font_sz_sp)
        
        layout.addRow(label_text, font_cb)
        layout.addRow("Size:", fs_row)
        return widget

    def _build_mode_tab(self, mode: StudioMode):
        tab = QWidget(); layout = QHBoxLayout(tab); layout.setContentsMargins(0, 0, 0, 0); layout.setSpacing(0)
        splitter = QSplitter(Qt.Horizontal)
        settings_scroll = QScrollArea(); settings_scroll.setWidgetResizable(True); settings_scroll.setFrameShape(QFrame.NoFrame)
        settings_scroll.setMinimumWidth(280) 
        settings_widget = QWidget(); s_layout = QVBoxLayout(settings_widget); s_layout.setContentsMargins(8, 8, 8, 8); s_layout.setSpacing(8)
        preview_widget = QWidget(); p_layout = QVBoxLayout(preview_widget); p_layout.setContentsMargins(8, 8, 8, 8); p_layout.setSpacing(8)
        lbl = QLabel(); lbl.setAlignment(Qt.AlignCenter); lbl.setStyleSheet("background: #11111b; border-radius: 8px;"); lbl.setMinimumSize(640, 360)
        p_layout.addWidget(lbl, 1)
        stats_row = QHBoxLayout(); stats_row.setContentsMargins(0, 0, 0, 0)
        stats_lbl = QLabel("Render: 0ms | WPM: 0 | Chars: 0/0"); stats_lbl.setStyleSheet("color: #a6adc8; font-size: 11px; font-family: monospace;")
        stats_row.addWidget(stats_lbl); stats_row.addStretch()
        guide_pad_chk = QCheckBox("Pad"); guide_pad_chk.toggled.connect(self._debounce_timer.start)
        guide_chrome_chk = QCheckBox("Chrome"); guide_chrome_chk.toggled.connect(self._debounce_timer.start)
        guide_code_chk = QCheckBox("Code"); guide_code_chk.toggled.connect(self._debounce_timer.start)
        stats_row.addWidget(guide_pad_chk); stats_row.addWidget(guide_chrome_chk); stats_row.addWidget(guide_code_chk)
        p_layout.addLayout(stats_row)
        ctrls = QHBoxLayout(); ctrls.setContentsMargins(0, 0, 0, 0)
        prev_btn = QPushButton("◀"); prev_btn.setFixedWidth(40); prev_btn.clicked.connect(lambda: self._step_frame(-1)); ctrls.addWidget(prev_btn)
        play_btn = QPushButton("▶ Animate"); play_btn.setFixedWidth(110); play_btn.setStyleSheet("QPushButton { background: #a6e3a1; color: #1e1e2e; font-weight: bold; border: none; border-radius: 6px; padding: 6px; }"); ctrls.addWidget(play_btn)
        next_btn = QPushButton("▶"); next_btn.setFixedWidth(40); next_btn.clicked.connect(lambda: self._step_frame(1)); ctrls.addWidget(next_btn)
        slider = QSlider(Qt.Horizontal); slider.setRange(0, 1000)
        time_lbl = QLabel("0:00 / 0:00"); time_lbl.setStyleSheet("color: #a6e3a1; font-family: monospace;"); time_lbl.setMinimumWidth(100)
        ctrls.addWidget(slider, 1); ctrls.addWidget(time_lbl); p_layout.addLayout(ctrls)
        settings_scroll.setWidget(settings_widget); splitter.addWidget(settings_scroll); splitter.addWidget(preview_widget)
        splitter.setSizes([450, 1000]); splitter.setStretchFactor(0, 0); splitter.setStretchFactor(1, 1); layout.addWidget(splitter)
        self.mode_tabs.addTab(tab, mode.value.split(" ")[0])
        return s_layout, lbl, play_btn, slider, time_lbl, prev_btn, next_btn, stats_lbl, guide_pad_chk, guide_chrome_chk, guide_code_chk

    def _update_mw_layout_visibility(self):
        n_panes = MULTI_WINDOW_LAYOUTS.get(self.mw_layout_cb.currentText(), 1)
        self.mw_font_grp1.setVisible(n_panes >= 1)
        self.mw_font_grp2.setVisible(n_panes >= 2)
        self.mw_font_grp3.setVisible(n_panes >= 3)
        self.mw_font_grp4.setVisible(n_panes >= 4)

        has_multi = n_panes >= 2
        self.diff_highlight_mw_chk.setVisible(has_multi)
        self.sync_mw_chk.setVisible(has_multi)

        self.mw_ratio_container.setVisible(n_panes == 2)

        self._debounce_timer.start()

    def _build_multi_window_tab(self):
        s_layout, lbl, play_btn, slider, time_lbl, prev_btn, next_btn, stats_lbl, g_pad, g_chrome, g_code = self._build_mode_tab(StudioMode.MULTI_WINDOW)
        grp = QGroupBox("Multi-Window Settings"); fl = QFormLayout(grp); fl.setSpacing(6)
        
        self.mw_layout_cb = QComboBox(); self.mw_layout_cb.addItems(list(MULTI_WINDOW_LAYOUTS.keys())); fl.addRow("Layout:", self.mw_layout_cb)

        self.mw_font_grp1 = self._create_font_group("mw", "Window 1 Font:")
        self.mw_font_grp2 = self._create_font_group("mw_2", "Window 2 Font:")
        self.mw_font_grp3 = self._create_font_group("mw_3", "Window 3 Font:")
        self.mw_font_grp4 = self._create_font_group("mw_4", "Window 4 Font:")
        fl.addRow(self.mw_font_grp1)
        fl.addRow(self.mw_font_grp2)
        fl.addRow(self.mw_font_grp3)
        fl.addRow(self.mw_font_grp4)
        
        self.mw_layout_cb.currentIndexChanged.connect(self._update_mw_layout_visibility)
        
        self.mw_wpm_sp = QSpinBox(); self.mw_wpm_sp.setRange(30, 300); self.mw_wpm_sp.setValue(100); fl.addRow("WPM:", self.mw_wpm_sp)
        self.mw_typo_sp = QDoubleSpinBox(); self.mw_typo_sp.setRange(0.0, 0.2); self.mw_typo_sp.setSingleStep(0.01); fl.addRow("Typo Rate:", self.mw_typo_sp)
        self.mw_shorts_chk = QCheckBox("Auto-adjust for Shorts (<3 min)"); fl.addRow(self.mw_shorts_chk)
        self.diff_highlight_mw_chk = QCheckBox("Dynamic Diff Highlighting"); self.diff_highlight_mw_chk.setChecked(True); fl.addRow(self.diff_highlight_mw_chk)
        self.sync_mw_chk = QCheckBox("Synchronized Typing Completion"); self.sync_mw_chk.setChecked(True); fl.addRow(self.sync_mw_chk)

        self.mw_ratio_container = QWidget()
        ratio_layout = QHBoxLayout(self.mw_ratio_container)
        ratio_layout.setContentsMargins(0, 0, 0, 0); ratio_layout.setSpacing(6)
        ratio_layout.addWidget(QLabel("Pane Ratio:"))
        self.mw_ratio_sp = QSpinBox(); self.mw_ratio_sp.setRange(10, 90); self.mw_ratio_sp.setValue(50); self.mw_ratio_sp.setSuffix("%")
        ratio_layout.addWidget(self.mw_ratio_sp); ratio_layout.addStretch()
        fl.addRow(self.mw_ratio_container)
        s_layout.addWidget(grp); s_layout.addStretch()
        
        self.mw_preview_lbl = lbl; self.mw_play_btn = play_btn; self.mw_slider = slider; self.mw_time_lbl = time_lbl
        self.mw_prev_btn = prev_btn; self.mw_next_btn = next_btn; self.mw_stats_lbl = stats_lbl
        self.mw_g_pad = g_pad; self.mw_g_chrome = g_chrome; self.mw_g_code = g_code
        self.mw_play_btn.clicked.connect(lambda: self._toggle_preview(StudioMode.MULTI_WINDOW))
        self.mw_slider.valueChanged.connect(lambda v: self._on_slider_changed(StudioMode.MULTI_WINDOW, v))
        self.mw_layout_cb.setCurrentText(self.config.layout_mw)
        self._update_mw_layout_visibility()

    def _build_jr_vs_sr_tab(self):
        s_layout, lbl, play_btn, slider, time_lbl, prev_btn, next_btn, stats_lbl, g_pad, g_chrome, g_code = self._build_mode_tab(StudioMode.JR_VS_SR)
        grp = QGroupBox("Junior vs Senior Settings"); fl = QFormLayout(grp); fl.setSpacing(6)
        font_cb_jr, fs_row_jr = self._create_font_controls("jr"); fl.addRow("Junior Font:", font_cb_jr); fl.addRow("Junior Size:", fs_row_jr)
        font_cb_sr, fs_row_sr = self._create_font_controls("sr"); fl.addRow("Senior Font:", font_cb_sr); fl.addRow("Senior Size:", fs_row_sr) 
        self.jr_layout_cb = QComboBox(); self.jr_layout_cb.addItems(JR_VS_SR_LAYOUTS); fl.addRow("Layout:", self.jr_layout_cb)
        self.jr_wpm_sp = QSpinBox(); self.jr_wpm_sp.setRange(30, 300); self.jr_wpm_sp.setValue(90); fl.addRow("Junior WPM:", self.jr_wpm_sp)
        self.sr_wpm_sp = QSpinBox(); self.sr_wpm_sp.setRange(30, 300); self.sr_wpm_sp.setValue(130); fl.addRow("Senior WPM:", self.sr_wpm_sp)
        self.jr_typo_sp = QDoubleSpinBox(); self.jr_typo_sp.setRange(0.0, 0.2); self.jr_typo_sp.setSingleStep(0.01); fl.addRow("Typo Rate (Jr):", self.jr_typo_sp)
        self.jr_sound_cb = QComboBox(); self.jr_sound_cb.addItems(list(MODULAR_SOUND_PRESETS.keys())); fl.addRow("Junior Sound:", self.jr_sound_cb)
        self.sr_sound_cb = QComboBox(); self.sr_sound_cb.addItems(list(MODULAR_SOUND_PRESETS.keys())); fl.addRow("Senior Sound:", self.sr_sound_cb)
        s_layout.addWidget(grp)
        custom_grp = QGroupBox("Dual Custom Code (Overrides JSON/File)"); cl = QVBoxLayout(custom_grp); cl.setSpacing(4)
        cl.addWidget(QLabel("Junior Code:")); self.jr_custom_editor = QPlainTextEdit(); self.jr_custom_editor.setMaximumHeight(150); cl.addWidget(self.jr_custom_editor)
        cl.addWidget(QLabel("Senior Code:")); self.sr_custom_editor = QPlainTextEdit(); self.sr_custom_editor.setMaximumHeight(150); cl.addWidget(self.sr_custom_editor)
        s_layout.addWidget(custom_grp); s_layout.addStretch()
        self.jr_preview_lbl = lbl; self.jr_play_btn = play_btn; self.jr_slider = slider; self.jr_time_lbl = time_lbl
        self.jr_prev_btn = prev_btn; self.jr_next_btn = next_btn; self.jr_stats_lbl = stats_lbl
        self.jr_g_pad = g_pad; self.jr_g_chrome = g_chrome; self.jr_g_code = g_code
        self.jr_play_btn.clicked.connect(lambda: self._toggle_preview(StudioMode.JR_VS_SR))
        self.jr_slider.valueChanged.connect(lambda v: self._on_slider_changed(StudioMode.JR_VS_SR, v))

    def _build_code_yt_tab(self):
        s_layout, lbl, play_btn, slider, time_lbl, prev_btn, next_btn, stats_lbl, g_pad, g_chrome, g_code = self._build_mode_tab(StudioMode.CODE_YT)
        grp = QGroupBox("Code YT Settings"); fl = QFormLayout(grp); fl.setSpacing(6)
        font_cb, fs_row = self._create_font_controls("yt"); fl.addRow("Font:", font_cb); fl.addRow("Font Size:", fs_row)
        self.yt_wpm_sp = QSpinBox(); self.yt_wpm_sp.setRange(30, 300); self.yt_wpm_sp.setValue(100); fl.addRow("WPM:", self.yt_wpm_sp)
        self.yt_typo_sp = QDoubleSpinBox(); self.yt_typo_sp.setRange(0.0, 0.2); self.yt_typo_sp.setSingleStep(0.01); fl.addRow("Typo Rate:", self.yt_typo_sp)
        dur_row = QHBoxLayout(); dur_row.setContentsMargins(0, 0, 0, 0)
        for txt, secs in [("30s", 30), ("1m", 60), ("2m", 120), ("3m", 180)]:
            btn = QPushButton(txt); btn.setFixedWidth(40); btn.clicked.connect(lambda checked=False, s=secs: self._apply_target_duration(s)); dur_row.addWidget(btn)
        dur_row.addStretch(); fl.addRow("Quick Target:", dur_row)
        self.yt_zoom_chk = QCheckBox("Cinematic Ken Burns Zoom"); fl.addRow(self.yt_zoom_chk)
        self.yt_focus_chk = QCheckBox("Code Block Focus (Dimming)"); fl.addRow(self.yt_focus_chk)
        s_layout.addWidget(grp); s_layout.addStretch()
        self.yt_preview_lbl = lbl; self.yt_play_btn = play_btn; self.yt_slider = slider; self.yt_time_lbl = time_lbl
        self.yt_prev_btn = prev_btn; self.yt_next_btn = next_btn; self.yt_stats_lbl = stats_lbl
        self.yt_g_pad = g_pad; self.yt_g_chrome = g_chrome; self.yt_g_code = g_code
        self.yt_play_btn.clicked.connect(lambda: self._toggle_preview(StudioMode.CODE_YT))
        self.yt_slider.valueChanged.connect(lambda v: self._on_slider_changed(StudioMode.CODE_YT, v))

    def _build_text_emoji_tab(self):
        s_layout, lbl, play_btn, slider, time_lbl, prev_btn, next_btn, stats_lbl, g_pad, g_chrome, g_code = self._build_mode_tab(StudioMode.TEXT_EMOJI)
        grp = QGroupBox("Text & Emoji Settings"); fl = QFormLayout(grp); fl.setSpacing(6)
        font_cb, fs_row = self._create_font_controls("txt"); fl.addRow("Font:", font_cb); fl.addRow("Font Size:", fs_row)
        self.txt_wpm_sp = QSpinBox(); self.txt_wpm_sp.setRange(30, 300); self.txt_wpm_sp.setValue(100); fl.addRow("WPM:", self.txt_wpm_sp)
        self.txt_typo_sp = QDoubleSpinBox(); self.txt_typo_sp.setRange(0.0, 0.2); self.txt_typo_sp.setSingleStep(0.01); fl.addRow("Typo Rate:", self.txt_typo_sp)
        self.txt_shorts_chk = QCheckBox("Auto-adjust for Shorts (<3 min)"); fl.addRow(self.txt_shorts_chk)
        self.ascii_chk = QCheckBox("ASCII Art Mode (Centered)"); fl.addRow(self.ascii_chk)
        self.ansi_chk = QCheckBox("Render ANSI Colors (ASCII Art)"); fl.addRow(self.ansi_chk)
        self.txt_clean_chk = QCheckBox("Clean Text Spacing"); self.txt_clean_chk.setChecked(True); fl.addRow(self.txt_clean_chk)
        self.txt_markdown_chk = QCheckBox("Markdown Support (**bold**, *italic*)"); fl.addRow(self.txt_markdown_chk)
        self.txt_crt_chk = QCheckBox("CRT / Terminal Filter"); fl.addRow(self.txt_crt_chk)
        self.txt_bubbles_chk = QCheckBox("Chat Bubble Mode"); fl.addRow(self.txt_bubbles_chk)
        s_layout.addWidget(grp); s_layout.addStretch()
        self.txt_preview_lbl = lbl; self.txt_play_btn = play_btn; self.txt_slider = slider; self.txt_time_lbl = time_lbl
        self.txt_prev_btn = prev_btn; self.txt_next_btn = next_btn; self.txt_stats_lbl = stats_lbl
        self.txt_g_pad = g_pad; self.txt_g_chrome = g_chrome; self.txt_g_code = g_code
        self.txt_play_btn.clicked.connect(lambda: self._toggle_preview(StudioMode.TEXT_EMOJI))
        self.txt_slider.valueChanged.connect(lambda v: self._on_slider_changed(StudioMode.TEXT_EMOJI, v))

    def _apply_target_duration(self, secs):
        mode = self.config.mode
        
        if mode == StudioMode.MULTI_WINDOW:
            checked = [f for f in self._items if f.checked]
            if self.config.use_custom or not checked:
                code, _, _ = self.strategies[mode]._get_code(self.config, self._items, self.config.custom_code)
                longest_code = code
            else:
                longest_code = ""
                for it in checked:
                    c = read_text_file(it.path, self.config.txt_clean)
                    if len(c) > len(longest_code):
                        longest_code = c
            wpm = TypingAnimator.find_wpm_for_target(longest_code, secs, 0.5, 1.5)
            self.mw_wpm_sp.setValue(wpm)
            
        elif mode == StudioMode.JR_VS_SR:
            code1, code2, _, _, _ = self._get_jr_sr_codes()
            wpm1 = TypingAnimator.find_wpm_for_target(code1, secs, 0.5, 1.5)
            wpm2 = TypingAnimator.find_wpm_for_target(code2, secs, 0.5, 1.5)
            self.jr_wpm_sp.setValue(wpm1)
            self.sr_wpm_sp.setValue(wpm2)
            
        elif mode == StudioMode.CODE_YT:
            code, _, _ = self.strategies[mode]._get_code(self.config, self._items, self.config.custom_code)
            wpm = TypingAnimator.find_wpm_for_target(code, secs, 0.5, 1.5)
            self.yt_wpm_sp.setValue(wpm)
            
        elif mode == StudioMode.TEXT_EMOJI:
            code, _, _ = self.strategies[mode]._get_code(self.config, self._items, self.config.custom_code)
            wpm = TypingAnimator.find_wpm_for_target(code, secs, 0.5, 1.5)
            self.txt_wpm_sp.setValue(wpm)
            
        self.statusBar().showMessage(f"Adjusted WPM to hit ~{secs}s duration", 3000)

    def _create_quick_target_row(self):
        dur_row = QHBoxLayout(); dur_row.setContentsMargins(0, 0, 0, 0)
        for txt, secs in [("30s", 30), ("1m", 60), ("2m", 120), ("3m", 180), ("5m", 300)]:
            btn = QPushButton(txt); btn.setFixedWidth(40)
            btn.clicked.connect(lambda checked=False, s=secs: self._apply_target_duration(s))
            dur_row.addWidget(btn)
        dur_row.addStretch()
        return dur_row

    def _get_jr_sr_codes(self):
        if self.config.use_custom or (self.config.jr_custom_code and self.config.sr_custom_code):
            code1 = convert_shortcodes(self.config.jr_custom_code) if self.config.jr_custom_code else "def junior():\n    pass"
            code2 = convert_shortcodes(self.config.sr_custom_code) if self.config.sr_custom_code else "def senior():\n    pass"
            lang, t1, t2 = "python", "junior.py", "senior.py"
        else:
            checked = [f for f in self._items if f.checked]
            if not checked:
                c, l, t = self.strategies[StudioMode.JR_VS_SR]._get_code(self.config, self._items, self.config.custom_code)
                code1, code2, lang, t1, t2 = c, c, l, t, t
            else:
                it = checked[0]
                ext = os.path.splitext(it.path)[1].lower()
                if ext == ".json":
                    try:
                        with open(it.path, "r", encoding="utf-8") as f: data = json.load(f)
                        code1 = convert_shortcodes(data.get("junior_code", "")); code2 = convert_shortcodes(data.get("senior_code", ""))
                        lang = data.get("language", "python"); title = data.get("title", os.path.basename(it.path))
                        t1, t2 = f"{title} (Junior)", f"{title} (Senior)"
                        if not code1.strip(): code1 = "# Junior code missing in JSON"
                        if not code2.strip(): code2 = "# Senior code missing in JSON"
                    except:
                        c, l, t = self.strategies[StudioMode.JR_VS_SR]._get_code(self.config, self._items, self.config.custom_code)
                        code1, code2, lang, t1, t2 = c, c, l, t, t
                else:
                    c, l, t = self.strategies[StudioMode.JR_VS_SR]._get_code(self.config, self._items, self.config.custom_code)
                    code1, code2, lang, t1, t2 = c, c, l, t, t
        return code1, code2, lang, t1, t2

    def _step_frame(self, direction: int):
        if not self._cached_mp: return
        fps = self.config.fps; dt = direction / fps; dur = self._cached_mp.duration()
        self._preview_anim_t = max(0, min(dur, self._preview_anim_t + dt))
        self._preview_progress = self._preview_anim_t / dur if dur > 0 else 0; self._update_preview()

    def _browse_bgm(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Background Music", "", "Audio Files (*.mp3 *.wav *.m4a)")
        if path: self.bgm_edit.setText(path)

    def _test_sound(self):
        try:
            sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo)
            sample_text = "hello world 123"
            timestamps = []
            t = 0.0
            for ch in sample_text:
                timestamps.append((t, ch))
                if ch == ' ':
                    t += 0.10
                else:
                    t += 0.06
            
            pcm = sg.generate_pcm(timestamps, 1.0)
            if len(pcm) > 0:
                buf = io.BytesIO()
                with wave.open(buf, "w") as wf:
                    wf.setnchannels(2 if sg.stereo else 1)
                    wf.setsampwidth(2)
                    wf.setframerate(sg.sr)
                    wf.writeframes(pcm.tobytes())
                self._audio_player.stop()
                self._audio_buf = QBuffer()
                self._audio_buf.setData(buf.getvalue())
                self._audio_buf.open(QIODevice.ReadOnly)
                self._audio_out.setVolume(self.config.volume / 100.0)
                self._audio_player.setSourceDevice(self._audio_buf, QUrl())
                self._audio_player.play()
                self.statusBar().showMessage(f"🔊 Testing: {self.config.sound_preset} | Vol: {self.config.volume}% | Stereo: {self.config.stereo}", 3000)
        except Exception as e:
            logger.error("Audio test failed", exc_info=True)
            self.statusBar().showMessage(f"Audio test failed: {e}", 3000)

    def _connect_signals(self):
        def update_config(key, value): setattr(self.config, key, value); self._debounce_timer.start()
        self.theme_cb.currentTextChanged.connect(lambda v: update_config('theme', v))
        self.res_cb.currentTextChanged.connect(lambda v: update_config('resolution', v))
        self.fps_sp.valueChanged.connect(lambda v: update_config('fps', v))
        self.sound_chk.toggled.connect(lambda v: update_config('sound_enabled', v))
        self.preset_cb.currentTextChanged.connect(lambda v: update_config('sound_preset', v))
        self.stereo_chk.toggled.connect(lambda v: update_config('stereo', v))
        self.vol_sp.valueChanged.connect(lambda v: update_config('volume', v))
        self.encoder_cb.currentTextChanged.connect(lambda v: update_config('encoder', v))
        self.bgm_edit.textChanged.connect(lambda v: update_config('bgm_path', v))
        self.bgm_vol_sp.valueChanged.connect(lambda v: update_config('bgm_volume', v))
        self.bgm_duck_chk.toggled.connect(lambda v: update_config('bgm_duck', v))
        self.use_custom_chk.toggled.connect(lambda v: update_config('use_custom', v))
        self.custom_editor.textChanged.connect(lambda: update_config('custom_code', self.custom_editor.toPlainText()))
        self.yt_extras_chk.toggled.connect(lambda v: update_config('yt_extras', v))
        self.recursive_chk.toggled.connect(lambda v: update_config('recursive_scan', v))
        self.depth_sp.valueChanged.connect(lambda v: update_config('scan_depth', v))
        self.output_template_edit.textChanged.connect(lambda v: update_config('output_template', v))
        self.kb_enabled_chk.toggled.connect(lambda v: update_config('kb_enabled', v))
        self.kb_layout_cb.currentTextChanged.connect(lambda v: update_config('kb_layout', v))
        self.kb_position_cb.currentTextChanged.connect(lambda v: update_config('kb_position', v))
        self.kb_opacity_sp.valueChanged.connect(lambda v: update_config('kb_opacity', v))
        self.mw_font_cb.currentTextChanged.connect(lambda v: update_config('font_mw', v))
        self.mw_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_mw', v))
        self.mw_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_mw', v))
        self.mw_2_font_cb.currentTextChanged.connect(lambda v: update_config('font_mw_2', v))
        self.mw_2_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_mw_2', v))
        self.mw_2_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_mw_2', v))
        self.mw_3_font_cb.currentTextChanged.connect(lambda v: update_config('font_mw_3', v))
        self.mw_3_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_mw_3', v))
        self.mw_3_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_mw_3', v))
        self.mw_4_font_cb.currentTextChanged.connect(lambda v: update_config('font_mw_4', v))
        self.mw_4_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_mw_4', v))
        self.mw_4_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_mw_4', v))
        self.mw_layout_cb.currentTextChanged.connect(lambda v: update_config('layout_mw', v))
        self.mw_wpm_sp.valueChanged.connect(lambda v: update_config('wpm_mw', v))
        self.mw_typo_sp.valueChanged.connect(lambda v: update_config('typo_mw', v))
        self.mw_shorts_chk.toggled.connect(lambda v: update_config('shorts_mw', v))
        self.diff_highlight_mw_chk.toggled.connect(lambda v: update_config('diff_highlight_mw', v))
        self.sync_mw_chk.toggled.connect(lambda v: update_config('sync_mw', v))
        self.mw_ratio_sp.valueChanged.connect(lambda v: update_config('mw_ratio', v))
        self.jr_font_cb.currentTextChanged.connect(lambda v: update_config('font_jr', v))
        self.jr_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_jr', v))
        self.jr_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_jr', v))
        self.sr_font_cb.currentTextChanged.connect(lambda v: update_config('font_sr', v))
        self.sr_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_sr', v))
        self.sr_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_sr', v))
        self.jr_layout_cb.currentTextChanged.connect(lambda v: update_config('layout_jr', v))
        self.jr_wpm_sp.valueChanged.connect(lambda v: update_config('jr_wpm', v))
        self.sr_wpm_sp.valueChanged.connect(lambda v: update_config('sr_wpm', v))
        self.jr_typo_sp.valueChanged.connect(lambda v: update_config('typo_jr', v))
        self.jr_sound_cb.currentTextChanged.connect(lambda v: update_config('jr_sound', v))
        self.sr_sound_cb.currentTextChanged.connect(lambda v: update_config('sr_sound', v))
        self.jr_custom_editor.textChanged.connect(lambda: update_config('jr_custom_code', self.jr_custom_editor.toPlainText()))
        self.sr_custom_editor.textChanged.connect(lambda: update_config('sr_custom_code', self.sr_custom_editor.toPlainText()))
        self.yt_font_cb.currentTextChanged.connect(lambda v: update_config('font_yt', v))
        self.yt_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_yt', v))
        self.yt_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_yt', v))
        self.yt_wpm_sp.valueChanged.connect(lambda v: update_config('wpm_yt', v))
        self.yt_typo_sp.valueChanged.connect(lambda v: update_config('typo_yt', v))
        self.yt_zoom_chk.toggled.connect(lambda v: update_config('yt_zoom', v))
        self.yt_focus_chk.toggled.connect(lambda v: update_config('yt_focus', v))
        self.txt_font_cb.currentTextChanged.connect(lambda v: update_config('font_txt', v))
        self.txt_font_sz_auto.toggled.connect(lambda v: update_config('font_sz_auto_txt', v))
        self.txt_font_sz_sp.valueChanged.connect(lambda v: update_config('font_sz_txt', v))
        self.txt_wpm_sp.valueChanged.connect(lambda v: update_config('wpm_txt', v))
        self.txt_typo_sp.valueChanged.connect(lambda v: update_config('typo_txt', v))
        self.txt_shorts_chk.toggled.connect(lambda v: update_config('shorts_txt', v))
        self.ascii_chk.toggled.connect(lambda v: update_config('ascii_art', v))
        self.ansi_chk.toggled.connect(lambda v: update_config('ansi_colors', v))
        self.txt_clean_chk.toggled.connect(lambda v: update_config('txt_clean', v))
        self.txt_markdown_chk.toggled.connect(lambda v: update_config('txt_markdown', v))
        self.txt_crt_chk.toggled.connect(lambda v: update_config('txt_crt', v))
        self.txt_bubbles_chk.toggled.connect(lambda v: update_config('txt_bubbles', v))

        QShortcut(QKeySequence("Ctrl+F"), self).activated.connect(lambda: self.filter_edit.setFocus())
        QShortcut(QKeySequence("Escape"), self.filter_edit).activated.connect(self._clear_filter)

    def _on_table_context_menu(self, pos):
        item = self.table.itemAt(pos)
        if not item: return
        row = item.row()
        if row >= len(self._items): return
        from PySide6.QtWidgets import QMenu
        menu = QMenu(self); export_action = menu.addAction("Export This File Only")
        action = menu.exec_(self.table.viewport().mapToGlobal(pos))
        if action == export_action:
            for it in self._items: it.checked = False
            self._items[row].checked = True; self._refresh_table(); self._start_export()

    def _on_mode_changed(self, idx): self.config.mode = list(StudioMode)[idx]; self._debounce_timer.start()

    def _invalidate_preview(self): self._cached_mp = None; self._preview_scratch = None; self._update_preview()

    def _scan_dir(self, path):
        self._items.clear(); self._item_paths.clear()
        if not os.path.isdir(path): return
        max_depth = self.config.scan_depth if self.config.recursive_scan else 1
        skip_dirs = {".git", ".hg", ".svn", "__pycache__", "node_modules", ".venv", "venv", ".env", ".idea", ".vscode", "dist", "build", ".tox", ".mypy_cache", ".pytest_cache"}
        found = []
        for dirpath, dirnames, filenames in os.walk(path):
            rel = os.path.relpath(dirpath, path); depth = 1 if rel == "." else rel.count(os.sep) + 2
            if depth > max_depth: dirnames.clear(); continue
            dirnames[:] = [d for d in dirnames if d not in skip_dirs and not d.startswith(".")]
            for fname in sorted(filenames):
                ext = os.path.splitext(fname)[1].lower()
                if ext in SUPPORTED_EXTENSIONS: found.append(FileItem(path=os.path.join(dirpath, fname), checked=False))
        self._items = found; self._item_paths = {it.path for it in found}; self._refresh_table()

    def _add_files(self):
        paths, _ = QFileDialog.getOpenFileNames(self, "Select Files", "", "All Supported Files (*.py *.js *.txt *.md *.csv *.asc *.emoji *.json)")
        for p in paths:
            if p not in self._item_paths: item = FileItem(path=p, checked=False); self._items.append(item); self._item_paths.add(p)
        self._refresh_table()

    def _clear_list(self): self._items.clear(); self._item_paths.clear(); self._refresh_table(); self._invalidate_preview()

    def _select_all(self):
        for it in self._items: it.checked = True
        self._refresh_table_keep_filter(); self._update_sel_count(); self._debounce_timer.start()

    def _deselect_all(self):
        for it in self._items: it.checked = False
        self._refresh_table_keep_filter(); self._update_sel_count(); self._debounce_timer.start()

    def _populate_folder_filter(self):
        if not hasattr(self, 'folder_filter_cb'): return
        current_folder = self.folder_filter_cb.currentText()
        folders = set()
        for it in self._items:
            rel = os.path.relpath(it.path, str(INPUT_DIR))
            folder = os.path.dirname(rel)
            if folder == ".": folder = "[Root]"
            elif folder.startswith(".."): folder = "[External]"
            folders.add(folder)
        
        self.folder_filter_cb.blockSignals(True)
        self.folder_filter_cb.clear()
        self.folder_filter_cb.addItem("📁 All Folders")
        for f in sorted(folders):
            self.folder_filter_cb.addItem(f)
        idx = self.folder_filter_cb.findText(current_folder)
        if idx != -1: self.folder_filter_cb.setCurrentIndex(idx)
        self.folder_filter_cb.blockSignals(False)

    def _sync_filter_to_mode(self):
        mode = self.config.mode
        if mode == StudioMode.TEXT_EMOJI:
            self.type_filter_cb.setCurrentText("Text/Art")
        else:
            self.type_filter_cb.setCurrentText("Code")
        self._apply_filter()
        self.statusBar().showMessage(f"Filter synced to mode: {self.type_filter_cb.currentText()}", 2000)

    def _apply_filter(self):
        if not hasattr(self, 'filter_edit'): return
        text = self.filter_edit.text().strip()
        ext_filter = self.ext_filter_cb.currentText()
        type_filter = self.type_filter_cb.currentText()
        folder_filter = self.folder_filter_cb.currentText()
        case_sensitive = self.case_chk.isChecked()
        needle = text if case_sensitive else text.lower()

        for i, item in enumerate(self._items):
            # 1. Text match
            name = os.path.basename(item.path)
            path = item.path
            if not case_sensitive: name = name.lower(); path = path.lower()
            match_text = (needle in name) or (needle in path) if needle else True
            
            # 2. Ext match
            ext = os.path.splitext(item.path)[1].lower()
            match_ext = (ext_filter == "📂 All") or (ext == ext_filter.lower())
            
            # 3. Type/Category match
            match_type = True
            if type_filter != "All" and type_filter in FILE_CATEGORIES:
                match_type = ext in FILE_CATEGORIES[type_filter]
                
            # 4. Subfolder match
            match_folder = True
            if folder_filter != "📁 All Folders":
                rel = os.path.relpath(item.path, str(INPUT_DIR))
                folder = os.path.dirname(rel)
                if folder == ".": folder = "[Root]"
                elif folder.startswith(".."): folder = "[External]"
                match_folder = (folder == folder_filter)
                
            self.table.setRowHidden(i, not (match_text and match_ext and match_type and match_folder))
        self._update_sel_count()

    def _clear_filter(self):
        self.filter_edit.clear()
        self.ext_filter_cb.setCurrentIndex(0)
        self.type_filter_cb.setCurrentIndex(0)
        self.folder_filter_cb.setCurrentIndex(0)
        self.case_chk.setChecked(False)

    def _select_visible(self):
        for i in range(self.table.rowCount()):
            if not self.table.isRowHidden(i) and i < len(self._items):
                self._items[i].checked = True
        self._refresh_table_keep_filter()
        self._update_sel_count()
        self._debounce_timer.start()

    def _deselect_visible(self):
        for i in range(self.table.rowCount()):
            if not self.table.isRowHidden(i) and i < len(self._items):
                self._items[i].checked = False
        self._refresh_table_keep_filter()
        self._update_sel_count()
        self._debounce_timer.start()

    def _refresh_table_keep_filter(self):
        """Refresh table contents but re-apply the current filter afterwards."""
        self.table.blockSignals(True)
        self.table.setRowCount(len(self._items))
        for i, item in enumerate(self._items):
            chk = QTableWidgetItem()
            chk.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled)
            chk.setCheckState(Qt.Checked if item.checked else Qt.Unchecked)
            self.table.setItem(i, 0, chk)
            self.table.setItem(i, 1, QTableWidgetItem(os.path.basename(item.path)))
            self.table.setItem(i, 2, QTableWidgetItem(item.status))
        self.table.blockSignals(False)
        self._apply_filter()

    def _update_sel_count(self):
        count = sum(1 for it in self._items if it.checked)
        total = len(self._items)
        if hasattr(self, 'table') and self.table.rowCount() == total:
            visible = sum(1 for i in range(self.table.rowCount()) if not self.table.isRowHidden(i))
            if visible < total:
                self._sel_count_lbl.setText(f"{count}/{total} sel · {visible} shown")
            else:
                self._sel_count_lbl.setText(f"{count}/{total} selected")
        else:
            self._sel_count_lbl.setText(f"{count}/{total} selected")

    def _refresh_table(self):
        self.table.blockSignals(True); self.table.setRowCount(len(self._items))
        for i, item in enumerate(self._items):
            chk = QTableWidgetItem(); chk.setFlags(Qt.ItemIsUserCheckable | Qt.ItemIsEnabled); chk.setCheckState(Qt.Checked if item.checked else Qt.Unchecked)
            self.table.setItem(i, 0, chk); self.table.setItem(i, 1, QTableWidgetItem(os.path.basename(item.path))); self.table.setItem(i, 2, QTableWidgetItem(item.status))
        self.table.blockSignals(False)
        if hasattr(self, 'filter_edit'):
            self._populate_folder_filter()
            self._apply_filter()
        if hasattr(self, '_sel_count_lbl'):
            self._update_sel_count()

    def _on_item_changed(self, item):
        row = item.row()
        if item.column() == 0:
            self._items[row].checked = item.checkState() == Qt.Checked
            self._update_sel_count(); self._debounce_timer.start()

    def _update_preview(self):
        if self._cached_mp is None:
            strategy = self.strategies[self.config.mode]
            self._cached_mp = strategy.build_panes(self.config, self._items, self.config.custom_code)
            if self._cached_mp: self._preview_scratch = QImage(self._cached_mp.frame_w, self._cached_mp.frame_h, QImage.Format_RGB32)
        if not self._cached_mp: return
        t_start = _time.perf_counter(); t = self._cached_mp.duration() * self._preview_progress
        
        if self.config.mode == StudioMode.MULTI_WINDOW:
            active_lbl, active_g_pad, active_g_chrome, active_g_code = self.mw_preview_lbl, self.mw_g_pad, self.mw_g_chrome, self.mw_g_code
            active_slider, active_time_lbl, active_stats = self.mw_slider, self.mw_time_lbl, self.mw_stats_lbl
        elif self.config.mode == StudioMode.JR_VS_SR:
            active_lbl, active_g_pad, active_g_chrome, active_g_code = self.jr_preview_lbl, self.jr_g_pad, self.jr_g_chrome, self.jr_g_code
            active_slider, active_time_lbl, active_stats = self.jr_slider, self.jr_time_lbl, self.jr_stats_lbl
        elif self.config.mode == StudioMode.CODE_YT:
            active_lbl, active_g_pad, active_g_chrome, active_g_code = self.yt_preview_lbl, self.yt_g_pad, self.yt_g_chrome, self.yt_g_code
            active_slider, active_time_lbl, active_stats = self.yt_slider, self.yt_time_lbl, self.yt_stats_lbl
        elif self.config.mode == StudioMode.TEXT_EMOJI:
            active_lbl, active_g_pad, active_g_chrome, active_g_code = self.txt_preview_lbl, self.txt_g_pad, self.txt_g_chrome, self.txt_g_code
            active_slider, active_time_lbl, active_stats = self.txt_slider, self.txt_time_lbl, self.txt_stats_lbl
        else: return
        
        draw_guides = active_g_pad.isChecked() or active_g_chrome.isChecked() or active_g_code.isChecked()
        img = self._cached_mp.render_frame(t, self._preview_scratch, draw_guides=draw_guides)
        if self.config.txt_crt:
            p = QPainter(img); p.setPen(Qt.NoPen); p.setBrush(QColor(0, 0, 0, 80))
            for y in range(0, img.height(), 3): p.drawRect(0, y, img.width(), 1)
            p.setBrush(QColor(0, 255, 0, 20)); p.drawRect(0, 0, img.width(), img.height()); p.end()
        active_lbl.setPixmap(QPixmap.fromImage(img).scaled(active_lbl.size(), Qt.KeepAspectRatio, Qt.SmoothTransformation))
        render_time = (_time.perf_counter() - t_start) * 1000; dur = self._cached_mp.duration()
        active_time_lbl.setText(f"{int(t//60)}:{int(t%60):02d} / {int(dur//60)}:{int(dur%60):02d}")
        total_chars = sum(len(a.display_chars) for _, a, _ in self._cached_mp.panes)
        visible_chars = sum(a.visible_at(t) for _, a, _ in self._cached_mp.panes)
        active_stats.setText(f"Render: {render_time:.1f}ms | Chars: {visible_chars}/{total_chars}")
        if not self._preview_animating:
            active_slider.blockSignals(True); active_slider.setValue(int(self._preview_progress * 1000)); active_slider.blockSignals(False)

    def _on_slider_changed(self, mode, val):
        if mode != self.config.mode: return
        self._preview_progress = val / 1000.0
        self._preview_anim_t = self._preview_progress * (self._cached_mp.duration() if self._cached_mp else 0)
        self._update_preview()

    def _toggle_preview(self, mode):
        if mode != self.config.mode: return
        if self._preview_animating:
            self._preview_animating = False; self._preview_timer.stop(); self._audio_player.stop()
            if mode == StudioMode.MULTI_WINDOW: self.mw_play_btn.setText("▶ Animate")
            elif mode == StudioMode.JR_VS_SR: self.jr_play_btn.setText("▶ Animate")
            elif mode == StudioMode.CODE_YT: self.yt_play_btn.setText("▶ Animate")
            elif mode == StudioMode.TEXT_EMOJI: self.txt_play_btn.setText("▶ Animate")
        else:
            if self._cached_mp is None: return
            self._preview_animating = True
            if self._preview_anim_t >= self._cached_mp.duration(): self._preview_anim_t = 0
            if mode == StudioMode.MULTI_WINDOW: self.mw_play_btn.setText("⏸ Pause")
            elif mode == StudioMode.JR_VS_SR: self.jr_play_btn.setText("⏸ Pause")
            elif mode == StudioMode.CODE_YT: self.yt_play_btn.setText("⏸ Pause")
            elif mode == StudioMode.TEXT_EMOJI: self.txt_play_btn.setText("⏸ Pause")
            
            if self.config.sound_enabled:
                try:
                    if self.config.mode == StudioMode.JR_VS_SR:
                        sg1 = SimpleSoundGen(preset=self.config.jr_sound, stereo=self.config.stereo)
                        pcm1 = sg1.generate_pcm(self._cached_mp.panes[0][1].char_timestamps(), 1.0)
                        sg2 = SimpleSoundGen(preset=self.config.sr_sound, stereo=self.config.stereo)
                        pcm2 = sg2.generate_pcm(self._cached_mp.panes[1][1].char_timestamps(), 1.0)
                        
                        max_len = max(len(pcm1), len(pcm2))
                        mix = np.zeros(max_len, dtype=np.int32)
                        mix[:len(pcm1)] += pcm1
                        mix[:len(pcm2)] += pcm2
                        pcm = np.clip(mix, -32768, 32767).astype(np.int16)
                        
                        channels, sample_rate = (2 if self.config.stereo else 1), sg1.sr
                    else:
                        sg = SimpleSoundGen(preset=self.config.sound_preset, stereo=self.config.stereo)
                        pcm = sg.generate_pcm(self._cached_mp.char_timestamps_all(), 1.0) 
                        channels, sample_rate = (2 if sg.stereo else 1), sg.sr

                    if len(pcm) > 0:
                        buf = io.BytesIO()
                        with wave.open(buf, "w") as wf:
                            wf.setnchannels(channels)
                            wf.setsampwidth(2)
                            wf.setframerate(sample_rate)
                            wf.writeframes(pcm.tobytes())
                        self._audio_buf = QBuffer(); self._audio_buf.setData(buf.getvalue()); self._audio_buf.open(QIODevice.ReadOnly)
                        self._audio_out.setVolume(self.config.volume / 100.0)
                        self._audio_player.setSourceDevice(self._audio_buf, QUrl())
                        self._audio_player.play()
                except Exception:
                    logger.error("Failed to generate preview audio", exc_info=True)
            self._preview_timer.start()

    def _advance_preview(self):
        if not self._cached_mp: return
        self._preview_anim_t += 0.033; dur = self._cached_mp.duration()
        if self._preview_anim_t >= dur: self._preview_anim_t = dur; self._toggle_preview(self.config.mode)
        self._preview_progress = self._preview_anim_t / dur if dur > 0 else 0; self._update_preview()

    def _start_export(self):
        if self.config.use_custom: items = [FileItem(path="custom_code.py", checked=True)]
        else: items = [it for it in self._items if it.checked]
        if not items: QMessageBox.information(self, "Nothing selected", "Check files to export or enable Custom Code."); return
        
        for it in self._items:
            if it.checked: it.status = "Pending"
        self._refresh_table()
        
        self.export_commands.clear()
        self._batch_cancelled = False
        self.batch_done = 0
        self.batch_start_time = _time.time()
        
        for item in items:
            base_name = os.path.splitext(os.path.basename(item.path))[0]; date_str = datetime.now().strftime("%Y%m%d")
            lang = EXT_TO_LANGUAGE.get(os.path.splitext(item.path)[1].lower(), "text")
            out_name = self.config.output_template.format(name=base_name, date=date_str, lang=lang) + ".mp4"
            out_path = str(OUTPUT_DIR / out_name)
            cmd = ExportCommand(item=item, output_path=out_path, config=copy.deepcopy(self.config))
            cmd.status = "Pending"
            self.export_commands.append(cmd)
            
        self.batch_total = len(self.export_commands)
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, self.batch_total)
        self.progress_bar.setValue(0)
        self.export_btn.setEnabled(False)
        self.skip_btn.setEnabled(True)
        self.cancel_btn.setEnabled(True)
        self.batch_info_lbl.setText(f"Starting batch of {self.batch_total} videos...")
        self._process_export_queue()

    def _process_export_queue(self):
        if not self.export_commands:
            self.export_btn.setEnabled(True)
            self.skip_btn.setEnabled(False)
            self.cancel_btn.setEnabled(False)
            self.progress_bar.setVisible(False)
            self.batch_info_lbl.setText("Batch complete!")
            QMessageBox.information(self, "Done", "Batch export complete!")
            if self.shutdown_chk.isChecked():
                self._perform_shutdown()
            return
            
        self.current_command = self.export_commands.popleft()
        self.current_command.status = "Running"
        self.current_command.item.status = "Running"
        self._refresh_table()
        
        self.statusBar().showMessage(f"Preparing {os.path.basename(self.current_command.output_path)}...")
        QApplication.processEvents()
        
        strategy = self.strategies[self.config.mode]
        try:
            self.current_command.mp = strategy.build_panes(self.current_command.config, [self.current_command.item], self.current_command.config.custom_code)
        except Exception as e:
            logger.error(f"Failed to build panes for {self.current_command.output_path}", exc_info=True)
            self._on_item_failed(self.current_command, str(e))
            return
            
        if not self.current_command.mp:
            self._on_item_failed(self.current_command, "Empty renderer")
            return
            
        self._exporter = VideoExporter(self.current_command)
        self._exporter.progress.connect(self._on_export_progress)
        self._exporter.status.connect(lambda s: self.statusBar().showMessage(s))
        self._exporter.finished_ok.connect(lambda p: self._on_item_done(self.current_command, p))
        self._exporter.error.connect(lambda e: self._on_item_failed(self.current_command, e))
        self._exporter.start()

    def _on_export_progress(self, p):
        item_name = os.path.basename(self.current_command.output_path)
        self.statusBar().showMessage(f"Rendering {item_name}: {p}%")
        
        total_progress = self.batch_done + (p / 100.0)
        pct = int((total_progress / self.batch_total) * 100) if self.batch_total > 0 else 0
        
        elapsed = _time.time() - self.batch_start_time
        if total_progress > 0:
            eta = (elapsed / total_progress) * (self.batch_total - total_progress)
            eta_str = f"{int(eta // 60)}m {int(eta % 60)}s"
        else:
            eta_str = "..."
            
        self.batch_info_lbl.setText(f"Item {self.batch_done + 1}/{self.batch_total} | Overall: {pct}% | ETA: {eta_str}")
        self.progress_bar.setValue(int(total_progress))

    def _on_item_done(self, cmd, path): 
        cmd.item.status = "Done"
        self.batch_done += 1
        self._refresh_table()
        self.progress_bar.setValue(self.batch_done)
        self._process_export_queue()
        
    def _on_item_failed(self, cmd, err):
        if self._batch_cancelled:
            cmd.item.status = "Cancelled"
            self._refresh_table()
            return
            
        cmd.item.status = "Skipped" if err == "Cancelled" else "Failed"
        self.batch_done += 1
        self._refresh_table()
        self.progress_bar.setValue(self.batch_done)
        self.statusBar().showMessage(f"Item {os.path.basename(cmd.output_path)} {cmd.item.status}.", 2000)
        self._process_export_queue()

    def _skip_current(self):
        if self._exporter:
            self.statusBar().showMessage(f"Skipping {os.path.basename(self.current_command.output_path)}...")
            self._exporter.cancel() 

    def _cancel_export(self): 
        self._batch_cancelled = True
        if self._exporter: self._exporter.cancel()
        self.export_commands.clear()
        if self.current_command: self.current_command.item.status = "Cancelled"
        self._refresh_table()
        self.export_btn.setEnabled(True)
        self.skip_btn.setEnabled(False)
        self.cancel_btn.setEnabled(False)
        self.progress_bar.setVisible(False)
        self.batch_info_lbl.setText("Batch cancelled")
        self.statusBar().showMessage("Batch export cancelled", 3000)

    def _perform_shutdown(self):
        reply = QMessageBox.question(self, "Auto Action", "Batch export complete. Do you want to shutdown the PC now?", QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        if reply == QMessageBox.Yes:
            try:
                if platform.system() == "Windows":
                    subprocess.run(["shutdown", "/s", "/t", "30"])
                elif platform.system() == "Linux":
                    subprocess.run(["shutdown", "-h", "now"])
                elif platform.system() == "Darwin":
                    subprocess.run(["shutdown", "-h", "now"])
            except Exception:
                pass

    def _save_project(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save Project", "", "Studio Project (*.studio)")
        if not path: return
        config_dict = asdict(self.config)
        config_dict['mode'] = self.config.mode.value
        with open(path, "w", encoding="utf-8") as f: json.dump(config_dict, f, indent=2)
        self.statusBar().showMessage("Project saved!", 3000)

    def _load_project(self):
        path, _ = QFileDialog.getOpenFileName(self, "Load Project", "", "Studio Project (*.studio)")
        if not path: return
        try:
            with open(path, "r", encoding="utf-8") as f: data = json.load(f)
            if 'mode' in data and isinstance(data['mode'], str):
                data['mode'] = StudioMode(data['mode'])
            self.config = StudioConfig(**data)
        except Exception:
            logger.error("Failed to load project file", exc_info=True)
            QMessageBox.warning(self, "Load Error", "Failed to load project. The file might be corrupted.")
            return

        self.mode_tabs.setCurrentIndex(list(StudioMode).index(self.config.mode))

        self.theme_cb.setCurrentText(self.config.theme)
        self.res_cb.setCurrentText(self.config.resolution)
        self.fps_sp.setValue(self.config.fps)
        self.sound_chk.setChecked(self.config.sound_enabled)
        self.preset_cb.setCurrentText(self.config.sound_preset)
        self.stereo_chk.setChecked(self.config.stereo)
        self.vol_sp.setValue(self.config.volume)
        self.encoder_cb.setCurrentText(self.config.encoder)
        self.bgm_edit.setText(self.config.bgm_path)
        self.bgm_vol_sp.setValue(self.config.bgm_volume)
        self.bgm_duck_chk.setChecked(self.config.bgm_duck)
        self.use_custom_chk.setChecked(self.config.use_custom)
        self.custom_editor.setPlainText(self.config.custom_code)
        self.yt_extras_chk.setChecked(self.config.yt_extras)
        self.kb_enabled_chk.setChecked(self.config.kb_enabled)
        self.kb_layout_cb.setCurrentText(self.config.kb_layout)
        self.kb_position_cb.setCurrentText(self.config.kb_position)
        self.kb_opacity_sp.setValue(self.config.kb_opacity)
        self.recursive_chk.setChecked(self.config.recursive_scan)
        self.depth_sp.setValue(self.config.scan_depth)
        self.output_template_edit.setText(self.config.output_template)
        
        self.mw_font_cb.setCurrentText(self.config.font_mw)
        self.mw_font_sz_auto.setChecked(self.config.font_sz_auto_mw)
        self.mw_font_sz_sp.setValue(self.config.font_sz_mw)
        self.mw_2_font_cb.setCurrentText(self.config.font_mw_2)
        self.mw_2_font_sz_auto.setChecked(self.config.font_sz_auto_mw_2)
        self.mw_2_font_sz_sp.setValue(self.config.font_sz_mw_2)
        self.mw_3_font_cb.setCurrentText(self.config.font_mw_3)
        self.mw_3_font_sz_auto.setChecked(self.config.font_sz_auto_mw_3)
        self.mw_3_font_sz_sp.setValue(self.config.font_sz_mw_3)
        self.mw_4_font_cb.setCurrentText(self.config.font_mw_4)
        self.mw_4_font_sz_auto.setChecked(self.config.font_sz_auto_mw_4)
        self.mw_4_font_sz_sp.setValue(self.config.font_sz_mw_4)
        self.mw_layout_cb.setCurrentText(self.config.layout_mw)
        self._update_mw_layout_visibility()
        self.mw_wpm_sp.setValue(self.config.wpm_mw)
        self.mw_typo_sp.setValue(self.config.typo_mw)
        self.mw_shorts_chk.setChecked(self.config.shorts_mw)
        self.diff_highlight_mw_chk.setChecked(self.config.diff_highlight_mw)
        self.sync_mw_chk.setChecked(self.config.sync_mw)
        self.mw_ratio_sp.setValue(self.config.mw_ratio)
        
        self.jr_font_cb.setCurrentText(self.config.font_jr)
        self.jr_font_sz_auto.setChecked(self.config.font_sz_auto_jr)
        self.jr_font_sz_sp.setValue(self.config.font_sz_jr)
        self.sr_font_cb.setCurrentText(self.config.font_sr)
        self.sr_font_sz_auto.setChecked(self.config.font_sz_auto_sr)
        self.sr_font_sz_sp.setValue(self.config.font_sz_sr)
        self.jr_layout_cb.setCurrentText(self.config.layout_jr)
        self.jr_wpm_sp.setValue(self.config.jr_wpm)
        self.sr_wpm_sp.setValue(self.config.sr_wpm)
        self.jr_typo_sp.setValue(self.config.typo_jr)
        self.jr_sound_cb.setCurrentText(self.config.jr_sound)
        self.sr_sound_cb.setCurrentText(self.config.sr_sound)
        self.jr_custom_editor.setPlainText(self.config.jr_custom_code)
        self.sr_custom_editor.setPlainText(self.config.sr_custom_code)
        
        self.yt_font_cb.setCurrentText(self.config.font_yt)
        self.yt_font_sz_auto.setChecked(self.config.font_sz_auto_yt)
        self.yt_font_sz_sp.setValue(self.config.font_sz_yt)
        self.yt_wpm_sp.setValue(self.config.wpm_yt)
        self.yt_typo_sp.setValue(self.config.typo_yt)
        self.yt_zoom_chk.setChecked(self.config.yt_zoom)
        self.yt_focus_chk.setChecked(self.config.yt_focus)
        
        self.txt_font_cb.setCurrentText(self.config.font_txt)
        self.txt_font_sz_auto.setChecked(self.config.font_sz_auto_txt)
        self.txt_font_sz_sp.setValue(self.config.font_sz_txt)
        self.txt_wpm_sp.setValue(self.config.wpm_txt)
        self.txt_typo_sp.setValue(self.config.typo_txt)
        self.txt_shorts_chk.setChecked(self.config.shorts_txt)
        self.ascii_chk.setChecked(self.config.ascii_art)
        self.ansi_chk.setChecked(self.config.ansi_colors)
        self.txt_clean_chk.setChecked(self.config.txt_clean)
        self.txt_markdown_chk.setChecked(self.config.txt_markdown)
        self.txt_crt_chk.setChecked(self.config.txt_crt)
        self.txt_bubbles_chk.setChecked(self.config.txt_bubbles)
        
        self.statusBar().showMessage("Project loaded!", 3000)
        self._invalidate_preview()

    def _load_settings(self):
        if not SETTINGS_FILE.exists(): return
        try:
            with open(SETTINGS_FILE, "r") as f: data = json.load(f)
            self.mode_tabs.setCurrentIndex(data.get("mode_idx", 0)); self.theme_cb.setCurrentText(data.get("theme", "Dracula"))
            self.shutdown_chk.setChecked(data.get("shutdown_when_done", False))
        except Exception:
            logger.error("Failed to load settings.json", exc_info=True)

    def closeEvent(self, e):
        with open(SETTINGS_FILE, "w") as f: json.dump({"mode_idx": self.mode_tabs.currentIndex(), "theme": self.config.theme, "shutdown_when_done": self.shutdown_chk.isChecked()}, f)
        super().closeEvent(e)

# =====================================================================
# 11. ENTRY POINT
# =====================================================================

STYLE = """
QMainWindow, QDialog { background: #1e1e2e; }
QGroupBox { color: #cdd6f4; font-weight: bold; font-size: 12px; border: 1px solid #45475a; border-radius: 8px; margin-top: 10px; padding-top: 14px; }
QGroupBox::title { subcontrol-origin: margin; left: 12px; }
QLabel { color: #cdd6f4; }
QCheckBox { color: #cdd6f4; spacing: 6px; }
QCheckBox::indicator { width: 16px; height: 16px; border-radius: 3px; border: 1px solid #45475a; background: #313244; }
QCheckBox::indicator:checked { background: #89b4fa; border-color: #89b4fa; }
QTableWidget { background: #181825; color: #cdd6f4; gridline-color: #313244; border: none; outline: none; border-radius: 6px; }
QTableWidget::item { padding: 4px 6px; border-bottom: 1px solid #11111b; }
QTableWidget::item:selected { background: #89b4fa; color: #1e1e2e; }
QHeaderView::section { background: #1e1e2e; color: #a6adc8; border: none; padding: 4px; font-size: 10px; border-radius: 0; }
QComboBox, QSpinBox, QDoubleSpinBox, QLineEdit { background: #313244; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; padding: 4px 8px; min-height: 22px; }
QComboBox::drop-down { border: none; }
QComboBox QAbstractItemView { background: #313244; color: #cdd6f4; selection-background-color: #89b4fa; selection-color: #1e1e2e; border: 1px solid #45475a; }
QPushButton { background: #313244; color: #cdd6f4; border: 1px solid #45475a; border-radius: 6px; padding: 6px 12px; min-height: 22px; }
QPushButton:hover { background: #45475a; border-color: #89b4fa; }
QProgressBar { background: #313244; border: none; border-radius: 4px; text-align: center; color: #cdd6f4; min-height: 20px; }
QProgressBar::chunk { background: #89b4fa; border-radius: 4px; }
QTabWidget::pane { border: 1px solid #45475a; border-radius: 6px; background: #1e1e2e; top: -1px; }
QTabBar::tab { background: #313244; color: #a6adc8; padding: 6px 12px; border: 1px solid #45475a; border-bottom: none; border-top-left-radius: 6px; border-top-right-radius: 6px; font-weight: bold; }
QTabBar::tab:selected { background: #1e1e2e; color: #cdd6f4; border-bottom: 2px solid #89b4fa; }
QTabBar::tab:hover:!selected { background: #45475a; }
QPlainTextEdit { background: #11111b; color: #cdd6f4; border: 1px solid #45475a; border-radius: 4px; }
QSplitter { background: #11111b; }
QSplitter::handle { background: #181825; }
QSplitter::handle:horizontal { width: 8px; border-left: 1px solid #11111b; border-right: 1px solid #11111b; }
QSplitter::handle:horizontal:hover { background: #45475a; }
QSplitter::handle:vertical { height: 8px; border-top: 1px solid #11111b; border-bottom: 1px solid #11111b; }
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
    app = QApplication(sys.argv); app.setStyle("Fusion"); app.setStyleSheet(STYLE)
    pal = QPalette()
    pal.setColor(QPalette.Window, QColor("#1e1e2e")); pal.setColor(QPalette.WindowText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Base, QColor("#313244")); pal.setColor(QPalette.Text, QColor("#cdd6f4"))
    pal.setColor(QPalette.Button, QColor("#313244")); pal.setColor(QPalette.ButtonText, QColor("#cdd6f4"))
    pal.setColor(QPalette.Highlight, QColor("#89b4fa")); pal.setColor(QPalette.HighlightedText, QColor("#1e1e2e"))
    app.setPalette(pal)
    win = MainWindow(); win.show(); sys.exit(app.exec())
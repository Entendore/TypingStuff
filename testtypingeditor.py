#!/usr/bin/env python3
"""
ASCII / Unicode / Emoji Typing Video Studio — Complete Edition
==============================================================
All features, all improvements, one file.
"""
from __future__ import annotations

import bisect, copy, gc, io, json, logging, math, os, platform, queue, random, re, shutil, subprocess, sys, tempfile, threading, time as _time, unicodedata, wave, zlib
from collections import deque
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, asdict
from datetime import datetime
from enum import Enum, auto
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple, Union, runtime_checkable

import numpy as np
from PySide6.QtCore import (QEvent, QIODevice, QPoint, QPointF, QRect, QRectF, Qt, QThread, QTimer, QUrl, Signal, QBuffer, QSize)
from PySide6.QtGui import (QColor, QFont, QFontDatabase, QFontMetrics, QImage, QKeySequence, QLinearGradient, QPainter, QPainterPath, QPalette, QPen, QPixmap, QRadialGradient, QShortcut)
from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
from PySide6.QtWidgets import (QApplication, QCheckBox, QComboBox, QFileDialog, QFormLayout, QFrame, QGroupBox, QHBoxLayout, QHeaderView, QLabel, QLineEdit, QMainWindow, QMessageBox, QPlainTextEdit, QProgressBar, QPushButton, QScrollArea, QSlider, QSpinBox, QDoubleSpinBox, QSplitter, QTableWidget, QTableWidgetItem, QTabWidget, QVBoxLayout, QWidget)

try:
    from numba import njit
    _HAS_NUMBA = True
except ImportError:
    _HAS_NUMBA = False
try:
    import psutil
    _HAS_PSUTIL = True
except ImportError:
    _HAS_PSUTIL = False

logger = logging.getLogger("Studio")
logger.setLevel(logging.DEBUG)
_h = logging.FileHandler("studio.log", mode='w', encoding='utf-8')
_h.setFormatter(logging.Formatter("%(asctime)s %(levelname)s %(message)s"))
logger.addHandler(_h)
_h2 = logging.StreamHandler(sys.stderr)
_h2.setLevel(logging.ERROR)
_h2.setFormatter(logging.Formatter("[!] %(message)s"))
logger.addHandler(_h2)

CWD = Path.cwd()
INPUT_DIR, OUTPUT_DIR, TEMP_DIR = CWD/"input", CWD/"output", CWD/"temp"
SETTINGS_FILE = CWD/"settings.json"
for _d in (INPUT_DIR, OUTPUT_DIR, TEMP_DIR): _d.mkdir(parents=True, exist_ok=True)

SUPPORTED_EXTENSIONS = frozenset({".txt",".md",".csv",".asc",".ascii",".art",".nfo",".diz",".emoji",".emo",".u8",".utf8",".ansi"})
RESOLUTIONS = {"1920x1080":(1920,1080),"1280x720":(1280,720),"3840x2160":(3840,2160),"1080x1920 (9:16)":(1080,1920),"2560x1440":(2560,1440)}
ENCODERS = ["YouTube (H.264/AAC)","NVENC (NVIDIA)","QSV (Intel)","AMF (AMD)"]

THEMES = {
    "Dracula": {"background":"#282a36","foreground":"#f8f8f2","comment":"#6272a4","keyword":"#ff79c6","string":"#f1fa8c","number":"#bd93f9","function":"#50fa7b","builtin":"#8be9fd","operator":"#ff79c6","class_name":"#8be9fd","line_number":"#6272a4","current_line":"#44475a","cursor":"#f8f8f2","title_bar":"#21222c","title_text":"#8be9fd","window_border":"#191a21","accent":"#bd93f9"},
    "One Dark": {"background":"#282c34","foreground":"#abb2bf","comment":"#5c6370","keyword":"#c678dd","string":"#98c379","number":"#d19a66","function":"#61afef","builtin":"#e5c07b","operator":"#c678dd","class_name":"#e5c07b","line_number":"#4b5263","current_line":"#2c313c","cursor":"#528bff","title_bar":"#21252b","title_text":"#61afef","window_border":"#181a1f","accent":"#61afef"},
    "Solarized": {"background":"#002b36","foreground":"#93a1a1","comment":"#586e75","keyword":"#859900","string":"#2aa198","number":"#d33682","function":"#268bd2","builtin":"#b58900","operator":"#cb4b16","class_name":"#b58900","line_number":"#586e75","current_line":"#073642","cursor":"#eee8d5","title_bar":"#073642","title_text":"#2aa198","window_border":"#073642","accent":"#268bd2"},
    "Nord": {"background":"#2e3440","foreground":"#d8dee9","comment":"#616e88","keyword":"#81a1c1","string":"#a3be8c","number":"#b48ead","function":"#88c0d0","builtin":"#ebcb8b","operator":"#81a1c1","class_name":"#8fbcbb","line_number":"#4c566a","current_line":"#3b4252","cursor":"#eceff4","title_bar":"#292e39","title_text":"#88c0d0","window_border":"#292e39","accent":"#88c0d0"},
    "Gruvbox": {"background":"#282828","foreground":"#ebdbb2","comment":"#928374","keyword":"#fb4934","string":"#b8bb26","number":"#d3869b","function":"#fabd2f","builtin":"#fe8019","operator":"#fb4934","class_name":"#fabd2f","line_number":"#7c6f64","current_line":"#3c3836","cursor":"#ebdbb2","title_bar":"#1d2021","title_text":"#fabd2f","window_border":"#1d2021","accent":"#fabd2f"},
    "ASCII Classic": {"background":"#000000","foreground":"#00ff00","comment":"#008000","keyword":"#00ff00","string":"#00ffff","number":"#ffff00","function":"#ffffff","builtin":"#00ffff","operator":"#00ff00","class_name":"#ffffff","line_number":"#404040","current_line":"#102010","cursor":"#00ff00","title_bar":"#000000","title_text":"#00ff00","window_border":"#202020","accent":"#00ff00"},
    "Synthwave": {"background":"#1a0033","foreground":"#ff79c6","comment":"#5a3a8c","keyword":"#ff006e","string":"#ffbe0b","number":"#8338ec","function":"#3a86ff","builtin":"#ff006e","operator":"#fb5607","class_name":"#ffbe0b","line_number":"#5a3a8c","current_line":"#2d1b4e","cursor":"#ff79c6","title_bar":"#0d001a","title_text":"#ff006e","window_border":"#0d001a","accent":"#ffbe0b"},
    "Amber Term": {"background":"#0a0a00","foreground":"#ffb000","comment":"#665000","keyword":"#ffb000","string":"#ffff00","number":"#ff8800","function":"#ffcc00","builtin":"#ffaa00","operator":"#ffb000","class_name":"#ffdd00","line_number":"#443000","current_line":"#151500","cursor":"#ffb000","title_bar":"#000000","title_text":"#ffb000","window_border":"#000000","accent":"#ff8800"},
}

EMOJI_SHORTCODES = {":rocket:":"🚀",":fire:":"🔥",":sparkles:":"✨",":heart:":"❤️",":check:":"✅",":x:":"❌",":warning:":"⚠️",":star:":"⭐",":thumbsup:":"👍",":100:":"💯",":party:":"🎉",":tada:":"🎉",":cool:":"😎",":laugh:":"😂",":cry:":"😢",":think:":"🤔",":ok:":"👌",":wave:":"👋",":clap:":"👏",":pray:":"🙏",":muscle:":"💪",":brain:":"🧠",":eye:":"👀",":eyes:":"👀",":skull:":"💀",":ghost:":"👻",":robot:":"🤖",":alien:":"👽",":moon:":"🌙",":sun:":"☀️",":cloud:":"☁️",":bolt:":"⚡",":rainbow:":"🌈",":bug:":"🐛",":snake:":"🐍",":turtle:":"🐢",":whale:":"🐳",":cat:":"🐱",":dog:":"🐶",":unicorn:":"🦄",":dragon:":"🐉",":pizza:":"🍕",":coffee:":"☕",":beer:":"🍺",":taco:":"🌮",":burger:":"🍔",":cake:":"🍰",":apple:":"🍎",":computer:":"💻",":keyboard:":"⌨️",":mouse:":"🖱️",":phone:":"📱",":watch:":"⌚",":book:":"📚",":pencil:":"✏️",":art:":"🎨",":music:":"🎵",":game:":"🎮",":trophy:":"🏆",":medal:":"🏅",":target:":"🎯",":bomb:":"💣",":gear:":"⚙️",":mag:":"🔍",":bulb:":"💡",":bell:":"🔔",":lock:":"🔒",":key:":"🔑",":wrench:":"🔧",":hammer:":"🔨",":anchor:":"⚓",":crown:":"👑",":gem:":"💎",":clock:":"⏰",":hourglass:":"⏳",":map:":"🗺️",":flag:":"🏁",":rocket_launch:":"🚀",":angry:":"😠",":sad:":"😢",":happy:":"😊",":love:":"🥰",":shocked:":"😱",":sleepy:":"😴",":sick:":"🤢",":dizzy:":"💫",":poop:":"💩",":egg:":"🥚",":seedling:":"🌱",":tree:":"🌳",":flower:":"🌸",":cactus:":"🌵",":mushroom:":"🍄"}

ASCII_RAMPS = {"Standard (10)":" .'`^\",:;Il!i><~+_-?][}{1)(|/tfjrxnuvczXYUJCLQ0OZmwqpdbkhao*#MW&8%B@$","Blocks (4)":" ░▒▓█","Minimal (6)":" .:-=+*#%@","Binary (2)":" 01","Shade (5)":" ·∶∙•●","Dots (3)":" .·•","Hex (16)":" 0123456789ABCDEF","Braille (8)":" ⠂⠐⠠⠄⠠⠤⠴⠶⠦⠧⠇⠏⠧⠷⠿"}

# ═══════════════════════════════════════════════════════════════
# UNICODE & EMOJI UTILITIES
# ═══════════════════════════════════════════════════════════════

ZWJ, VS15, VS14 = '\u200d', '\ufe0f', '\ufe0e'
EMOJI_MOD_FITZ = range(0x1F3FB, 0x1F3FF+1)
_EMOJI_RANGES = [(0x00A9,0x00AE),(0x2000,0x3300),(0x1F1E6,0x1F1FF),(0x1F300,0x1F5FF),(0x1F600,0x1F64F),(0x1F680,0x1F6FF),(0x1F700,0x1F77F),(0x1F780,0x1F7FF),(0x1F800,0x1F8FF),(0x1F900,0x1F9FF),(0x1FA00,0x1FA6F),(0x1FA70,0x1FAFF),(0x2600,0x27BF),(0xFE00,0xFE0F)]
_EMOJI_SET = frozenset({c for lo,hi in _EMOJI_RANGES for c in range(lo,hi+1)})

def is_emoji_char(cp:int)->bool: return cp in _EMOJI_SET
def is_emoji(t:str)->bool:
    if not t: return False
    if ZWJ in t or VS15 in t: return True
    if any(ord(c) in EMOJI_MOD_FITZ for c in t): return True
    if len(t)>=2 and all(0x1F1E6<=ord(c)<=0x1F1FF for c in t[:2]): return True
    if len(t)>=2 and t[-1]=='\u20e3': return True
    return is_emoji_char(ord(t[0]))

def char_width(ch:str)->int:
    if not ch: return 0
    cp=ord(ch[0])
    if cp<0x20: return 4 if ch=='\t' else 0
    if ch in (ZWJ,VS15,VS14) or cp in EMOJI_MOD_FITZ or unicodedata.combining(ch)!=0: return 0
    if is_emoji_char(cp): return 2
    return 2 if unicodedata.east_asian_width(ch) in ('W','F') else 1

def split_graphemes(text:str)->List[str]:
    if not text: return []
    g=[]; i,n=0,len(text)
    while i<n:
        c=text[i]; i+=1
        if c=='\r' and i<n and text[i]=='\n': g.append('\r\n'); i+=1; continue
        if 0x1F1E6<=ord(c)<=0x1F1FF and i<n and 0x1F1E6<=ord(text[i])<=0x1F1FF: g.append(c+text[i]); i+=1; continue
        while i<n:
            nx=text[i]
            if nx==ZWJ:
                c+=nx; i+=1
                if i<n: c+=text[i]; i+=1
                continue
            if nx in(VS15,VS14) or ord(nx) in EMOJI_MOD_FITZ: c+=nx; i+=1; continue
            if nx=='\u20e3':
                c+=nx; i+=1
                if i<n and text[i]==VS15: c+=text[i]; i+=1
                continue
            if 0xE0030<=ord(nx)<=0xE007F or unicodedata.combining(nx)!=0: c+=nx; i+=1; continue
            break
        g.append(c)
    return g

def convert_shortcodes(t:str)->str:
    for c,e in EMOJI_SHORTCODES.items(): t=t.replace(c,e)
    return t

def read_text_file(path:Path, clean:bool=True)->str:
    ext=path.suffix.lower()
    encs=["utf-8"]
    if ext in(".nfo",".diz",".asc",".ascii",".art",".ansi"): encs=["cp437","cp850","latin-1","utf-8"]
    text=""
    for enc in encs:
        try: text=path.read_text(encoding=enc); break
        except(UnicodeDecodeError,LookupError): continue
    else: text=path.read_text(encoding="utf-8",errors="replace")
    text=convert_shortcodes(text)
    if clean and ext not in(".asc",".ascii",".art",".nfo",".diz",".emoji",".emo",".ansi"):
        text=text.replace("\xa0"," ").replace("\xad","")
        text=re.sub(r'[ \t]+\n','\n',text)
        text="\n".join(l.rstrip() for l in text.splitlines())
    return text.replace('\r\n','\n').replace('\r','\n')

# ═══════════════════════════════════════════════════════════════
# COLOR SYSTEM
# ═══════════════════════════════════════════════════════════════

class ColorMode(Enum):
    MONOCHROME="Monochrome"; ANSI="ANSI Escape Codes"; LUMINANCE="Luminance Mapped"
    SCRIPT="Unicode Script"; CATEGORY="Unicode Category"; SYNTAX="Syntax Highlight"
    RAINBOW="Rainbow"; GRADIENT="Gradient"; BLOCK_GLOW="Block Glow"

@dataclass(slots=True)
class ColorStop:
    pos: float; color: QColor

COLOR_PALETTES: Dict[str,List[ColorStop]]={
    "Fire":[ColorStop(0,QColor("#1a0500")),ColorStop(.2,QColor("#4d1300")),ColorStop(.4,QColor("#992100")),ColorStop(.6,QColor("#e63900")),ColorStop(.8,QColor("#ff8800")),ColorStop(1,QColor("#ffdd00"))],
    "Ocean":[ColorStop(0,QColor("#001428")),ColorStop(.2,QColor("#00294d")),ColorStop(.4,QColor("#004d80")),ColorStop(.6,QColor("#0080cc")),ColorStop(.8,QColor("#33b5e5")),ColorStop(1,QColor("#aaf0ff"))],
    "Forest":[ColorStop(0,QColor("#0a1a00")),ColorStop(.2,QColor("#1a3300")),ColorStop(.4,QColor("#2d6600")),ColorStop(.6,QColor("#44aa00")),ColorStop(.8,QColor("#88dd44")),ColorStop(1,QColor("#ddffaa"))],
    "Sunset":[ColorStop(0,QColor("#1a0033")),ColorStop(.2,QColor("#4d0066")),ColorStop(.4,QColor("#993366")),ColorStop(.6,QColor("#cc5599")),ColorStop(.8,QColor("#ff8866")),ColorStop(1,QColor("#ffdd99"))],
    "Ice":[ColorStop(0,QColor("#000a1a")),ColorStop(.2,QColor("#001a33")),ColorStop(.4,QColor("#003366")),ColorStop(.6,QColor("#336699")),ColorStop(.8,QColor("#99ccdd")),ColorStop(1,QColor("#ddf0ff"))],
    "Neon":[ColorStop(0,QColor("#0a0014")),ColorStop(.2,QColor("#1a0033")),ColorStop(.4,QColor("#660099")),ColorStop(.6,QColor("#ff00ff")),ColorStop(.8,QColor("#00ffff")),ColorStop(1,QColor("#ffff00"))],
    "Terminal Green":[ColorStop(0,QColor("#001a00")),ColorStop(.3,QColor("#003300")),ColorStop(.6,QColor("#00cc00")),ColorStop(.85,QColor("#33ff33")),ColorStop(1,QColor("#aaffaa"))],
    "Amber":[ColorStop(0,QColor("#0a0500")),ColorStop(.3,QColor("#1a0f00")),ColorStop(.6,QColor("#cc7700")),ColorStop(.85,QColor("#ffaa00")),ColorStop(1,QColor("#ffdd44"))],
    "Grayscale":[ColorStop(0,QColor("#000000")),ColorStop(.5,QColor("#555555")),ColorStop(1,QColor("#ffffff"))],
    "Dracula":[ColorStop(0,QColor("#21222c")),ColorStop(.2,QColor("#44475a")),ColorStop(.4,QColor("#6272a4")),ColorStop(.6,QColor("#bd93f9")),ColorStop(.8,QColor("#ff79c6")),ColorStop(1,QColor("#f8f8f2"))],
    "Synthwave":[ColorStop(0,QColor("#0d001a")),ColorStop(.2,QColor("#1a0033")),ColorStop(.4,QColor("#5a3a8c")),ColorStop(.6,QColor("#ff006e")),ColorStop(.8,QColor("#ffbe0b")),ColorStop(1,QColor("#3a86ff"))],
}

ANSI_COLORS={0:"#000000",1:"#800000",2:"#008000",3:"#808000",4:"#000080",5:"#800080",6:"#008080",7:"#c0c0c0",8:"#808080",9:"#ff0000",10:"#00ff00",11:"#ffff00",12:"#0000ff",13:"#ff00ff",14:"#00ffff",15:"#ffffff"}
_ANSI_RE=re.compile(r'\x1B\[(\d+(?:;\d+)*)?m')

@dataclass(slots=True)
class AnsiStyle:
    fg:Optional[QColor]=None; bg:Optional[QColor]=None; bold:bool=False; italic:bool=False; underline:bool=False; faint:bool=False

@dataclass(slots=True)
class AnsiSegment:
    text:str; style:AnsiStyle

def parse_ansi(text:str)->List[AnsiSegment]:
    segs:List[AnsiSegment]=[]; st=AnsiStyle(); pos=0
    for m in _ANSI_RE.finditer(text):
        if m.start()>pos: segs.append(AnsiSegment(text[pos:m.start()],copy.copy(st)))
        codes=[int(c) for c in m.group(1).split(';')] if m.group(1) else [0]
        i=0
        while i<len(codes):
            c=codes[i]
            match c:
                case 0: st=AnsiStyle()
                case 1: st.bold=True
                case 2: st.faint=True
                case 3: st.italic=True
                case 4: st.underline=True
                case 22: st.bold=False; st.faint=False
                case 23: st.italic=False
                case 24: st.underline=False
                case _ if 30<=c<=37: st.fg=QColor(ANSI_COLORS[c-30])
                case 38:
                    if i+2<len(codes) and codes[i+1]==5:
                        idx=codes[i+2]; st.fg=QColor(f"#{idx//36*51:02x}{(idx//6)%6*51:02x}{idx%6*51:02x}") if idx<216 else QColor(ANSI_COLORS.get(15-(idx-216),"#fff")); i+=2
                    elif i+4<len(codes) and codes[i+1]==2: st.fg=QColor(codes[i+2],codes[i+3],codes[i+4]); i+=4
                case _ if 40<=c<=47: st.bg=QColor(ANSI_COLORS[c-40])
                case 48:
                    if i+2<len(codes) and codes[i+1]==5:
                        idx=codes[i+2]; st.bg=QColor(f"#{idx//36*51:02x}{(idx//6)%6*51:02x}{idx%6*51:02x}") if idx<216 else QColor(ANSI_COLORS.get(15-(idx-216),"#000")); i+=2
                    elif i+4<len(codes) and codes[i+1]==2: st.bg=QColor(codes[i+2],codes[i+3],codes[i+4]); i+=4
                case _ if 90<=c<=97: st.fg=QColor(ANSI_COLORS[c-90+8])
                case _ if 100<=c<=107: st.bg=QColor(ANSI_COLORS[c-100+8])
            i+=1
        pos=m.end()
    if pos<len(text): segs.append(AnsiSegment(text[pos:],copy.copy(st)))
    elif not segs: segs.append(AnsiSegment(text,AnsiStyle()))
    return segs

_CHAR_LUM:Dict[str,float]={}
def _build_lum():
    ramp=" .'`^\",:;Il!i><~+_-?][}{1)(|/tfjrxnuvczXYUJCLQ0OZmwqpdbkhao*#MW&8%B@$"
    for i,ch in enumerate(ramp): _CHAR_LUM[ch]=i/max(1,len(ramp)-1)
    for i,ch in enumerate(" ░▒▓█"): _CHAR_LUM[ch]=i/4.0
    for cp in range(0x2500,0x2580): _CHAR_LUM[chr(cp)]=0.3
_build_lum()

def get_char_lum(ch:str)->float:
    if ch in _CHAR_LUM: return _CHAR_LUM[ch]
    if is_emoji(ch): return 0.8
    cp=ord(ch[0]) if ch else 0
    if 0x2580<=cp<=0x259F: return 0.5
    if 0x2500<=cp<=0x257F: return 0.3
    cat=unicodedata.category(ch)
    return 0.7 if cat.startswith('L') else (0.75 if cat.startswith('N') else (0.5 if cat.startswith('P') else 0.5))

def lerp_c(c1:QColor,c2:QColor,t:float)->QColor:
    t=max(0.0,min(1.0,t))
    return QColor(int(c1.r+(c2.r-c1.r)*t),int(c1.g+(c2.g-c1.g)*t),int(c1.b+(c2.b-c1.b)*t))
# Patch: QColor doesn't have .r/.g/.b — use red()/green()/blue()
def lerp_c(c1:QColor,c2:QColor,t:float)->QColor:
    t=max(0.0,min(1.0,t))
    return QColor(int(c1.red()+(c2.red()-c1.red())*t),int(c1.green()+(c2.green()-c1.green())*t),int(c1.blue()+(c2.blue()-c1.blue())*t))

def pal_lookup(pal:List[ColorStop],t:float)->QColor:
    t=max(0.0,min(1.0,t))
    if not pal: return QColor("#fff")
    if len(pal)==1: return pal[0].color
    for i in range(len(pal)-1):
        if pal[i].pos<=t<=pal[i+1].pos:
            lt=(t-pal[i].pos)/max(.001,pal[i+1].pos-pal[i].pos)
            return lerp_c(pal[i].color,pal[i+1].color,lt)
    return pal[-1].color

def detect_script(ch:str)->str:
    if not ch: return "common"
    cp=ord(ch[0])
    if is_emoji_char(cp): return "emoji"
    if 0x2500<=cp<=0x257F: return "box"
    if 0x2580<=cp<=0x259F: return "block"
    if 0x4E00<=cp<=0x9FFF: return "han"
    if 0x3040<=cp<=0x309F: return "hiragana"
    if 0x30A0<=cp<=0x30FF: return "katakana"
    if 0xAC00<=cp<=0xD7AF: return "hangul"
    if 0x0590<=cp<=0x05FF: return "hebrew"
    if 0x0600<=cp<=0x06FF: return "arabic"
    if 0x0900<=cp<=0x097F: return "devanagari"
    if 0x0400<=cp<=0x04FF: return "cyrillic"
    if 0x0370<=cp<=0x03FF: return "greek"
    cat=unicodedata.category(ch)
    if cat.startswith('L'): return "latin"
    if cat.startswith('N'): return "number"
    if cat.startswith('P'): return "punctuation"
    if cat.startswith('S'): return "symbol"
    return "common"

def detect_category(ch:str)->str:
    if not ch: return "other"
    if is_emoji(ch): return "emoji"
    cat=unicodedata.category(ch)
    if cat.startswith('Lu'): return "uppercase"
    if cat.startswith('Ll'): return "lowercase"
    if cat.startswith('L'): return "letter"
    if cat.startswith('N'): return "number"
    if cat.startswith('P'): return "punctuation"
    if cat.startswith('S'): return "symbol"
    if cat.startswith('Z'): return "space"
    return "other"

_URL_RE=re.compile(r'https?://[^\s]+|www\.[^\s]+')
_EMAIL_RE=re.compile(r'[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}')
_HASH_RE=re.compile(r'#[\w]+')
_MENTION_RE=re.compile(r'@[\w]+')
_CODE_RE=re.compile(r'`[^`]+`')

@dataclass(slots=True)
class SynMatch:
    s:int; e:int; kind:str

def detect_syntax(text:str)->List[SynMatch]:
    ms:List[SynMatch]=[]
    for m in _URL_RE.finditer(text): ms.append(SynMatch(m.start(),m.end(),'url'))
    for m in _EMAIL_RE.finditer(text): ms.append(SynMatch(m.start(),m.end(),'email'))
    for m in _HASH_RE.finditer(text): ms.append(SynMatch(m.start(),m.end(),'hashtag'))
    for m in _MENTION_RE.finditer(text): ms.append(SynMatch(m.start(),m.end(),'mention'))
    for m in _CODE_RE.finditer(text): ms.append(SynMatch(m.start(),m.end(),'code'))
    return ms

class ColorResolver:
    def __init__(self, cfg:'StudioConfig', theme:Dict[str,str]):
        self.cfg=cfg; self.theme=theme
        qc={k:QColor(v) for k,v in theme.items() if isinstance(v,str) and v.startswith("#")}
        self.fg=qc.get("foreground",QColor("#f8f8f2"))
        self.accent=qc.get("accent",QColor("#bd93f9"))
        self.kw=qc.get("keyword",QColor("#ff79c6"))
        self.str=qc.get("string",QColor("#f1fa8c"))
        self.num=qc.get("number",QColor("#bd93f9"))
        self.fn=qc.get("function",QColor("#50fa7b"))
        self.builtin=qc.get("builtin",QColor("#8be9fd"))
        self.cmt=qc.get("comment",QColor("#6272a4"))
        self.scripts={"latin":self.fg,"han":QColor("#f9e2af"),"hiragana":QColor("#f5c2e7"),"katakana":QColor("#f5c2e7"),"hangul":QColor("#89dceb"),"hebrew":QColor("#fab387"),"arabic":QColor("#f38ba8"),"devanagari":QColor("#cba6f7"),"cyrillic":QColor("#94e2d5"),"greek":QColor("#f9e2af"),"box":self.accent,"block":self.accent,"emoji":None,"number":self.num,"punctuation":self.cmt,"symbol":self.builtin,"common":self.fg}
        self.cats={"uppercase":self.kw,"lowercase":self.fg,"letter":self.fg,"number":self.num,"punctuation":self.cmt,"symbol":self.builtin,"space":None,"emoji":None,"other":self.fg}
        self.syn={"url":self.builtin,"email":self.fn,"hashtag":self.kw,"mention":self.str,"code":self.cmt}

    def resolve(self, g:str, li:int, ci:int, x:float, y:float, w:float, h:float, char_syntax:Dict[int,str]) -> Optional[QColor]:
        if self.cfg.txt_rainbow and self.cfg.ascii_art:
            return QColor.fromHsv((li*8+ci*4)%360,200,240)
        if self.cfg.txt_rainbow:
            return QColor.fromHsv((li*12+ci*6)%360,180,240)
        if self.cfg.txt_gradient:
            d=self.cfg.txt_gradient_dir
            t=y/max(1,h) if d=="Vertical" else (x/max(1,w) if d=="Horizontal" else (x/max(1,w)+y/max(1,h))/2)
            return QColor.fromHsv(int(max(0,min(1,t))*300)%360,200,240)
        # Syntax override
        kind=char_syntax.get(ci)
        if kind and kind in self.syn: return self.syn[kind]
        mode=self.cfg.txt_color_mode
        match mode:
            case "Luminance Mapped":
                if is_emoji(g): return None
                return pal_lookup(COLOR_PALETTES.get(self.cfg.txt_palette,COLOR_PALETTES["Dracula"]),get_char_lum(g))
            case "Unicode Script":
                return self.scripts.get(detect_script(g),self.fg)
            case "Unicode Category":
                return self.cats.get(detect_category(g),self.fg)
            case "Block Glow":
                if is_emoji(g): return None
                cp=ord(g[0]) if g else 0
                if 0x2580<=cp<=0x259F: return self.accent.lighter(130)
                if 0x2500<=cp<=0x257F: return self.accent
                return pal_lookup(COLOR_PALETTES.get("Dracula",COLOR_PALETTES["Dracula"]),get_char_lum(g))
            case _:  # Monochrome
                s=detect_script(g)
                return None if s=="emoji" else (self.accent if s in("box","block") else self.fg)

# ═══════════════════════════════════════════════════════════════
# DSP & SOUND
# ═══════════════════════════════════════════════════════════════

SR=48000
if _HAS_NUMBA:
    @njit(cache=True)
    def _nb_k(x,sr):
        n=len(x);y=np.empty(n,dtype=np.float64)
        if sr==48000:
            b0,b1,b2,a1,a2=1.535,-2.612,1.239,-1.690,0.733
            c0,c1,c2,d1,d2=1.0,-2.0,1.0,-1.990,0.990
        else:
            for i in range(n):y[i]=x[i]; return y
        z1=z2=0.0
        for i in range(n):
            xn=x[i];yn=b0*xn+z1;z1=b1*xn-a1*yn+z2;z2=b2*xn-a2*yn;y[i]=yn
        z1=z2=0.0
        for i in range(n):
            xn=y[i];yn=c0*xn+z1;z1=c1*xn-d1*yn+z2;z2=c2*xn-d2*yn;y[i]=yn
        return y

def _norm_lufs(x,sr,tl=-14.0):
    if len(x)<sr//2: return x
    if _HAS_NUMBA:
        xk=_nb_k(x.astype(np.float64),sr);ms=float(np.mean(xk**2))
        if ms<1e-20: return x
        cl=-0.691+10*np.log10(ms)
        if not np.isfinite(cl) or cl<=-70: return x
        return (x.astype(np.float64)*(10**((tl-cl)/20))).astype(np.float32)
    return x

class DSP:
    @staticmethod
    def env(n,sr,a=0.001,dr=30.0,ac=2.0):
        t=np.arange(n,dtype=np.float64)/sr;e=np.exp(-t*dr);as_=max(1,int(a*sr))
        if as_<n: e[:as_]=np.linspace(0,1,as_)**ac*np.exp(-np.arange(as_,dtype=np.float64)/sr*dr)
        return e
    @staticmethod
    def lp(c,sr=SR,nt=127):
        if nt%2==0:nt+=1
        fc=min(max(1.0,c),sr/2-1)/sr;n=np.arange(nt,dtype=np.float64);c_=(nt-1)/2
        h=np.sinc(2*fc*(n-c_));w=.42-.5*np.cos(2*np.pi*n/(nt-1))+.08*np.cos(4*np.pi*n/(nt-1));h*=w;s=np.sum(h)
        return h/s if s>0 else h
    @staticmethod
    def conv(x,h):
        n,nh=len(x),len(h)
        if nh<=1: return x*h[0] if nh else x
        nf=1<<((n+nh-1).bit_length())
        return np.fft.irfft(np.fft.rfft(x,nf)*np.fft.rfft(h,nf),nf)[:n]
    @staticmethod
    def f_lp(x,c,sr=SR): return DSP.conv(x,DSP.lp(c,sr))
    @staticmethod
    def f_hp(x,c,sr=SR):
        h=DSP.lp(c,sr,63);h=-h;h[len(h)//2]+=1;return DSP.conv(x,h)
    @staticmethod
    def f_bp(x,l,h,sr=SR): return DSP.f_lp(x,h,sr)-DSP.f_lp(x,l,sr)
    @staticmethod
    def sine(f,n,sr): return np.sin(2*np.pi*f*(np.arange(n,dtype=np.float64)/sr))
    @staticmethod
    def fm(c,mr,mi,n,sr):
        t=np.arange(n,dtype=np.float64)/sr; return np.sin(2*np.pi*c*t+mi*np.sin(2*np.pi*c*mr*t))
    @staticmethod
    def wnoise(n,rng): return rng.randn(n).astype(np.float64)
    @staticmethod
    def bnoise(n,rng):
        w=rng.randn(n).astype(np.float64);b=np.cumsum(w)-np.mean(w);pk=np.max(np.abs(b))
        return b/pk*.5 if pk>0 else b*.5
    @staticmethod
    def modal(ms,n,sr):
        t=np.arange(n,dtype=np.float64)/sr;o=np.zeros(n,dtype=np.float64)
        for f,d,a in ms: o+=np.sin(2*np.pi*f*t)*np.exp(-d*t)*a
        return o
    @staticmethod
    def i16(x,db=-1.0):
        pk=np.max(np.abs(x)) if len(x)>0 else 0
        return np.zeros_like(x,dtype=np.int16) if pk<1e-10 else np.clip(x*(10**(db/20)/pk)*32767,-32768,32767).astype(np.int16)

@dataclass(slots=True)
class Voice:
    osc:str="sine";freq:float=440;mr:float=1;mi:float=0;a:float=.001;dr:float=30;ac:float=2
    filt:str="none";fc:float=8000;fh:float=12000;drive:float=0;gain:float=.5;delay:float=0
    modes:Optional[List[Tuple[float,float,float]]]=None

@dataclass(slots=True)
class Sound:
    dur:float=.12;layers:List[Voice]=field(default_factory=list)

S_PRESETS={
    "Mechanical":Sound(.12,[Voice(osc="wnoise",a=.0001,dr=400,filt="bp",fc=3000,fh=6000,drive=1.5,gain=.5),Voice(osc="fm",freq=1200,mr=2,mi=.4,a=.0003,dr=80,filt="lp",fc=3500,gain=.35),Voice(osc="sine",freq=150,a=.0015,dr=50,filt="lp",fc=500,gain=.45,delay=.002)]),
    "Cherry MX Red":Sound(.10,[Voice(osc="wnoise",a=.0003,dr=250,filt="bp",fc=1500,fh=4000,gain=.15),Voice(osc="sine",freq=140,a=.0012,dr=40,filt="lp",fc=500,gain=.55),Voice(osc="sine",freq=70,a=.0015,dr=30,filt="lp",fc=250,gain=.5,delay=.001)]),
    "ASMR Deep Thock":Sound(.15,[Voice(osc="sine",freq=110,a=.003,dr=25,filt="lp",fc=400,gain=.75),Voice(osc="sine",freq=60,a=.004,dr=20,filt="lp",fc=200,gain=.6,delay=.001),Voice(osc="wnoise",a=.006,dr=45,filt="lp",fc=900,gain=.2)]),
    "Typewriter":Sound(.18,[Voice(osc="sine",freq=2000,a=.001,dr=15,filt="lp",fc=3000,gain=.6),Voice(osc="wnoise",a=.0005,dr=100,filt="bp",fc=1000,fh=3000,gain=.3,delay=.005)]),
    "Cyberpunk":Sound(.10,[Voice(osc="fm",freq=800,mr=3.5,mi=1.5,a=.0005,dr=40,filt="lp",fc=4000,gain=.4),Voice(osc="sine",freq=80,a=.002,dr=30,filt="lp",fc=200,gain=.5,delay=.001)]),
    "Crystal Chime":Sound(.40,[Voice(osc="modal",modes=[(1500,7,1),(3150,5,.5),(4950,3,.3),(7050,2,.2)],a=.0001,dr=7,filt="lp",fc=16000,gain=.5)]),
    "Soft Pop":Sound(.10,[Voice(osc="sine",freq=500,a=.0008,dr=60,filt="lp",fc=2000,gain=.35),Voice(osc="sine",freq=200,a=.001,dr=40,filt="lp",fc=800,gain=.4,delay=.001),Voice(osc="wnoise",a=.0003,dr=300,filt="bp",fc=3000,fh=6000,gain=.1)]),
}

E_SOUNDS={
    "🎉":Sound(.30,[Voice(osc="modal",modes=[(523,5,1),(659,4,.7),(784,3,.5),(1047,2,.3)],a=.001,dr=6,filt="lp",fc=12000,gain=.4),Voice(osc="wnoise",a=.0003,dr=150,filt="bp",fc=3000,fh=8000,gain=.15)]),
    "💥":Sound(.18,[Voice(osc="wnoise",a=.0001,dr=300,filt="bp",fc=200,fh=8000,drive=2,gain=.5),Voice(osc="sine",freq=80,a=.0003,dr=40,filt="lp",fc=300,gain=.4)]),
    "🔥":Sound(.20,[Voice(osc="wnoise",a=.0005,dr=80,filt="bp",fc=500,fh=3000,gain=.4),Voice(osc="bnoise",a=.001,dr=20,filt="lp",fc=400,gain=.3)]),
    "❤️":Sound(.20,[Voice(osc="sine",freq=440,a=.005,dr=8,filt="lp",fc=2000,gain=.5),Voice(osc="sine",freq=220,a=.006,dr=6,filt="lp",fc=1000,gain=.4,delay=.05)]),
    "⚡":Sound(.15,[Voice(osc="wnoise",a=.0001,dr=400,filt="bp",fc=2000,fh=10000,drive=1.5,gain=.4),Voice(osc="fm",freq=2000,mr=2.5,mi=1.5,a=.0002,dr=60,filt="hp",fc=1500,gain=.3)]),
}

class SoundEngine:
    def __init__(self,sr=SR): self.sr=sr
    def _voice(self,sp:Voice,n,rng)->np.ndarray:
        sig=np.zeros(n,dtype=np.float64)
        match sp.osc:
            case "sine": sig=DSP.sine(sp.freq,n,self.sr)
            case "fm": sig=DSP.fm(sp.freq,sp.mr,sp.mi,n,self.sr)
            case "wnoise": sig=DSP.wnoise(n,rng)
            case "bnoise": sig=DSP.bnoise(n,rng)
            case "modal" if sp.modes: sig=DSP.modal(sp.modes,n,self.sr)
        sig*=DSP.env(n,self.sr,sp.a,sp.dr,sp.ac)
        match sp.filt:
            case "lp": sig=DSP.f_lp(sig,sp.fc,self.sr)
            case "hp": sig=DSP.f_hp(sig,sp.fc,self.sr)
            case "bp": sig=DSP.f_bp(sig,sp.fc,sp.fh,self.sr)
        if sp.drive>0: sig=np.tanh(sig*sp.drive)/max(.001,np.tanh(sp.drive))
        d=int(sp.delay*self.sr)
        return np.concatenate([np.zeros(d,dtype=np.float64),sig[:n-d]])*sp.gain if d>0 and d<n else sig*sp.gain
    def render(self,sp:Sound,seed:int)->np.ndarray:
        rng=np.random.RandomState(seed);n=int(self.sr*sp.dur);mix=np.zeros(n,dtype=np.float64)
        for v in sp.layers: mix+=self._voice(v,n,rng)
        return DSP.i16(DSP.f_hp(mix,20,self.sr,63))

class SoundGen:
    _ROWS=("`1234567890-=","qwertyuiop[]\\","asdfghjkl;'","zxcvbnm,./")
    _SHIFT=[1.5,.5,-.5,-2.0]
    def __init__(self,sr=SR,preset="Mechanical",stereo=False):
        self.sr=sr;self.preset=preset;self.stereo=stereo
        eng=SoundEngine(sr);sp=S_PRESETS.get(preset,S_PRESETS["Mechanical"])
        self.clicks=[eng.render(sp,i) for i in range(32)]
        self.spaces=[eng.render(sp,100+i) for i in range(16)]
        self.enters=[eng.render(sp,200+i) for i in range(8)]
        self.emoji:Dict[str,List[np.ndarray]]={"default":[eng.render(Sound(.10,[Voice(osc="modal",modes=[(1200,8,1),(2400,5,.4)],a=.0002,dr=12,filt="lp",fc=10000,gain=.35)]),300+i) for i in range(8)]}
        for e,es in E_SOUNDS.items(): self.emoji[e]=[eng.render(es,400+i) for i in range(4)]
    def _esh(self,ch,rng):
        return rng.choice(self.emoji[ch]) if ch in self.emoji else rng.choice(self.emoji["default"])
    def _psh(self,snd,st):
        if st==0 or len(snd)<8: return snd
        f=2**(st/12);no=len(snd);nn=max(1,int(no/f))
        if nn==no: return snd
        idx=np.linspace(0,no-1,nn);i0=idx.astype(np.int32);fr=idx-i0;i1=np.minimum(i0+1,no-1)
        s=snd.astype(np.float64);return(s[i0]*(1-fr)+s[i1]*fr).astype(np.int16)
    def gen(self,ts,vol=.5):
        if not ts: return np.zeros(0,dtype=np.int16)
        sr=self.sr;tot=max(t for t,_ in ts)+.3;n=int(sr*tot)
        rng=random.Random(98765);raw=[];si=[];pans=[]
        for t,ch in ts:
            if is_emoji(ch): snd=self._esh(ch,rng);vm,pan=rng.uniform(.9,1.15),rng.uniform(-.2,.2)
            elif ch=="\n": snd,vm,pan=rng.choice(self.enters),rng.uniform(1.05,1.2),.2
            elif ch==" ": snd,vm,pan=rng.choice(self.spaces),rng.uniform(1,1.15),0
            else:
                bs=rng.choice(self.clicks)
                sh=self._SHIFT[next((i for i,r in enumerate(self._ROWS) if ch.lower() in r),3)]
                snd=self._psh(bs,sh) if sh else bs;vm,pan=rng.uniform(.95,1.1),rng.uniform(-.3,.3)
            s=int(t*sr);e=min(s+len(snd),n)
            if s<n: raw.append(snd[:e-s].astype(np.float32)*vol*vm);si.append(s)
            if self.stereo: pans.append(pan)
        if not raw: return np.zeros(n,dtype=np.int16)
        if self.stereo:
            ml,mr=np.zeros(n,dtype=np.float32),np.zeros(n,dtype=np.float32)
            for i,snd in enumerate(raw):
                s=si[i];pan=pans[i]
                lg=np.cos((pan+1)*np.pi/4);rg=np.sin((pan+1)*np.pi/4)
                e=min(s+len(snd),n);ml[s:e]+=snd[:e-s]*lg;mr[s:e]+=snd[:e-s]*rg
            ml=_norm_lufs(ml,sr);mr=_norm_lufs(mr,sr)
            o=np.empty(n*2,dtype=np.int16)
            o[0::2]=np.clip(ml*32767,-32768,32767).astype(np.int16);o[1::2]=np.clip(mr*32767,-32768,32767).astype(np.int16)
            return o
        starts=np.array(si,dtype=np.int64);lens=np.array([len(s) for s in raw],dtype=np.int64)
        flat=np.concatenate(raw);offs=np.zeros(len(raw),dtype=np.int64)
        for i in range(1,len(raw)): offs[i]=offs[i-1]+lens[i-1]
        mix=np.zeros(n,dtype=np.float32)
        for i in range(len(starts)): mix[int(starts[i]):int(starts[i]+lens[i])]+=flat[int(offs[i]):int(offs[i]+lens[i])]
        mix=_norm_lufs(mix,sr)
        return np.clip(mix*32767,-32768,32767).astype(np.int16)

# ═══════════════════════════════════════════════════════════════
# TYPING ANIMATOR & PARTICLES
# ═══════════════════════════════════════════════════════════════

class EmojiAnim(Enum):
    BOUNCE="Bounce";SLIDE="Slide Up";ZOOM="Zoom In";FADE="Fade In";WIGGLE="Wiggle";EXPLODE="Explode"

@dataclass(slots=True)
class TProfile:
    wpm:int=100;sp:float=.5;ep:float=1.5;tr:float=0;is_text:bool=False;anim:str="Bounce";glitch:float=0

class Animator:
    def __init__(self,code,prof,seed=42):
        self.code,self.prof=code,prof;self.err=0;rng=random.Random(seed)
        chars=split_graphemes(code) if prof.is_text else list(code)
        bd=1/((prof.wpm*5)/60);t=prof.sp
        self.dc=[];self._ts=[];self.tl=[];self.kinds=[]
        self._glitch=list("01!@#$%^&*abcdef");self._gi:Dict[int,List[str]]={}
        for ch in chars:
            k=self._cls(ch)
            if k=='text' and rng.random()<prof.tr:
                self.err+=1;t+=bd*rng.uniform(.5,1)
                tc=rng.choice("abcdefghijklmnopqrstuvwxyz")
                self.tl.append((t,tc));self.dc.append(tc);self._ts.append(t);self.kinds.append('text')
                t+=bd*rng.uniform(.5,1);self.tl.append((t,'\b'));self.dc.append('\b');self._ts.append(t);self.kinds.append('text')
            self.tl.append((t,ch));self.dc.append(ch);self._ts.append(t);self.kinds.append(k)
            if k=='text' and prof.glitch>0 and rng.random()<prof.glitch:
                self._gi[len(self.dc)-1]=[rng.choice(self._glitch) for _ in range(rng.randint(2,5))]
            if k=='emoji': t+=bd*rng.uniform(1.5,2.5)
            elif ch in".!?": t+=bd*rng.uniform(4,6)
            elif ch in",;:": t+=bd*rng.uniform(2,3.5)
            elif ch=='\n': t+=bd*rng.uniform(3,5)
            else: t+=bd*rng.uniform(.7,1.3)
        self._dur=t+prof.ep
    @staticmethod
    def _cls(ch):
        match ch:
            case'\n':return'newline'
            case' ':return'space'
            case'\t':return'tab'
            case _ if is_emoji(ch):return'emoji'
            case _:return'text'
    def dur(self):return self._dur
    def vis(self,t):return bisect.bisect_right(self._ts,t) if t>0 else 0
    def timestamps(self):return self.tl
    def kind(self,i):return self.kinds[i] if 0<=i<len(self.kinds) else'text'
    def ts_at(self,i):return self._ts[i] if 0<=i<len(self._ts) else 0.0
    def glitch_at(self,i):return self._gi.get(i,[])
    def active_key(self,t,fd=.18):
        if not self._ts or t<self._ts[0]:return None,0
        i=bisect.bisect_right(self._ts,t)
        if i==0:return None,0
        ts,ch=self.tl[i-1];el=t-ts
        return(ch,max(0,(1-el/fd)**1.5))if el<fd else(None,0)
    @staticmethod
    def wpm_for(text,td,sp,ep):
        a=td-sp-ep
        return 300 if a<=0 else max(30,min(300,int(60/max(.01,a/max(1,len(split_graphemes(text))*1.2))/5)))

@dataclass(slots=True)
class Particle:
    x:float;y:float;vx:float;vy:float;life:float;max_life:float;color:QColor;size:float;shape:str="circle"

class Particles:
    def __init__(self):self.ps:List[Particle]=[];self._rng=random.Random()
    def burst(self,x,y,c=12,palette=None):
        if palette is None:palette=[QColor("#ff595e"),QColor("#ffca3a"),QColor("#8ac926"),QColor("#1982c4"),QColor("#6a4c93")]
        for _ in range(c):
            a=self._rng.uniform(0,2*math.pi);sp=self._rng.uniform(80,280);lf=self._rng.uniform(.4,.9)
            self.ps.append(Particle(x=x,y=y,vx=math.cos(a)*sp,vy=math.sin(a)*sp-60,life=lf,max_life=lf,color=self._rng.choice(palette),size=self._rng.uniform(4,10),shape=self._rng.choice(["circle","square","star"])))
    def update(self,dt):
        alive=[]
        for p in self.ps:
            p.life-=dt
            if p.life<=0:continue
            p.vy+=480*dt;p.x+=p.vx*dt;p.y+=p.vy*dt;alive.append(p)
        self.ps=alive
    def draw(self,p):
        for p in self.ps:
            a=max(0,p.life/p.max_life);c=QColor(p.color);c.setAlpha(int(255*a))
            p.setBrush(c);p.setPen(Qt.NoPen)
            match p.shape:
                case"circle":p.drawEllipse(QPointF(p.x,p.y),p.size*a,p.size*a)
                case"square":s=p.size*a;p.drawRect(QRectF(p.x-s/2,p.y-s/2,s,s))
                case"star":
                    path=QPainterPath()
                    for i in range(10):
                        an=i*math.pi/5-math.pi/2;r=p.size*a if i%2==0 else p.size*a*.4
                        x=p.x+math.cos(an)*r;y=p.y+math.sin(an)*r
                        if i==0:path.moveTo(x,y)
                        else:path.lineTo(x,y)
                    path.closeSubpath();p.drawPath(path)

# ═══════════════════════════════════════════════════════════════
# KEYBOARD OVERLAY
# ═══════════════════════════════════════════════════════════════

KB_LAYOUTS={"QWERTY":[[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("-",1),("=",1),("Bksp",2)],[("Tab",1.5),("Q",1),("W",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("[",1),("]",1),("\\",1.5)],[("Caps",1.75),("A",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),(";",1),("'",1),("Enter",2.25)],[("Shift",2.25),("Z",1),("X",1),("C",1),("V",1),("B",1),("N",1),("M",1),(",",1),(".",1),("/",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Fn",1.25),("Menu",1.25),("Ctrl",1.25)]],"AZERTY":[[("²",1),("&",1),("é",1),("\"",1),("'",1),("(",1),("-",1),("è",1),("_",1),("ç",1),("à",1),(")",1),("=",1),("Bksp",2)],[("Tab",1.5),("A",1),("Z",1),("E",1),("R",1),("T",1),("Y",1),("U",1),("I",1),("O",1),("P",1),("^",1),("$",1),("Enter",1.5)],[("Caps",1.75),("Q",1),("S",1),("D",1),("F",1),("G",1),("H",1),("J",1),("K",1),("L",1),("M",1),("ù",1),("*",1),("Enter",2.25)],[("Shift",1.25),("<",1),("W",1),("X",1),("C",1),("V",1),("B",1),("N",1),(",",1),(";",1),(":",1),("!",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]],"Dvorak":[[("`",1),("1",1),("2",1),("3",1),("4",1),("5",1),("6",1),("7",1),("8",1),("9",1),("0",1),("[",1),("]",1),("Bksp",2)],[("Tab",1.5),("'",1),(",",1),(".",1),("P",1),("Y",1),("F",1),("G",1),("C",1),("R",1),("L",1),("/",1),("=",1),("\\",1.5)],[("Caps",1.75),("A",1),("O",1),("E",1),("U",1),("I",1),("D",1),("H",1),("T",1),("N",1),("S",1),("-",1),("Enter",2.25)],[("Shift",2.25),(";",1),("Q",1),("J",1),("K",1),("X",1),("B",1),("M",1),("W",1),("V",1),("Z",1),("Shift",2.75)],[("Ctrl",1.25),("Win",1.25),("Alt",1.25),("",6.25),("Alt",1.25),("Win",1.25),("Menu",1.25),("Ctrl",1.25)]]}

class KBOverlay:
    def __init__(self,vw,vh,ln="QWERTY",theme=None,op=.82,pos="bottom_center"):
        self.vw,self.vh,self.theme,self.op=vw,vh,theme,op
        self.rows=KB_LAYOUTS.get(ln,KB_LAYOUTS["QWERTY"])
        self.cm:Dict[str,Tuple[int,int]]={}
        for ri,row in enumerate(self.rows):
            for ci,(lbl,_) in enumerate(row):
                if len(lbl)==1:self.cm[lbl]=self.cm[lbl.lower()]=(ri,ci)
                if lbl=="":self.cm[" "]=(ri,ci)
                elif"enter"in lbl.lower():self.cm["\n"]=(ri,ci)
                elif"tab"in lbl.lower():self.cm["\t"]=(ri,ci)
                elif"bksp"in lbl.lower():self.cm["\b"]=(ri,ci)
        for s,b in{"~":"`","!":"1","@":"2","#":"3","$":"4","%":"5","^":"6","&":"7","*":"8","(":"9",")":"0","_":"-","+=":"=","{":"[","}":"]","|":"\\",":":";",'"':"'","<":",",">":".","?":"/"}.items():
            if b in self.cm:self.cm[s]=self.cm[b]
        tw=int(vw*.65);self.ku=max(14,min(55,int(tw/15)));self.kg=max(2,self.ku//14);self.kh=int(self.ku*.82)
        self._w=int(max(sum(w for _,w in r)for r in self.rows)*self.ku+(max(len(r)for r in self.rows)-1)*self.kg)
        self._h=int(len(self.rows)*self.kh+(len(self.rows)-1)*self.kg)
        self.pos=pos;self._x,self._y=0,0;self.kr:Dict[Tuple[int,int],QRect]={};self._rebuild()
    def h_needed(self):return self._h+max(16,self.vh//30)
    def _apply(self,yt=None):
        mx=max(8,self.vw//60);my=max(8,self.vh//60)
        if"center"in self.pos:self._x=(self.vw-self._w)//2
        elif"right"in self.pos:self._x=self.vw-self._w-mx
        elif"left"in self.pos:self._x=mx
        if"top"in self.pos:self._y=my
        else:
            self._y=yt if yt is not None else self.vh-self._h-my
            self._y=max(my,min(self.vh-self._h-my,self._y))
    def _rebuild(self):
        self.kr={}
        for ri,row in enumerate(self.rows):
            x=self._x
            for ci,(_,w) in enumerate(row):
                kw=int(w*self.ku)-self.kg;y=self._y+ri*(self.kh+self.kg)
                self.kr[(ri,ci)]=QRect(x,y,kw,self.kh);x+=int(w*self.ku)
    def reposition(self,yt=None):self._apply(yt);self._rebuild()
    def resolve(self,ch):return self.cm.get(ch)
    def draw(self,p,ak=None,fl=0.0):
        p.save();p.setOpacity(self.op);p.setRenderHint(QPainter.Antialiasing)
        th=self.theme or THEMES["Dracula"];r=max(3,self.ku//8);pad=max(6,self.ku//4)
        p.setPen(QPen(QColor(th["window_border"]),max(1,self.ku//20)));p.setBrush(QColor(th["title_bar"]))
        p.drawRoundedRect(self._x-pad,self._y-pad,self._w+2*pad,self._h+2*pad,r*2,r*2)
        kbg=QColor(th["background"]);kbr=QColor(th["window_border"]);lc=QColor(th["foreground"]);mc=QColor(th["line_number"]);hlb=QColor(th["cursor"])
        hkf=None
        if fl>0 and ak is not None:
            hkf=QColor(int(kbg.red()+(hlb.red()-kbg.red())*fl),int(kbg.green()+(hlb.green()-kbg.green())*fl),int(kbg.blue()+(hlb.blue()-kbg.blue())*fl))
            hlg=QColor(hlb);hlg.setAlpha(int(60*fl));hle=max(3,int(self.ku*.12*fl))
        for(ri,ci),rect in self.kr.items():
            lbl=self.rows[ri][ci][0];ia=(ak is not None and ak==(ri,ci))
            if ia and hkf is not None:
                p.setPen(Qt.PenStyle.NoPen);p.setBrush(hlg);p.drawRoundedRect(rect.adjusted(-hle,-hle,hle,hle),r,r);p.setBrush(hkf);p.setPen(QPen(kbr,1))
            else:
                p.setPen(Qt.PenStyle.NoPen);p.setBrush(kbr.darker(150));p.drawRoundedRect(rect.adjusted(0,3,0,3),r,r);p.setBrush(kbg);p.setPen(QPen(kbr,1))
            p.drawRoundedRect(rect,r,r)
            if lbl:
                p.setPen(mc if len(lbl)>1 else lc);p.setFont(QFont("Segoe UI",max(7,int(self.ku*.30))));p.drawText(rect,Qt.AlignCenter,lbl)
        p.restore()

# ═══════════════════════════════════════════════════════════════
# CONFIG
# ═══════════════════════════════════════════════════════════════

@dataclass
class StudioConfig:
    theme:str="Dracula";resolution:str="1920x1080";fps:int=30
    sound_enabled:bool=True;sound_preset:str="Mechanical";stereo:bool=False;volume:int=50
    encoder:str="YouTube (H.264/AAC)";bgm_path:str="";bgm_volume:int=30;bgm_duck:bool=True
    use_custom:bool=False;custom_code:str=""
    kb_enabled:bool=False;kb_layout:str="QWERTY";kb_position:str="Bottom Center";kb_opacity:float=0.82
    wpm_txt:int=100;typo_txt:float=0.0;shorts_txt:bool=False;ascii_art:bool=False
    txt_markdown:bool=False;txt_crt:bool=False;txt_bubbles:bool=False;txt_clean:bool=True
    txt_rainbow:bool=False;txt_pop_emoji:bool=True;txt_particles:bool=True
    txt_emoji_anim:str="Bounce";txt_glitch:float=0.0;txt_gradient:bool=False
    txt_gradient_dir:str="Vertical";txt_cursor_style:str="Block";txt_tab_size:int=4
    txt_color_mode:str="Monochrome";txt_palette:str="Dracula";txt_ansi_bg:bool=True;txt_glow:float=0.5
    font_txt:str="Consolas";font_sz_auto_txt:bool=False;font_sz_txt:int=22
    yt_extras:bool=True;recursive_scan:bool=True;scan_depth:int=10;output_template:str="{name}_{date}"
    batch_parallel:int=1;max_ram_mb:int=4096;frame_compress:bool=True
    retry_on_fail:bool=True;batch_order:str="Smart (Complexity)"
    playback_speed:float=1.0;loop_mode:bool=False;preview_scale:float=1.0

# ═══════════════════════════════════════════════════════════════
# RENDERER
# ═══════════════════════════════════════════════════════════════

class Renderer:
    def __init__(self,w,h,theme="Dracula",ff="Consolas",fs=22,sln=True,swc=True,pad=24,ts=4,lang="text",aam=False,cfg=None,kb=None):
        self.w,self.h=w,h;self.theme=THEMES.get(theme,THEMES["Dracula"])
        self.ff,self.fs=ff,fs;self.sln,self.swc=sln,swc;self.pad=min(pad,max(8,min(w,h)//30)
        self.ts,self.lang,self.aam=ts,lang,aam;self.cfg=cfg;self.kb=kb;self._cr=QRect(0,0,1,1)
        _f=[ff,"Noto Color Emoji","Segoe UI Emoji","Apple Color Emoji","JetBrains Mono","Consolas","monospace"]
        self.font=QFont(ff,fs);self.font.setFamilies(list(dict.fromkeys(_f)));self.font.setFixedPitch(not aam)
        self.fm=QFontMetrics(self.font);self.cw=self.fm.horizontalAdvance("M");self.lh=self.fm.height();self._ta=self.cw*ts
        qc={k:QColor(v) for k,v in self.theme.items() if isinstance(v,str) and v.startswith("#")}
        self._fg=qc.get("foreground",QColor("#f8f8f2"));self._ln=qc.get("line_number",QColor("#6272a4"))
        self._cur=qc.get("cursor",QColor("#f8f8f2"));self._cl=qc.get("current_line",QColor("#44475a"));self._acc=qc.get("accent",QColor("#bd93f9"))
        self._cr=ColorResolver(cfg,self.theme) if cfg else None;self._parts=Particles();self._bf=set();self._ansi=parse_ansi("") if False else [];self._has_ansi=False
        self._bg()
    def _bg(self):
        self._bi=QImage(self.w,self.h,QImage.Format_RGB32);self._bi.fill(QColor(self.theme["background"]))
        p=QPainter(self._bi);p.setRenderHint(QPainter.Antialiasing)
        bg={k:QColor(v) for k,v in self.theme.items() if isinstance(v,str) and v.startswith("#")}.get("background",QColor("#282a36"))
        g=QLinearGradient(0,0,0,self.h);g.setColorAt(0,bg.lighter(105));g.setColorAt(1,bg);p.fillRect(0,0,self.w,self.h,g)
        pad,ch=self.pad,42 if self.swc else 0;ww=self.w-2*self.pad
        kbh=self.kb.h_needed() if self.kb else 0;kbt=self.kb and"top"in self.kb.pos
        ah=self.h-2*self.pad;twh=ah-kbh;mr=float('inf') if self.aam else 2.0
        if twh>ww*mr:twh=int(ww*mr)
        sy=self.pad+(ah-(twh+kbh))//2;wy=sy+(kbh if kbt else 0);wh=twh;wx,ww=self.pad,self.w-2*self.pad
        p.setPen(Qt.PenStyle.NoPen);p.setBrush(QColor(0,0,0,60));p.drawRoundedRect(wx+4,wy+4,ww,wh,12,12)
        p.setPen(QColor(self.theme["window_border"]));p.setBrush(QColor(self.theme["background"]));p.drawRoundedRect(wx,wy,ww,wh,12,12)
        if self.swc:
            p.setPen(Qt.PenStyle.NoPen);p.setBrush(QColor(self.theme["title_bar"]));p.drawRoundedRect(wx,wy,ww,ch,12,12);p.drawRect(wx,wy+ch-12,ww,12)
            for i,c in enumerate(["#ff5f56","#ffbd2e","#27c93f"]):p.setBrush(QColor(c));p.setPen(Qt.PenStyle.NoPen);p.drawEllipse(QPoint(wx+20+i*24,wy+19),7,7)
            self._cr=QRect(wx+4,wy+ch,ww-8,wh-ch)
        else:self._cr=QRect(wx+4,wy,ww-8,wh)
        if self.kb:self.kb.reposition(wy+wh+max(8,self.h//60) if not kbt else sy)
        p.end()
    @staticmethod
    def afs(lc,w,h,pad=24,sc=True,sl=True,text=None,ff="Consolas",kbh=0,aam=False):
        ch=42 if sc else 0;mr=float('inf') if aam else 1.5;ah=h-2*pad-kbh
        if ah>w*mr:ah=int(w*mr)
        rh,rw=ah-ch,w-2*pad-8
        if rh<20 or rw<40 or lc<1:return 14
        mc=80
        if text:mc=max(mc,max((sum(4 if g=='\t' else char_width(g) for g in split_graphemes(l)) for l in text.split("\n")),default=1))
        def lnw(cw):return(len(str(lc))*cw+32+int(cw*1.5)) if sl else 0
        lo,hi,best=6,max(14,min(128,int(w/40))),14
        while lo<=hi:
            mid=(lo+hi)//2;fm=QFontMetrics(QFont(ff,mid));lc2=lc if aam else min(lc,35);cc=mc if aam else min(mc,120)
            if lc2*fm.height()<=rh:
                cw=fm.horizontalAdvance("M")
                if cc*cw+lnw(cw)<=rw:best=mid;lo=mid+1
                else:hi=mid-1
            else:hi=mid-1
        return max(6,best)
    def _lw(self,lg):return sum(self.ts if g=='\t' else(0 if g in('\n','\r\n') else char_width(g)) for g in lg)
    @staticmethod
    def _eob(t,s=1.7):t-=1;return 1+(s+1)*t*t*t+s*t*t
    @staticmethod
    def _eoc(t):return 1-(1-t)**3
    @staticmethod
    def _eoe(t):
        if t in(0.0,1.0):return t
        return 2**(-10*t)*math.sin((t*10-.75)*(2*math.pi/3))+1
    def _et(self,st,pr):
        match st:
            case"Bounce":s=self._eob(pr)*.5+.5;return(s,s,0,0)
            case"Slide Up":s=self._eoc(pr)*.5+.5;return(s,s,0,(1-self._eoc(pr))*-self.lh*.5)
            case"Zoom In":s=self._eoe(pr);return(s,s,0,0)
            case"Fade In":return(1,1,0,0)
            case"Wiggle":a=math.sin(pr*math.pi*6)*(1-pr)*.3;return(1,1,math.cos(a)*3,math.sin(a)*3)
            case"Explode":s=2-1.5*self._eoc(pr);return(s,s,0,0)
            case _:return(1,1,0,0)
    def _gc(self,x,y,w,h):
        if not self.cfg or not self.cfg.txt_gradient:return self._fg
        d=self.cfg.txt_gradient_dir;t=y/max(1,h) if d=="Vertical" else(x/max(1,w) if d=="Horizontal" else(x/max(1,w)+y/max(1,h))/2)
        return QColor.fromHsv(int(max(0,min(1,t))*300)%360,200,240)
    def _dc(self,p,x,y):
        st=self.cfg.txt_cursor_style if self.cfg else"Block";w=max(2,self.fs//10);pad=(self.lh-self.fm.height())//2;cy=y+pad+1;ch=self.fm.height()-2
        match st:
            case"Block":gc=QColor(self._cur);gc.setAlpha(60);p.fillRect(x-w,cy-2,w*3,ch+4,gc);gc.setAlpha(100);p.fillRect(x-1,cy-1,w*2,ch+2,gc);p.fillRect(x,cy,w,ch,self._cur)
            case"Beam":p.fillRect(x,cy,max(2,self.cw//8),ch,self._cur)
            case"Underline":p.fillRect(x,cy+ch-max(2,self.fs//8),self.cw,max(2,self.fs//8),self._cur)
    def _ai(self,li,ii,lines):return sum(len(lines[i])+1 for i in range(li))+ii
    def set_ansi(self,code):
        self._has_ansi='\x1B[' in code
        self._ansi=[parse_ansi(l) for l in code.split('\n')] if self._has_ansi else []
    def render(self,dc,nv,cv=True,target=None,ac=None,kf=0,tt="",t=0,anim=None,dg=False):
        img=target if target is not None else QImage(self.w,self.h,QImage.Format_RGB32)
        if target is None:img.fill(QColor(self.theme["background"]))
        p=QPainter(img);p.setRenderHint(QPainter.TextAntialiasing);p.drawImage(0,0,self._bi);cr=self._cr
        if self.swc:p.setPen(QColor(self.theme["title_text"]));p.setFont(QFont(self.ff,max(8,min(12,self.w//80))));p.drawText(QRect(self.pad,cr.top()-42,cr.width(),42),Qt.AlignCenter,tt)
        out:List[str]=[]
        for ch in dc[:nv]:
            if ch=="\b":
                if out:out.pop()
            else:out.append(ch)
        ib,ii_=False,False
        if self.cfg and self.cfg.txt_markdown:
            no=[];i=0
            while i<len(out):
                if"".join(out[i:i+2])=="**":ib=not ib;i+=2;continue
                if out[i]=="*" and not ib:ii_=not ii_;i+=1;continue
                no.append(out[i]);i+=1
            out=no
        lines:List[List[str]=[[]]
        for g in out:
            if g=='\n':lines.append([])
            else:lines[-1].append(g)
        cl=len(lines)-1;tl=len(lines);mv=max(1,-(-cr.height()//self.lh))
        sc=0 if self.aam else(max(0,min(cl-mv+5,tl-mv)) if cl>=mv-5 else max(0,cl-3))
        lg=max(12,int(self.cw*1.5));lnw=(len(str(tl+sc))*self.cw+32+lg) if(self.sln and not self.aam) else 0
        x0,ya=cr.left()+lnw,cr.top();p.setClipRect(cr);p.setFont(self.font)
        for si in range(mv):
            li=sc+si
            if li>=tl:break
            y=ya;ya+=self.lh;lg_=lines[li];x0b=x0
            if self.cfg and self.cfg.txt_bubbles:
                ls="".join(lg_);bw=min(cr.width()-30,self._lw(lg_)*self.cw+30);br=QRect(x0,y+5,bw,self.lh-10)
                if ls.startswith("Me:"):br.moveRight(cr.right()-10);p.setBrush(QColor("#007AFF"));p.setPen(Qt.NoPen)
                else:p.setBrush(QColor("#333333"));p.setPen(Qt.NoPen)
                p.drawRoundedRect(br,10,10);x0b=br.left()+10
            if li==cl and not(self.aam or(self.cfg and self.cfg.txt_bubbles)):p.fillRect(cr.left(),y,cr.width(),self.lh,self._cl)
            if self.sln and lnw>0 and not self.aam:p.setPen(self._ln);p.drawText(QRect(cr.left(),y,lnw-lg,self.lh),Qt.AlignRight|Qt.AlignVCenter,str(li+1))
            if not lg_:
                if cv and li==cl:self._dc(p,int(x0b),int(y));continue
            lwp=self._lw(lg_)*self.cw;x=x0+(cr.width()-lnw-lwp)//2 if self.aam else x0b
            # Syntax detection
            char_syn:Dict[int,str]={}
            if self.cfg and self._cr and self.cfg.txt_color_mode=="Syntax Highlight":
                ls="".join(lg_)
                for sm in detect_syntax(ls):
                    for ci in range(sm.s,min(sm.e,len(ls))):char_syn[ci]=sm.kind
            for idx,g in enumerate(lg_):
                if g=='\t':x+=self._ta;continue
                gw=char_width(g)*self.cw;ai=self._ai(li,idx,lines)
                cts=anim.ts_at(ai) if anim else 0;k=anim.kind(ai) if anim else'text';el=t-cts
                dg_=g
                if k=='text' and anim and self.cfg and self.cfg.txt_glitch>0:
                    gc=anim.glitch_at(ai)
                    if gc and 0<=el<.18:
                        gi=int(el/.18*len(gc))
                        if 0<=gi<len(gc):dg_=gc[gi]
                sp,pk,pp=False,'text',0
                if 0<=el<.30:
                    pp=el/.30
                    if k=='emoji' and self.cfg and self.cfg.txt_pop_emoji:sp,pk=True,'emoji'
                    elif self.cfg and self.cfg.txt_pop_emoji and not self.aam:sp=True
                if k=='emoji' and self.cfg and self.cfg.txt_particles and 0<=el<.05 and ai not in self._bf:
                    self._bf.add(ai);self._parts.burst(x+gw/2,y+self.lh/2,10)
                # Color resolution
                color=None
                if self._cr:
                    color=self._cr.resolve(g,li,idx,x,y,cr.width(),cr.height(),char_syn)
                else:
                    s=detect_script(g)
                    if s=="emoji":color=None
                    elif s in("box","block"):color=self._acc
                    else:color=self._fg
                p.save()
                if sp:
                    st=self.cfg.txt_emoji_anim if k=='emoji' else"Bounce"
                    sx,sy,ox,oy=self._et(st,pp);cx=x+gw/2;cy=y+self.lh*.5
                    p.translate(cx+ox,cy+oy);p.scale(sx,sy);p.translate(-cx,-cy)
                    if st=="Fade In":p.setOpacity(self._eoc(pp))
                if color is not None:p.setPen(color)
                if ib or ii_:
                    f=QFont(self.font);f.setBold(ib);f.setItalic(ii_);p.setFont(f)
                else:p.setFont(self.font)
                p.drawText(QRect(int(x),int(y),int(gw),int(self.lh)),Qt.AlignLeft|Qt.AlignVCenter,dg_);p.restore();x+=gw
            if cv and li==cl:self._dc(p,int(x),int(y))
        p.setClipping(False)
        if self.cfg and self.cfg.txt_particles:self._parts.update(1/30);self._parts.draw(p)
        if self.kb and ac and kf>0:
            ak=self.kb.resolve(ac)
            if ak:self.kb.draw(p,ak,kf)
        if dg:
            p.setRenderHint(QPainter.Antialiasing);p.setPen(QPen(QColor(255,0,0,150),2,Qt.DashLine));p.setBrush(Qt.NoBrush);p.drawRect(24,24,self.w-48,self.h-48)
            p.setPen(QPen(QColor(0,150,255,150),2,Qt.DashLine));p.setBrush(Qt.NoBrush);p.drawRect(self._cr)
        p.end();return img

class MPRenderer:
    def __init__(self,panes,fw,fh,cfg):self.panes=panes;self.fw,self.fh=fw,fh;self.cfg=cfg;self.pr=[QRect(0,0,fw,fh)]
    def dur(self):return max(a.dur() for _,a,_ in self.panes) if self.panes else 0
    def ts_all(self):
        ts=[]
        for _,a,_ in self.panes:ts.extend(a.timestamps())
        return ts
    def render(self,t,target=None,dg=False):
        img=target if target is not None else QImage(self.fw,self.fh,QImage.Format_RGB32);img.fill(QColor("#0d0d12"))
        p=QPainter(img);p.setRenderHint(QPainter.SmoothPixmapTransform)
        for i,(r,a,tt) in enumerate(self.panes):
            if i>=len(self.pr):break
            rect=self.pr[i];nv=a.vis(t);ac,kf=a.active_key(t)
            pi=r.render(a.dc,nv,True,ac=ac,kf=kf,tt=tt,target=QImage(rect.width(),rect.height(),QImage.Format_RGB32),t=t,anim=a,dg=dg)
            p.drawImage(rect.topLeft(),pi)
        p.end();return img

# ═══════════════════════════════════════════════════════════════
# STRATEGY
# ═══════════════════════════════════════════════════════════════

class Strategy:
    def build(self,cfg,files,cc):
        w,h=RESOLUTIONS.get(cfg.resolution,(1920,1080));code,lang,tt=self._code(cfg,files,cc)
        wpm=Animator.wpm_for(code,179,.5,1.5) if cfg.shorts_txt else cfg.wpm_txt
        a=Animator(code,TProfile(wpm=wpm,tr=cfg.typo_txt,is_text=True,anim=cfg.txt_emoji_anim,glitch=cfg.txt_glitch))
        r=self._renderer(cfg,w,h,code,tt,lang);r.set_ansi(code)
        return MPRenderer([(r,a,tt)],w,h,cfg)
    def _code(self,cfg,files,cc):
        if cfg.use_custom:
            code=convert_shortcodes(cc);return(code if code.strip() else"✨ Welcome!","text","custom.txt")
        checked=[f for f in files if f.checked]
        if not checked:return("Hello 👋\nAdd files!\n🚀","text","preview.txt")
        it=checked[0];return(read_text_file(Path(it.path),cfg.txt_clean),"text",os.path.basename(it.path))
    def _renderer(self,cfg,w,h,code,tt,lang):
        ff=cfg.font_txt;fa=cfg.font_sz_auto_txt;fsz=cfg.font_sz_txt
        kbh=int(w*.65/15*.82)*5+20 if cfg.kb_enabled else 0
        fs=Renderer.afs(code.count("\n")+1,w,h,text=code,ff=ff,kbh=kbh,aam=cfg.ascii_art) if fa else fsz
        kb=None
        if cfg.kb_enabled:kb=KBOverlay(w,h,cfg.kb_layout,THEMES.get(cfg.theme,THEMES["Dracula"]),cfg.kb_opacity,cfg.kb_position.lower().replace(" ","_"))
        return Renderer(w,h,cfg.theme,ff,fs,lang=lang,aam=cfg.ascii_art,cfg=cfg,kb=kb,ts=cfg.txt_tab_size)

# ═══════════════════════════════════════════════════════════════
# MEMORY & CONCURRENCY
# ═══════════════════════════════════════════════════════════════

class MemMon:
    def __init__(self,max_mb=4096):self.max_mb=max_mb;self._s=deque(maxlen=10);self._lk=threading.Lock()
    def rss(self):
        if _HAS_PSUTIL:
            try:return psutil.Process().memory_info().rss/(1024*1024)
            except:pass
        try:
            import resource;u=resource.getrusage(resource.RUSAGE_SELF)
            return u.ru_maxrss/(1024 if platform.system()=="Darwin" else 1)/1024
        except:return 0
    def sample(self):
        r=self.rss()
        with self._lk:self._s.append(r)
        return r
    def avg(self):
        with self._lk:return sum(self._s)/len(self._s) if self._s else 0
    def workers(self,req):
        r=self.avg()
        if r<=0:return req
        ratio=r/self.max_mb
        if ratio>.85:return max(1,req//4)
        if ratio>.70:return max(1,req//2)
        if ratio>.55:return max(1,int(req*.75))
        return req
    def report(self):
        r=self.rss();return f"RSS:{r:.0f}MB({r/self.max_mb*100:.0f}%)" if r>0 else"RSS:N/A"

class FramePool:
    def __init__(self,w,h,n=4):
        self._w,self._h=w,h;self._q=queue.Queue(maxsize=n);self._all=[QImage(w,h,QImage.Format_RGB32) for _ in range(n)]
        for im in self._all:self._q.put(im)
    def acq(self,t=60):
        try:return self._q.get(timeout=t)
        except queue.Empty:return None
    def rel(self,im):
        if im:
            try:self._q.put_nowait(im)
            except queue.Full:pass
    def drain(self):
        while not self._q.empty():
            try:self._q.get_nowait()
            except queue.Empty:break
        self._all.clear()

def q_depth(w,h,max_mb,comp=True):
    fb=w*h*3;eb=max(1,fb//5) if comp else fb
    return max(4,min(30,(max_mb*1024*1024)//max(1,eb)))

class FrameCache:
    def __init__(self,n=120):self._c:Dict[int,QImage]={};self._o:deque=deque();self._n=n;self._lk=threading.Lock()
    def get(self,fi):
        with self._lk:
            im=self._c.get(fi)
            if im is not None:self._o.remove(fi);self._o.append(fi)
            return im
    def put(self,fi,im):
        with self._lk:
            if fi in self._c:self._o.remove(fi)
            self._c[fi]=im;self._o.append(fi)
            while len(self._c)>self._n:oldest=self._o.popleft();self._c.pop(oldest,None)
    def clear(self):
        with self._lk:self._c.clear();self._o.clear()
    def __len__(self):return len(self._c)

class TLSlider(QSlider):
    seek=Signal(float)
    def __init__(self,o=Qt.Horizontal,p=None):
        super().__init__(o,p);self._mk=[];self._wf=None;self._dur=0;self._drag=False
    def set_markers(self,ts,dur):
        self._dur=max(.001,dur);self._mk=[min(1,max(0,t/self._dur)) for t in ts];self.update()
    def set_wave(self,pcm):
        try:
            mono=pcm if len(pcm.shape)==1 else pcm.reshape(-1,2)[:,0];cs=max(1,len(mono)//200)
            self._wf=np.array([np.max(np.abs(mono[i:i+cs])) for i in range(0,len(mono),cs)],dtype=np.float32)
            if self._wf.max()>0:self._wf/=self._wf.max()
        except:self._wf=None
        self.update()
    def clear_wave(self):self._wf=None;self.update()
    def mousePressEvent(self,e):
        if e.button()==Qt.MouseButton.LeftButton:
            self._drag=True;v=self._vfp(e.position().toPoint().x() if hasattr(e,'position') else e.pos().x());self.setValue(v);self.seek.emit(v/1000*self._dur)
        super().mousePressEvent(e)
    def mouseMoveEvent(self,e):
        if self._drag:v=self._vfp(e.position().toPoint().x() if hasattr(e,'position') else e.pos().x());self.setValue(v);self.seek.emit(v/1000*self._dur)
        super().mouseMoveEvent(e)
    def mouseReleaseEvent(self,e):self._drag=False;super().mouseReleaseEvent(e)
    def _vfp(self,x):
        r=self.rect();m=12;u=max(1,r.width()-2*m);t=max(0,min(1,(x-m)/u));return int(t*self.maximum())
    def paintEvent(self,e):
        p=QPainter(self);p.setRenderHint(QPainter.Antialiasing);r=self.rect();m=12;th=6;ty=r.height()//2-th//2;tr=QRect(m,ty,r.width()-2*m,th)
        p.setPen(Qt.NoPen);p.setBrush(QColor("#313244"));p.drawRoundedRect(tr,3,3)
        if self._wf is not None and len(self._wf)>1:
            wr=QRect(m,ty-12,r.width()-2*m,th+24);w=wr.width();h=wr.height();cx=wr.left();cy=wr.center().y()
            p.setPen(QPen(QColor("#45475a"),1))
            for i,amp in enumerate(self._wf[:w]):bh=int(amp*h*.4);p.drawLine(cx+i,cy-bh,cx+i,cy+bh)
        pr=self.value()/max(1,self.maximum());fw=int((r.width()-2*m)*pr);p.setBrush(QColor("#89b4fa"));p.drawRoundedRect(QRect(m,ty,fw,th),3,3)
        p.setBrush(QColor("#fabd2f"))
        for mk in self._mk:mx=m+int(mk*(r.width()-2*m));p.drawEllipse(QPoint(mx,r.height()//2),3,3)
        ph=m+int(pr*(r.width()-2*m));p.setPen(QPen(QColor("#f8f8f2"),2));p.drawLine(ph,ty-4,ph,ty+th+4);p.setBrush(QColor("#f8f8f2"));p.drawEllipse(QPoint(ph,r.height()//2),5,5)
        p.end()

# ═══════════════════════════════════════════════════════════════
# EXPORT PIPELINE
# ═══════════════════════════════════════════════════════════════

@dataclass
class FileItem:
    path:str;checked:bool=False;status:str="PENDING"

@dataclass
class ExportCmd:
    item:FileItem;output:str;config:StudioConfig;mp:Optional[MPRenderer]=None;status:str="PENDING";cx:float=0;rc:int=0;mr:int=1

class Exporter(QThread):
    progress=Signal(int,str);status=Signal(str,str);done=Signal(str);error=Signal(str,str);mem=Signal(str)
    def __init__(self,cmd):
        super().__init__();self.cmd=cmd;self.mp=cmd.mp;self.out=cmd.output;self.fps=cmd.config.fps;self.cfg=cmd.config;self._can=threading.Event();self.w,self.h=self.mp.fw,self.mp.fh;self._mm=MemMon(self.cfg.max_ram_mb);self._fp:Optional[FramePool]=None
    def cancel(self):self._can.set()
    def _crt(self,img):
        p=QPainter(img);p.setRenderHint(QPainter.Antialiasing);p.setPen(Qt.NoPen);p.setBrush(QColor(0,0,0,70))
        for y in range(0,self.h,3):p.drawRect(0,y,self.w,1)
        p.setBrush(QColor(0,255,100,12));p.drawRect(0,0,self.w,self.h)
        g=QRadialGradient(self.w/2,self.h/2,max(self.w,self.h)*.7);g.setColorAt(0,QColor(0,0,0,0));g.setColorAt(.7,QColor(0,0,0,0));g.setColorAt(1,QColor(0,0,0,120))
        p.setBrush(g);p.setPen(Qt.NoPen);p.drawRect(0,0,self.w,self.h);p.setBrush(QColor(0,0,0,18))
        for x in range(0,self.w,2):p.drawRect(x,0,1,self.h);p.end()
    def _fb(self,img):
        ptr=img.constBits();ptr.setsize(img.bytesPerLine()*self.h);arr=np.frombuffer(ptr,dtype=np.uint8).reshape((self.h,img.bytesPerLine()//4,4));return np.ascontiguousarray(arr[:,:self.w,2::-1]).tobytes()
    def _cmd(self,audio):
        cmd=["ffmpeg","-y","-f","rawvideo","-pix_fmt","rgb24","-s",f"{self.w}x{self.h}","-r",str(self.fps),"-i","pipe:0"]
        if audio:cmd+=["-i",audio,"-map","0:v","-map","1:a"]
        else:cmd+=["-map","0:v"]
        enc=self.cfg.encoder
        match enc:
            case"YouTube (H.264/AAC)":px=self.w*self.h;mr=int((px/2073600)*12000000);cmd+=["-c:v","libx264","-preset","slow","-crf","17","-maxrate",f"{mr}","-bufsize",f"{mr*2}","-pix_fmt","yuv420p"]
            case"NVENC (NVIDIA)":cmd+=["-c:v","h264_nvenc","-preset","p5","-rc","vbr","-cq","19","-b:v","0","-pix_fmt","yuv420p"]
            case"QSV (Intel)":cmd+=["-c:v","h264_qsv","-preset","slow","-global_quality","19","-pix_fmt","yuv420p"]
            case"AMF (AMD)":cmd+=["-c:v","h264_amf","-preset","quality","-rc","cqp","-qp_i","19","-qp_p","19","-pix_fmt","yuv420p"]
            case _:cmd+=["-c:v","libx264","-preset","slow","-crf","17","-pix_fmt","yuv420p"]
        if audio:cmd+=["-c:a","aac","-b:a","256k"]
        cmd+=["-movflags","+faststart",self.out];return cmd
    def run(self):
        tmp=tempfile.mkdtemp(dir=str(TEMP_DIR),prefix="exp_")
        try:
            td=self.mp.dur();nf=int(td*self.fps);ap=os.path.join(tmp,"a.wav")
            if self.cfg.sound_enabled:
                sg=SoundGen(sr=SR,preset=self.cfg.sound_preset,stereo=self.cfg.stereo);pcm=sg.gen(self.mp.ts_all(),1.0)
                with wave.open(ap,"w") as wf:wf.setnchannels(2 if sg.stereo else 1);wf.setsampwidth(2);wf.setframerate(sg.sr);wf.writeframes(pcm.tobytes())
            cmd=self._cmd(ap if self.cfg.sound_enabled else None)
            si=subprocess.STARTUPINFO()
            if platform.system()=="Windows":si.dwFlags|=subprocess.STARTF_USESHOWWINDOW;si.wShowWindow=subprocess.SW_HIDE
            proc=subprocess.Popen(cmd,stdin=subprocess.PIPE,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,startupinfo=si)
            qd=q_depth(self.w,self.h,self.cfg.max_ram_mb,self.cfg.frame_compress);self._fp=FramePool(self.w,self.h,min(qd,4));comp=self.cfg.frame_compress
            bw=max(2,(os.cpu_count()or 4)-1);mw=self._mm.workers(bw)
            if self.cfg.batch_parallel>1:mw=max(1,mw//self.cfg.batch_parallel)
            def rf(fi):
                buf=self._fp.acq()
                if buf is None:return(fi,None)
                try:
                    t=fi/self.fps;img=self.mp.render(t,buf)
                    if self.cfg.txt_crt:self._crt(img)
                    raw=self._fb(img);data=zlib.compress(raw,1) if comp else raw;return(fi,data)
                except Exception:logger.error(f"Frame {fi}",exc_info=True);return(fi,None)
                finally:self._fp.rel(buf)
            ex=ThreadPoolExecutor(max_workers=mw)
            try:
                fi=0;tp=[.25,.5,.75] if self.cfg.yt_extras else[];ti=0
                while fi<nf and not self._can.is_set():
                    ce=min(fi+qd*2,nf);fut={ex.submit(rf,cfi):cfi for cfi in range(fi,ce)}
                    for cfi in range(fi,ce):
                        if self._can.is_set():break
                        f=next(f for f,idx in fut.items() if idx==cfi);_,fd=f.result()
                        if fd is None:self.error.emit("Render failed",self.out);self._can.set();break
                        try:proc.stdin.write(fd)
                        except BrokenPipeError:
                            se=proc.stderr.read().decode('utf-8',errors='ignore') if proc.stderr else"";self.error.emit(f"FFmpeg:{se[:500]}",self.out);self._can.set();break
                        if ti<len(tp) and cfi==int(nf*tp[ti]):tp_=os.path.splitext(self.out)[0]+f"_thumb_{ti+1}.jpg";self.mp.render(cfi/self.fps,QImage(self.w,self.h,QImage.Format_RGB32)).save(tp_,"JPG",95);ti+=1
                        if cfi%30==0:self.progress.emit(int(cfi/nf*100),self.out);self.status.emit(f"Frame {cfi}/{nf}",self.out)
                        if cfi%60==0:self._mm.sample();self.mem.emit(self._mm.report())
                    fi=ce;self._mm.sample()
            finally:
                ex.shutdown(wait=False)
                if self._fp:self._fp.drain()
            try:proc.stdin.close()
            if self._can.is_set():proc.kill()
            proc.wait(timeout=30)
            except subprocess.TimeoutExpired:proc.kill();proc.wait()
            except:pass
            gc.collect()
            if not self._can.is_set():self.progress.emit(100,self.out);self.done.emit(self.out)
            else:self.error.emit("Cancelled",self.out)
        except Exception as e:logger.error(f"Export failed {self.out}",exc_info=True);self.error.emit(str(e),self.out)
        finally:shutil.rmtree(tmp,ignore_errors=True);gc.collect()

class BatchMgr(QThread):
    progress=Signal(int,str);started_=Signal(str);done_=Signal(str);failed_=Signal(str,str);retried_=Signal(str,int);finished_=Signal(int,int);mem=Signal(str)
    def __init__(self,cmds,cfg,strat,items):
        super().__init__();self.cmds=list(cmds);self.cfg=cfg;self.strat=strat;self.items=items;self._can=threading.Event();self._active:List[Exporter]=[];self._lk=threading.Lock();self.t0=0;self.dc=0;self.fc=0;self._q:deque=deque()
    def cancel(self):
        self._can.set()
        with self._lk:
            for e in self._active:e.cancel()
    def _cx(self,cmd):
        w,h=RESOLUTIONS.get(cmd.config.resolution,(1920,1080));code,_,_=self.strat._code(cmd.config,[cmd.item],cmd.config.custom_code);return w*h*math.sqrt(max(1,len(split_graphemes(code))))*cmd.config.fps
    def run(self):
        self.t0=_time.time()
        for c in self.cmds:c.cx=self._cx(c)
        if"Smart"in self.cfg.batch_order:self.cmds.sort(key=lambda c:c.cx)
        elif"Random"in self.cfg.batch_order:random.shuffle(self.cmds)
        self._q=deque(self.cmds);total=len(self.cmds);par=max(1,min(4,self.cfg.batch_parallel));sem=threading.Semaphore(par);threads:List[Exporter]=[]
        while self._q and not self._can.is_set():
            sem.acquire()
            if self._can.is_set():sem.release();break
            cmd=self._q.popleft()
            try:cmd.mp=self.strat.build(cmd.config,[cmd.item],cmd.config.custom_code)
            except Exception as e:self.failed_.emit(cmd.output,str(e));self.fc+=1;sem.release();continue
            if not cmd.mp:self.failed_.emit(cmd.output,"Empty");self.fc+=1;sem.release();continue
            ex=Exporter(cmd)
            with self._lk:self._active.append(ex);self.started_.emit(cmd.output)
            p=cmd.output;ex.done.connect(lambda p:self._on_done(p,sem));ex.error.connect(lambda e,p:self._on_fail(e,p,sem,cmd));ex.progress.connect(lambda pct,p:self._emit());ex.mem.connect(self.mem.emit);ex.start();threads.append(ex)
        for t in threads:t.wait()
        self.finished_.emit(self.dc,total)
    def _on_done(self,p,sem):self.dc+=1;self.done_.emit(p);sem.release();self._emit()
    def _on_fail(self,e,p,sem,cmd):
        if self.cfg.retry_on_fail and cmd.rc<cmd.mr and not self._can.is_set():
            cmd.rc+=1;self.retried_.emit(p,cmd.rc);rc=copy.deepcopy(cmd.config);rc.fps=max(24,rc.fps-6);cmd.config=rc
            with self._lk:self._q.appendleft(cmd);sem.release();return
        self.fc+=1;self.failed_.emit(p,e);sem.release();self._emit()
    def _emit(self):
        total=len(self.cmds);done=self.dc+self.fc;pct=int(done/total*100) if total>0 else 0;el=_time.time()-self.t0;eta=(el/done*(total-done)) if done>0 else 0
        self.progress.emit(pct,f"Done:{done}/{total} Fail:{self.fc} ETA:{int(eta//60)}m{int(eta%60)}s")
    @staticmethod
    def estimate(cmds,strat):
        tt,ts=0.0,0.0
        for cmd in cmds:
            w,h=RESOLUTIONS.get(cmd.config.resolution,(1920,1080));code,_,_=strat._code(cmd.config,[cmd.item],cmd.config.custom_code);cc=len(split_graphemes(code));d=cc/max(1,cmd.config.wpm_txt*5/60)+2;sm=int((w*h/2073600)*8e6)*d/8/(1024*1024);tt+=d;ts+=sm
        return{"t":f"{int(tt//60)}m{int(tt%60)}s","s":f"{ts:.0f}MB" if ts<1024 else f"{ts/1024:.1f}GB","n":len(cmds)}

# ═══════════════════════════════════════════════════════════════
# GUI
# ═══════════════════════════════════════════════════════════════

class BTable(QTableWidget):
    def __init__(self,r=0,c=0,p=None):super().__init__(r,c,p);self._anc=None
    def mousePressEvent(self,e):
        if e.button()!=Qt.MouseButton.LeftButton:super().mousePressEvent(e);return
        pos=e.position().toPoint() if hasattr(e,'position') else e.pos();item=self.itemAt(pos)
        if not item:super().mousePressEvent(e);return
        row=item.row();ci=self.item(row,0)
        if ci is None:super().mousePressEvent(e);return
        ns=(ci.checkState()==Qt.CheckState.Unchecked)
        if(QApplication.keyboardModifiers()&Qt.ShiftModifier)and self._anc is not None and self._anc!=row:
            lo,hi=min(self._anc,row),max(self._anc,row);self.blockSignals(True)
            for i in range(lo,hi+1):
                if(x:=self.item(i,0))is not None:x.setCheckState(Qt.Checked if ns else Qt.Unchecked)
            self.blockSignals(False);self.itemChanged.emit(ci)
        else:
            if item.column()!=0:ci.setCheckState(Qt.Checked if ns else Unchecked)
            self._anc=row;self.itemChanged.emit(ci)
        if item.column()!=0:super().mousePressEvent(e)

class Win(QMainWindow):
    def __init__(self):
        super().__init__();self.setWindowTitle("ASCII/Unicode/Emoji Studio");self.resize(1400,900);self.cfg=StudioConfig()
        self.strat=Strategy();self._items:List[FileItem]=[];self._paths=set();self._bm:Optional[BatchMgr]=None
        self._can=False;self._mm=MemMon(self.cfg.max_ram_mb)
        self._pa=False;self._pt=0.0;self._pp=.3;self._fc=FrameCache(120);self._fps_c=deque(maxlen=30);self._scale=1.0
        self._dt=QTimer(self);self._dt.setSingleShot(True);self._dt.setInterval(200);self._dt.timeout.connect(self._inv)
        self._pt2=QTimer(self);self._pt2.setInterval(33);self._pt2.timeout.connect(self._adv)
        self._cm:Optional[MPRenderer]=None;self._ps:Optional[QImage]=None
        self._ap=QMediaPlayer();self._ao=QAudioOutput();self._ap.setAudioOutput(self._ao);self._ab:Optional[QBuffer]=None
        self._mt=QTimer(self);self._mt.setInterval(5000);self._mt.timeout.connect(self._mem)
        self.bt=0;self.bd=0;self.bs=0
        self._build();self._sig();self._load();self._scan(str(INPUT_DIR));self._ks()
        QTimer.singleShot(500,self._upd);self._mt.start()
    def _ks(self):
        for k,fn in[("Space",self._tog),("Left",lambda:self._sf(-1)),("Right",lambda:self._sf(1)),("Shift+Left",lambda:self._sr(-5)),("Shift+Right",lambda:self._sr(5)),("Home",lambda:self._st(0)),("End",lambda:self._st(self._cm.dur() if self._cm else 0)),("L",self._tl),("C",self._cc)]:
            QShortcut(QKeySequence(k),self).activated.connect(fn)
    def _tl(self):self.cfg.loop_mode=not self.cfg.loop_mode;self.statusBar().showMessage(f"Loop:{'ON' if self.cfg.loop_mode else'OFF'}",2000)
    def _cc(self):self._fc.clear();self.statusBar().showMessage("Cache cleared",2000);self._upd()
    def _sr(self,d):
        if not self._cm:return
        self._st(max(0,min(self._cm.dur(),self._pt+d)))
    def _st(self,t):
        if not self._cm:return
        d=self._cm.dur();t=max(0,min(d,t));self._pt=t;self._pp=t/d if d>0 else 0
        r=self._cm.panes[0][0];r._parts.ps.clear();r._bf.clear()
        if self._pa:
            try:self._ap.setPosition(int(t*1000))
            except:pass
        self._upd()
    def _cs(self):
        if not self._cm:return 1.0
        tp=self._cm.fw*self._cm.fh
        return .5 if tp>4e6 else(.75 if tp>2e6 else 1.0)
    def _cps(self):
        ss=[.25,.5,1,2,4];i=ss.index(self.cfg.playback_speed) if self.cfg.playback_speed in ss else 2;i=(i+1)%len(ss);self.cfg.playback_speed=ss[i];self.statusBar().showMessage(f"Speed:{ss[i]}x",2000);self._pt2.setInterval(int(33/ss[i]))
    def _build(self):
        root=QSplitter(Qt.Horizontal);self.setCentralWidget(root)
        left=QWidget();left.setMinimumWidth(300);ll=QVBoxLayout(left);ll.setContentsMargins(0,0,0,0);ll.setSpacing(0)
        hdr=QFrame();hdr.setFixedHeight(40);hdr.setStyleSheet("QFrame{background:#1e1e2e;border-bottom:1px solid #11111b;}");hl=QHBoxLayout(hdr);hl.setContentsMargins(12,0,8,0)
        hl.addWidget(QLabel("📂 FILES"));hl.addStretch();ll.addWidget(hdr)
        ls=QSplitter(Qt.Vertical);ls.setHandleWidth(6);ll.addWidget(ls,1)
        fb=QWidget();fl=QVBoxLayout(fb);fl.setContentsMargins(8,8,8,8);fl.setSpacing(8)
        br=QHBoxLayout()
        self.sb=QPushButton("🔄 Scan");self.sb.clicked.connect(lambda:self._scan(str(INPUT_DIR)));br.addWidget(self.sb)
        self.ab=QPushButton("➕ Add");self.ab.clicked.connect(self._add);br.addWidget(self.ab)
        self.cb=QPushButton("✖ Clear");self.cb.clicked.connect(self._cl);br.addWidget(self.cb);br.addStretch()
        self.rc=QCheckBox("Sub");self.rc.setChecked(True);br.addWidget(self.rc);br.addWidget(QLabel("Depth:"))
        self.ds=QSpinBox();self.ds.setRange(1,99);self.ds.setValue(10);self.ds.setFixedWidth(50);br.addWidget(self.ds);fl.addLayout(br)
        sr=QHBoxLayout()
        self.sa=QPushButton("☑ All");self.sa.clicked.connect(self._sa);sr.addWidget(self.sa)
        self.da=QPushButton("☐ None");self.da.clicked.connect(self._dn);sr.addWidget(self.da);sr.addStretch()
        self._sc=QLabel("0 selected");self._sc.setStyleSheet("color:#a6adc8;font-size:11px;");sr.addWidget(self._sc);fl.addLayout(sr)
        self.tbl=BTable(0,3);self.tbl.setHorizontalHeaderLabels(["","File","Status"]);self.tbl.setSelectionBehavior(QTableWidget.SelectRows);self.tbl.setEditTriggers(QTableWidget.NoEditTriggers);self.tbl.verticalHeader().setVisible(False);self.tbl.itemChanged.connect(self._ic);self.tbl.setContextMenuPolicy(Qt.CustomContextMenu);self.tbl.customContextMenuRequested.connect(self._cm2)
        h=self.tbl.horizontalHeader();h.setSectionResizeMode(0,QHeaderView.Fixed);h.resizeSection(0,36);h.setSectionResizeMode(1,QHeaderView.Stretch);h.setSectionResizeMode(2,QHeaderView.Fixed);h.resizeSection(2,100);fl.addWidget(self.tbl)
        ls.addWidget(fb)
        self.tabs=QTabWidget();self.tabs.setDocumentMode(True)
        # Video tab
        vt=QWidget();vf=QFormLayout(vt);vf.setSpacing(6);vf.setContentsMargins(8,8,8,8)
        self.tc=QComboBox();self.tc.addItems(list(THEMES.keys()));vf.addRow("Theme:",self.tc)
        self.rcb=QComboBox();self.rcb.addItems(list(RESOLUTIONS.keys()));vf.addRow("Resolution:",self.rcb)
        self.fs=QSpinBox();self.fs.setRange(30,60);self.fs.setSingleStep(30);self.fs.setValue(30);vf.addRow("FPS:",self.fs)
        self.ec=QComboBox();self.ec.addItems(ENCODERS);vf.addRow("Encoder:",self.ec)
        self.yc=QCheckBox("YT Extras");self.yc.setChecked(True);vf.addRow(self.yc)
        self.ot=QLineEdit();self.ot.setText("{name}_{date}");vf.addRow("Output:",self.ot)
        qt=QHBoxLayout()
        for t,s in[("30s",30),("1m",60),("2m",120),("3m",180),("5m",300)]:
            b=QPushButton(t);b.setFixedWidth(40);b.clicked.connect(lambda c=False,s=s:self._atd(s));qt.addWidget(b)
        qt.addStretch();vf.addRow("Quick:",qt)
        vtw=QScrollArea();vtw.setWidgetResizable(True);vtw.setWidget(vt);vtw.setFrameShape(QFrame.NoFrame);self.tabs.addTab(vtw,"Video")
        # Audio tab
        at=QWidget();af=QFormLayout(at);af.setSpacing(6);af.setContentsMargins(8,8,8,8)
        self.snd=QCheckBox("Audio");self.snd.setChecked(True);af.addRow(self.snd)
        self.pc=QComboBox();self.pc.addItems(list(S_PRESETS.keys()));af.addRow("Preset:",self.pc)
        self.stc=QCheckBox("Stereo");af.addRow(self.stc)
        self.vl=QSpinBox();self.vl.setRange(0,100);self.vl.setValue(50);self.vl.setSuffix("%");af.addRow("Vol:",self.vl)
        self.ts=QPushButton("🔊 Test");self.ts.setStyleSheet("QPushButton{background:#89b4fa;color:#1e1e2e;font-weight:bold;border:none;border-radius:4px;padding:6px;}");self.ts.clicked.connect(self._tsnd);af.addRow("Preview:",self.ts)
        atw=QScrollArea();atw.setWidgetResizable(True);atw.setWidget(at);atw.setFrameShape(QFrame.NoFrame);self.tabs.addTab(atw,"Audio")
        # KB tab
        kt=QWidget();kf=QFormLayout(kt);kf.setSpacing(6);kf.setContentsMargins(8,8,8,8)
        self.kc=QCheckBox("Keyboard");kf.addRow(self.kc)
        self.kl=QComboBox();self.kl.addItems(list(KB_LAYOUTS.keys()));kf.addRow("Layout:",self.kl)
        self.kp=QComboBox();self.kp.addItems(["Bottom Center","Bottom Right","Bottom Left","Top Center","Top Right","Top Left"]);kf.addRow("Pos:",self.kp)
        self.ko=QDoubleSpinBox();self.ko.setRange(.1,1);self.ko.setSingleStep(.05);self.ko.setValue(.82);kf.addRow("Opacity:",self.ko)
        ktw=QScrollArea();ktw.setWidgetResizable(True);ktw.setWidget(kt);ktw.setFrameShape(QFrame.NoFrame);self.tabs.addTab(ktw,"Keyboard")
        # Custom tab
        ct=QWidget();cv=QVBoxLayout(ct);cv.setSpacing(6);cv.setContentsMargins(8,8,8,8)
        self.uc=QCheckBox("Custom Code");cv.addWidget(self.uc);cv.addWidget(QLabel("Input (:rocket: -> 🚀):"))
        self.ce=QPlainTextEdit();self.ce.setPlaceholderText(":rocket: -> 🚀 :fire: -> 🔥");cv.addWidget(self.ce,1)
        cv.addWidget(QLabel("Preview:"))
        self.sp=QPlainTextEdit();self.sp.setReadOnly(True);self.sp.setMaximumHeight(120);self.sp.setStyleSheet("QPlainTextEdit{background:#11111b;color:#a6e3a1;}");cv.addWidget(self.sp)
        cr=QHBoxLayout()
        self.i2a=QPushButton("🖼️ Image→ASCII");self.i2a.clicked.connect(self._i2a);cr.addWidget(self.i2a)
        self.ar=QComboBox();self.ar.addItems(list(ASCII_RAMPS.keys()));cr.addWidget(QLabel("Ramp:"));cr.addWidget(self.ar)
        self.aw=QSpinBox();self.aw.setRange(20,400);self.aw.setValue(100);cr.addWidget(QLabel("W:"));cr.addWidget(self.aw);cr.addStretch();cv.addLayout(cr)
        ctw=QScrollArea();ctw.setWidgetResizable(True);ctw.setWidget(ct);ctw.setFrameShape(QFrame.NoFrame);self.tabs.addTab(ctw,"Custom")
        # Batch tab
        bt=QWidget();bf=QFormLayout(bt);bf.setSpacing(6);bf.setContentsMargins(8,8,8,8)
        self.bp=QSpinBox();self.bp.setRange(1,4);self.bp.setValue(1);bf.addRow("Parallel:",self.bp)
        self.rm=QSpinBox();self.rm.setRange(512,32768);self.rm.setValue(4096);self.rm.setSuffix(" MB");bf.addRow("Max RAM:",self.rm)
        self.fc2=QCheckBox("Compress Frames");self.fc2.setChecked(True);bf.addRow(self.fc2)
        self.rt=QCheckBox("Auto-Retry");self.rt.setChecked(True);bf.addRow(self.rt)
        self.bo=QComboBox();self.bo.addItems(["Smart (Complexity)","File Order","Random"]);bf.addRow("Order:",self.bo)
        self.ml=QLabel("RSS:--");self.ml.setStyleSheet("color:#a6e3a1;font-family:monospace;font-size:11px;");bf.addRow("Mem:",self.ml)
        er=QHBoxLayout();self.dr=QPushButton("📊 Estimate");self.dr.clicked.connect(self._dry);er.addWidget(self.dr);er.addStretch();bf.addRow("Est:",er)
        self.el=QLabel("Click Estimate.");self.el.setWordWrap(True);self.el.setStyleSheet("color:#a6adc8;font-size:11px;");bf.addRow(self.el)
        btw=QScrollArea();btw.setWidgetResizable(True);btw.setWidget(bt);btw.setFrameShape(QFrame.NoFrame);self.tabs.addTab(btw,"Batch")
        ls.addWidget(self.tabs);ls.setSizes([250,500])
        # Bottom bar
        bb=QVBoxLayout();bb.setContentsMargins(8,4,8,8);bb.setSpacing(6)
        self.pb=QProgressBar();self.pb.setVisible(False);self.pb.setFormat("%v/%m (%p%)");bb.addWidget(self.pb)
        b2=QHBoxLayout()
        self.eb=QPushButton("🎬 Export");self.eb.setStyleSheet("QPushButton{background:#a6e3a1;color:#1e1e2e;font-weight:bold;border:none;border-radius:6px;padding:8px;}");self.eb.clicked.connect(self._exp);b2.addWidget(self.eb,1)
        self.sk=QPushButton("⏭ Skip");self.sk.setFixedWidth(80);self.sk.setEnabled(False);self.sk.clicked.connect(self._ska);b2.addWidget(self.sk)
        self.cn=QPushButton("✖ Cancel");self.cn.setFixedWidth(80);self.cn.setEnabled(False);self.cn.clicked.connect(self._cex);b2.addWidget(self.cn);bb.addLayout(b2)
        b3=QHBoxLayout()
        self.sp2=QPushButton("💾 Save");self.sp2.clicked.connect(self._save);b3.addWidget(self.sp2)
        self.lp=QPushButton("📂 Load");self.lp.clicked.connect(self._load2);b3.addWidget(self.lp);bb.addLayout(b3)
        ir=QHBoxLayout()
        self.bi=QLabel("Ready.");self.bi.setStyleSheet("color:#a6adc8;font-size:11px;font-weight:bold;");ir.addWidget(self.bi,1)
        self.sd=QCheckBox("Shutdown when done");self.sd.setStyleSheet("color:#a6adc8;font-size:11px;");ir.addWidget(self.sd);bb.addLayout(ir)
        ll.addLayout(bb);root.addWidget(left)
        # Preview area
        mw=QWidget();ml=QHBoxLayout(mw);ml.setContentsMargins(0,0,0,0);ml.setSpacing(0)
        sp=QSplitter(Qt.Horizontal)
        ssw=QScrollArea();ssw.setWidgetResizable(True);ssw.setFrameShape(QFrame.NoFrame);ssw.setMinimumWidth(320)
        sw=QWidget();sl=QVBoxLayout(sw);sl.setContentsMargins(8,8,8,8);sl.setSpacing(8)
        g=QGroupBox("Text/Emoji/ASCII Settings");f=QFormLayout(g);f.setSpacing(6)
        fcb=QComboBox();fcb.addItems(["Consolas","JetBrains Mono","Fira Code","monospace"]);self.tfc=fcb
        fsa=QCheckBox("Auto");self.tfa=fsa;fr=QHBoxLayout();fr.addWidget(fsa)
        fss=QSpinBox();fss.setRange(8,72);fss.setValue(22);fss.setEnabled(False);self.tfs=fss;fsa.toggled.connect(fss.setEnabled);fr.addWidget(fss);f.addRow("Font:",fcb);f.addRow("Size:",fr)
        self.tw=QSpinBox();self.tw.setRange(30,300);self.tw.setValue(100);f.addRow("WPM:",self.tw)
        self.tt=QDoubleSpinBox();self.tt.setRange(0,.2);self.tt.setSingleStep(.01);f.addRow("Typo:",self.tt)
        self.tg=QDoubleSpinBox();self.tg.setRange(0,1);self.tg.setSingleStep(.05);f.addRow("Glitch:",self.tg)
        self.ts2=QCheckBox("Shorts");f.addRow(self.ts2)
        self.ai=QCheckBox("ASCII Art");f.addRow(self.ai)
        self.tcl=QCheckBox("Clean");self.tcl.setChecked(True);f.addRow(self.tcl)
        self.tm=QCheckBox("Markdown");f.addRow(self.tm)
        self.tc2=QCheckBox("CRT");f.addRow(self.tc2)
        self.tb2=QCheckBox("Bubbles");f.addRow(self.tb2)
        self.tr=QCheckBox("Rainbow");f.addRow(self.tr)
        self.tgr=QCheckBox("Gradient");f.addRow(self.tgr)
        self.tgd=QComboBox();self.tgd.addItems(["Vertical","Horizontal","Diagonal"]);f.addRow("Grad Dir:",self.tgd)
        self.tcm=QComboBox();self.tcm.addItems([m.value for m in ColorMode]);f.addRow("Color Mode:",self.tcm)
        self.tpl=QComboBox();self.tpl.addItems(list(COLOR_PALETTES.keys()));f.addRow("Palette:",self.tpl)
        self.tpo=QCheckBox("Pop Emoji");self.tpo.setChecked(True);f.addRow(self.tpo)
        self.tea=QComboBox();self.tea.addItems([e.value for e in EmojiAnim]);f.addRow("Anim:",self.tea)
        self.tpa=QCheckBox("Particles");self.tpa.setChecked(True);f.addRow(self.tpa)
        self.tcs=QComboBox();self.tcs.addItems(["Block","Beam","Underline"]);f.addRow("Cursor:",self.tcs)
        self.tts=QSpinBox();self.tts.setRange(1,16);self.tts.setValue(4);f.addRow("Tab:",self.tts)
        sl.addWidget(g);sl.addStretch();ssw.setWidget(sw);sp.addWidget(ssw)
        pw=QWidget();pl=QVBoxLayout(pw);pl.setContentsMargins(8,8,8,8);pl.setSpacing(8)
        self.plbl=QLabel();self.plbl.setAlignment(Qt.AlignCenter);self.plbl.setStyleSheet("background:#11111b;border-radius:8px;");self.plbl.setMinimumSize(640,360);pl.addWidget(self.plbl,1)
        sh=QHBoxLayout()
        self.stl=QLabel("Render:0ms|Chars:0/0|Emoji:0");self.stl.setStyleSheet("color:#a6adc8;font-size:11px;font-family:monospace;");sh.addWidget(self.stl);sh.addStretch()
        self.gp=QCheckBox("Pad");self.gp.toggled.connect(self._dt.start);self.gc=QCheckBox("Chrome");self.gc.toggled.connect(self._dt.start);self.gd=QCheckBox("Code");self.gd.toggled.connect(self._dt.start)
        sh.addWidget(self.gp);sh.addWidget(self.gc);sh.addWidget(self.gd);pl.addLayout(sh)
        ct2=QHBoxLayout()
        self.pp=QPushButton("◀");self.pp.setFixedWidth(40);self.pp.clicked.connect(lambda:self._sf(-1));ct2.addWidget(self.pp)
        self.pb2=QPushButton("▶ Animate");self.pb2.setFixedWidth(110);self.pb2.setStyleSheet("QPushButton{background:#a6e3a1;color:#1e1e2e;font-weight:bold;border:none;border-radius:6px;padding:6px;}");self.pb2.clicked.connect(self._tog);ct2.addWidget(self.pb2)
        self.pn=QPushButton("▶");self.pn.setFixedWidth(40);self.pn.clicked.connect(lambda:self._sf(1));ct2.addWidget(self.pn)
        self.spd=QPushButton("1.0x");self.spd.setFixedWidth(50);self.spd.setStyleSheet("QPushButton{color:#89b4fa;font-weight:bold;font-family:monospace;}");self.spd.clicked.connect(self._cps);ct2.addWidget(self.spd)
        self.lp2=QPushButton("🔁");self.lp2.setFixedWidth(40);self.lp2.setCheckable(True);self.lp2.setStyleSheet("QPushButton{color:#a6adc8;}QPushButton:checked{background:#89b4fa;color:#1e1e2e;}");self.lp2.clicked.connect(self._tl);ct2.addWidget(self.lp2)
        self.cc2=QPushButton("🧹");self.cc2.setFixedWidth(40);self.cc2.clicked.connect(self._cc);ct2.addWidget(self.cc2)
        self.sl2=TLSlider(Qt.Horizontal);self.sl2.setRange(0,1000);self.sl2.seek.connect(self._st);self.tl2=QLabel("0:00/0:00");self.tl2.setStyleSheet("color:#a6e3a1;font-family:monospace;");self.tl2.setMinimumWidth(100);ct2.addWidget(self.sl2,1);ct2.addWidget(self.tl2);pl.addLayout(ct2)
        pr=QHBoxLayout()
        self.pf=QLabel("FPS:--|Render:--ms|Cache:0");self.pf.setStyleSheet("color:#585b70;font-size:10px;font-family:monospace;");pr.addWidget(self.pf);pr.addStretch()
        self.sc2=QLabel("Scale:100%");self.sc2.setStyleSheet("color:#585b70;font-size:10px;font-family:monospace;");pr.addWidget(self.sc2);pl.addLayout(pr)
        sp.addWidget(pw);sp.setSizes([450,1000]);ml.addWidget(sp);root.addWidget(mw);root.setSizes([400,1000])
        self.ce.textChanged.connect(self._usp);self._usp()
    def _usp(self):
        t=self.ce.toPlainText();e=convert_shortcodes(t);g=split_graphemes(e);ec=sum(1 for c in g if is_emoji(c));self.sp.setPlainText(f"📊 {len(g)} graphemes|{ec} emoji|{e.count(chr(10))+1} lines\n\n{e}")
    def _i2a(self):
        p,_=QFileDialog.getOpenFileName(self,"Image","","Images (*.png *.jpg *.jpeg *.bmp *.gif *.webp)")
        if not p:return
        img=QImage(p)
        if img.isNull():QMessageBox.warning(self,"Error","Failed");return
        aa=image_to_ascii(img,self.aw.value(),self.ar.currentText());self.ce.textCursor().insertText("\n"+aa+"\n");self.uc.setChecked(True)
    def _mem(self):self._mm.sample();self.ml.setText(self._mm.report())
    def _dry(self):
        items=[FileItem("custom.txt",True)] if self.cfg.use_custom else [i for i in self._items if i.checked]
        if not items:QMessageBox.information(self,"None","Check files.");return
        cmds=[]
        for it in items:
            bn=os.path.splitext(os.path.basename(it.path))[0];ds=datetime.now().strftime("%Y%m%d");on=self.cfg.output_template.format(name=bn,date=ds,lang="text")+".mp4";cmds.append(ExportCmd(it,str(OUTPUT_DIR/on),copy.deepcopy(self.cfg)))
        est=BatchMgr.estimate(cmds,self.strat);self.el.setText(f"📊 {est['n']} items|⏱️ ~{est['t']}|💾 ~{est['s']}")
    def _atd(self,s):
        code,_,_=self.strat._code(self.cfg,self._items,self.cfg.custom_code);self.tw.setValue(Animator.wpm_for(code,s,.5,1.5));self.statusBar().showMessage(f"WPM for ~{s}s",3000)
    def _sf(self,d):
        if not self._cm:return
        dur=self._cm.dur();self._pt=max(0,min(dur,self._pt+d/self.cfg.fps));self._pp=self._pt/dur if dur>0 else 0;self._upd()
    def _tsnd(self):
        try:
            sg=SoundGen(preset=self.cfg.sound_preset,stereo=self.cfg.stereo);s="hello 🚀 world ✨ 🎉 💥";ts=[];t=0
            for g in split_graphemes(s):ts.append((t,g));t+=.2 if is_emoji(g) else(.1 if g==' ' else .06)
            pcm=sg.gen(ts,1)
            if len(pcm)>0:
                buf=io.BytesIO()
                with wave.open(buf,"w") as wf:wf.setnchannels(2 if sg.stereo else 1);wf.setsampwidth(2);wf.setframerate(sg.sr);wf.writeframes(pcm.tobytes())
                self._ap.stop();self._ab=QBuffer();self._ab.setData(buf.getvalue());self._ab.open(QIODevice.ReadOnly);self._ao.setVolume(self.cfg.volume/100);self._ap.setSourceDevice(self._ab,QUrl());self._ap.play();self.statusBar().showMessage(f"🔊 {self.cfg.sound_preset}",3000)
        except Exception as e:logger.error("Audio test",exc_info=True);self.statusBar().showMessage(f"Failed:{e}",3000)
    def _sig(self):
        def uc(k,v):setattr(self.cfg,k,v);self._dt.start()
        self.tc.currentTextChanged.connect(lambda v:uc('theme',v))
        self.rcb.currentTextChanged.connect(lambda v:uc('resolution',v))
        self.fs.valueChanged.connect(lambda v:uc('fps',v))
        self.snd.toggled.connect(lambda v:uc('sound_enabled',v))
        self.pc.currentTextChanged.connect(lambda v:uc('sound_preset',v))
        self.stc.toggled.connect(lambda v:uc('stereo',v))
        self.vl.valueChanged.connect(lambda v:uc('volume',v))
        self.ec.currentTextChanged.connect(lambda v:uc('encoder',v))
        self.uc.toggled.connect(lambda v:uc('use_custom',v))
        self.ce.textChanged.connect(lambda:uc('custom_code',self.ce.toPlainText()))
        self.yc.toggled.connect(lambda v:uc('yt_extras',v))
        self.rc.toggled.connect(lambda v:uc('recursive_scan',v))
        self.ds.valueChanged.connect(lambda v:uc('scan_depth',v))
        self.ot.textChanged.connect(lambda v:uc('output_template',v))
        self.kc.toggled.connect(lambda v:uc('kb_enabled',v))
        self.kl.currentTextChanged.connect(lambda v:uc('kb_layout',v))
        self.kp.currentTextChanged.connect(lambda v:uc('kb_position',v))
        self.ko.valueChanged.connect(lambda v:uc('kb_opacity',v))
        self.tfc.currentTextChanged.connect(lambda v:uc('font_txt',v))
        self.tfa.toggled.connect(lambda v:uc('font_sz_auto_txt',v))
        self.tfs.valueChanged.connect(lambda v:uc('font_sz_txt',v))
        self.tw.valueChanged.connect(lambda v:uc('wpm_txt',v))
        self.tt.valueChanged.connect(lambda v:uc('typo_txt',v))
        self.tg.valueChanged.connect(lambda v:uc('txt_glitch',v))
        self.ts2.toggled.connect(lambda v:uc('shorts_txt',v))
        self.ai.toggled.connect(lambda v:uc('ascii_art',v))
        self.tcl.toggled.connect(lambda v:uc('txt_clean',v))
        self.tm.toggled.connect(lambda v:uc('txt_markdown',v))
        self.tc2.toggled.connect(lambda v:uc('txt_crt',v))
        self.tb2.toggled.connect(lambda v:uc('txt_bubbles',v))
        self.tr.toggled.connect(lambda v:uc('txt_rainbow',v))
        self.tgr.toggled.connect(lambda v:uc('txt_gradient',v))
        self.tgd.currentTextChanged.connect(lambda v:uc('txt_gradient_dir',v))
        self.tcm.currentTextChanged.connect(lambda v:uc('txt_color_mode',v))
        self.tpl.currentTextChanged.connect(lambda v:uc('txt_palette',v))
        self.tpo.toggled.connect(lambda v:uc('txt_pop_emoji',v))
        self.tea.currentTextChanged.connect(lambda v:uc('txt_emoji_anim',v))
        self.tpa.toggled.connect(lambda v:uc('txt_particles',v))
        self.tcs.currentTextChanged.connect(lambda v:uc('txt_cursor_style',v))
        self.tts.valueChanged.connect(lambda v:uc('txt_tab_size',v))
        self.bp.valueChanged.connect(lambda v:(uc('batch_parallel',v),self._mm.__init__(self.cfg.max_ram_mb)))
        self.rm.valueChanged.connect(lambda v:(uc('max_ram_mb',v),self._mm.__init__(v)))
        self.fc2.toggled.connect(lambda v:uc('frame_compress',v))
        self.rt.toggled.connect(lambda v:uc('retry_on_fail',v))
        self.bo.currentTextChanged.connect(lambda v:uc('batch_order',v))
    def _cm2(self,pos):
        item=self.tbl.itemAt(pos)
        if not item:return
        row=item.row()
        if row>=len(self._items):return
        from PySide6.QtWidgets import QMenu;m=QMenu(self);ea=m.addAction("Export This Only")
        if m.exec_(self.tbl.viewport().mapToGlobal(pos))==ea:
            for it in self._items:it.checked=False
            self._items[row].checked=True;self._rt();self._exp()
    def _inv(self):self._cm=None;self._ps=None;self._fc.clear();self._upd()
    def _scan(self,path):
        self._items.clear();self._paths.clear()
        if not os.path.isdir(path):return
        md=self.cfg.scan_depth if self.cfg.recursive_scan else 1
        skip={".git",".hg",".svn","__pycache__","node_modules",".venv","venv",".env",".idea",".vscode","dist","build",".tox",".mypy_cache"}
        found=[]
        for dp,dns,fns in os.walk(path):
            rel=os.path.relpath(dp,path);d=1 if rel=="." else rel.count(os.sep)+2
            if d>md:dns.clear();continue
            dns[:]=[x for x in dns if x not in skip and not x.startswith(".")]
            for fn in sorted(fns):
                if os.path.splitext(fn)[1].lower() in SUPPORTED_EXTENSIONS:found.append(FileItem(os.path.join(dp,fn),True))
        self._items=found;self._paths={i.path for i in found};self._rt()
    def _add(self):
        ps,_=QFileDialog.getOpenFileNames(self,"Files","","Supported (*.txt *.md *.csv *.asc *.ascii *.art *.nfo *.diz *.emoji *.emo *.u8 *.utf8 *.ansi)")
        for p in ps:
            if p not in self._paths:self._items.append(FileItem(p,True));self._paths.add(p)
        self._rt()
    def _cl(self):self._items.clear();self._paths.clear();self._rt();self._inv()
    def _sa(self):
        for i in self._items:i.checked=True
        self._rt();self._sc.setText(f"{sum(1 for i in self._items if i.checked)}/{len(self._items)}");self._dt.start()
    def _dn(self):
        for i in self._items:i.checked=False
        self._rt();self._sc.setText(f"{sum(1 for i in self._items if i.checked)}/{len(self._items)}");self._dt.start()
    def _rt(self):
        self.tbl.blockSignals(True);self.tbl.setRowCount(len(self._items))
        for i,it in enumerate(self._items):
            c=QTableWidgetItem();c.setFlags(Qt.ItemIsUserCheckable|Qt.ItemIsEnabled);c.setCheckState(Qt.Checked if it.checked else Qt.Unchecked)
            self.tbl.setItem(i,0,c);self.tbl.setItem(i,1,QTableWidgetItem(os.path.basename(it.path)));self.tbl.setItem(i,2,QTableWidgetItem(it.status))
        self.tbl.blockSignals(False)
    def _ic(self,item):
        if item.column()==0:self._items[item.row()].checked=item.checkState()==Qt.Checked;self._sc.setText(f"{sum(1 for i in self._items if i.checked)}/{len(self._items)}");self._dt.start()
    def _upd(self):
        if self._cm is None:
            self._cm=self.strat.build(self.cfg,self._items,self.cfg.custom_code)
            if self._cm:self._ps=QImage(self._cm.fw,self._cm.fh,QImage.Format_RGB32);self._scale=self._cs();self.sc2.setText(f"Scale:{int(self._scale*100)}%")
            anim=self._cm.panes[0][1] if self._cm else None
            if anim:self.sl2.set_markers([ts for ts,ch in anim.tl if is_emoji(ch)],self._cm.dur())
            if self._cm and self.cfg.sound_enabled:
                try:sg=SoundGen(preset=self.cfg.sound_preset,stereo=self.cfg.stereo);pcm=sg.gen(self._cm.ts_all(),1.0);self.sl2.set_wave(pcm)
                except:self.sl2.clear_wave()
            else:self.sl2.clear_wave()
        if not self._cm:return
        ts=_time.perf_counter();t=self._cm.dur()*self._pp;fi=int(t*self.cfg.fps)
        ci=self._fc.get(fi)
        if ci is not None:img=ci
        else:
            img=self._cm.render(t,self._ps,dg=self.gp.isChecked() or self.gc.isChecked() or self.gd.isChecked())
            if not self._pa:self._fc.put(fi,img.copy())
        if self.cfg.txt_crt:
            p=QPainter(img);p.setRenderHint(QPainter.Antialiasing);p.setPen(Qt.NoPen);p.setBrush(QColor(0,0,0,70))
            for y in range(0,img.height(),3):p.drawRect(0,y,img.width(),1)
            p.setBrush(QColor(0,255,100,12));p.drawRect(0,0,img.width(),img.height())
            g=QRadialGradient(img.width()/2,img.height()/2,max(img.width(),img.height())*.7);g.setColorAt(0,QColor(0,0,0,0));g.setColorAt(.7,QColor(0,0,0,0));g.setColorAt(1,QColor(0,0,0,120))
            p.setBrush(g);p.setPen(Qt.NoPen);p.drawRect(0,0,img.width(),img.height());p.end()
        self.plbl.setPixmap(QPixmap.fromImage(img).scaled(self.plbl.size(),Qt.KeepAspectRatio,Qt.SmoothTransformation))
        rt=(_time.perf_counter()-ts)*1000;self._fps_c.append(rt);d=self._cm.dur()
        self.tl2.setText(f"{int(t//60)}:{int(t%60):02d}/{int(d//60)}:{int(d%60):02d}")
        a=self._cm.panes[0][1];ec=sum(1 for g in a.dc if is_emoji(g));gc=len(split_graphemes(self._cm.panes[0][2]+"".join(a.dc)))
        self.stl.setText(f"Render:{rt:.1f}ms|Chars:{a.vis(t)}/{len(a.dc)}|Emoji:{ec}|Graphemes:{gc}")
        ar=sum(self._fps_c)/max(1,len(self._fps_c));ef=1000/max(1,ar)
        self.pf.setText(f"FPS:{ef:.0f}|Render:{ar:.1f}ms|Cache:{len(self._fc)}")
        if not self._pa:self.sl2.blockSignals(True);self.sl2.setValue(int(self._pp*1000));self.sl2.blockSignals(False)
    def _tog(self):
        if self._pa:self._pa=False;self._pt2.stop();self._ap.stop();self.pb2.setText("▶ Animate")
        else:
            if self._cm is None:return
            self._pa=True
            if self._pt>=self._cm.dur():self._pt=0;self._fc.clear()
            self.pb2.setText("⏸ Pause")
            if self.cfg.sound_enabled:
                try:
                    sg=SoundGen(preset=self.cfg.sound_preset,stereo=self.cfg.stereo);pcm=sg.gen(self._cm.ts_all(),1.0)
                    if len(pcm)>0:
                        buf=io.BytesIO()
                        with wave.open(buf,"w") as wf:wf.setnchannels(2 if sg.stereo else 1);wf.setsampwidth(2);wf.setframerate(sg.sr);wf.writeframes(pcm.tobytes())
                        self._ab=QBuffer();self._ab.setData(buf.getvalue());self._ab.open(QIODevice.ReadOnly);self._ao.setVolume(self.cfg.volume/100);self._ap.setSourceDevice(self._ab,QUrl());self._ap.setPosition(int(self._pt*1000));self._ap.play()
                except:logger.error("Audio preview failed",exc_info=True)
            self._pt2.setInterval(int(33/self.cfg.playback_speed));self._pt2.start()
    def _adv(self):
        if not self._cm:return
        self._pt+=.033*self.cfg.playback_speed;d=self._cm.dur()
        if self._pt>=d:
            if self.cfg.loop_mode:
                self._pt=0;r=self._cm.panes[0][0];r._parts.ps.clear();r._bf.clear()
                if self.cfg.sound_enabled:
                    try:self._ap.setPosition(0);self._ap.play()
                    except:pass
            else:self._pt=d;self._tog();return
        self._pp=self._pt/d if d>0 else 0
        if self._pa and self.cfg.sound_enabled:
            try:
                ap=self._ap.position()/1000;dr=abs(ap-self._pt)
                if dr>.5:self._ap.setPosition(int(self._pt*1000))
            except:pass
        self._upd()
    def _exp(self):
        items=[FileItem("custom.txt",True)] if self.cfg.use_custom else [i for i in self._items if i.checked]
        if not items:QMessageBox.information(self,"None","Check files.");return
        for it in self._items:
            if it.checked:it.status="PENDING"
        self._rt();self._can=False;cmds=[]
        for it in items:
            bn=os.path.splitext(os.path.basename(it.path))[0];ds=datetime.now().strftime("%Y%m%d");on=self.cfg.output_template.format(name=bn,date=ds,lang="text")+".mp4";cmds.append(ExportCmd(it,str(OUTPUT_DIR/on),copy.deepcopy(self.cfg)))
        self.bt=len(cmds);self.bd=0;self.bs=_time.time();self.pb.setVisible(True);self.pb.setRange(0,self.bt);self.pb.setValue(0);self.eb.setEnabled(False);self.sk.setEnabled(True);self.cn.setEnabled(True)
        self.bi.setText(f"Starting {self.bt} videos (parallel={self.cfg.batch_parallel})...")
        self._bm=BatchMgr(cmds,self.cfg,self.strat,self._items)
        self._bm.progress.connect(lambda p,i:(self.bi.setText(i),self.pb.setValue(int(p*self.bt/100))))
        self._bm.started_.connect(lambda p:self._uis(os.path.basename(p),"RUNNING"))
        self._bm.done_.connect(lambda p:(self._uis(os.path.basename(p),"DONE"),setattr(self,'bd',self.bd+1),self.pb.setValue(self.bd),gc.collect()))
        self._bm.failed_.connect(lambda p,e:self._uis(os.path.basename(p),"FAILED"))
        self._bm.finished_.connect(self._bf2);self._bm.mem.connect(lambda s:self.ml.setText(s));self._bm.start()
    def _uis(self,n,s):
        for it in self._items:
            if os.path.basename(it.path)==os.path.splitext(n)[0]:it.status=s;break
        self._rt();self.statusBar().showMessage(f"{s}:{n}",2000)
    def _bf2(self,d,t):
        self.eb.setEnabled(True);self.sk.setEnabled(False);self.cn.setEnabled(False);self.pb.setVisible(False)
        el=_time.time()-self.bs;self.bi.setText(f"Done! {d}/{t} in {int(el//60)}m{int(el%60)}s")
        QMessageBox.information(self,"Done",f"{d}/{t} done.\nTime:{int(el//60)}m{int(el%60)}s")
        if self.sd.isChecked():self._sd2();gc.collect()
    def _ska(self):
        if self._bm:self.statusBar().showMessage("Skipping...");self._bm.cancel()
    def _cex(self):
        self._can=True
        if self._bm:self._bm.cancel()
        self.eb.setEnabled(True);self.sk.setEnabled(False);self.cn.setEnabled(False);self.pb.setVisible(False);self.bi.setText("Cancelled")
        for it in self._items:
            if it.status in("PENDING","RUNNING"):it.status="CANCELLED"
        self._rt()
    def _sd2(self):
        if QMessageBox.question(self,"Shutdown?","Shutdown PC?",QMessageBox.Yes|QMessageBox.No,QMessageBox.No)==QMessageBox.Yes:
            try:
                if platform.system()=="Windows":subprocess.run(["shutdown","/s","/t","30"])
                elif platform.system()=="Linux":subprocess.run(["shutdown","-h","now"])
                elif platform.system()=="Darwin":subprocess.run(["shutdown","-h","now"])
            except:pass
    def _save(self):
        p,_=QFileDialog.getSaveFileName(self,"Save","","Studio (*.studio)")
        if p:
            with open(p,"w",encoding="utf-8") as f:json.dump(asdict(self.cfg),f,indent=2)
            self.statusBar().showMessage("Saved!",3000)
    def _load2(self):
        p,_=QFileDialog.getOpenFileName(self,"Load","","Studio (*.studio)")
        if not p:return
        try:
            with open(p,"r",encoding="utf-8") as f:self.cfg=StudioConfig(**json.load(f))
        except:QMessageBox.warning(self,"Error","Failed.");return
        self.tc.setCurrentText(self.cfg.theme);self.rcb.setCurrentText(self.cfg.resolution);self.fs.setValue(self.cfg.fps)
        self.snd.setChecked(self.cfg.sound_enabled);self.pc.setCurrentText(self.cfg.sound_preset);self.stc.setChecked(self.cfg.stereo);self.vl.setValue(self.cfg.volume);self.ec.setCurrentText(self.cfg.encoder)
        self.uc.setChecked(self.cfg.use_custom);self.ce.setPlainText(self.cfg.custom_code);self.yc.setChecked(self.cfg.yt_extras);self.rc.setChecked(self.cfg.recursive_scan);self.ds.setValue(self.cfg.scan_depth);self.ot.setText(self.cfg.output_template)
        self.kc.setChecked(self.cfg.kb_enabled);self.kl.setCurrentText(self.cfg.kb_layout);self.kp.setCurrentText(self.cfg.kb_position);self.ko.setValue(self.cfg.kb_opacity)
        self.tfc.setCurrentText(self.cfg.font_txt);self.tfa.setChecked(self.cfg.font_sz_auto_txt);self.tfs.setValue(self.cfg.font_sz_txt);self.tw.setValue(self.cfg.wpm_txt);self.tt.setValue(self.cfg.typo_txt);self.tg.setValue(self.cfg.txt_glitch)
        self.ts2.setChecked(self.cfg.shorts_txt);self.ai.setChecked(self.cfg.ascii_art);self.tcl.setChecked(self.cfg.txt_clean);self.tm.setChecked(self.cfg.txt_markdown);self.tc2.setChecked(self.cfg.txt_crt);self.tb2.setChecked(self.cfg.txt_bubbles)
        self.tr.setChecked(self.cfg.txt_rainbow);self.tgr.setChecked(self.cfg.txt_gradient);self.tgd.setCurrentText(self.cfg.txt_gradient_dir);self.tcm.setCurrentText(self.cfg.txt_color_mode);self.tpl.setCurrentText(self.cfg.txt_palette)
        self.tpo.setChecked(self.cfg.txt_pop_emoji);self.tea.setCurrentText(self.cfg.txt_emoji_anim);self.tpa.setChecked(self.cfg.txt_particles);self.tcs.setCurrentText(self.cfg.txt_cursor_style);self.tts.setValue(self.cfg.txt_tab_size)
        self.bp.setValue(self.cfg.batch_parallel);self.rm.setValue(self.cfg.max_ram_mb);self.fc2.setChecked(self.cfg.frame_compress);self.rt.setChecked(self.cfg.retry_on_fail);self.bo.setCurrentText(self.cfg.batch_order)
        self.statusBar().showMessage("Loaded!",3000);self._inv()
    def _load(self):
        if SETTINGS_FILE.exists():
            try:
                d=json.loads(SETTINGS_FILE.read_text());self.tc.setCurrentText(d.get("theme","Dracula"));self.sd.setChecked(d.get("shutdown_when_done",False))
            except:pass
    def closeEvent(self,e):
        SETTINGS_FILE.write_text(json.dumps({"theme":self.cfg.theme,"shutdown_when_done":self.sd.isChecked()}));super().closeEvent(e)

def image_to_ascii(image: QImage, target_width: int = 80, ramp: str = "Standard (10)") -> str:
    ramp_chars = ASCII_RAMPS.get(ramp, ASCII_RAMPS["Standard (10)"])
    aspect = image.height() / max(1, image.width()); th = max(1, int(target_width * aspect * 0.5))
    sc = image.scaled(target_width, th, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
    if sc.format() != QImage.Format_RGB32: sc = sc.convertToFormat(QImage.Format_RGB32)
    ptr = sc.constBits(); ptr.setsize(sc.bytesPerLine() * sc.height())
    arr = np.frombuffer(ptr, dtype=np.uint8).reshape((sc.height(), sc.bytesPerLine() // 4, 4))
    lum = 0.2126 * arr[:, :, 0] + 0.7152 * arr[:, :, 1] + 0.0722 * arr[:, :, 2]
    idx = np.clip(lum / 255.0 * (len(ramp_chars) - 1), 0, len(ramp_chars) - 1).astype(int)
    return "\n".join("".join(ramp_chars[idx[y, x]] for x in range(target_width)) for y in range(th))

STYLE="""QMainWindow,QDialog{background:#1e1e2e;}
QGroupBox{color:#cdd6f4;font-weight:bold;font-size:12px;border:1px solid #45475a;border-radius:8px;margin-top:10px;padding-top:14px;}
QGroupBox::title{subcontrol-origin:margin;left:12px;}
QLabel{color:#cdd6f4;}
QCheckBox{color:#cdd6f4;spacing:6px;}
QCheckBox::indicator{width:16px;height:16px;border-radius:3px;border:1px solid #45475a;background:#313244;}
QCheckBox::indicator:checked{background:#89b4fa;border-color:#89b4fa;}
QTableWidget{background:#181825;color:#cdd6f4;gridline-color:#313244;border:none;outline:none;border-radius:6px;}
QTableWidget::item{padding:4px 6px;border-bottom:1px solid #11111b;}
QTableWidget::item:selected{background:#89b4fa;color:#1e1e2e;}
QHeaderView::section{background:#1e1e2e;color:#a6adc8;border:none;padding:4px;font-size:10px;}
QComboBox,QSpinBox,QDoubleSpinBox,QLineEdit{background:#313244;color:#cdd6f4;border:1px solid #45475a;border-radius:4px;padding:4px 8px;min-height:22px;}
QComboBox::drop-down{border:none;}
QComboBox QAbstractItemView{background:#313244;color:#cdd6f4;selection-background-color:#89b4fa;selection-color:#1e1e2e;border:1px solid #45475a;}
QPushButton{background:#313244;color:#cdd6f4;border:1px solid #45475a;border-radius:6px;padding:6px 12px;min-height:22px;}
QPushButton:hover{background:#45475a;border-color:#89b4fa;}
QProgressBar{background:#313244;border:none;border-radius:4px;text-align:center;color:#cdd6f4;min-height:20px;}
QProgressBar::chunk{background:#89b4fa;border-radius:4px;}
QTabWidget::pane{border:1px solid #45475a;border-radius:6px;background:#1e1e2e;top:-1px;}
QTabBar::tab{background:#313244;color:#a6adc8;padding:6px 12px;border:1px solid #45475a;border-bottom:none;border-top-left-radius:6px;border-top-right-radius:6px;font-weight:bold;}
QTabBar::tab:selected{background:#1e1e2e;color:#cdd6f4;border-bottom:2px solid #89b4fa;}
QPlainTextEdit{background:#11111b;color:#cdd6f4;border:1px solid #45475a;border-radius:4px;}
QSplitter{background:#11111b;}
QSplitter::handle{background:#181825;}
QSplitter::handle:horizontal{width:8px;border-left:1px solid #11111b;border-right:1px solid #11111b;}
QSplitter::handle:horizontal:hover{background:#45475a;}
QScrollArea{background:transparent;border:none;}
QScrollBar:vertical{background:#181825;width:8px;border:none;border-radius:4px;}
QScrollBar::handle:vertical{background:#45475a;border-radius:4px;min-height:20px;}
QScrollBar::handle:vertical:hover{background:#585b70;}
QScrollBar:horizontal{background:#181825;height:8px;border:none;border-radius:4px;}
QScrollBar::handle:horizontal{background:#45475a;border-radius:4px;min-width:20px;}
"""

if __name__=="__main__":
    app=QApplication(sys.argv);app.setStyle("Fusion");app.setStyleSheet(STYLE)
    pal=QPalette();pal.setColor(QPalette.Window,QColor("#1e1e2e"));pal.setColor(QPalette.WindowText,QColor("#cdd6f4"));pal.setColor(QPalette.Base,QColor("#313244"));pal.setColor(QPalette.Text,QColor("#cdd6f4"));pal.setColor(QPalette.Button,QColor("#313244"));pal.setColor(QPalette.ButtonText,QColor("#cdd6f4"));pal.setColor(QPalette.Highlight,QColor("#89b4fa"));pal.setColor(QPalette.HighlightedText,QColor("#1e1e2e"));app.setPalette(pal)
    w=Win();w.show();sys.exit(app.exec())
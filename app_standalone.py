#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DES Secure Messenger – Telegram/Messenger Style UI
Đề tài nhóm 27 – Mã hóa DES 2 chiều qua mạng TCP

STANDALONE VERSION: Tất cả DES algorithm nhúng trong file
"""

import tkinter as tk
from tkinter import scrolledtext, messagebox, font as tkfont, filedialog
import socket
import threading
import time
import random
import string
import math
import os
import hashlib
import zlib

try:
    import winsound
    HAS_SOUND = True
except ImportError:
    HAS_SOUND = False


# ============================================================
#   DES CORE - Thuật toán DES tự implement
# ============================================================

# ---- Bảng hoán vị PC-1 (keyp) ----
keyp = [57,49,41,33,25,17, 9,
         1,58,50,42,34,26,18,
        10, 2,59,51,43,35,27,
        19,11, 3,60,52,44,36,
        63,55,47,39,31,23,15,
         7,62,54,46,38,30,22,
        14, 6,61,53,45,37,29,
        21,13, 5,28,20,12, 4]

# ---- Số bit dịch trái mỗi vòng ----
shift_table = [1,1,2,2,2,2,2,2,1,2,2,2,2,2,2,1]

# ---- Bảng nén khóa PC-2 ----
key_comp = [14,17,11,24, 1, 5,
             3,28,15, 6,21,10,
            23,19,12, 4,26, 8,
            16, 7,27,20,13, 2,
            41,52,31,37,47,55,
            30,40,51,45,33,48,
            44,49,39,56,34,53,
            46,42,50,36,29,32]

# ---- Bảng hoán vị IP ----
initial_perm = [58,50,42,34,26,18,10, 2,
                60,52,44,36,28,20,12, 4,
                62,54,46,38,30,22,14, 6,
                64,56,48,40,32,24,16, 8,
                57,49,41,33,25,17, 9, 1,
                59,51,43,35,27,19,11, 3,
                61,53,45,37,29,21,13, 5,
                63,55,47,39,31,23,15, 7]

# ---- Bảng mở rộng E ----
exp_d = [32, 1, 2, 3, 4, 5,
          4, 5, 6, 7, 8, 9,
          8, 9,10,11,12,13,
         12,13,14,15,16,17,
         16,17,18,19,20,21,
         20,21,22,23,24,25,
         24,25,26,27,28,29,
         28,29,30,31,32, 1]

# ---- 8 hộp S-Box ----
s = [
    [[14,4,13,1,2,15,11,8,3,10,6,12,5,9,0,7],
     [0,15,7,4,14,2,13,1,10,6,12,11,9,5,3,8],
     [4,1,14,8,13,6,2,11,15,12,9,7,3,10,5,0],
     [15,12,8,2,4,9,1,7,5,11,3,14,10,0,6,13]],

    [[15,1,8,14,6,11,3,4,9,7,2,13,12,0,5,10],
     [3,13,4,7,15,2,8,14,12,0,1,10,6,9,11,5],
     [0,14,7,11,10,4,13,1,5,8,12,6,9,3,2,15],
     [13,8,10,1,3,15,4,2,11,6,7,12,0,5,14,9]],

    [[10,0,9,14,6,3,15,5,1,13,12,7,11,4,2,8],
     [13,7,0,9,3,4,6,10,2,8,5,14,12,11,15,1],
     [13,6,4,9,8,15,3,0,11,1,2,12,5,10,14,7],
     [1,10,13,0,6,9,8,7,4,15,14,3,11,5,2,12]],

    [[7,13,14,3,0,6,9,10,1,2,8,5,11,12,4,15],
     [13,8,11,5,6,15,0,3,4,7,2,12,1,10,14,9],
     [10,6,9,0,12,11,7,13,15,1,3,14,5,2,8,4],
     [3,15,0,6,10,1,13,8,9,4,5,11,12,7,2,14]],

    [[2,12,4,1,7,10,11,6,8,5,3,15,13,0,14,9],
     [14,11,2,12,4,7,13,1,5,0,15,10,3,9,8,6],
     [4,2,1,11,10,13,7,8,15,9,12,5,6,3,0,14],
     [11,8,12,7,1,14,2,13,6,15,0,9,10,4,5,3]],

    [[12,1,10,15,9,2,6,8,0,13,3,4,14,7,5,11],
     [10,15,4,2,7,12,9,5,6,1,13,14,0,11,3,8],
     [9,14,15,5,2,8,12,3,7,0,4,10,1,13,11,6],
     [4,3,2,12,9,5,15,10,11,14,1,7,6,0,8,13]],

    [[4,11,2,14,15,0,8,13,3,12,9,7,5,10,6,1],
     [13,0,11,7,4,9,1,10,14,3,5,12,2,15,8,6],
     [1,4,11,13,12,3,7,14,10,15,6,8,0,5,9,2],
     [6,11,13,8,1,4,10,7,9,5,0,15,14,2,3,12]],

    [[13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7],
     [1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2],
     [7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8],
     [2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11]],
]

# ---- Bảng hoán vị P-Box ----
per = [16,7,20,21,29,12,28,17,
        1,15,23,26, 5,18,31,10,
        2, 8,24,14,32,27, 3, 9,
       19,13,30, 6,22,11, 4,25]

# ---- Bảng hoán vị cuối IP^-1 ----
final_perm = [40,8,48,16,56,24,64,32,
              39,7,47,15,55,23,63,31,
              38,6,46,14,54,22,62,30,
              37,5,45,13,53,21,61,29,
              36,4,44,12,52,20,60,28,
              35,3,43,11,51,19,59,27,
              34,2,42,10,50,18,58,26,
              33,1,41, 9,49,17,57,25]

# ==============================================================
#   CÁC HÀM HỖ TRỢ DES
# ==============================================================

def permute(k, arr):
    """Tương đương hàm permute()"""
    return "".join(k[arr[i] - 1] for i in range(len(arr)))

def shift_left_fn(k, shifts):
    """Tương đương hàm shift_left()"""
    for _ in range(shifts):
        k = k[1:] + k[0]
    return k

def xor_(a, b):
    """Tương đương hàm xor_()"""
    ans = ""
    for i in range(len(a)):
        ans += "0" if a[i] == b[i] else "1"
    return ans

def hex2bin(s):
    """Chuyển hex sang binary string"""
    mp = {'0':'0000','1':'0001','2':'0010','3':'0011',
          '4':'0100','5':'0101','6':'0110','7':'0111',
          '8':'1000','9':'1001','A':'1010','B':'1011',
          'C':'1100','D':'1101','E':'1110','F':'1111'}
    return "".join(mp[c] for c in s.upper())

def bin2hex(s):
    """Chuyển binary string sang hex"""
    mp = {v: k for k, v in
          {'0':'0000','1':'0001','2':'0010','3':'0011',
           '4':'0100','5':'0101','6':'0110','7':'0111',
           '8':'1000','9':'1001','A':'1010','B':'1011',
           'C':'1100','D':'1101','E':'1110','F':'1111'}.items()}
    return "".join(mp[s[i:i+4]] for i in range(0, len(s), 4))

def str_to_hex(text):
    """Chuyển chuỗi ký tự sang hex"""
    return text.encode('utf-8').hex().upper()

def hex_to_str(h):
    """Chuyển hex về chuỗi ký tự"""
    return bytes.fromhex(h).decode('utf-8', errors='replace')

# ==============================================================
#   TẠO KHÓA CON
# ==============================================================

def generate_round_keys(key_str):
    """Tạo 16 khóa con 48-bit từ khóa gốc 8 ký tự"""
    key = hex2bin(str_to_hex(key_str))
    key = permute(key, keyp)
    left  = key[:28]
    right = key[28:]
    rkb = []
    rk  = []
    for i in range(16):
        left  = shift_left_fn(left,  shift_table[i])
        right = shift_left_fn(right, shift_table[i])
        combine    = left + right
        round_key  = permute(combine, key_comp)
        rkb.append(round_key)
        rk.append(bin2hex(round_key))
    return rkb, rk

# ==============================================================
#   MÃ HÓA MỘT BLOCK
# ==============================================================

def encrypt_block(pt, rkb, rk):
    """Mã hóa 1 block 16 ký tự hex (64 bit)"""
    pt = hex2bin(pt)
    pt = permute(pt, initial_perm)

    left  = pt[:32]
    right = pt[32:]

    for i in range(16):
        right_expanded = permute(right, exp_d)
        x = xor_(rkb[i], right_expanded)
        op = ""
        for j in range(8):
            row = 2 * int(x[j*6]) + int(x[j*6 + 5])
            col = (8 * int(x[j*6+1]) + 4 * int(x[j*6+2])
                   + 2 * int(x[j*6+3]) + int(x[j*6+4]))
            val = s[j][row][col]
            op += format(val, '04b')
        op = permute(op, per)
        x = xor_(op, left)
        left = x
        if i != 15:
            left, right = right, left

    combine = left + right
    cipher  = bin2hex(permute(combine, final_perm))
    return cipher

# ==============================================================
#   MÃ HÓA CHUỖI DÀI
# ==============================================================

def encrypt_hex(hex_string, rkb, rk):
    """Cắt chuỗi hex thành từng block 16 ký tự rồi mã hóa"""
    remainder = len(hex_string) % 16
    if remainder != 0:
        padding_len = (16 - remainder) // 2
        hex_string += '20' * padding_len

    result = ""
    for i in range(0, len(hex_string), 16):
        block = hex_string[i:i+16]
        result += encrypt_block(block, rkb, rk)
    return result

# ==============================================================
#   HÀM MÃ HÓA CHÍNH
# ==============================================================

def encrypt_text(plaintext, key):
    """Mã hóa chuỗi văn bản bằng DES"""
    rkb, rk = generate_round_keys(key)
    hex_pt   = str_to_hex(plaintext)
    return encrypt_hex(hex_pt, rkb, rk)

def encrypt_hex_data(hex_string, key):
    """Mã hóa hex data trực tiếp (cho file binary) - KHÔNG convert thêm"""
    rkb, rk = generate_round_keys(key)
    return encrypt_hex(hex_string, rkb, rk)

# ==============================================================
#   HÀM GIẢI MÃ
# ==============================================================

def decrypt_text(ciphertext_hex, key):
    """Giải mã chuỗi hex bằng DES, trả về text string"""
    rkb, rk = generate_round_keys(key)
    rkb = rkb[::-1]
    rk  = rk[::-1]
    decrypted_hex = encrypt_hex(ciphertext_hex, rkb, rk)
    raw = bytes.fromhex(decrypted_hex)
    pad_len = raw[-1]
    if pad_len <= 8:
        raw = raw[:-pad_len]
    return raw.decode('utf-8', errors='replace').rstrip('\x00').rstrip(' ')

def decrypt_hex_only(ciphertext_hex, key):
    """Giải mã chuỗi hex bằng DES, trả về hex string (cho file/chunks)"""
    rkb, rk = generate_round_keys(key)
    rkb = rkb[::-1]
    rk  = rk[::-1]
    decrypted_hex = encrypt_hex(ciphertext_hex, rkb, rk)
    raw = bytes.fromhex(decrypted_hex)
    pad_len = raw[-1]
    if pad_len <= 8:
        raw = raw[:-pad_len]
    return raw.hex().upper()

def decrypt_hex_no_padding(ciphertext_hex, key):
    """Giải mã chuỗi hex bằng DES, trả về hex string (KHÔNG xóa padding - cho file chunks)"""
    rkb, rk = generate_round_keys(key)
    rkb = rkb[::-1]
    rk  = rk[::-1]
    decrypted_hex = encrypt_hex(ciphertext_hex, rkb, rk)
    return decrypted_hex


# ═══════════════════════════════════════════════════════
#  THEME – High-contrast Telegram dark
# ═══════════════════════════════════════════════════════
TG_BG          = "#17212B"   # nền chính
TG_SIDEBAR     = "#0D1525"   # sidebar tối sắc nét
TG_TOPBAR      = "#1A2840"   # topbar hơi sáng hơn nền
TG_INPUT_BG    = "#0D1525"   # input
TG_MSG_SENT    = "#2D6098"   # bubble gửi — xanh đậm rõ
TG_MSG_RECV    = "#1E3248"   # bubble nhận — xanh than rõ
TG_ACCENT      = "#5EA8FF"   # xanh sáng
TG_ACCENT2     = "#90CAFF"   # xanh sáng hơn (hover)
TG_GREEN       = "#2ECC71"   # xanh lá sáng
TG_ERROR       = "#FF5252"   # đỏ sáng
TG_YELLOW      = "#FFD54F"   # vàng sáng

TG_TEXT        = "#F0F4F8"   # text chính — gần trắng
TG_TEXT_DIM    = "#9DBDD8"   # text phụ — xanh nhạt đủ đọc
TG_TEXT_TIME   = "#7EB8E8"   # timestamp
TG_DIVIDER     = "#0A111C"   # đường kẻ

TG_HOVER       = "#1E3252"   # hover state
TG_SELECTED    = "#253D5E"   # selected state
TG_FIELD_BG    = "#162030"   # ô input trong sidebar
TG_FIELD_BD    = "#3A6080"   # viền ô input

FONT_UI        = "Segoe UI"

def get_local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


# ════════════════════════════════════════════════════════
#  TOOLTIP
# ════════════════════════════════════════════════════════
class Tooltip:
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tip = None
        widget.bind("<Enter>", self.show)
        widget.bind("<Leave>", self.hide)

    def show(self, e=None):
        x = self.widget.winfo_rootx() + 20
        y = self.widget.winfo_rooty() + self.widget.winfo_height() + 4
        self.tip = tk.Toplevel(self.widget)
        self.tip.wm_overrideredirect(True)
        self.tip.wm_geometry(f"+{x}+{y}")
        lbl = tk.Label(self.tip, text=self.text, bg="#1A2B3C", fg=TG_TEXT,
                       font=(FONT_UI, 9), padx=8, pady=4, relief="flat")
        lbl.pack()

    def hide(self, e=None):
        if self.tip:
            self.tip.destroy()
            self.tip = None


# ════════════════════════════════════════════════════════
#  ICON BUTTON (text-based, circular hover)
# ════════════════════════════════════════════════════════
class IconButton(tk.Label):
    def __init__(self, parent, icon, command=None, size=22,
                 fg=TG_TEXT_DIM, hover_fg=TG_ACCENT, bg=TG_TOPBAR, tooltip=None, **kw):
        super().__init__(parent, text=icon, font=(FONT_UI, size), bg=bg,
                         fg=fg, cursor="hand2", pady=2, padx=4, **kw)
        self._bg = bg
        self._fg = fg
        self._hover_fg = hover_fg
        self._cmd = command
        self.bind("<Enter>", lambda e: self.configure(fg=hover_fg))
        self.bind("<Leave>", lambda e: self.configure(fg=fg))
        self.bind("<ButtonPress-1>", lambda e: command() if command else None)
        if tooltip:
            Tooltip(self, tooltip)


# ════════════════════════════════════════════════════════
#  ROUNDED SEND BUTTON
# ════════════════════════════════════════════════════════
class SendButton(tk.Canvas):
    def __init__(self, parent, command=None, size=40, **kw):
        super().__init__(parent, width=size, height=size, bg=TG_INPUT_BG,
                         highlightthickness=0, cursor="hand2", **kw)
        self._size = size
        self._cmd = command
        self._hover = False
        self._draw(False)
        self.bind("<Enter>", lambda e: self._draw(True))
        self.bind("<Leave>", lambda e: self._draw(False))
        self.bind("<ButtonPress-1>", lambda e: command() if command else None)

    def _draw(self, hover):
        self.delete("all")
        s = self._size
        r = s // 2
        color = TG_ACCENT2 if hover else TG_ACCENT
        self.create_oval(2, 2, s-2, s-2, fill=color, outline="")
        # Paper-plane icon
        pts = [r-2, 6, r+14, r, r-2, r+3, r-2, s-8, r+4, r+2]
        self.create_polygon(pts, fill="white", outline="", smooth=False)
        self.create_line(r-2, r+3, r+8, r-1, fill="white", width=1.5)

    def set_icon(self, icon):
        """Toggle icon between send and cancel."""
        self.delete("all")
        s = self._size
        if icon == "cancel":
            self.create_oval(2, 2, s-2, s-2, fill=TG_ERROR, outline="")
            self.create_line(10, 10, s-10, s-10, fill="white", width=2.5)
            self.create_line(s-10, 10, 10, s-10, fill="white", width=2.5)
        else:
            self._draw(False)


# ════════════════════════════════════════════════════════
#  MAIN APP
# ════════════════════════════════════════════════════════
class DESMessengerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("DES Secure Messenger")
        self.root.configure(bg=TG_BG)

        sw = root.winfo_screenwidth()
        sh = root.winfo_screenheight()
        w = min(1000, int(sw * 0.78))
        h = min(740, int(sh * 0.85))
        x = (sw - w) // 2
        y = (sh - h) // 2
        root.geometry(f"{w}x{h}+{x}+{y}")
        root.minsize(680, 500)
        root.resizable(True, True)

        # State
        self.server_running = False
        self.server_socket  = None
        self.server_thread  = None
        self.msg_count_sent = 0
        self.msg_count_recv = 0
        self._sending       = False
        self._send_socket   = None
        self.local_ip       = get_local_ip()
        self._sidebar_visible = True
        self._log_visible     = False
        self.selected_files = []  # List file được chọn để gửi
        self.pending_files  = {}  # Lưu chunks: {file_name: {chunk_num: cipher_data, total_chunks: N, key: K}}
        self.receive_folder = os.path.expanduser("~")  # Mặc định: home directory

        self._build_gui()
        self._set_status("Sẵn sàng", TG_GREEN)
        self._sys_msg(f"🔐 DES Secure Messenger khởi động  •  IP: {self.local_ip}")

    # ────────────────────────────────────────────────────
    #  BUILD GUI
    # ────────────────────────────────────────────────────
    def _build_gui(self):
        # Root layout: sidebar | chat area
        self.root.columnconfigure(0, weight=0)
        self.root.columnconfigure(1, weight=1)
        self.root.rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_chat_area()

    # ─── SIDEBAR ─────────────────────────────────────────
    def _build_sidebar(self):
        self.sidebar = tk.Frame(self.root, bg=TG_SIDEBAR, width=280)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)
        self.sidebar.columnconfigure(0, weight=1)

        # ---- TOP SEARCH BAR ----
        top = tk.Frame(self.sidebar, bg=TG_SIDEBAR, pady=8, padx=10)
        top.grid(row=0, column=0, sticky="ew")
        top.columnconfigure(0, weight=1)

        tk.Label(top, text="🔐 DES Messenger", font=(FONT_UI, 13, "bold"),
                 bg=TG_SIDEBAR, fg=TG_TEXT).grid(row=0, column=0, sticky="w")
        tk.Label(top, text=f"IP: {self.local_ip}", font=(FONT_UI, 8),
                 bg=TG_SIDEBAR, fg=TG_TEXT_DIM).grid(row=1, column=0, sticky="w")

        # ---- DIVIDER ----
        tk.Frame(self.sidebar, bg=TG_DIVIDER, height=1).grid(row=1, column=0, sticky="ew")

        # ---- SETTINGS SECTIONS ----
        scroll_frame = tk.Frame(self.sidebar, bg=TG_SIDEBAR)
        scroll_frame.grid(row=2, column=0, sticky="nsew", padx=0, pady=0)
        self.sidebar.rowconfigure(2, weight=1)
        scroll_frame.columnconfigure(0, weight=1)

        # SERVER card
        self._build_server_section(scroll_frame)
        # CONNECT card
        self._build_connect_section(scroll_frame)
        # KEY card
        self._build_key_section(scroll_frame)
        # SAVE FOLDER card
        self._build_save_folder_section(scroll_frame)

        # ---- STATUS FOOTER ----
        tk.Frame(self.sidebar, bg=TG_DIVIDER, height=1).grid(row=3, column=0, sticky="ew")
        foot = tk.Frame(self.sidebar, bg=TG_SIDEBAR, pady=8, padx=10)
        foot.grid(row=4, column=0, sticky="ew")
        foot.columnconfigure(1, weight=1)

        self.dot_status = tk.Label(foot, text="●", font=(FONT_UI, 10),
                                   bg=TG_SIDEBAR, fg=TG_GREEN)
        self.dot_status.grid(row=0, column=0, padx=(0, 6))
        self.lbl_status = tk.Label(foot, text="Sẵn sàng", font=(FONT_UI, 9),
                                   bg=TG_SIDEBAR, fg=TG_TEXT_DIM, anchor="w")
        self.lbl_status.grid(row=0, column=1, sticky="ew")

    def _section_header(self, parent, title, icon, row):
        """Section header with bold title and accent icon."""
        frm = tk.Frame(parent, bg=TG_SIDEBAR)
        frm.grid(row=row, column=0, sticky="ew", padx=0, pady=0)
        frm.columnconfigure(0, weight=1)
        # Header bar — slightly lighter than sidebar for contrast
        hdr = tk.Frame(frm, bg=TG_HOVER, pady=8, padx=12, cursor="hand2")
        hdr.pack(fill="x")
        tk.Label(hdr, text=icon, font=(FONT_UI, 12), bg=TG_HOVER, fg=TG_ACCENT2
                 ).pack(side="left", padx=(0, 8))
        tk.Label(hdr, text=title, font=(FONT_UI, 10, "bold"),
                 bg=TG_HOVER, fg=TG_TEXT).pack(side="left")
        # Thin accent underline
        tk.Frame(frm, bg=TG_ACCENT, height=1).pack(fill="x")
        body = tk.Frame(frm, bg=TG_SIDEBAR, padx=14, pady=8)
        body.pack(fill="x")
        body.columnconfigure(0, weight=1)
        return body

    def _field_label(self, parent, text, row):
        tk.Label(parent, text=text, font=(FONT_UI, 9), bg=TG_SIDEBAR,
                 fg=TG_TEXT_DIM, anchor="w").grid(row=row, column=0, sticky="ew", pady=(4, 1))

    def _field_entry(self, parent, default, row):
        var = tk.StringVar(value=default)
        ent = tk.Entry(parent, textvariable=var,
                       font=(FONT_UI, 10), bg=TG_FIELD_BG, fg=TG_TEXT,
                       insertbackground=TG_ACCENT, relief="flat", bd=0,
                       highlightbackground=TG_FIELD_BD, highlightcolor=TG_ACCENT2,
                       highlightthickness=1)
        ent.grid(row=row, column=0, sticky="ew", ipady=6, pady=(0, 2))
        return ent, var

    def _build_server_section(self, parent):
        body = self._section_header(parent, "Server", "⚡", 0)
        self._field_label(body, "Cổng lắng nghe", 0)
        self.ent_port, _ = self._field_entry(body, "9999", 1)

        # Buttons row
        btn_row = tk.Frame(body, bg=TG_SIDEBAR)
        btn_row.grid(row=2, column=0, sticky="ew", pady=(6, 0))
        btn_row.columnconfigure(0, weight=1)

        self.btn_listen_canvas = tk.Canvas(btn_row, height=34, bg=TG_SIDEBAR, highlightthickness=0)
        self.btn_listen_canvas.grid(row=0, column=0, sticky="ew")
        self.btn_listen_canvas.bind("<Configure>", lambda e: self._draw_btn(
            self.btn_listen_canvas, self._srv_btn_text, self._srv_btn_color))
        self.btn_listen_canvas.bind("<ButtonPress-1>", lambda e: self._toggle_server())
        self.btn_listen_canvas.bind("<Enter>", lambda e: self._draw_btn(
            self.btn_listen_canvas, self._srv_btn_text, self._srv_btn_color, hover=True))
        self.btn_listen_canvas.bind("<Leave>", lambda e: self._draw_btn(
            self.btn_listen_canvas, self._srv_btn_text, self._srv_btn_color, hover=False))
        self._srv_btn_text = "▶  Bắt đầu nghe"
        self._srv_btn_color = TG_ACCENT

        self.lbl_srv = tk.Label(body, text="⭘  Chưa kích hoạt", font=(FONT_UI, 8),
                                bg=TG_SIDEBAR, fg=TG_TEXT_DIM, anchor="w")
        self.lbl_srv.grid(row=3, column=0, sticky="ew", pady=(4, 0))

    def _build_connect_section(self, parent):
        body = self._section_header(parent, "Kết nối đến", "🌐", 1)
        self._field_label(body, "IP máy đích", 0)
        self.ent_ip, _ = self._field_entry(body, self.local_ip, 1)
        self._field_label(body, "Cổng đích", 2)
        self.ent_tport, _ = self._field_entry(body, "9999", 3)

    def _build_key_section(self, parent):
        body = self._section_header(parent, "Khóa DES", "🔑", 2)
        self._field_label(body, "Khóa (đúng 8 ký tự)", 0)
        self.ent_key, _ = self._field_entry(body, "", 1)
        self.ent_key.bind("<KeyRelease>", self._key_changed)

        self.lbl_kcount = tk.Label(body, text="0 / 8", font=(FONT_UI, 8),
                                   bg=TG_SIDEBAR, fg=TG_TEXT_DIM, anchor="e")
        self.lbl_kcount.grid(row=2, column=0, sticky="ew")

        # Random key button
        rand_btn = tk.Label(body, text="🎲  Tạo ngẫu nhiên", font=(FONT_UI, 9, "bold"),
                            bg=TG_HOVER, fg=TG_ACCENT2, cursor="hand2", pady=6)
        rand_btn.grid(row=3, column=0, sticky="ew", pady=(6, 0))
        rand_btn.bind("<ButtonPress-1>", lambda e: self._rand_key())
        rand_btn.bind("<Enter>", lambda e: rand_btn.configure(bg=TG_SELECTED))
        rand_btn.bind("<Leave>", lambda e: rand_btn.configure(bg=TG_HOVER))

    def _build_save_folder_section(self, parent):
        body = self._section_header(parent, "Nơi lưu file", "💾", 3)
        self._field_label(body, "Thư mục lưu file nhận được", 0)
        
        # Frame cho folder display + browse button
        folder_row = tk.Frame(body, bg=TG_SIDEBAR)
        folder_row.grid(row=1, column=0, sticky="ew", pady=(0, 2))
        folder_row.columnconfigure(0, weight=1)
        
        # Display folder path (truncated if too long)
        self.lbl_folder = tk.Label(folder_row, text=self.receive_folder, 
                                   font=(FONT_UI, 8), bg=TG_FIELD_BG, fg=TG_TEXT,
                                   anchor="w", padx=8, pady=6, relief="flat")
        self.lbl_folder.grid(row=0, column=0, sticky="ew")
        
        # Browse button
        browse_btn = tk.Label(body, text="📂  Chọn thư mục", font=(FONT_UI, 9, "bold"),
                             bg=TG_HOVER, fg=TG_ACCENT2, cursor="hand2", pady=6)
        browse_btn.grid(row=2, column=0, sticky="ew", pady=(6, 0))
        browse_btn.bind("<ButtonPress-1>", lambda e: self._browse_save_folder())
        browse_btn.bind("<Enter>", lambda e: browse_btn.configure(bg=TG_SELECTED))
        browse_btn.bind("<Leave>", lambda e: browse_btn.configure(bg=TG_HOVER))

    def _browse_save_folder(self):
        """Mở dialog chọn thư mục lưu file"""
        from tkinter.filedialog import askdirectory
        folder = askdirectory(title="Chọn thư mục lưu file nhận được", initialdir=self.receive_folder)
        if folder:
            self.receive_folder = folder
            # Cập nhật label hiển thị
            display_path = folder if len(folder) <= 40 else "..." + folder[-37:]
            self.lbl_folder.config(text=display_path)
            self._log("SYSTEM", f"📂 Thư mục lưu: {folder}")

    def _draw_btn(self, canvas, text, color, hover=False):
        canvas.delete("all")
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w <= 1:
            return
        bg = self._lighten(color, 20) if hover else color
        r = 6
        self._rounded_rect(canvas, 1, 1, w-1, h-1, r, fill=bg, outline="")
        canvas.create_text(w//2, h//2, text=text, fill="white",
                           font=(FONT_UI, 9, "bold"))

    @staticmethod
    def _lighten(hexc, amt):
        try:
            rv = max(0, min(255, int(hexc[1:3], 16) + amt))
            gv = max(0, min(255, int(hexc[3:5], 16) + amt))
            bv = max(0, min(255, int(hexc[5:7], 16) + amt))
            return f"#{rv:02x}{gv:02x}{bv:02x}"
        except Exception:
            return hexc

    @staticmethod
    def _rounded_rect(canvas, x1, y1, x2, y2, r, **kw):
        canvas.create_arc(x1, y1, x1+2*r, y1+2*r, start=90, extent=90, style="pieslice", **kw)
        canvas.create_arc(x2-2*r, y1, x2, y1+2*r, start=0, extent=90, style="pieslice", **kw)
        canvas.create_arc(x1, y2-2*r, x1+2*r, y2, start=180, extent=90, style="pieslice", **kw)
        canvas.create_arc(x2-2*r, y2-2*r, x2, y2, start=270, extent=90, style="pieslice", **kw)
        canvas.create_rectangle(x1+r, y1, x2-r, y2, **kw)
        canvas.create_rectangle(x1, y1+r, x2, y2-r, **kw)

    # ─── CHAT AREA ───────────────────────────────────────
    def _build_chat_area(self):
        chat_wrapper = tk.Frame(self.root, bg=TG_BG)
        chat_wrapper.grid(row=0, column=1, sticky="nsew")
        chat_wrapper.rowconfigure(1, weight=1)
        chat_wrapper.columnconfigure(0, weight=1)

        # TOP BAR
        self._build_topbar(chat_wrapper)
        # MESSAGE FRAME
        self._build_messages(chat_wrapper)
        # INPUT BAR
        self._build_inputbar(chat_wrapper)
        # LOG PANEL (collapsible at bottom)
        self._build_log_panel(chat_wrapper)

    def _build_topbar(self, parent):
        topbar = tk.Frame(parent, bg=TG_TOPBAR, pady=0)
        topbar.grid(row=0, column=0, sticky="ew")

        # Thin accent line on top
        accent_line = tk.Frame(topbar, bg=TG_ACCENT, height=2)
        accent_line.pack(fill="x", side="top")

        inner = tk.Frame(topbar, bg=TG_TOPBAR, pady=8, padx=14)
        inner.pack(fill="x")
        inner.columnconfigure(2, weight=1)

        # Avatar circle (canvas)
        av = tk.Canvas(inner, width=38, height=38, bg=TG_TOPBAR, highlightthickness=0)
        av.grid(row=0, column=0, rowspan=2)
        av.create_oval(2, 2, 36, 36, fill=TG_ACCENT, outline="")
        av.create_text(20, 20, text="D", fill="white", font=(FONT_UI, 14, "bold"))

        # Online dot
        av.create_oval(26, 26, 36, 36, fill=TG_BG, outline="")
        self.online_dot = tk.Canvas(inner, width=12, height=12, bg=TG_TOPBAR, highlightthickness=0)
        self.online_dot.grid(row=0, column=1, sticky="sw", padx=2, pady=(0,2))
        self.online_dot.create_oval(1, 1, 11, 11, fill=TG_TEXT_DIM, outline="")

        # Name & subtitle
        info = tk.Frame(inner, bg=TG_TOPBAR)
        info.grid(row=0, column=2, sticky="ew", padx=(10, 0))
        tk.Label(info, text="DES Secure Channel", font=(FONT_UI, 12, "bold"),
                 bg=TG_TOPBAR, fg=TG_TEXT, anchor="w").pack(anchor="w")
        self.lbl_sub = tk.Label(info, text="Mã hóa đầu cuối  •  Đề tài nhóm 27",
                                font=(FONT_UI, 8), bg=TG_TOPBAR, fg=TG_TEXT_DIM, anchor="w")
        self.lbl_sub.pack(anchor="w")

        # Action buttons (right)
        btn_frame = tk.Frame(inner, bg=TG_TOPBAR)
        btn_frame.grid(row=0, column=3, sticky="e", padx=(8, 0))

        IconButton(btn_frame, "📋", command=self._toggle_log,
                   bg=TG_TOPBAR, tooltip="Nhật ký chi tiết").pack(side="left", padx=2)
        IconButton(btn_frame, "🗑", command=self._clear_chat,
                   bg=TG_TOPBAR, fg=TG_TEXT_DIM, hover_fg=TG_ERROR, tooltip="Xóa chat").pack(side="left", padx=2)

        # Thin divider line
        tk.Frame(topbar, bg=TG_DIVIDER, height=1).pack(fill="x")

    def _build_messages(self, parent):
        """Scrollable chat message area."""
        msg_frame = tk.Frame(parent, bg=TG_BG)
        msg_frame.grid(row=1, column=0, sticky="nsew")
        msg_frame.rowconfigure(0, weight=1)
        msg_frame.columnconfigure(0, weight=1)

        # Canvas + scrollbar for message bubbles
        self.msg_canvas = tk.Canvas(msg_frame, bg=TG_BG, highlightthickness=0,
                                    yscrollcommand=lambda *a: self.msg_scrollbar.set(*a))
        self.msg_scrollbar = tk.Scrollbar(msg_frame, orient="vertical",
                                          command=self.msg_canvas.yview)
        self.msg_scrollbar.grid(row=0, column=1, sticky="ns")
        self.msg_canvas.grid(row=0, column=0, sticky="nsew")

        # Inner frame holding all bubbles
        self.bubbles_frame = tk.Frame(self.msg_canvas, bg=TG_BG)
        self.bubbles_win = self.msg_canvas.create_window(
            (0, 0), window=self.bubbles_frame, anchor="nw", tags="bwin")

        self.bubbles_frame.bind("<Configure>", self._on_bubbles_configure)
        self.msg_canvas.bind("<Configure>", self._on_canvas_configure)

        # Mouse wheel
        self.msg_canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.bubbles_frame.bind("<MouseWheel>", self._on_mousewheel)

    def _on_bubbles_configure(self, e):
        self.msg_canvas.configure(scrollregion=self.msg_canvas.bbox("all"))

    def _on_canvas_configure(self, e):
        self.msg_canvas.itemconfigure("bwin", width=e.width)

    def _on_mousewheel(self, e):
        self.msg_canvas.yview_scroll(int(-1 * (e.delta / 120)), "units")

    def _build_inputbar(self, parent):
        """Telegram-style input bar with drag-drop support."""
        bar = tk.Frame(parent, bg=TG_INPUT_BG, pady=10, padx=12)
        bar.grid(row=2, column=0, sticky="ew")
        bar.columnconfigure(1, weight=1)

        # Accent top border (thicker, more visible)
        tk.Frame(bar, bg=TG_ACCENT, height=1).grid(row=0, column=0, columnspan=3, sticky="ew", pady=(0, 10))

        # File button
        IconButton(bar, "📁", command=self._choose_file, bg=TG_INPUT_BG, size=16, fg=TG_TEXT_DIM,
                   hover_fg=TG_ACCENT2, tooltip="Chọn file (Ctrl để chọn nhiều)").grid(row=1, column=0, padx=(0, 4))

        # Emoji / attach button
        IconButton(bar, "😊", bg=TG_INPUT_BG, size=16, fg=TG_TEXT_DIM,
                   hover_fg=TG_ACCENT2, tooltip="Emoji").grid(row=1, column=0, padx=(35, 8))

        # Text input — with visible border
        txt_frame = tk.Frame(bar, bg=TG_FIELD_BG, pady=2,
                             highlightbackground=TG_FIELD_BD, highlightthickness=1)
        txt_frame.grid(row=1, column=1, sticky="ew")
        txt_frame.columnconfigure(0, weight=1)

        self.txt_msg = tk.Text(txt_frame, font=(FONT_UI, 11), bg=TG_FIELD_BG, fg=TG_TEXT,
                               insertbackground=TG_ACCENT2, relief="flat", height=1,
                               wrap="word", bd=6, highlightthickness=0, maxundo=50)
        self.txt_msg.grid(row=0, column=0, sticky="ew")
        self.txt_msg.bind("<KeyRelease>", self._on_msg_keyrelease)
        self.txt_msg.bind("<Control-Return>", lambda e: self._on_send())
        self.txt_msg.bind("<Return>", self._on_return_key)

        # Placeholder
        self._placeholder_visible = True
        self._set_placeholder()
        self.txt_msg.bind("<FocusIn>",  self._on_focus_in)
        self.txt_msg.bind("<FocusOut>", self._on_focus_out)

        # Send button
        self.send_btn = SendButton(bar, command=self._on_send, size=42)
        self.send_btn.grid(row=1, column=2, padx=(10, 0))

        # Hint text + File info
        hint_row = tk.Frame(bar, bg=TG_INPUT_BG)
        hint_row.grid(row=2, column=0, columnspan=3, sticky="ew", pady=(4, 0))
        hint_row.columnconfigure(1, weight=1)
        
        tk.Label(hint_row, text="↵ Enter gửi  •  Shift+Enter xuống dòng",
                 font=(FONT_UI, 8), bg=TG_INPUT_BG, fg=TG_TEXT_DIM
                 ).grid(row=0, column=0, sticky="w")
        
        self.lbl_file = tk.Label(hint_row, text="", font=(FONT_UI, 8),
                                 bg=TG_INPUT_BG, fg=TG_ACCENT, anchor="e")
        self.lbl_file.grid(row=0, column=1, sticky="ew")

        # File list display with delete buttons
        self.files_list_frame = tk.Frame(bar, bg=TG_INPUT_BG, pady=0)
        self.files_list_frame.grid(row=3, column=0, columnspan=3, sticky="ew")

    def _set_placeholder(self):
        self.txt_msg.delete("1.0", "end")
        self.txt_msg.insert("1.0", "Nhập tin nhắn...")
        self.txt_msg.configure(fg="#5A7A90")
        self._placeholder_visible = True

    def _on_focus_in(self, e):
        if self._placeholder_visible:
            self.txt_msg.delete("1.0", "end")
            self.txt_msg.configure(fg=TG_TEXT)
            self._placeholder_visible = False

    def _on_focus_out(self, e):
        content = self.txt_msg.get("1.0", "end").strip()
        if not content:
            self._set_placeholder()

    def _on_msg_keyrelease(self, e):
        # Auto-resize (max 5 lines)
        lines = int(self.txt_msg.index("end-1c").split(".")[0])
        self.txt_msg.configure(height=min(max(lines, 1), 5))

    def _on_return_key(self, e):
        if not (e.state & 0x1):  # no Shift held
            self._on_send()
            return "break"

    def _clear_selected_files(self):
        """Clear selected files list"""
        self.selected_files = []
        self._update_file_list_display()

    def _remove_file(self, file_path):
        """Remove a specific file from the selected files list"""
        if file_path in self.selected_files:
            self.selected_files.remove(file_path)
            self._update_file_list_display()
            file_name = os.path.basename(file_path)
            self._log("INFO", f"Đã xóa file: {file_name}")

    def _build_log_panel(self, parent):
        """Collapsible activity log panel at bottom."""
        self.log_panel = tk.Frame(parent, bg=TG_SIDEBAR, height=0)
        self.log_panel.grid(row=3, column=0, sticky="ew")
        self.log_panel.grid_remove()  # hidden by default

        header = tk.Frame(self.log_panel, bg="#0D1822", pady=4, padx=10)
        header.pack(fill="x")
        tk.Label(header, text="📋  NHẬT KÝ HOẠT ĐỘNG", font=(FONT_UI, 9, "bold"),
                 bg="#0D1822", fg=TG_ACCENT).pack(side="left")
        self.lbl_cnt = tk.Label(header, text="📤 0  📥 0", font=(FONT_UI, 9),
                                bg="#0D1822", fg=TG_TEXT_DIM)
        self.lbl_cnt.pack(side="left", padx=10)
        close_lbl = tk.Label(header, text="✕", font=(FONT_UI, 11), bg="#0D1822",
                              fg=TG_TEXT_DIM, cursor="hand2")
        close_lbl.pack(side="right")
        close_lbl.bind("<ButtonPress-1>", lambda e: self._toggle_log())

        self.log = scrolledtext.ScrolledText(
            self.log_panel, font=("Consolas", 9), bg="#0E1621", fg=TG_TEXT,
            relief="flat", state="disabled", wrap="word", bd=6, height=8)
        self.log.pack(fill="both", expand=True)

        self.log.tag_configure("SEND",  foreground="#5288C1", font=("Consolas", 9, "bold"))
        self.log.tag_configure("RECV",  foreground="#4CAF50", font=("Consolas", 9, "bold"))
        self.log.tag_configure("ERROR", foreground=TG_ERROR,  font=("Consolas", 9, "bold"))
        self.log.tag_configure("INFO",  foreground=TG_TEXT_DIM)
        self.log.tag_configure("HEX",   foreground="#FFB300")
        self.log.tag_configure("TIME",  foreground=TG_ACCENT)
        self.log.tag_configure("SEP",   foreground=TG_DIVIDER)
        self.log.tag_configure("VAL",   foreground=TG_TEXT, font=("Consolas", 9, "bold"))

    # ────────────────────────────────────────────────────
    #  BUBBLE MESSAGES
    # ────────────────────────────────────────────────────
    def _add_bubble(self, text, direction, timestamp=None, details=None, cipher=None):
        """direction: 'sent' | 'received' | 'system'"""
        ts = timestamp or time.strftime("%H:%M")
        parent = self.bubbles_frame

        if direction == "system":
            # System message – centered
            row = tk.Frame(parent, bg=TG_BG, pady=4)
            row.pack(fill="x", padx=20)
            lbl = tk.Label(row, text=text, font=(FONT_UI, 8),
                           bg="#1A2B3C", fg=TG_TEXT_DIM, padx=10, pady=3)
            lbl.pack()
            return

        row = tk.Frame(parent, bg=TG_BG, pady=3)
        row.pack(fill="x", padx=12)

        is_sent = direction == "sent"

        # Bubble container
        bubble_outer = tk.Frame(row, bg=TG_BG)
        if is_sent:
            bubble_outer.pack(side="right", anchor="e")
        else:
            bubble_outer.pack(side="left", anchor="w")

        # Draw bubble using Canvas for rounded corner look
        bubble_color = TG_MSG_SENT if is_sent else TG_MSG_RECV
        label_fg     = TG_TEXT

        # Frame holds the text + time
        content = tk.Frame(bubble_outer, bg=bubble_color, padx=12, pady=6)
        content.pack()

        if details:
            # Show encrypted details (collapsible)
            tag = tk.Label(content, text="🔒 Đã mã hóa DES",
                           font=(FONT_UI, 8, "italic"), bg=bubble_color,
                           fg=TG_TEXT_DIM, anchor="w")
            tag.pack(anchor="w")

        msg_lbl = tk.Label(content, text=text, font=(FONT_UI, 11),
                           bg=bubble_color, fg=label_fg, wraplength=320,
                           justify="left" if not is_sent else "left", anchor="w")
        msg_lbl.pack(anchor="w")
        msg_lbl.bind("<Configure>", lambda e, l=msg_lbl: l.configure(
            wraplength=max(80, min(320, e.width - 10))))

        # Nút "Xem mã" nếu có cipher
        if cipher and is_sent:
            btn_row = tk.Frame(content, bg=bubble_color)
            btn_row.pack(anchor="w", pady=(4, 0))
            cipher_btn = tk.Label(btn_row, text="🔍 Xem mã", font=(FONT_UI, 8, "bold"),
                                 bg=bubble_color, fg=TG_ACCENT2, cursor="hand2", padx=2, pady=1)
            cipher_btn.pack()
            cipher_btn.bind("<ButtonPress-1>", lambda e, c=cipher: self._show_cipher_popup(c))

        time_row = tk.Frame(content, bg=bubble_color)
        time_row.pack(fill="x")
        tk.Label(time_row, text=ts, font=(FONT_UI, 7),
                 bg=bubble_color, fg=TG_TEXT_DIM).pack(side="right")
        if is_sent:
            # Double checkmarks
            tk.Label(time_row, text="✓✓", font=(FONT_UI, 7),
                     bg=bubble_color, fg=TG_ACCENT2).pack(side="right", padx=(0, 3))

        self._scroll_to_bottom()

    def _scroll_to_bottom(self):
        self.root.after(50, lambda: self.msg_canvas.yview_moveto(1.0))

    def _sys_msg(self, text):
        self._add_bubble(text, "system")

    # ────────────────────────────────────────────────────
    #  FILE OPERATIONS
    # ────────────────────────────────────────────────────
    def _choose_file(self):
        """Browse and select multiple files to send"""
        files = filedialog.askopenfilenames(
            title="Chọn file để gửi (có thể chọn nhiều file)",
            filetypes=[
                ("All files", "*.*"),
                ("Text", "*.txt *.md *.csv *.log"),
                ("Images", "*.png *.jpg *.jpeg *.gif *.bmp *.tiff *.webp *.ico"),
                ("Audio", "*.mp3 *.wav *.flac *.aac *.ogg *.m4a *.wma"),
                ("Video", "*.mp4 *.avi *.mkv *.mov *.flv *.wmv *.webm *.m4v"),
                ("Documents", "*.pdf *.doc *.docx *.xls *.xlsx *.ppt *.pptx *.odt *.rtf"),
                ("Archives", "*.zip *.rar *.7z *.tar *.gz *.bz2"),
                ("Executables", "*.exe *.dll *.so *.sh *.bat"),
            ]
        )
        if files:
            self.selected_files.extend(files)  # Thêm vào danh sách
            self._update_file_list_display()
            self._log("INFO", f"Đã chọn {len(files)} file")

    def _update_file_list_display(self):
        """Update the file list label and display"""
        # Update summary label
        if not self.selected_files:
            self.lbl_file.configure(text="")
            self._render_files_list()
            return
        
        total_size = sum(os.path.getsize(f) for f in self.selected_files if os.path.isfile(f))
        if len(self.selected_files) == 1:
            file_name = os.path.basename(self.selected_files[0])
            self.lbl_file.configure(text=f"📦 {file_name} ({total_size} bytes)")
        else:
            self.lbl_file.configure(text=f"📦 {len(self.selected_files)} files ({total_size} bytes)")
        
        # Render files list with delete buttons
        self._render_files_list()

    def _render_files_list(self):
        """Render the list of selected files with delete buttons"""
        # Clear existing widgets
        for widget in self.files_list_frame.winfo_children():
            widget.destroy()
        
        if not self.selected_files:
            return
        
        # Add each file with a delete button
        for idx, file_path in enumerate(self.selected_files):
            if not os.path.isfile(file_path):
                continue
            
            file_name = os.path.basename(file_path)
            file_size = os.path.getsize(file_path)
            
            # File row
            file_row = tk.Frame(self.files_list_frame, bg=TG_INPUT_BG)
            file_row.pack(fill="x", padx=10, pady=2)
            file_row.columnconfigure(0, weight=1)
            
            # File info
            file_info = tk.Label(file_row, text=f"📄 {file_name} ({file_size} bytes)",
                                font=(FONT_UI, 8), bg=TG_INPUT_BG, fg=TG_TEXT_DIM, anchor="w")
            file_info.grid(row=0, column=0, sticky="ew")
            
            # Delete button (X)
            del_btn = tk.Label(file_row, text="✕", font=(FONT_UI, 9, "bold"),
                              bg=TG_INPUT_BG, fg=TG_ERROR, cursor="hand2")
            del_btn.grid(row=0, column=1, padx=(5, 0))
            del_btn.bind("<ButtonPress-1>", lambda e, f=file_path: self._remove_file(f))
            del_btn.bind("<Enter>", lambda e, l=del_btn: l.configure(fg="#FF7070"))
            del_btn.bind("<Leave>", lambda e, l=del_btn: l.configure(fg=TG_ERROR))
    
    # ────────────────────────────────────────────────────
    #  TOGGLE LOG / CLEAR
    # ────────────────────────────────────────────────────
    def _toggle_log(self):
        self._log_visible = not self._log_visible
        if self._log_visible:
            self.log_panel.grid()
        else:
            self.log_panel.grid_remove()

    def _clear_chat(self):
        for w in self.bubbles_frame.winfo_children():
            w.destroy()
        self.msg_count_sent = 0
        self.msg_count_recv = 0
        self._update_cnt()
        self._sys_msg(f"💬 Chat đã được xóa  •  {time.strftime('%H:%M')}")

    # ────────────────────────────────────────────────────
    #  STATUS HELPERS
    # ────────────────────────────────────────────────────
    def _set_status(self, text, color=TG_GREEN):
        self.dot_status.configure(fg=color)
        self.lbl_status.configure(text=text)
        # also update online dot in topbar
        self.online_dot.delete("all")
        self.online_dot.create_oval(1, 1, 11, 11, fill=color, outline="")

    def _update_cnt(self):
        self.lbl_cnt.configure(text=f"📤 {self.msg_count_sent}  📥 {self.msg_count_recv}")

    def _key_changed(self, e=None):
        n = len(self.ent_key.get())
        if n == 8:
            self.lbl_kcount.configure(text="✓ 8/8", fg=TG_GREEN)
        elif n > 8:
            self.lbl_kcount.configure(text=f"✗ {n}/8 (quá)", fg=TG_ERROR)
        else:
            self.lbl_kcount.configure(text=f"{n} / 8", fg=TG_TEXT_DIM)

    # ────────────────────────────────────────────────────
    #  LOG HELPERS
    # ────────────────────────────────────────────────────
    def _log(self, tag, msg):
        def _w():
            self.log.configure(state="normal")
            ts = time.strftime("%H:%M:%S")
            prefix = {"SEND": "[GỬI]", "RECV": "[NHẬN]",
                      "ERROR": "[LỖI]", "INFO": "[INFO]"}.get(tag, "[INFO]")
            self.log.insert("end", f" [{ts}] {prefix}  {msg}\n", tag)
            self.log.configure(state="disabled")
            self.log.see("end")
        self.root.after(0, _w)

    def _log_detail(self, tag, label, value):
        def _w():
            self.log.configure(state="normal")
            ts = time.strftime("%H:%M:%S")
            prefix = {"SEND": "[GỬI]", "RECV": "[NHẬN]"}.get(tag, "[INFO]")
            self.log.insert("end", f" [{ts}] {prefix}  {label}: ", tag)
            vtag = "HEX" if "hex" in label.lower() else (
                "TIME" if "thời gian" in label.lower() else "VAL")
            self.log.insert("end", f"{value}\n", vtag)
            self.log.configure(state="disabled")
            self.log.see("end")
        self.root.after(0, _w)

    def _log_sep(self):
        def _w():
            self.log.configure(state="normal")
            self.log.insert("end", f" {'─' * 45}\n", "SEP")
            self.log.configure(state="disabled")
        self.root.after(0, _w)

    def _format_cipher_display(self, cipher_hex, chars_per_line=64):
        """Format mã hóa hex thành dạng dễ đọc (64 ký tự/dòng + dòng số)"""
        lines = []
        total = len(cipher_hex)
        for i in range(0, total, chars_per_line):
            line = cipher_hex[i:i+chars_per_line]
            line_num = (i // chars_per_line) + 1
            lines.append(f"[{line_num:04d}] {line}")
        return "\n".join(lines)

    def _log_cipher(self, tag, label, cipher_hex):
        """Log mã hóa với format đẹp - hiển thị từng dòng ngắn"""
        def _w():
            self.log.configure(state="normal")
            ts = time.strftime("%H:%M:%S")
            prefix = {"SEND": "[GỬI]", "RECV": "[NHẬN]"}.get(tag, "[INFO]")
            
            # Header
            self.log.insert("end", f" [{ts}] {prefix}  {label}:\n", tag)
            
            # Format cipher thành từng dòng 64 ký tự
            formatted = self._format_cipher_display(cipher_hex, 64)
            for line in formatted.split('\n'):
                self.log.insert("end", f"   {line}\n", "HEX")
            
            # Footer - stats
            self.log.insert("end", f"   ➜ Tổng: {len(cipher_hex)} ký tự ({len(cipher_hex)//2} bytes)\n", "VAL")
            
            self.log.configure(state="disabled")
            self.log.see("end")
        self.root.after(0, _w)

    def _show_cipher_popup(self, cipher_hex):
        """Hiển thị popup với mã hóa đầy đủ, có thể copy"""
        popup = tk.Toplevel(self.root)
        popup.title("🔐 Xem Mã Hóa DES")
        popup.configure(bg=TG_BG)
        popup.geometry("750x600")
        popup.resizable(True, True)
        
        # Header
        header = tk.Frame(popup, bg=TG_TOPBAR, pady=10, padx=14)
        header.pack(fill="x")
        header.columnconfigure(1, weight=1)
        
        tk.Label(header, text="🔐 Dữ liệu Mã Hóa (HEX)", font=(FONT_UI, 12, "bold"),
                bg=TG_TOPBAR, fg=TG_TEXT).grid(row=0, column=0, columnspan=2, sticky="w")
        tk.Label(header, text=f"Kích thước: {len(cipher_hex)} ký tự ({len(cipher_hex)//2} bytes)", 
                font=(FONT_UI, 9), bg=TG_TOPBAR, fg=TG_TEXT_DIM).grid(row=1, column=0, sticky="w")
        
        # Copy button
        def copy_all():
            popup.clipboard_clear()
            popup.clipboard_append(cipher_hex)
            messagebox.showinfo("✓ Sao chép", "Đã sao chép mã hóa vào clipboard!")
        
        tk.Button(header, text="📋 Sao chép tất cả", font=(FONT_UI, 9),
                 bg=TG_ACCENT, fg="white", command=copy_all, relief="flat", bd=0, padx=10, pady=5
                 ).grid(row=1, column=1, sticky="e")
        
        # Text widget with scroll
        text_frame = tk.Frame(popup, bg=TG_BG)
        text_frame.pack(fill="both", expand=True, padx=10, pady=10)
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(0, weight=1)
        
        scrollbar = tk.Scrollbar(text_frame)
        scrollbar.grid(row=0, column=1, sticky="ns")
        
        text_widget = tk.Text(text_frame, font=("Courier New", 10), bg=TG_FIELD_BG, fg=TG_TEXT,
                             yscrollcommand=scrollbar.set, relief="flat", bd=2,
                             wrap="word", padx=8, pady=8)
        text_widget.grid(row=0, column=0, sticky="nsew")
        scrollbar.config(command=text_widget.yview)
        
        # Format cipher - 64 ký tự/dòng
        formatted = self._format_cipher_display(cipher_hex, 64)
        text_widget.insert("1.0", formatted)
        text_widget.config(state="disabled")
        
        # Footer with stats
        footer = tk.Frame(popup, bg=TG_TOPBAR, pady=8, padx=14)
        footer.pack(fill="x")
        
        stats = f"📊 {len(cipher_hex)} ký tự | {len(cipher_hex)//2} bytes | {len(cipher_hex)//4} dòng"
        tk.Label(footer, text=stats, font=(FONT_UI, 8),
                bg=TG_TOPBAR, fg=TG_TEXT_DIM).pack(side="left")

    def _check_file_magic(self, file_bytes, file_name):
        """Kiểm tra magic bytes để xác thực loại & tính toàn vẹn tệp"""
        if not file_bytes or len(file_bytes) < 4:
            return "⚠ Tệp quá nhỏ (<4 bytes)"
        
        # Từ điển magic bytes cho các định dạng thông dụng
        magic_signatures = {
            b'\xD0\xCF\x11\xE0': "📊 XLS/DOC (OLE Compound)",
            b'\x89PNG\r\n\x1a\n': "🖼️ PNG",
            b'\xFF\xD8\xFF': "📸 JPEG",
            b'GIF8': "🎬 GIF",
            b'PK\x03\x04': "📦 ZIP/DOCX/XLSX",
            b'%PDF': "📄 PDF",
            b'\x7FELF': "⚙️ ELF Binary",
        }
        
        first_bytes = file_bytes[:8]
        hex_start = first_bytes.hex().upper()
        
        # Kiểm tra từng magic signature
        for magic, desc in magic_signatures.items():
            if first_bytes.startswith(magic):
                return f"✓ {desc} (magic OK: {hex_start[:len(magic)*2]})"
        
        # Nếu không match, trả về cảnh báo với hex đầu
        return f"⚠ Unknown filetype - magic: {hex_start[:16]}... (có thể bị hỏng)"

    def _export_cipher_archive(self, file_name, file_size, total_chunks, cipher_chunks_dict, key_used):
        """Export mã hóa từng chunk vào file .cipher"""
        try:
            # Tạo file name
            name_parts = file_name.rsplit('.', 1)
            if len(name_parts) == 2:
                cipher_file = f"{name_parts[0]}.cipher"
            else:
                cipher_file = f"{file_name}.cipher"
            
            ts = time.strftime("%Y-%m-%d %H:%M:%S")
            
            with open(cipher_file, 'w', encoding='utf-8') as f:
                # Header
                f.write("=" * 70 + "\n")
                f.write("🔐 DES ENCRYPTED FILE ARCHIVE\n")
                f.write("=" * 70 + "\n\n")
                
                # Metadata
                f.write(f"📄 Original File: {file_name}\n")
                f.write(f"📊 File Size: {file_size} bytes\n")
                f.write(f"🧩 Total Chunks: {total_chunks}\n")
                f.write(f"🔑 Key SHA256: {hashlib.sha256(key_used.encode()).hexdigest()[:16]}...\n")
                f.write(f"⏰ Exported: {ts}\n")
                f.write(f"💻 App: DES Secure Messenger (Group 27)\n")
                f.write("\n" + "=" * 70 + "\n\n")
                
                # Cipher data
                total_cipher_len = 0
                for chunk_num in range(1, total_chunks + 1):
                    if chunk_num in cipher_chunks_dict:
                        cipher = cipher_chunks_dict[chunk_num]
                        total_cipher_len += len(cipher)
                        
                        f.write(f"[Chunk {chunk_num}/{total_chunks}] ({len(cipher)} ký tự, {len(cipher)//2} bytes)\n")
                        f.write("─" * 70 + "\n")
                        
                        # Format 64 ký tự/dòng
                        for i in range(0, len(cipher), 64):
                            line = cipher[i:i+64]
                            line_num = (i // 64) + 1
                            f.write(f"[{line_num:04d}] {line}\n")
                        
                        f.write("\n")
                
                # Footer
                f.write("=" * 70 + "\n")
                f.write(f"📈 STATISTICS\n")
                f.write("=" * 70 + "\n")
                f.write(f"Total Cipher Text: {total_cipher_len} characters ({total_cipher_len//2} bytes)\n")
                f.write(f"Compression: Original {file_size} → Encrypted {total_cipher_len//2} bytes\n")
                f.write(f"Average per Chunk: {total_cipher_len//total_chunks} chars\n")
                f.write(f"\n✅ Export completed at {ts}\n")
            
            return cipher_file
        except Exception as e:
            self._log("ERROR", f"Export cipher file failed: {e}")
            return None

    def _save_encrypted_file_on_receive(self, file_name, file_size, total_chunks, cipher_chunks_dict, key_used, save_folder):
        """Lưu file mã hóa nhận được vào thư mục nhận, cùng chỗ với file đã giải mã"""
        try:
            # Tạo file name cho file mã hóa
            name_parts = file_name.rsplit('.', 1)
            if len(name_parts) == 2:
                cipher_file_name = f"{name_parts[0]}.cipher"
            else:
                cipher_file_name = f"{file_name}.cipher"
            
            cipher_file_path = os.path.join(save_folder, cipher_file_name)
            ts = time.strftime("%Y-%m-%d %H:%M:%S")
            
            with open(cipher_file_path, 'w', encoding='utf-8') as f:
                # Header
                f.write("=" * 70 + "\n")
                f.write("🔐 DES ENCRYPTED FILE ARCHIVE\n")
                f.write("=" * 70 + "\n\n")
                
                # Metadata
                f.write(f"📄 Original File: {file_name}\n")
                f.write(f"📊 File Size: {file_size} bytes\n")
                f.write(f"🧩 Total Chunks: {total_chunks}\n")
                f.write(f"🔑 Key SHA256: {hashlib.sha256(key_used.encode()).hexdigest()[:16]}...\n")
                f.write(f"⏰ Received: {ts}\n")
                f.write(f"💻 App: DES Secure Messenger (Group 27)\n")
                f.write("\n" + "=" * 70 + "\n\n")
                
                # Cipher data
                total_cipher_len = 0
                for chunk_num in range(1, total_chunks + 1):
                    if chunk_num in cipher_chunks_dict:
                        cipher = cipher_chunks_dict[chunk_num]
                        total_cipher_len += len(cipher)
                        
                        f.write(f"[Chunk {chunk_num}/{total_chunks}] ({len(cipher)} ký tự, {len(cipher)//2} bytes)\n")
                        f.write("─" * 70 + "\n")
                        
                        # Format 64 ký tự/dòng
                        for i in range(0, len(cipher), 64):
                            line = cipher[i:i+64]
                            line_num = (i // 64) + 1
                            f.write(f"[{line_num:04d}] {line}\n")
                        
                        f.write("\n")
                
                # Footer
                f.write("=" * 70 + "\n")
                f.write(f"📈 STATISTICS\n")
                f.write("=" * 70 + "\n")
                f.write(f"Total Cipher Text: {total_cipher_len} characters ({total_cipher_len//2} bytes)\n")
                f.write(f"Compression: Original {file_size} → Encrypted {total_cipher_len//2} bytes\n")
                f.write(f"Average per Chunk: {total_cipher_len//total_chunks} chars\n")
                f.write(f"\n✅ Saved at {ts}\n")
            
            self._log("INFO", f"💾 Encrypted file saved: {cipher_file_path}")
            return cipher_file_path
        except Exception as e:
            self._log("ERROR", f"Save encrypted file failed: {e}")
            return None

    # ────────────────────────────────────────────────────
    #  KEY UTILS
    # ────────────────────────────────────────────────────
    def _rand_key(self):
        chars = string.ascii_letters + string.digits
        key = "".join(random.choice(chars) for _ in range(8))
        self.ent_key.delete(0, "end")
        self.ent_key.insert(0, key)
        self._key_changed()
        self._log("INFO", f"Đã tạo khóa ngẫu nhiên: {key}")

    def _play_sound(self):
        if HAS_SOUND:
            try:
                winsound.MessageBeep(winsound.MB_OK)
            except Exception:
                pass

    # ────────────────────────────────────────────────────
    #  SERVER
    # ────────────────────────────────────────────────────
    def _toggle_server(self):
        if not self.server_running:
            self._start_server()
        else:
            self._stop_server()

    def _start_server(self):
        port_s = self.ent_port.get().strip()
        if not port_s.isdigit():
            messagebox.showerror("Lỗi", "Cổng phải là số nguyên.")
            return
        port = int(port_s)
        try:
            self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            self.server_socket.bind(("0.0.0.0", port))
            self.server_socket.listen(5)
            self.server_socket.settimeout(1.0)
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể mở cổng {port}:\n{e}")
            return

        self.server_running = True
        self._srv_btn_text  = "⏹  Dừng nghe"
        self._srv_btn_color = TG_ERROR
        self._draw_btn(self.btn_listen_canvas, self._srv_btn_text, self._srv_btn_color)
        self.lbl_srv.configure(text=f"● Đang nghe cổng {port}", fg=TG_GREEN)
        self.ent_port.configure(state="disabled")
        self._set_status(f"Nghe cổng {port}", TG_GREEN)
        self._sys_msg(f"🟢 Server bắt đầu nghe  •  Cổng {port}")
        self._log("INFO", f"Server bắt đầu nghe trên cổng {port}")

        self.server_thread = threading.Thread(target=self._server_loop, daemon=True)
        self.server_thread.start()

    def _stop_server(self):
        self.server_running = False
        if self.server_socket:
            try:
                self.server_socket.close()
            except Exception:
                pass
            self.server_socket = None
        self._srv_btn_text  = "▶  Bắt đầu nghe"
        self._srv_btn_color = TG_ACCENT
        self._draw_btn(self.btn_listen_canvas, self._srv_btn_text, self._srv_btn_color)
        self.lbl_srv.configure(text="⭘  Chưa kích hoạt", fg=TG_TEXT_DIM)
        self.ent_port.configure(state="normal")
        self._set_status("Server đã dừng", TG_TEXT_DIM)
        self._sys_msg("🔴 Server đã dừng")
        self._log("INFO", "Server đã dừng")

    def _server_loop(self):
        while self.server_running:
            try:
                conn, addr = self.server_socket.accept()
                threading.Thread(target=self._handle_client,
                                 args=(conn, addr), daemon=True).start()
            except socket.timeout:
                continue
            except Exception:
                break

    def _handle_client(self, conn, addr):
        try:
            # Đọc từng message tuần tự + gửi ACK
            conn.settimeout(30)
            
            while True:
                try:
                    # Đọc từng byte tới \n
                    data = b""
                    while True:
                        chunk = conn.recv(1)
                        if not chunk:
                            return
                        data += chunk
                        if data.endswith(b'\n'):
                            break
                    
                    raw = data.decode("utf-8", errors="replace").strip()
                    if not raw:
                        break
                    
                    self._log_sep()
                    self._log("RECV", f"Từ {addr[0]} ({len(raw)} ký tự)")
                    
                    recv_key = self.ent_key.get().strip()
                    if len(recv_key) != 8:
                        self._log("ERROR", f"Khóa lỗi ({len(recv_key)} ký tự)")
                        conn.sendall(b"NACK|KEY|Bad key\n")
                        continue
                    
                    parts = raw.split("|", 6)
                    if len(parts) < 2:
                        self._log("ERROR", f"Format lỗi")
                        conn.sendall(b"NACK|FORMAT|Bad format\n")
                        continue
                    
                    msg_type = parts[0]
                    
                    # === FILE PROTOCOL ===
                    if msg_type == "FILE" and len(parts) == 7:
                        file_name, file_size_str, total_chunks_str, chunk_num_str, chunk_hash, cipher_chunk = parts[1:7]
                        try:
                            file_size = int(file_size_str)
                            total_chunks = int(total_chunks_str)
                            chunk_num = int(chunk_num_str)
                            
                            self._log_detail("RECV", "File", f"{file_name} [{chunk_num}/{total_chunks}]")
                            
                            if file_name not in self.pending_files:
                                self.pending_files[file_name] = {
                                    'chunks': {},
                                    'file_size': file_size,
                                    'total_chunks': total_chunks
                                }
                            
                            self.pending_files[file_name]['chunks'][chunk_num] = cipher_chunk
                            
                            # ✓ GỬIACK NGAY CHO CHUNK NÀY
                            conn.sendall(f"ACK|{chunk_num}\n".encode("utf-8"))
                            self._log("RECV", f"📤 ACK chunk {chunk_num}")
                            
                            # Check all chunks
                            if len(self.pending_files[file_name]['chunks']) == total_chunks:
                                self._log("RECV", f"✓ Tất cả {total_chunks} chunks")
                                
                                try:
                                    # Giải nén từng chunk riêng lẻ (vì sender nén mỗi chunk riêng)
                                    file_bytes = b""
                                    for i in range(1, total_chunks + 1):
                                        if i in self.pending_files[file_name]['chunks']:
                                            cipher_c = self.pending_files[file_name]['chunks'][i]
                                            t0 = time.perf_counter()
                                            chunk_hex = decrypt_hex_no_padding(cipher_c, recv_key)
                                            dt = (time.perf_counter() - t0) * 1000
                                            
                                            # Chuyển hex → bytes → giải nén chunk này
                                            compressed_chunk = bytes.fromhex(chunk_hex)
                                            decompressed_chunk = zlib.decompress(compressed_chunk)
                                            file_bytes += decompressed_chunk
                                            
                                            self._log("RECV", f"  [{i}] Giải mã & nén ({dt:.1f}ms, {len(decompressed_chunk)} bytes)")
                                    
                                    # Sau khi ghép tất cả chunks: lưu file
                                    name_parts = file_name.rsplit('.', 1)
                                    if len(name_parts) == 2:
                                        output_name = f"{name_parts[0]}_decrypted.{name_parts[1]}"
                                    else:
                                        output_name = f"{file_name}_decrypted"
                                    
                                    # Lưu vào folder được chọn
                                    output_file = os.path.join(self.receive_folder, output_name)
                                    
                                    with open(output_file, 'wb') as f:
                                        f.write(file_bytes)
                                    
                                    # Lưu file mã hóa cùng vị trí
                                    cipher_chunks = self.pending_files[file_name]['chunks']
                                    cipher_file = self._save_encrypted_file_on_receive(
                                        file_name, 
                                        file_size, 
                                        total_chunks, 
                                        cipher_chunks, 
                                        recv_key,
                                        self.receive_folder
                                    )
                                    
                                    # Kiểm tra magic bytes để xác nhận file OK
                                    magic_info = self._check_file_magic(file_bytes, file_name)
                                    
                                    plain = f"📦 {file_name}\n📂 {os.path.abspath(output_file)}\n💾 {len(file_bytes)} bytes"
                                    if cipher_file:
                                        plain += f"\n🔐 Mã hóa: {cipher_file}"
                                    self._log("RECV", f"✓ Lưu: {output_file}")
                                    if cipher_file:
                                        self._log("RECV", f"🔐 Mã hóa: {cipher_file}")
                                    self._log("RECV", f"📋 {magic_info}")
                                    
                                    del self.pending_files[file_name]
                                    self.msg_count_recv += 1
                                    self.root.after(0, self._update_cnt)
                                    self.root.after(0, lambda p=plain: self._on_msg_received(p, None, 0))
                                except Exception as e:
                                    self._log("ERROR", f"Reassemble lỗi: {e}")
                                    if file_name in self.pending_files:
                                        del self.pending_files[file_name]
                            else:
                                self._log("RECV", f"⏳ Chờ ({len(self.pending_files[file_name]['chunks'])}/{total_chunks})")
                            
                            continue
                        except ValueError as e:
                            self._log("ERROR", f"FILE parse lỗi: {e}")
                            conn.sendall(b"NACK|PARSE|Parse error\n")
                            continue
                    
                    # === TEXT PROTOCOL ===
                    elif msg_type == "TEXT" and len(parts) == 2:
                        cipher = parts[1]
                        self._log_detail("RECV", "Loại", "Text message")
                        self._log_detail("RECV", "Bản mã", cipher[:80] + "...")
                        
                        try:
                            t0 = time.perf_counter()
                            decrypted_text = decrypt_text(cipher, recv_key)
                            dt = (time.perf_counter() - t0) * 1000
                            
                            self._log_detail("RECV", "Giải mã (ms)", f"{dt:.2f}")
                            self._log("RECV", f"✓ Tin: {decrypted_text}")
                            
                            # ✓ GỬI ACK CHO TEXT
                            conn.sendall(b"ACK|TEXT\n")
                            self._log("RECV", f"📤 ACK text")
                            
                            self.msg_count_recv += 1
                            self.root.after(0, self._update_cnt)
                            self.root.after(0, lambda p=decrypted_text: self._on_msg_received(p, None, dt))
                        except Exception as e:
                            self._log("ERROR", f"Giải mã lỗi: {e}")
                            conn.sendall(b"NACK|DECRYPT|Decrypt error\n")
                            continue
                    
                    else:
                        self._log("ERROR", f"Type lỗi: {msg_type}")
                        conn.sendall(b"NACK|TYPE|Unknown type\n")
                        continue
                    
                except socket.timeout:
                    self._log("RECV", "Timeout - closing")
                    break
                except Exception as inner_err:
                    self._log("ERROR", f"Inner error: {inner_err}")
                    break
            
            threading.Thread(target=self._play_sound, daemon=True).start()
        
        except Exception as e:
            err_msg = f"Lỗi: {type(e).__name__}: {e}"
            self._log("ERROR", err_msg)
            self.root.after(0, lambda m=err_msg: messagebox.showerror("Lỗi Receiver", m))
        finally:
            conn.close()
    def _on_msg_received(self, plain, file_name, dt):
        if file_name:
            # Hiển thị thông tin file (không show nội dung)
            self._add_bubble(plain, "received", details=True)
            self._set_status(f"Nhận file  •  {time.strftime('%H:%M')}", TG_GREEN)
        else:
            # Hiển thị tin nhắn text
            self._add_bubble(plain, "received", details=True)
            self._set_status(f"Nhận tin nhắn  •  {time.strftime('%H:%M')}", TG_GREEN)
        self._update_cnt()

    # ────────────────────────────────────────────────────
    #  GỬI TIN
    # ────────────────────────────────────────────────────
    def _cancel_send(self):
        if self._send_socket:
            try:
                self._send_socket.close()
            except Exception:
                pass
            self._send_socket = None
        self._sending = False
        self._log("INFO", "Đã hủy gửi")
        self._set_status("Đã hủy gửi", TG_YELLOW)
        self.send_btn.set_icon("send")

    def _on_send(self):
        if self._sending:
            self._cancel_send()
            return

        key = self.ent_key.get().strip()
        if len(key) != 8:
            messagebox.showwarning("Lỗi khóa",
                                   f"Khóa phải đúng 8 ký tự!\nHiện tại: {len(key)} ký tự.")
            self._log("ERROR", f"Khóa không hợp lệ ({len(key)} ký tự)")
            return

        # ---- Gửi FILE hoặc TEXT ----
        if self.selected_files:
            # Gửi FILES (có thể nhiều file)
            tip   = self.ent_ip.get().strip()
            tport = self.ent_tport.get().strip()
            if not tip or not tport.isdigit():
                messagebox.showwarning("Lỗi", "IP đích và cổng đích không hợp lệ.")
                return
            
            # Check total size
            total_size = sum(os.path.getsize(f) for f in self.selected_files if os.path.isfile(f))
            file_count = len(self.selected_files)
            
            # Hiển thị bubble cho tất cả files
            size_mb = total_size / (1024 * 1024)
            if file_count == 1:
                file_name = os.path.basename(self.selected_files[0])
                self._add_bubble(f"📦 Gửi file: {file_name}\n({total_size} bytes)", "sent")
            else:
                self._add_bubble(f"📦 Gửi {file_count} files\n({total_size} bytes, {size_mb:.1f}MB)", "sent")
            
            files_to_send = list(self.selected_files)
            self.selected_files = []
            self._update_file_list_display()
            
            self._sending = True
            self._set_status(f"Đang gửi {file_count} file...", TG_YELLOW)
            self.send_btn.set_icon("cancel")
            
            # Gửi từng file
            threading.Thread(target=self._send_multiple_files_worker,
                             args=(files_to_send, key, tip, int(tport)), daemon=True).start()
        else:
            # Gửi TEXT
            if self._placeholder_visible:
                return

            msg = self.txt_msg.get("1.0", "end").strip()
            if not msg:
                return

            tip   = self.ent_ip.get().strip()
            tport = self.ent_tport.get().strip()
            if not tip or not tport.isdigit():
                messagebox.showwarning("Lỗi", "IP đích và cổng đích không hợp lệ.")
                return

            # Show the message bubble immediately (optimistic UI)
            self._add_bubble(msg, "sent")
            self._set_placeholder()

            self._sending = True
            self._set_status("Đang gửi ...", TG_YELLOW)
            self.send_btn.set_icon("cancel")

            threading.Thread(target=self._send_worker,
                             args=(msg, key, tip, int(tport)), daemon=True).start()

    def _send_multiple_files_worker(self, files_list, key, target_ip, target_port):
        """Gửi nhiều file tuần tự với compression, checksum, ACK/NACK"""
        try:
            self._log_sep()
            self._log("SEND", f"Bắt đầu gửi {len(files_list)} files (có compression + checksum)...")
            
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self._send_socket = sock
            sock.settimeout(30)
            sock.connect((target_ip, target_port))
            
            for file_idx, file_path in enumerate(files_list, 1):
                if not self._sending:
                    break
                
                if not os.path.isfile(file_path):
                    self._log("ERROR", f"[{file_idx}] File không tồn tại: {file_path}")
                    continue
                
                file_name = os.path.basename(file_path)
                self._log_sep()
                self._log_detail("SEND", f"File {file_idx}/{len(files_list)}", file_name)
                
                # Đọc file nhị phân
                with open(file_path, 'rb') as f:
                    file_bytes = f.read()
                
                self._log_detail("SEND", "Kích thước gốc", f"{len(file_bytes)} bytes")
                
                # Chia thành chunks
                CHUNK_SIZE = 65536
                chunks = [file_bytes[i:i+CHUNK_SIZE] for i in range(0, len(file_bytes), CHUNK_SIZE)]
                total_chunks = len(chunks)
                file_size = len(file_bytes)
                self._log_detail("SEND", "Số chunks", str(total_chunks))
                
                # Dict lưu cipher chunks để export sau
                cipher_chunks = {}
                
                # Gửi từng chunk với compression + checksum + ACK
                for chunk_num, chunk in enumerate(chunks, 1):
                    if not self._sending:
                        break
                    
                    # Tính checksum của chunk gốc (trước nén)
                    chunk_hash = hashlib.md5(chunk).hexdigest()[:8]
                    
                    # Nén chunk
                    t_compress = time.perf_counter()
                    chunk_compressed = zlib.compress(chunk, level=6)
                    dt_compress = (time.perf_counter() - t_compress) * 1000
                    compression_ratio = len(chunk_compressed) / len(chunk) * 100
                    
                    # Convert chunk compressed → hex → encrypt
                    chunk_hex = chunk_compressed.hex().upper()
                    t0 = time.perf_counter()
                    cipher_chunk = encrypt_hex_data(chunk_hex, key)
                    dt_cipher = (time.perf_counter() - t0) * 1000
                    
                    # Lưu cipher chunk để export sau
                    cipher_chunks[chunk_num] = cipher_chunk
                    
                    # Log chi tiết mã hóa (đầu tiên, rồi cuối cùng)
                    if chunk_num == 1:
                        # Chỉ log chi tiết mã hóa cho chunk đầu tiên (tránh spam)
                        self._log_cipher("SEND", f"📦 Mã Hóa Chunk 1/{total_chunks} (đầu {min(128, len(cipher_chunk))} ký tự)", cipher_chunk[:256])
                    
                    # Protocol: FILE|FILE_NAME|FILE_SIZE|TOTAL|CHUNK_NUM|HASH|CIPHER_COMPRESSED\n
                    data_to_send = f"FILE|{file_name}|{file_size}|{total_chunks}|{chunk_num}|{chunk_hash}|{cipher_chunk}\n"
                    
                    # Gửi chunk và chờ ACK (retry tối đa 3 lần)
                    max_retries = 3
                    for retry in range(max_retries):
                        try:
                            sock.sendall(data_to_send.encode("utf-8"))
                            
                            # Chờ ACK/NACK (timeout 15 giây - tăng để tránh timeout khi bên nhận xử lý lâu)
                            sock.settimeout(15)
                            ack_response = sock.recv(1024).decode("utf-8", errors="ignore").strip()
                            
                            if ack_response.startswith("ACK"):
                                # ✓ OK
                                self._log("SEND", f"  [{chunk_num}/{total_chunks}] ✓ ACK ({len(chunk)}→{len(chunk_compressed)} bytes, {compression_ratio:.1f}%, cipher {dt_cipher:.1f}ms)")
                                break
                            elif ack_response.startswith("NACK"):
                                # ✗ Chunk bị lỗi, gửi lại
                                reason = ack_response.split("|")[2] if len(ack_response.split("|")) > 2 else "unknown"
                                self._log("SEND", f"  [{chunk_num}/{total_chunks}] ✗ NACK: {reason} (retry {retry+1}/{max_retries})")
                                if retry < max_retries - 1:
                                    continue
                                else:
                                    self._log("ERROR", f"Chunk {chunk_num} failed after {max_retries} retries")
                                    break
                            else:
                                self._log("SEND", f"  [{chunk_num}/{total_chunks}] ? Unknown response: {ack_response[:50]}")
                                break
                        
                        except socket.timeout:
                            self._log("SEND", f"  [{chunk_num}/{total_chunks}] ⏱ Timeout (retry {retry+1}/{max_retries})")
                            if retry < max_retries - 1:
                                continue
                            else:
                                self._log("ERROR", f"Chunk {chunk_num} timeout after {max_retries} retries")
                                break
                
                # Export cipher archive
                cipher_file = self._export_cipher_archive(file_name, file_size, total_chunks, cipher_chunks, key)
                if cipher_file:
                    self._log("SEND", f"💾 Mã hóa đã lưu: {cipher_file}")
                
                self._log("SEND", f"✓ File {file_idx} hoàn tất")
            
            sock.close()
            self._send_socket = None
            
            self._log("SEND", f"✓ Đã gửi tất cả {len(files_list)} files (với compression + checksum) tới {target_ip}:{target_port}")
            self.msg_count_sent += len(files_list)
            self.root.after(0, self._update_cnt)
            self.root.after(0, lambda: self._set_status(
                f"Đã gửi {len(files_list)} files  •  {time.strftime('%H:%M')}", TG_GREEN))

        except ConnectionRefusedError:
            if not self._sending:
                return
            m = (f"Kết nối bị từ chối bởi {target_ip}:{target_port}\n"
                 "Máy đích chưa bấm 'Bắt đầu nghe'.")
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Bị từ chối", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except socket.timeout:
            if not self._sending:
                return
            m = f"Timeout kết nối tới {target_ip}:{target_port}\nFirewall chặn hoặc IP sai."
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Timeout", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except OSError as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi mạng: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi mạng", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        except Exception as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        finally:
            self.root.after(0, self._finish_send)

    def _finish_send(self):
        self._sending = False
        self._send_socket = None
        self.send_btn.set_icon("send")

    def _send_file_worker(self, file_path, file_name, key, target_ip, target_port):
        """Mã hóa và gửi file với chunked encryption"""
        CHUNK_SIZE = 65536  # 64KB chunks
        
        try:
            self._log_sep()
            
            # Đọc file nhị phân
            with open(file_path, 'rb') as f:
                file_bytes = f.read()
            
            self._log_detail("SEND", "File gốc", file_name)
            self._log_detail("SEND", "Kích thước", f"{len(file_bytes)} bytes")
            
            # Chia thành chunks
            chunks = [file_bytes[i:i+CHUNK_SIZE] for i in range(0, len(file_bytes), CHUNK_SIZE)]
            total_chunks = len(chunks)
            self._log_detail("SEND", "Số chunks", str(total_chunks))
            
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self._send_socket = sock
            sock.settimeout(30)
            sock.connect((target_ip, target_port))
            
            self._log("SEND", f"Đang gửi {total_chunks} chunks tới {target_ip}:{target_port}...")
            
            # Gửi từng chunk
            for chunk_num, chunk in enumerate(chunks, 1):
                if not self._sending:
                    break
                
                # Convert chunk → hex → encrypt
                chunk_hex = chunk.hex().upper()
                t0 = time.perf_counter()
                cipher_chunk = encrypt_text(chunk_hex, key)
                dt = (time.perf_counter() - t0) * 1000
                
                # Protocol: FILE|FILE_NAME|TOTAL|CHUNK_NUM|CIPHER_CHUNK\n (KHÔNG gửi khóa)
                data_to_send = f"FILE|{file_name}|{total_chunks}|{chunk_num}|{cipher_chunk}\n"
                sock.sendall(data_to_send.encode("utf-8"))
                
                self._log("SEND", f"[{chunk_num}/{total_chunks}] Chunk gửi ({len(chunk)} bytes → {dt:.1f}ms)")
            
            sock.close()
            self._send_socket = None
            
            self._log("SEND", f"✓ Đã gửi {total_chunks} chunks tới {target_ip}:{target_port}")
            self.msg_count_sent += 1
            self.root.after(0, self._update_cnt)
            self.root.after(0, lambda: self._set_status(
                f"Đã gửi file  •  {time.strftime('%H:%M')}", TG_GREEN))

        except ConnectionRefusedError:
            if not self._sending:
                return
            m = (f"Kết nối bị từ chối bởi {target_ip}:{target_port}\n"
                 "Máy đích chưa bấm 'Bắt đầu nghe'.")
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Bị từ chối", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except socket.timeout:
            if not self._sending:
                return
            m = f"Timeout kết nối tới {target_ip}:{target_port}\nFirewall chặn hoặc IP sai."
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Timeout", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except OSError as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi mạng: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi mạng", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        except Exception as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        finally:
            self.root.after(0, self._finish_send)

    def _send_worker(self, message, key, target_ip, target_port):
        try:
            self._log_sep()
            self._log_detail("SEND", "Nội dung gốc", message)

            t0 = time.perf_counter()
            cipher = encrypt_text(message, key)
            dt = (time.perf_counter() - t0) * 1000

            # Log chi tiết mã hóa với format đẹp
            self._log_cipher("SEND", "📦 Bản Mã (Encrypted Hex)", cipher)
            self._log_detail("SEND", "Thời gian mã hóa", f"{dt:.2f} ms")
            self._log("SEND", f"Đang kết nối tới {target_ip}:{target_port}...")

            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self._send_socket = sock
            sock.settimeout(3)
            sock.connect((target_ip, target_port))
            sock.sendall(f"TEXT|{cipher}\n".encode("utf-8"))  # Gửi CHỈ mã hóa, KHÔNG gửi khóa
            sock.close()
            self._send_socket = None

            self._log("SEND", f"✓ Đã gửi tới {target_ip}:{target_port}")
            self.msg_count_sent += 1
            self.root.after(0, self._update_cnt)
            self.root.after(0, lambda: self._set_status(
                f"Đã gửi  •  {time.strftime('%H:%M')}", TG_GREEN))

        except ConnectionRefusedError:
            if not self._sending:
                return
            m = (f"Kết nối bị từ chối bởi {target_ip}:{target_port}\n"
                 "Máy đích chưa bấm 'Bắt đầu nghe'.")
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Bị từ chối", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except socket.timeout:
            if not self._sending:
                return
            m = f"Timeout kết nối tới {target_ip}:{target_port}\nFirewall chặn hoặc IP sai."
            self._log("ERROR", m.split('\n')[0])
            self.root.after(0, lambda: self._set_status("Timeout", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi kết nối", m))
        except OSError as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi mạng: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi mạng", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        except Exception as e:
            if not self._sending:
                return
            self._log("ERROR", f"Lỗi: {e}")
            self.root.after(0, lambda: self._set_status("Lỗi", TG_ERROR))
            self.root.after(0, lambda: messagebox.showerror("Lỗi", str(e)))
        finally:
            self.root.after(0, self._finish_send)


# ════════════════════════════════════════════════════════
if __name__ == "__main__":
    root = tk.Tk()
    app = DESMessengerApp(root)
    root.mainloop()

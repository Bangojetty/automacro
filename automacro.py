"""
AutoMacro - Global Keyboard/Mouse Macro App
Sends inputs via Windows SendInput API so they work even when games are in focus.
"""

import ctypes
import ctypes.wintypes as wintypes
import json
import os
import sys
import threading
import time
import tkinter as tk
from pathlib import Path

import math

import customtkinter as ctk
from PIL import Image, ImageDraw, ImageTk
from pynput import keyboard as pynput_kb, mouse as pynput_mouse

# ─── Windows SendInput Structures ────────────────────────────────────────────

INPUT_MOUSE = 0
INPUT_KEYBOARD = 1

KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_SCANCODE = 0x0008

MOUSEEVENTF_MOVE = 0x0001
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
MOUSEEVENTF_RIGHTDOWN = 0x0008
MOUSEEVENTF_RIGHTUP = 0x0010
MOUSEEVENTF_MIDDLEDOWN = 0x0020
MOUSEEVENTF_MIDDLEUP = 0x0040
MOUSEEVENTF_ABSOLUTE = 0x8000

SM_CXSCREEN = 0
SM_CYSCREEN = 1

user32 = ctypes.windll.user32
kernel32 = ctypes.windll.kernel32


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", ctypes.c_long),
        ("dy", ctypes.c_long),
        ("mouseData", ctypes.c_ulong),
        ("dwFlags", ctypes.c_ulong),
        ("time", ctypes.c_ulong),
        ("dwExtraInfo", ctypes.POINTER(ctypes.c_ulong)),
    ]


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", ctypes.c_ushort),
        ("wScan", ctypes.c_ushort),
        ("dwFlags", ctypes.c_ulong),
        ("time", ctypes.c_ulong),
        ("dwExtraInfo", ctypes.POINTER(ctypes.c_ulong)),
    ]


class HARDWAREINPUT(ctypes.Structure):
    _fields_ = [
        ("uMsg", ctypes.c_ulong),
        ("wParamL", ctypes.c_ushort),
        ("wParamH", ctypes.c_ushort),
    ]


class INPUT_UNION(ctypes.Union):
    _fields_ = [
        ("mi", MOUSEINPUT),
        ("ki", KEYBDINPUT),
        ("hi", HARDWAREINPUT),
    ]


class INPUT(ctypes.Structure):
    _fields_ = [
        ("type", ctypes.c_ulong),
        ("union", INPUT_UNION),
    ]


# ─── Virtual Key Code Map ────────────────────────────────────────────────────

VK_MAP = {
    # Letters
    **{chr(c): c for c in range(ord("A"), ord("Z") + 1)},
    # Digits
    **{str(i): 0x30 + i for i in range(10)},
    # Function keys
    **{f"F{i}": 0x6F + i for i in range(1, 13)},
    # Special keys
    "SPACE": 0x20, "ENTER": 0x0D, "TAB": 0x09, "ESCAPE": 0x1B, "ESC": 0x1B,
    "BACKSPACE": 0x08, "DELETE": 0x2E, "INSERT": 0x2D,
    "HOME": 0x24, "END": 0x23, "PAGEUP": 0x21, "PAGEDOWN": 0x22,
    "UP": 0x26, "DOWN": 0x28, "LEFT": 0x25, "RIGHT": 0x27,
    "SHIFT": 0x10, "LSHIFT": 0xA0, "RSHIFT": 0xA1,
    "CTRL": 0x11, "LCTRL": 0xA2, "RCTRL": 0xA3,
    "ALT": 0x12, "LALT": 0xA4, "RALT": 0xA5,
    "CAPSLOCK": 0x14, "NUMLOCK": 0x90, "SCROLLLOCK": 0x91,
    # Numpad
    **{f"NUM{i}": 0x60 + i for i in range(10)},
    "MULTIPLY": 0x6A, "ADD": 0x6B, "SUBTRACT": 0x6D,
    "DECIMAL": 0x6E, "DIVIDE": 0x6F,
    # Punctuation
    "SEMICOLON": 0xBA, "EQUALS": 0xBB, "COMMA": 0xBC,
    "MINUS": 0xBD, "PERIOD": 0xBE, "SLASH": 0xBF,
    "BACKTICK": 0xC0, "LBRACKET": 0xDB, "BACKSLASH": 0xDC,
    "RBRACKET": 0xDD, "QUOTE": 0xDE,
}

# Build reverse map for display
VK_REVERSE = {v: k for k, v in VK_MAP.items()}

# Friendly names for all available keys — grouped by type, alphabetical within each group
_LETTERS = sorted(k for k in VK_MAP if len(k) == 1 and k.isalpha())
_DIGITS = sorted(k for k in VK_MAP if len(k) == 1 and k.isdigit())
_FKEYS = [f"F{i}" for i in range(1, 13)]
_MODIFIERS = sorted({"SHIFT", "LSHIFT", "RSHIFT", "CTRL", "LCTRL", "RCTRL",
                      "ALT", "LALT", "RALT"})
_NAVIGATION = sorted({"UP", "DOWN", "LEFT", "RIGHT", "HOME", "END",
                       "PAGEUP", "PAGEDOWN", "INSERT", "DELETE"})
_NUMPAD = [f"NUM{i}" for i in range(10)] + sorted(
    {"MULTIPLY", "ADD", "SUBTRACT", "DECIMAL", "DIVIDE"})
_OTHER = sorted(set(VK_MAP.keys()) - set(_LETTERS) - set(_DIGITS) - set(_FKEYS)
                - set(_MODIFIERS) - set(_NAVIGATION) - set(_NUMPAD))
ALL_KEY_NAMES = _LETTERS + _DIGITS + _FKEYS + _MODIFIERS + _NAVIGATION + _NUMPAD + _OTHER

# Hotkey-compatible key names (subset used for global hotkey config)
HOTKEY_KEYS = [f"F{i}" for i in range(1, 13)] + [
    "HOME", "END", "INSERT", "DELETE", "PAGEUP", "PAGEDOWN",
    "NUMLOCK", "SCROLLLOCK", "PAUSE",
]


def vk_for_key(name: str) -> int | None:
    return VK_MAP.get(name.upper())


# ─── InputSimulator ──────────────────────────────────────────────────────────

class InputSimulator:
    """Send global keyboard and mouse inputs via Windows SendInput API."""

    @staticmethod
    def _send(inputs: list[INPUT]):
        n = len(inputs)
        arr = (INPUT * n)(*inputs)
        user32.SendInput(n, ctypes.pointer(arr), ctypes.sizeof(INPUT))

    @staticmethod
    def send_key_down(vk: int):
        scan = user32.MapVirtualKeyW(vk, 0)
        inp = INPUT()
        inp.type = INPUT_KEYBOARD
        inp.union.ki.wVk = vk
        inp.union.ki.wScan = scan
        inp.union.ki.dwFlags = 0
        InputSimulator._send([inp])

    @staticmethod
    def send_key_up(vk: int):
        scan = user32.MapVirtualKeyW(vk, 0)
        inp = INPUT()
        inp.type = INPUT_KEYBOARD
        inp.union.ki.wVk = vk
        inp.union.ki.wScan = scan
        inp.union.ki.dwFlags = KEYEVENTF_KEYUP
        InputSimulator._send([inp])

    @staticmethod
    def send_key_tap(vk: int):
        InputSimulator.send_key_down(vk)
        time.sleep(0.01)
        InputSimulator.send_key_up(vk)

    @staticmethod
    def send_mouse_click(x: int, y: int, button: str = "left"):
        screen_w = user32.GetSystemMetrics(SM_CXSCREEN)
        screen_h = user32.GetSystemMetrics(SM_CYSCREEN)
        abs_x = int(x * 65535 / screen_w)
        abs_y = int(y * 65535 / screen_h)

        if button == "right":
            down_flag = MOUSEEVENTF_RIGHTDOWN
            up_flag = MOUSEEVENTF_RIGHTUP
        elif button == "middle":
            down_flag = MOUSEEVENTF_MIDDLEDOWN
            up_flag = MOUSEEVENTF_MIDDLEUP
        else:
            down_flag = MOUSEEVENTF_LEFTDOWN
            up_flag = MOUSEEVENTF_LEFTUP

        move = INPUT()
        move.type = INPUT_MOUSE
        move.union.mi.dx = abs_x
        move.union.mi.dy = abs_y
        move.union.mi.dwFlags = MOUSEEVENTF_MOVE | MOUSEEVENTF_ABSOLUTE

        down = INPUT()
        down.type = INPUT_MOUSE
        down.union.mi.dx = abs_x
        down.union.mi.dy = abs_y
        down.union.mi.dwFlags = down_flag | MOUSEEVENTF_ABSOLUTE

        up = INPUT()
        up.type = INPUT_MOUSE
        up.union.mi.dx = abs_x
        up.union.mi.dy = abs_y
        up.union.mi.dwFlags = up_flag | MOUSEEVENTF_ABSOLUTE

        InputSimulator._send([move, down, up])


# ─── InputRecorder ───────────────────────────────────────────────────────────

class InputRecorder:
    """Capture live keyboard and mouse events and build an action list."""

    # Map pynput special Key enum values to VK_MAP names
    _PYNPUT_KEY_MAP = {
        pynput_kb.Key.space: "SPACE",
        pynput_kb.Key.enter: "ENTER",
        pynput_kb.Key.tab: "TAB",
        pynput_kb.Key.esc: "ESC",
        pynput_kb.Key.backspace: "BACKSPACE",
        pynput_kb.Key.delete: "DELETE",
        pynput_kb.Key.insert: "INSERT",
        pynput_kb.Key.home: "HOME",
        pynput_kb.Key.end: "END",
        pynput_kb.Key.page_up: "PAGEUP",
        pynput_kb.Key.page_down: "PAGEDOWN",
        pynput_kb.Key.up: "UP",
        pynput_kb.Key.down: "DOWN",
        pynput_kb.Key.left: "LEFT",
        pynput_kb.Key.right: "RIGHT",
        pynput_kb.Key.shift: "SHIFT",
        pynput_kb.Key.shift_l: "LSHIFT",
        pynput_kb.Key.shift_r: "RSHIFT",
        pynput_kb.Key.ctrl: "CTRL",
        pynput_kb.Key.ctrl_l: "LCTRL",
        pynput_kb.Key.ctrl_r: "RCTRL",
        pynput_kb.Key.alt: "ALT",
        pynput_kb.Key.alt_l: "LALT",
        pynput_kb.Key.alt_r: "RALT",
        pynput_kb.Key.caps_lock: "CAPSLOCK",
        pynput_kb.Key.num_lock: "NUMLOCK",
        pynput_kb.Key.scroll_lock: "SCROLLLOCK",
        **{getattr(pynput_kb.Key, f"f{i}", None): f"F{i}" for i in range(1, 13)},
    }

    def __init__(self, on_action=None, stop_key="F8"):
        self._on_action = on_action  # callback(action: dict)
        self._stop_key = stop_key.upper()
        self._kb_listener = None
        self._mouse_listener = None
        self._last_time = None
        self.recording = False

    def start(self):
        self.recording = True
        self._last_time = time.monotonic()
        self._kb_listener = pynput_kb.Listener(
            on_press=self._on_key_press, suppress=False
        )
        self._mouse_listener = pynput_mouse.Listener(
            on_click=self._on_mouse_click, suppress=False
        )
        self._kb_listener.start()
        self._mouse_listener.start()

    def stop(self):
        self.recording = False
        if self._kb_listener:
            self._kb_listener.stop()
            self._kb_listener = None
        if self._mouse_listener:
            self._mouse_listener.stop()
            self._mouse_listener = None

    def _elapsed_ms(self) -> int:
        now = time.monotonic()
        ms = int((now - self._last_time) * 1000)
        self._last_time = now
        return ms

    def _emit(self, action: dict):
        if self._on_action:
            self._on_action(action)

    def _on_key_press(self, key):
        if not self.recording:
            return
        name = self._resolve_key(key)
        if name is None:
            return
        delay = self._elapsed_ms()
        if name.upper() == self._stop_key:
            return  # stop key is handled by the app, ignore it here
        self._emit({"type": "key", "key": name, "action": "tap", "delay": delay})

    def _on_mouse_click(self, x, y, button, pressed):
        if not self.recording or not pressed:
            return
        delay = self._elapsed_ms()
        btn_name = "right" if button == pynput_mouse.Button.right else (
            "middle" if button == pynput_mouse.Button.middle else "left"
        )
        self._emit({"type": "click", "x": x, "y": y, "button": btn_name, "delay": delay})

    def _resolve_key(self, key) -> str | None:
        # Special keys
        name = self._PYNPUT_KEY_MAP.get(key)
        if name:
            return name
        # Character keys
        try:
            char = key.char
            if char and char.upper() in VK_MAP:
                return char.upper()
        except AttributeError:
            pass
        return None


# ─── MacroEngine ─────────────────────────────────────────────────────────────

class MacroEngine:
    """Execute a list of macro actions in a background thread."""

    def __init__(self, on_status=None, on_action=None):
        self._thread: threading.Thread | None = None
        self._stop_event = threading.Event()
        self._on_status = on_status  # callback(str)
        self._on_action = on_action  # callback() — fired after each action
        self.running = False

    def start(self, actions: list[dict], repeat: int):
        if self.running:
            return
        self._stop_event.clear()
        self.running = True
        self._thread = threading.Thread(
            target=self._run, args=(actions, repeat), daemon=True
        )
        self._thread.start()
        if self._on_status:
            self._on_status("running")

    def stop(self):
        self._stop_event.set()
        self.running = False
        if self._on_status:
            self._on_status("stopped")

    def _run(self, actions: list[dict], repeat: int):
        iteration = 0
        try:
            while not self._stop_event.is_set():
                iteration += 1
                if self._on_status:
                    if repeat == 0:
                        self._on_status(f"running (loop {iteration}, infinite)")
                    else:
                        self._on_status(f"running (loop {iteration}/{repeat})")

                for action in actions:
                    if self._stop_event.is_set():
                        break
                    self._execute_action(action)
                    if self._on_action:
                        self._on_action()
                    delay_ms = action.get("delay", 0)
                    if delay_ms > 0:
                        self._interruptible_sleep(delay_ms / 1000.0)

                if repeat != 0 and iteration >= repeat:
                    break
        finally:
            self.running = False
            if self._on_status:
                self._on_status("stopped")

    def _execute_action(self, action: dict):
        atype = action.get("type")
        if atype == "key":
            vk = vk_for_key(action["key"])
            if vk is None:
                return
            key_action = action.get("action", "tap")
            if key_action == "press":
                InputSimulator.send_key_down(vk)
            elif key_action == "release":
                InputSimulator.send_key_up(vk)
            else:
                InputSimulator.send_key_tap(vk)
        elif atype == "click":
            InputSimulator.send_mouse_click(
                action["x"], action["y"], action.get("button", "left")
            )
        elif atype == "delay":
            extra = action.get("delay", 0)
            if extra > 0:
                self._interruptible_sleep(extra / 1000.0)

    def _interruptible_sleep(self, seconds: float):
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if self._stop_event.is_set():
                return
            time.sleep(min(0.05, end - time.monotonic()))


# ─── GlobalHotkeyManager ────────────────────────────────────────────────────

class GlobalHotkeyManager:
    """Use Windows RegisterHotKey API for a true OS-level global hotkey."""

    HOTKEY_ID = 1  # arbitrary ID for our single hotkey

    def __init__(self, hotkey: str, callback):
        self._callback = callback
        self._vk = 0
        self._running = False
        self._thread: threading.Thread | None = None
        self.set_hotkey(hotkey)

    def set_hotkey(self, hotkey: str):
        self.stop()
        vk = vk_for_key(hotkey)
        if vk is None:
            return
        self._vk = vk
        self._running = True
        self._thread = threading.Thread(target=self._hotkey_thread, daemon=True)
        self._thread.start()

    def stop(self):
        if self._running:
            self._running = False
            # Post WM_QUIT to unblock GetMessage in the hotkey thread
            if self._thread and self._thread.is_alive():
                tid = getattr(self, "_thread_id", None)
                if tid:
                    ctypes.windll.user32.PostThreadMessageW(tid, 0x0012, 0, 0)  # WM_QUIT
            self._thread = None

    def _hotkey_thread(self):
        """Runs its own message loop — RegisterHotKey is per-thread."""
        self._thread_id = kernel32.GetCurrentThreadId()
        # 0 = no modifier, self._vk = virtual key code
        if not user32.RegisterHotKey(None, self.HOTKEY_ID, 0, self._vk):
            # Registration failed (key might be reserved)
            return
        try:
            msg = wintypes.MSG()
            while self._running:
                # GetMessage blocks until a message arrives (including WM_HOTKEY)
                ret = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if ret <= 0:  # WM_QUIT or error
                    break
                if msg.message == 0x0312:  # WM_HOTKEY
                    self._callback()
        finally:
            user32.UnregisterHotKey(None, self.HOTKEY_ID)


# ─── UI ──────────────────────────────────────────────────────────────────────

class AutoMacroApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title("AutoMacro")
        self.geometry("620x720")
        self.minsize(620, 550)
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.actions: list[dict] = []
        self.hotkey = "F6"
        self.macro_name = "Untitled"

        self._recording_hotkey = False
        self._input_recording = False
        self.engine = MacroEngine(on_status=self._on_engine_status,
                                   on_action=self._on_engine_action)
        self.hotkey_mgr = GlobalHotkeyManager(self.hotkey, self._toggle_macro)
        self.recorder = InputRecorder(on_action=self._on_recorded_action, stop_key="F8")

        self._build_ui()
        self._create_overlay()
        self._refresh_action_list()
        self._update_status("Stopped")

        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── UI Construction ──────────────────────────────────────────────────

    def _build_ui(self):
        # Menu bar
        menubar = tk.Menu(self)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Save Macro...", command=self._save_macro)
        file_menu.add_command(label="Load Macro...", command=self._load_macro)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_close)
        menubar.add_cascade(label="File", menu=file_menu)
        self.configure(menu=menubar)

        # Main container
        main = ctk.CTkFrame(self)
        main.pack(fill="both", expand=True, padx=10, pady=10)

        # ── Action list header
        header = ctk.CTkFrame(main, fg_color="transparent")
        header.pack(fill="x", pady=(0, 5))
        ctk.CTkLabel(header, text="Macro Actions", font=("", 16, "bold")).pack(
            side="left"
        )

        # ── Action list (scrollable)
        self.action_frame = ctk.CTkScrollableFrame(main, height=300)
        self.action_frame.pack(fill="both", expand=True, pady=(0, 10))

        # ── Add action buttons
        btn_row = ctk.CTkFrame(main, fg_color="transparent")
        btn_row.pack(fill="x", pady=(0, 10))
        ctk.CTkButton(btn_row, text="Add Key Press", width=140,
                       command=self._dlg_add_key).pack(side="left", padx=(0, 5))
        ctk.CTkButton(btn_row, text="Add Mouse Click", width=140,
                       command=self._dlg_add_click).pack(side="left", padx=(0, 5))
        ctk.CTkButton(btn_row, text="Add Delay", width=100,
                       command=self._dlg_add_delay).pack(side="left", padx=(0, 5))
        self.record_input_btn = ctk.CTkButton(
            btn_row, text="Record Inputs (F8)", width=150,
            fg_color="#7b3fa0", hover_color="#9b52c4",
            command=self._toggle_input_recording,
        )
        self.record_input_btn.pack(side="left", padx=(0, 5))
        ctk.CTkButton(btn_row, text="Clear All", width=90, fg_color="#aa3333",
                       hover_color="#cc4444",
                       command=self._clear_actions).pack(side="right")

        # ── Controls row 1: Repeat + Hotkey
        ctrl1 = ctk.CTkFrame(main)
        ctrl1.pack(fill="x", pady=(0, 5))

        ctk.CTkLabel(ctrl1, text="Repeat:").pack(side="left", padx=(10, 5))
        self.repeat_var = ctk.StringVar(value="1")
        self.repeat_entry = ctk.CTkEntry(ctrl1, width=60, textvariable=self.repeat_var)
        self.repeat_entry.pack(side="left", padx=(0, 5))

        self.infinite_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(ctrl1, text="Infinite", variable=self.infinite_var,
                         command=self._on_infinite_toggle).pack(side="left", padx=(0, 20))

        ctk.CTkLabel(ctrl1, text="Hotkey:").pack(side="left", padx=(10, 5))
        self.hotkey_label = ctk.CTkLabel(ctrl1, text=self.hotkey, width=60,
                                          font=("", 13, "bold"))
        self.hotkey_label.pack(side="left", padx=(0, 5))
        self.record_hotkey_btn = ctk.CTkButton(
            ctrl1, text="Record", width=70, command=self._start_hotkey_recording,
        )
        self.record_hotkey_btn.pack(side="left", padx=(0, 10))

        # ── Controls row 2: Start / Stop
        ctrl2 = ctk.CTkFrame(main, fg_color="transparent")
        ctrl2.pack(fill="x", pady=(0, 10))

        self.start_btn = ctk.CTkButton(ctrl2, text="Start (F6)", height=36,
                                         fg_color="#2d8a4e", hover_color="#36a85c",
                                         command=self._toggle_macro)
        self.start_btn.pack(fill="x", padx=10)

        # ── Status bar
        self.status_label = ctk.CTkLabel(main, text="Stopped", anchor="w",
                                          font=("", 12))
        self.status_label.pack(fill="x")

    # ── Action List Rendering ────────────────────────────────────────────

    def _refresh_action_list(self):
        for w in self.action_frame.winfo_children():
            w.destroy()

        if not self.actions:
            ctk.CTkLabel(self.action_frame, text="No actions yet. Add some above.",
                          text_color="gray").pack(pady=20)
            return

        for i, action in enumerate(self.actions):
            row = ctk.CTkFrame(self.action_frame)
            row.pack(fill="x", pady=2, padx=2)

            # Double-click to edit
            def bind_dblclick(widget, idx=i):
                widget.bind("<Double-Button-1>", lambda e, j=idx: self._edit_action(j))
                for child in widget.winfo_children():
                    bind_dblclick(child, idx)

            # Index
            ctk.CTkLabel(row, text=f"#{i+1}", width=35, font=("", 12, "bold")).pack(
                side="left", padx=(5, 5)
            )

            # Description
            desc = self._describe_action(action)
            ctk.CTkLabel(row, text=desc, anchor="w").pack(
                side="left", fill="x", expand=True
            )

            # Delay badge
            delay = action.get("delay", 0)
            ctk.CTkLabel(row, text=f"{delay}ms", width=60, text_color="gray").pack(
                side="left", padx=5
            )

            bind_dblclick(row)

            # Move up
            if i > 0:
                ctk.CTkButton(
                    row, text="\u25b2", width=28, height=28,
                    command=lambda idx=i: self._move_action(idx, -1),
                ).pack(side="left", padx=1)

            # Move down
            if i < len(self.actions) - 1:
                ctk.CTkButton(
                    row, text="\u25bc", width=28, height=28,
                    command=lambda idx=i: self._move_action(idx, 1),
                ).pack(side="left", padx=1)

            # Delete
            ctk.CTkButton(
                row, text="\u2715", width=28, height=28,
                fg_color="#aa3333", hover_color="#cc4444",
                command=lambda idx=i: self._delete_action(idx),
            ).pack(side="left", padx=(1, 5))

    @staticmethod
    def _describe_action(action: dict) -> str:
        atype = action.get("type")
        if atype == "key":
            return f"Key: {action['key'].upper()}  ({action.get('action', 'tap')})"
        elif atype == "click":
            return f"Click: ({action['x']}, {action['y']})  {action.get('button', 'left')}"
        elif atype == "delay":
            return f"Delay: {action.get('delay', 0)} ms"
        return "Unknown"

    def _move_action(self, index: int, direction: int):
        new_idx = index + direction
        if 0 <= new_idx < len(self.actions):
            self.actions[index], self.actions[new_idx] = (
                self.actions[new_idx], self.actions[index]
            )
            self._refresh_action_list()

    def _delete_action(self, index: int):
        self.actions.pop(index)
        self._refresh_action_list()

    def _clear_actions(self):
        self.actions.clear()
        self._refresh_action_list()

    # ── Dialogs ──────────────────────────────────────────────────────────

    def _edit_action(self, index: int):
        action = self.actions[index]
        atype = action.get("type")
        if atype == "key":
            self._dlg_add_key(edit_index=index)
        elif atype == "click":
            self._dlg_add_click(edit_index=index)
        elif atype == "delay":
            self._dlg_add_delay(edit_index=index)

    def _dlg_add_key(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Key Press" if editing else "Add Key Press")
        dlg.geometry("320x310")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Key:").pack(pady=(15, 0))
        key_var = ctk.StringVar(value=existing.get("key", "A"))
        ctk.CTkComboBox(dlg, values=ALL_KEY_NAMES, variable=key_var, width=200).pack(
            pady=5
        )

        ctk.CTkLabel(dlg, text="Action:").pack()
        action_var = ctk.StringVar(value=existing.get("action", "tap"))
        ctk.CTkComboBox(
            dlg, values=["tap", "press", "release"], variable=action_var, width=200
        ).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay after (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", 100)))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 100
            new_action = {
                "type": "key",
                "key": key_var.get(),
                "action": action_var.get(),
                "delay": max(0, delay),
            }
            if editing:
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=10)

    def _dlg_add_click(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Mouse Click" if editing else "Add Mouse Click")
        dlg.geometry("320x280")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        coord_frame = ctk.CTkFrame(dlg, fg_color="transparent")
        coord_frame.pack(pady=(15, 5))

        ctk.CTkLabel(coord_frame, text="X:").pack(side="left", padx=(0, 5))
        x_var = ctk.StringVar(value=str(existing.get("x", 0)))
        ctk.CTkEntry(coord_frame, textvariable=x_var, width=70).pack(
            side="left", padx=(0, 15)
        )
        ctk.CTkLabel(coord_frame, text="Y:").pack(side="left", padx=(0, 5))
        y_var = ctk.StringVar(value=str(existing.get("y", 0)))
        ctk.CTkEntry(coord_frame, textvariable=y_var, width=70).pack(side="left")

        def pick_position():
            dlg.withdraw()
            self.withdraw()

            overlay = ctk.CTkToplevel()
            overlay.attributes("-fullscreen", True)
            overlay.attributes("-alpha", 0.3)
            overlay.attributes("-topmost", True)
            overlay.configure(cursor="crosshair")

            def on_click(event):
                x_var.set(str(event.x_root))
                y_var.set(str(event.y_root))
                overlay.destroy()
                self.deiconify()
                dlg.deiconify()

            overlay.bind("<Button-1>", on_click)

        ctk.CTkButton(dlg, text="Pick from Screen", command=pick_position).pack(
            pady=5
        )

        ctk.CTkLabel(dlg, text="Button:").pack()
        btn_var = ctk.StringVar(value=existing.get("button", "left"))
        ctk.CTkComboBox(
            dlg, values=["left", "right", "middle"], variable=btn_var, width=200
        ).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay after (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", 200)))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            try:
                x, y = int(x_var.get()), int(y_var.get())
                delay = int(delay_var.get())
            except ValueError:
                x, y, delay = 0, 0, 200
            new_action = {
                "type": "click",
                "x": x, "y": y,
                "button": btn_var.get(),
                "delay": max(0, delay),
            }
            if editing:
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=10)

    def _dlg_add_delay(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Delay" if editing else "Add Delay")
        dlg.geometry("280x140")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Delay (ms):").pack(pady=(20, 0))
        delay_var = ctk.StringVar(value=str(existing.get("delay", 500)))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 500
            new_action = {"type": "delay", "delay": max(0, delay)}
            if editing:
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=10)

    # ── Controls ─────────────────────────────────────────────────────────

    def _toggle_macro(self):
        if self.engine.running:
            self.engine.stop()
        else:
            if not self.actions:
                return
            repeat = 0 if self.infinite_var.get() else int(self.repeat_var.get() or 1)
            self.engine.start(list(self.actions), repeat)

    def _toggle_input_recording(self):
        if self._input_recording:
            self._stop_input_recording()
        else:
            self._start_input_recording()

    def _start_input_recording(self):
        self._input_recording = True
        self.recorder.start()
        self.record_input_btn.configure(
            text="Stop Recording (F8)", fg_color="#c0392b", hover_color="#e74c3c"
        )
        self._update_status("recording inputs — press F8 to stop")

    def _stop_input_recording(self):
        self._input_recording = False
        self.recorder.stop()
        self.record_input_btn.configure(
            text="Record Inputs (F8)", fg_color="#7b3fa0", hover_color="#9b52c4"
        )
        self._update_status("Stopped")

    def _on_recorded_action(self, action: dict):
        # Called from pynput thread — schedule on UI thread
        self.after(0, self._append_recorded_action, action)

    def _append_recorded_action(self, action: dict):
        # Stop recording if F8 was pressed
        key = action.get("key", "")
        if action.get("type") == "key" and key.upper() == "F8":
            self._stop_input_recording()
            return
        self.actions.append(action)
        self._refresh_action_list()

    def _on_infinite_toggle(self):
        self.repeat_entry.configure(
            state="disabled" if self.infinite_var.get() else "normal"
        )

    def _start_hotkey_recording(self):
        """Enter hotkey recording mode — polls GetAsyncKeyState so it works globally."""
        self._recording_hotkey = True
        self.hotkey_mgr.stop()  # disable so the pressed key doesn't toggle macro
        self.record_hotkey_btn.configure(text="...", state="disabled")
        self.hotkey_label.configure(text="Press a key...")

        def poll_for_key():
            # Wait for all keys to be released first (so we don't instantly capture)
            time.sleep(0.2)
            while self._recording_hotkey:
                for name, vk in VK_MAP.items():
                    if user32.GetAsyncKeyState(vk) & 0x8000:
                        self.after(0, self._finish_hotkey_recording, name)
                        return
                time.sleep(0.05)

        t = threading.Thread(target=poll_for_key, daemon=True)
        t.start()

    def _finish_hotkey_recording(self, name: str):
        """Apply the recorded hotkey and resume normal operation."""
        self._recording_hotkey = False
        self.hotkey = name
        self.hotkey_label.configure(text=name)
        self.record_hotkey_btn.configure(text="Record", state="normal")
        self.start_btn.configure(text=f"Start ({name})")
        self.hotkey_mgr.set_hotkey(name)

    def _on_engine_status(self, status: str):
        # Called from engine thread — schedule on UI thread
        self.after(0, self._update_status, status)

    def _update_status(self, status: str):
        is_running = status.startswith("running")
        self.status_label.configure(
            text=f"Status: {status.capitalize()}",
            text_color="#4ade80" if is_running else "#94a3b8",
        )
        self.start_btn.configure(
            text=f"Stop ({self.hotkey})" if is_running else f"Start ({self.hotkey})",
            fg_color="#aa3333" if is_running else "#2d8a4e",
            hover_color="#cc4444" if is_running else "#36a85c",
        )
        self._update_overlay(is_running)

    # ── File Save / Load ─────────────────────────────────────────────────

    def _save_macro(self):
        from tkinter import filedialog

        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Save Macro",
        )
        if not path:
            return
        repeat = 0 if self.infinite_var.get() else int(self.repeat_var.get() or 1)
        data = {
            "name": self.macro_name,
            "hotkey": self.hotkey,
            "repeat": repeat,
            "actions": self.actions,
        }
        Path(path).write_text(json.dumps(data, indent=2), encoding="utf-8")

    def _load_macro(self):
        from tkinter import filedialog

        path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Load Macro",
        )
        if not path:
            return
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        self.actions = data.get("actions", [])
        self.macro_name = data.get("name", "Untitled")
        hotkey = data.get("hotkey", "F6")
        repeat = data.get("repeat", 1)

        self.hotkey = hotkey
        self.hotkey_label.configure(text=hotkey)
        self.start_btn.configure(text=f"Start ({hotkey})")
        self.hotkey_mgr.set_hotkey(hotkey)

        if repeat == 0:
            self.infinite_var.set(True)
            self._on_infinite_toggle()
        else:
            self.infinite_var.set(False)
            self._on_infinite_toggle()
            self.repeat_var.set(str(repeat))

        self._refresh_action_list()
        self.title(f"AutoMacro — {self.macro_name}")

    # ── Overlay ───────────────────────────────────────────────────────────

    # ── Overlay rendering (PIL for anti-aliasing) ─────────────────────

    OV_DISPLAY = 72       # final display size (50% bigger)
    OV_SCALE = 4          # render at 4x for AA
    OV_RENDER = OV_DISPLAY * OV_SCALE
    OV_RING_WIDTH = 5     # display pixels — thick ring
    OV_BORDER_WIDTH = 0   # no border
    OV_ARC_WIDTH = 4      # sweep width
    OV_STEPS = 24         # frames per full orbit
    OV_FRAME_MS = 18      # ms per frame (~432ms per orbit, 50% slower)

    def _ov_render_base(self) -> Image.Image:
        """Render the static ring with Genshin-style golden border, anti-aliased."""
        S = self.OV_RENDER
        img = Image.new("RGBA", (S, S), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        # Main black ring
        rw = self.OV_RING_WIDTH * self.OV_SCALE
        gap = 2 * self.OV_SCALE  # small margin from edge
        draw.ellipse([gap, gap, S - gap, S - gap],
                      fill=None, outline=(20, 20, 20, 230), width=rw)
        return img.resize((self.OV_DISPLAY, self.OV_DISPLAY), Image.LANCZOS)

    def _ov_render_dot(self, angle_deg: int) -> Image.Image:
        """Render just the green dot at angle_deg (RGBA, render size)."""
        S = self.OV_RENDER
        cx, cy = S // 2, S // 2
        gap = 2 * self.OV_SCALE
        rw = self.OV_RING_WIDTH * self.OV_SCALE
        orbit_r = (S // 2) - gap - rw // 2
        rad = math.radians(angle_deg - 90)
        dx = cx + orbit_r * math.cos(rad)
        dy = cy + orbit_r * math.sin(rad)
        dot_r = rw // 2
        img = Image.new("RGBA", (S, S), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        draw.ellipse([dx - dot_r, dy - dot_r, dx + dot_r, dy + dot_r],
                      fill=(0, 210, 200, 255))
        return img

    def _create_overlay(self):
        TRANS_COLOR = "#010101"
        D = self.OV_DISPLAY

        self._overlay = ctk.CTkToplevel(self)
        self._overlay.overrideredirect(True)
        self._overlay.attributes("-topmost", True)
        self._overlay.attributes("-transparentcolor", TRANS_COLOR)
        self._overlay.geometry(f"{D}x{D}+660+26")
        self._overlay.configure(fg_color=TRANS_COLOR)

        # Make overlay click-through (WS_EX_TRANSPARENT | WS_EX_LAYERED)
        self._overlay.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(self._overlay.winfo_id())
        GWL_EXSTYLE = -20
        WS_EX_LAYERED = 0x80000
        WS_EX_TRANSPARENT = 0x20
        style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
        ctypes.windll.user32.SetWindowLongW(
            hwnd, GWL_EXSTYLE, style | WS_EX_LAYERED | WS_EX_TRANSPARENT
        )

        self._ov_canvas = tk.Canvas(
            self._overlay, width=D, height=D,
            bg=TRANS_COLOR, highlightthickness=0,
        )
        self._ov_canvas.pack()

        # Pre-render the base ring
        self._ov_base = self._ov_render_base()
        self._ov_tk_img = ImageTk.PhotoImage(self._ov_base)
        self._ov_img_id = self._ov_canvas.create_image(
            D // 2, D // 2, image=self._ov_tk_img,
        )

        # Pre-render dot frames at each angle position
        step = 360 // self.OV_STEPS
        self._ov_dot_frames = {}  # angle -> PIL Image (RGBA, render size)
        for i in range(self.OV_STEPS):
            angle = i * step
            self._ov_dot_frames[i] = self._ov_render_dot(angle)

        # Active dots: list of current step indices
        self._ov_active_dots: list[int] = []
        self._ov_ticking = False

        # Note: overlay is click-through, no dragging needed

    def _update_overlay(self, is_running: bool):
        pass

    def _on_engine_action(self):
        self.after(0, self._spawn_dot)

    def _spawn_dot(self):
        """Add a new dot at step 0; start the tick loop if not running."""
        if not hasattr(self, "_ov_canvas"):
            return
        self._ov_active_dots.append(0)
        if not self._ov_ticking:
            self._ov_ticking = True
            self._ov_tick()

    def _ov_tick(self):
        """Advance all active dots one step and composite the frame."""
        # Advance each dot
        new_dots = []
        for step in self._ov_active_dots:
            step += 1
            if step < self.OV_STEPS:
                new_dots.append(step)
            # else: dot completed full orbit, remove it
        self._ov_active_dots = new_dots

        # Composite: base + all active dots
        S = self.OV_RENDER
        combined = self._ov_base.copy() if not new_dots else None
        if new_dots:
            composite = Image.new("RGBA", (S, S), (0, 0, 0, 0))
            for step in new_dots:
                dot_img = self._ov_dot_frames[step]
                composite = Image.alpha_composite(composite, dot_img)
            composite_small = composite.resize(
                (self.OV_DISPLAY, self.OV_DISPLAY), Image.LANCZOS
            )
            combined = self._ov_base.copy()
            combined.paste(composite_small, (0, 0), composite_small)

        self._ov_tk_img = ImageTk.PhotoImage(combined)
        self._ov_canvas.itemconfigure(self._ov_img_id, image=self._ov_tk_img)

        if new_dots:
            self.after(self.OV_FRAME_MS, self._ov_tick)
        else:
            self._ov_ticking = False

    # ── Cleanup ──────────────────────────────────────────────────────────

    def _on_close(self):
        self.engine.stop()
        self.hotkey_mgr.stop()
        self.recorder.stop()
        if hasattr(self, "_overlay"):
            self._overlay.destroy()
        self.destroy()


# ─── Entry Point ─────────────────────────────────────────────────────────────

def is_admin():
    try:
        return ctypes.windll.shell32.IsUserAnAdmin()
    except Exception:
        return False


if __name__ == "__main__":
    # Log file for debugging elevation issues
    log_file = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "automacro.log")

    if not is_admin():
        import subprocess
        # Get the real Python path (not the Windows Store stub)
        try:
            result = subprocess.run(
                ["py", "-c", "import sys; print(sys.executable)"],
                capture_output=True, text=True, timeout=5,
            )
            python_exe = result.stdout.strip()
            # Use pythonw.exe to avoid a console window
            pythonw = python_exe.replace("python.exe", "pythonw.exe")
            if os.path.exists(pythonw):
                python_exe = pythonw
        except Exception:
            python_exe = sys.executable
        script = os.path.abspath(sys.argv[0])
        with open(log_file, "w") as f:
            f.write(f"Elevating...\npython_exe: {python_exe}\nscript: {script}\n")
        ret = ctypes.windll.shell32.ShellExecuteW(
            None, "runas", python_exe, f'"{script}"', os.path.dirname(script), 1
        )
        with open(log_file, "a") as f:
            f.write(f"ShellExecuteW returned: {ret}\n")
        if ret <= 32:
            # Elevation failed or was cancelled, run without admin
            pass
        else:
            sys.exit(0)

    try:
        with open(log_file, "a") as f:
            f.write(f"Admin: {is_admin()}\nStarting app...\n")
        app = AutoMacroApp()
        app.mainloop()
    except Exception as e:
        with open(log_file, "a") as f:
            import traceback
            f.write(f"CRASH:\n{traceback.format_exc()}\n")
        raise

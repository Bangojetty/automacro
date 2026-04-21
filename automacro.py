"""
AutoMacro - Global Keyboard/Mouse Macro App
Sends inputs via Windows SendInput API so they work even when games are in focus.
"""

import ctypes
import ctypes.wintypes as wintypes
import json
import os
import queue
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
KEYEVENTF_UNICODE = 0x0004

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
    **{chr(c): c for c in range(ord("A"), ord("Z") + 1)},
    **{str(i): 0x30 + i for i in range(10)},
    **{f"F{i}": 0x6F + i for i in range(1, 13)},
    "SPACE": 0x20, "ENTER": 0x0D, "TAB": 0x09, "ESCAPE": 0x1B, "ESC": 0x1B,
    "BACKSPACE": 0x08, "DELETE": 0x2E, "INSERT": 0x2D,
    "HOME": 0x24, "END": 0x23, "PAGEUP": 0x21, "PAGEDOWN": 0x22,
    "UP": 0x26, "DOWN": 0x28, "LEFT": 0x25, "RIGHT": 0x27,
    "SHIFT": 0x10, "LSHIFT": 0xA0, "RSHIFT": 0xA1,
    "CTRL": 0x11, "LCTRL": 0xA2, "RCTRL": 0xA3,
    "ALT": 0x12, "LALT": 0xA4, "RALT": 0xA5,
    "CAPSLOCK": 0x14, "NUMLOCK": 0x90, "SCROLLLOCK": 0x91,
    **{f"NUM{i}": 0x60 + i for i in range(10)},
    "MULTIPLY": 0x6A, "ADD": 0x6B, "SUBTRACT": 0x6D,
    "DECIMAL": 0x6E, "DIVIDE": 0x6F,
    "SEMICOLON": 0xBA, "EQUALS": 0xBB, "COMMA": 0xBC,
    "MINUS": 0xBD, "PERIOD": 0xBE, "SLASH": 0xBF,
    "BACKTICK": 0xC0, "LBRACKET": 0xDB, "BACKSLASH": 0xDC,
    "RBRACKET": 0xDD, "QUOTE": 0xDE,
}

VK_REVERSE = {v: k for k, v in VK_MAP.items()}

_LETTERS = sorted(k for k in VK_MAP if len(k) == 1 and k.isalpha())
_DIGITS = sorted(k for k in VK_MAP if len(k) == 1 and k.isdigit())
_FKEYS = [f"F{i}" for i in range(1, 13)]
_MODIFIERS = sorted({"SHIFT", "LSHIFT", "RSHIFT", "CTRL", "LCTRL", "RCTRL", "ALT", "LALT", "RALT"})
_NAVIGATION = sorted({"UP", "DOWN", "LEFT", "RIGHT", "HOME", "END",
                       "PAGEUP", "PAGEDOWN", "INSERT", "DELETE"})
_NUMPAD = [f"NUM{i}" for i in range(10)] + sorted(
    {"MULTIPLY", "ADD", "SUBTRACT", "DECIMAL", "DIVIDE"})
_OTHER = sorted(set(VK_MAP.keys()) - set(_LETTERS) - set(_DIGITS) - set(_FKEYS)
                - set(_MODIFIERS) - set(_NAVIGATION) - set(_NUMPAD))
ALL_KEY_NAMES = _LETTERS + _DIGITS + _FKEYS + _MODIFIERS + _NAVIGATION + _NUMPAD + _OTHER

# Modifier key names used for combo detection
_MODIFIER_NAMES = frozenset({"CTRL", "LCTRL", "RCTRL", "SHIFT", "LSHIFT", "RSHIFT",
                              "ALT", "LALT", "RALT"})


def vk_for_key(name: str) -> int | None:
    return VK_MAP.get(name.upper())


def combo_display(keys: list[str]) -> str:
    """Human-readable combo string, e.g. ['LCTRL', 'C'] → 'Ctrl+C'."""
    parts = []
    for k in keys:
        ku = k.upper()
        if ku in ("CTRL", "LCTRL", "RCTRL"):
            parts.append("Ctrl")
        elif ku in ("SHIFT", "LSHIFT", "RSHIFT"):
            parts.append("Shift")
        elif ku in ("ALT", "LALT", "RALT"):
            parts.append("Alt")
        else:
            parts.append(ku)
    return "+".join(parts)


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
    def send_combo(keys: list[str]):
        """Press modifier keys, tap the final key, release modifiers."""
        vks = [vk_for_key(k) for k in keys]
        vks = [v for v in vks if v is not None]
        if not vks:
            return
        # Hold all but the last, tap the last, then release in reverse
        for vk in vks[:-1]:
            InputSimulator.send_key_down(vk)
            time.sleep(0.005)
        InputSimulator.send_key_tap(vks[-1])
        for vk in reversed(vks[:-1]):
            InputSimulator.send_key_up(vk)
            time.sleep(0.005)

    @staticmethod
    def send_string(text: str):
        for char in text:
            code = ord(char)
            down = INPUT()
            down.type = INPUT_KEYBOARD
            down.union.ki.wVk = 0
            down.union.ki.wScan = code
            down.union.ki.dwFlags = KEYEVENTF_UNICODE

            up = INPUT()
            up.type = INPUT_KEYBOARD
            up.union.ki.wVk = 0
            up.union.ki.wScan = code
            up.union.ki.dwFlags = KEYEVENTF_UNICODE | KEYEVENTF_KEYUP

            InputSimulator._send([down, up])
            time.sleep(0.005)

    @staticmethod
    def send_mouse_click(x: int, y: int, button: str = "left"):
        screen_w = user32.GetSystemMetrics(SM_CXSCREEN)
        screen_h = user32.GetSystemMetrics(SM_CYSCREEN)
        abs_x = int(x * 65535 / screen_w)
        abs_y = int(y * 65535 / screen_h)

        if button == "right":
            down_flag, up_flag = MOUSEEVENTF_RIGHTDOWN, MOUSEEVENTF_RIGHTUP
        elif button == "middle":
            down_flag, up_flag = MOUSEEVENTF_MIDDLEDOWN, MOUSEEVENTF_MIDDLEUP
        else:
            down_flag, up_flag = MOUSEEVENTF_LEFTDOWN, MOUSEEVENTF_LEFTUP

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
    """Capture live keyboard and mouse events and build an action list.

    Multi-key combos: when a modifier (Ctrl/Shift/Alt) is held while a
    non-modifier key is pressed, they are grouped into a single combo action
    instead of being recorded as separate key presses.
    """

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
        self._on_action = on_action
        self._stop_key = stop_key.upper()
        self._kb_listener = None
        self._mouse_listener = None
        self._last_time = None
        self.recording = False
        self._held_modifiers: set[str] = set()   # modifiers currently down
        self._used_in_combo: set[str] = set()    # modifiers already consumed by a combo

    def start(self):
        self.recording = True
        self._last_time = time.monotonic()
        self._held_modifiers.clear()
        self._used_in_combo.clear()
        self._kb_listener = pynput_kb.Listener(
            on_press=self._on_key_press,
            on_release=self._on_key_release,
            suppress=False,
        )
        self._mouse_listener = pynput_mouse.Listener(
            on_click=self._on_mouse_click, suppress=False
        )
        self._kb_listener.start()
        self._mouse_listener.start()

    def stop(self):
        self.recording = False
        self._held_modifiers.clear()
        self._used_in_combo.clear()
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
        name_upper = name.upper()

        if name_upper == self._stop_key:
            return

        if name_upper in _MODIFIER_NAMES:
            # Track but don't emit yet — wait to see if used in a combo
            self._held_modifiers.add(name_upper)
        else:
            delay = self._elapsed_ms()
            if self._held_modifiers:
                # Group held modifiers + this key into a combo
                # Order: Ctrl, Shift, Alt, then the main key
                ordered_mods = _order_modifiers(self._held_modifiers)
                keys = ordered_mods + [name_upper]
                self._emit({"type": "combo", "keys": keys, "delay": delay})
                self._used_in_combo.update(self._held_modifiers)
            else:
                self._emit({"type": "key", "key": name_upper, "action": "tap", "delay": delay})

    def _on_key_release(self, key):
        if not self.recording:
            return
        name = self._resolve_key(key)
        if name is None:
            return
        name_upper = name.upper()
        if name_upper in _MODIFIER_NAMES:
            if name_upper not in self._used_in_combo:
                # Standalone modifier press (not part of any combo) — emit it now
                delay = self._elapsed_ms()
                self._emit({"type": "key", "key": name_upper, "action": "tap", "delay": delay})
            self._held_modifiers.discard(name_upper)
            self._used_in_combo.discard(name_upper)

    def _on_mouse_click(self, x, y, button, pressed):
        if not self.recording or not pressed:
            return
        delay = self._elapsed_ms()
        btn_name = "right" if button == pynput_mouse.Button.right else (
            "middle" if button == pynput_mouse.Button.middle else "left"
        )
        self._emit({"type": "click", "x": x, "y": y, "button": btn_name, "delay": delay})

    def _resolve_key(self, key) -> str | None:
        name = self._PYNPUT_KEY_MAP.get(key)
        if name:
            return name
        try:
            char = key.char
            if char and char.upper() in VK_MAP:
                return char.upper()
        except AttributeError:
            pass
        return None


def _order_modifiers(mods: set[str]) -> list[str]:
    """Return modifiers in a canonical order: Ctrl, Shift, Alt."""
    order = ["CTRL", "LCTRL", "RCTRL", "SHIFT", "LSHIFT", "RSHIFT", "ALT", "LALT", "RALT"]
    return [m for m in order if m in mods]


# ─── MacroEngine ─────────────────────────────────────────────────────────────

class MacroEngine:
    """Execute a list of macro actions in a background thread."""

    def __init__(self, on_status=None, on_action=None):
        self._thread: threading.Thread | None = None
        self._stop_event = threading.Event()
        self._on_status = on_status
        self._on_action = on_action
        self.running = False

    def start(self, actions: list[dict], repeat: int):
        if self.running:
            return
        self._stop_event.clear()
        self.running = True
        self._thread = threading.Thread(target=self._run, args=(actions, repeat), daemon=True)
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
                    action_repeat = max(1, action.get("repeat", 1))
                    for _ in range(action_repeat):
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
        elif atype == "combo":
            InputSimulator.send_combo(action.get("keys", []))
        elif atype == "click":
            InputSimulator.send_mouse_click(action["x"], action["y"], action.get("button", "left"))
        elif atype == "delay":
            extra = action.get("delay", 0)
            if extra > 0:
                self._interruptible_sleep(extra / 1000.0)
        elif atype == "type_string":
            InputSimulator.send_string(action.get("text", ""))

    def _interruptible_sleep(self, seconds: float):
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            if self._stop_event.is_set():
                return
            time.sleep(min(0.05, end - time.monotonic()))


# ─── GlobalHotkeyManager ────────────────────────────────────────────────────

class GlobalHotkeyManager:
    """Single OS-level global hotkey via RegisterHotKey."""

    HOTKEY_ID = 1

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
            if self._thread and self._thread.is_alive():
                tid = getattr(self, "_thread_id", None)
                if tid:
                    user32.PostThreadMessageW(tid, 0x0012, 0, 0)
            self._thread = None

    def _hotkey_thread(self):
        self._thread_id = kernel32.GetCurrentThreadId()
        if not user32.RegisterHotKey(None, self.HOTKEY_ID, 0, self._vk):
            return
        try:
            msg = wintypes.MSG()
            while self._running:
                ret = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if ret <= 0:
                    break
                if msg.message == 0x0312:
                    self._callback()
        finally:
            user32.UnregisterHotKey(None, self.HOTKEY_ID)


# ─── MultiHotkeyManager ──────────────────────────────────────────────────────

class MultiHotkeyManager:
    """Manage N independent global hotkeys in a single message-loop thread."""

    _BASE_ID = 100

    def __init__(self):
        self._callbacks: dict[int, callable] = {}
        self._next_id = self._BASE_ID
        self._cmd_q: queue.Queue = queue.Queue()
        self._thread_id: int | None = None
        self._running = True
        self._ready = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()
        self._ready.wait(timeout=2.0)

    def register(self, hotkey: str, callback) -> int:
        vk = vk_for_key(hotkey)
        if vk is None:
            return -1
        hid = self._next_id
        self._next_id += 1
        self._callbacks[hid] = callback
        self._cmd_q.put(("reg", hid, vk))
        self._wake()
        return hid

    def unregister(self, hid: int):
        self._callbacks.pop(hid, None)
        self._cmd_q.put(("unreg", hid))
        self._wake()

    def unregister_all(self):
        for hid in list(self._callbacks.keys()):
            self.unregister(hid)

    def stop(self):
        self._running = False
        self._wake()

    def _wake(self):
        if self._thread_id:
            user32.PostThreadMessageW(self._thread_id, 0x0400, 0, 0)

    def _drain(self, registered: dict):
        while True:
            try:
                cmd = self._cmd_q.get_nowait()
            except queue.Empty:
                break
            if cmd[0] == "reg":
                _, hid, vk = cmd
                user32.RegisterHotKey(None, hid, 0, vk)
                registered[hid] = vk
            elif cmd[0] == "unreg":
                _, hid = cmd
                user32.UnregisterHotKey(None, hid)
                registered.pop(hid, None)

    def _loop(self):
        self._thread_id = kernel32.GetCurrentThreadId()
        self._ready.set()
        registered: dict[int, int] = {}
        try:
            msg = wintypes.MSG()
            while self._running:
                self._drain(registered)
                ret = user32.GetMessageW(ctypes.byref(msg), None, 0, 0)
                if ret <= 0:
                    break
                if msg.message == 0x0312:
                    hid = msg.wParam
                    cb = self._callbacks.get(hid)
                    if cb:
                        threading.Thread(target=cb, daemon=True).start()
        finally:
            for hid in list(registered.keys()):
                user32.UnregisterHotKey(None, hid)


# ─── UI ──────────────────────────────────────────────────────────────────────

class AutoMacroApp(ctk.CTk):
    PRESETS_DIR = Path(__file__).parent / "presets"

    def __init__(self):
        super().__init__()
        self.title("AutoMacro")
        self.geometry("820x720")
        self.minsize(720, 550)
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.PRESETS_DIR.mkdir(exist_ok=True)

        self.actions: list[dict] = []
        self.hotkey = "F6"
        self.macro_name = "Untitled"

        self._recording_hotkey = False
        self._input_recording = False

        self.engine = MacroEngine(on_status=self._on_engine_status,
                                   on_action=self._on_engine_action)
        self.hotkey_mgr = GlobalHotkeyManager(self.hotkey, self._toggle_macro)
        self.recorder = InputRecorder(on_action=self._on_recorded_action, stop_key="F8")
        self.action_hotkey_mgr = MultiHotkeyManager()
        self._action_hids: list[int] = []

        self._build_ui()
        self._create_overlay()
        self._refresh_action_list()
        self._update_status("Stopped")
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ── UI Construction ──────────────────────────────────────────────────

    def _build_ui(self):
        outer = ctk.CTkFrame(self, fg_color="transparent")
        outer.pack(fill="both", expand=True)

        sidebar = ctk.CTkFrame(outer, width=150, corner_radius=0)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)

        ctk.CTkLabel(sidebar, text="AutoMacro", font=("", 15, "bold")).pack(pady=(20, 30))

        self._tab_buttons: dict[str, ctk.CTkButton] = {}
        self._tab_frames: dict[str, ctk.CTkFrame] = {}

        for name, label in [("macro", "  Macro"), ("presets", "  Presets")]:
            btn = ctk.CTkButton(
                sidebar, text=label, width=130, height=38,
                fg_color="transparent", hover_color="#2a2d2e",
                anchor="w", font=("", 13),
                command=lambda n=name: self._switch_tab(n),
            )
            btn.pack(pady=3, padx=10)
            self._tab_buttons[name] = btn

        content = ctk.CTkFrame(outer, fg_color="transparent")
        content.pack(side="left", fill="both", expand=True, padx=10, pady=10)

        macro_frame = ctk.CTkFrame(content)
        self._tab_frames["macro"] = macro_frame
        self._build_macro_tab(macro_frame)

        presets_frame = ctk.CTkFrame(content)
        self._tab_frames["presets"] = presets_frame
        self._build_presets_tab(presets_frame)

        self._switch_tab("macro")

    def _switch_tab(self, name: str):
        for f in self._tab_frames.values():
            f.pack_forget()
        self._tab_frames[name].pack(fill="both", expand=True)
        for n, btn in self._tab_buttons.items():
            active = n == name
            btn.configure(
                fg_color="#1f6aa5" if active else "transparent",
                hover_color="#1a5a8f" if active else "#2a2d2e",
            )
        if name == "presets":
            self._refresh_presets()

    def _build_macro_tab(self, parent):
        name_row = ctk.CTkFrame(parent, fg_color="transparent")
        name_row.pack(fill="x", padx=10, pady=(10, 4))
        ctk.CTkLabel(name_row, text="Name:", width=50).pack(side="left")
        self.name_var = ctk.StringVar(value=self.macro_name)
        ctk.CTkEntry(name_row, textvariable=self.name_var, width=220).pack(side="left", padx=6)

        # Default delay — top-right
        ctk.CTkLabel(name_row, text="Default delay (ms):").pack(side="right", padx=(6, 0))
        self.default_delay_var = ctk.StringVar(value="100")
        ctk.CTkEntry(name_row, textvariable=self.default_delay_var, width=70).pack(side="right")

        ctk.CTkLabel(parent, text="Actions", font=("", 15, "bold"), anchor="w").pack(
            fill="x", padx=10, pady=(4, 2)
        )

        self.action_frame = ctk.CTkScrollableFrame(parent, height=260)
        self.action_frame.pack(fill="both", expand=True, padx=10, pady=(0, 8))

        # Add buttons — row 1
        btn_row1 = ctk.CTkFrame(parent, fg_color="transparent")
        btn_row1.pack(fill="x", padx=10, pady=(0, 4))
        ctk.CTkButton(btn_row1, text="Add Key", width=95,
                       command=self._dlg_add_key).pack(side="left", padx=(0, 4))
        ctk.CTkButton(btn_row1, text="Add Combo", width=100,
                       command=self._dlg_add_combo).pack(side="left", padx=(0, 4))
        ctk.CTkButton(btn_row1, text="Add Click", width=95,
                       command=self._dlg_add_click).pack(side="left", padx=(0, 4))
        ctk.CTkButton(btn_row1, text="Add Delay", width=95,
                       command=self._dlg_add_delay).pack(side="left", padx=(0, 4))
        ctk.CTkButton(btn_row1, text="Add Text", width=90,
                       command=self._dlg_add_string).pack(side="left", padx=(0, 4))

        # Add buttons — row 2
        btn_row2 = ctk.CTkFrame(parent, fg_color="transparent")
        btn_row2.pack(fill="x", padx=10, pady=(0, 8))
        self.record_input_btn = ctk.CTkButton(
            btn_row2, text="Record Inputs (F8)", width=160,
            fg_color="#7b3fa0", hover_color="#9b52c4",
            command=self._toggle_input_recording,
        )
        self.record_input_btn.pack(side="left", padx=(0, 4))
        ctk.CTkButton(btn_row2, text="Clear All", width=90,
                       fg_color="#aa3333", hover_color="#cc4444",
                       command=self._clear_actions).pack(side="left")

        ctrl1 = ctk.CTkFrame(parent)
        ctrl1.pack(fill="x", padx=10, pady=(0, 6))

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

        ctrl2 = ctk.CTkFrame(parent, fg_color="transparent")
        ctrl2.pack(fill="x", padx=10, pady=(0, 6))
        self.start_btn = ctk.CTkButton(
            ctrl2, text="Start (F6)", height=36,
            fg_color="#2d8a4e", hover_color="#36a85c",
            command=self._toggle_macro,
        )
        self.start_btn.pack(fill="x")

        self.status_label = ctk.CTkLabel(parent, text="Stopped", anchor="w", font=("", 12))
        self.status_label.pack(fill="x", padx=10)

    def _build_presets_tab(self, parent):
        header = ctk.CTkFrame(parent, fg_color="transparent")
        header.pack(fill="x", padx=10, pady=(12, 8))
        ctk.CTkLabel(header, text="Presets", font=("", 15, "bold")).pack(side="left")
        ctk.CTkButton(header, text="Save Current", width=120,
                       command=self._save_preset).pack(side="right")

        self.preset_frame = ctk.CTkScrollableFrame(parent)
        self.preset_frame.pack(fill="both", expand=True, padx=10, pady=(0, 10))

    # ── Presets ──────────────────────────────────────────────────────────

    def _refresh_presets(self):
        for w in self.preset_frame.winfo_children():
            w.destroy()
        files = sorted(self.PRESETS_DIR.glob("*.json"))
        if not files:
            ctk.CTkLabel(self.preset_frame, text="No presets saved yet.",
                          text_color="gray").pack(pady=20)
            return
        for path in files:
            row = ctk.CTkFrame(self.preset_frame)
            row.pack(fill="x", pady=3, padx=2)
            ctk.CTkLabel(row, text=path.stem, anchor="w", font=("", 13)).pack(
                side="left", fill="x", expand=True, padx=10)
            ctk.CTkButton(row, text="Load", width=70,
                           command=lambda p=path: self._load_preset_file(p)).pack(
                side="left", padx=4)
            ctk.CTkButton(row, text="\u2715", width=32, height=28,
                           fg_color="#aa3333", hover_color="#cc4444",
                           command=lambda p=path: self._delete_preset(p)).pack(
                side="left", padx=(0, 6))

    def _save_preset(self):
        name = self.name_var.get().strip() or "Untitled"
        safe = "".join(c if c.isalnum() or c in " _-" else "_" for c in name)
        path = self.PRESETS_DIR / f"{safe}.json"
        repeat = 0 if self.infinite_var.get() else int(self.repeat_var.get() or 1)
        data = {"name": name, "hotkey": self.hotkey, "repeat": repeat, "actions": self.actions}
        path.write_text(json.dumps(data, indent=2), encoding="utf-8")
        self._switch_tab("presets")

    def _load_preset_file(self, path: Path):
        data = json.loads(path.read_text(encoding="utf-8"))
        self._apply_macro_data(data)
        self._switch_tab("macro")

    def _delete_preset(self, path: Path):
        path.unlink(missing_ok=True)
        self._refresh_presets()

    def _apply_macro_data(self, data: dict):
        self.actions = data.get("actions", [])
        name = data.get("name", "Untitled")
        hotkey = data.get("hotkey", "F6")
        repeat = data.get("repeat", 1)

        self.macro_name = name
        self.name_var.set(name)
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

    # ── Action List Rendering ────────────────────────────────────────────

    def _refresh_action_list(self):
        for w in self.action_frame.winfo_children():
            w.destroy()

        self._rebuild_action_hotkeys()

        if not self.actions:
            ctk.CTkLabel(self.action_frame, text="No actions yet. Add some above.",
                          text_color="gray").pack(pady=20)
            return

        for i, action in enumerate(self.actions):
            row = ctk.CTkFrame(self.action_frame)
            row.pack(fill="x", pady=2, padx=2)

            def bind_dblclick(widget, idx=i):
                widget.bind("<Double-Button-1>", lambda e, j=idx: self._edit_action(j))
                for child in widget.winfo_children():
                    bind_dblclick(child, idx)

            ctk.CTkLabel(row, text=f"#{i+1}", width=30, font=("", 12, "bold")).pack(
                side="left", padx=(5, 3))

            desc = self._describe_action(action)
            ctk.CTkLabel(row, text=desc, anchor="w").pack(side="left", fill="x", expand=True)

            delay = action.get("delay", 0)
            ctk.CTkLabel(row, text=f"{delay}ms", width=55, text_color="gray").pack(
                side="left", padx=3)

            bind_dblclick(row)

            ctk.CTkButton(
                row, text="\u25b6", width=28, height=28,
                fg_color="#2d6a8a", hover_color="#3a85ad",
                command=lambda a=action: self._run_single_action(a),
            ).pack(side="left", padx=1)

            hk = action.get("hotkey", "")
            ctk.CTkButton(
                row, text=hk if hk else "+", width=46, height=28,
                fg_color="#2d5a2d" if hk else "#3a3a3a",
                hover_color="#3a7a3a" if hk else "#4a4a4a",
                font=("", 11),
                command=lambda idx=i: self._record_action_hotkey(idx),
            ).pack(side="left", padx=1)

            if i > 0:
                ctk.CTkButton(
                    row, text="\u25b2", width=28, height=28,
                    command=lambda idx=i: self._move_action(idx, -1),
                ).pack(side="left", padx=1)
            if i < len(self.actions) - 1:
                ctk.CTkButton(
                    row, text="\u25bc", width=28, height=28,
                    command=lambda idx=i: self._move_action(idx, 1),
                ).pack(side="left", padx=1)
            ctk.CTkButton(
                row, text="\u2715", width=28, height=28,
                fg_color="#aa3333", hover_color="#cc4444",
                command=lambda idx=i: self._delete_action(idx),
            ).pack(side="left", padx=(1, 5))

    @staticmethod
    def _describe_action(action: dict) -> str:
        atype = action.get("type")
        r = action.get("repeat", 1)
        suffix = f"  ×{r}" if r > 1 else ""
        if atype == "key":
            return f"Key: {action['key'].upper()}  ({action.get('action', 'tap')}){suffix}"
        elif atype == "combo":
            return f"Combo: {combo_display(action.get('keys', []))}{suffix}"
        elif atype == "click":
            return f"Click: ({action['x']}, {action['y']})  {action.get('button', 'left')}{suffix}"
        elif atype == "delay":
            return f"Delay: {action.get('delay', 0)} ms{suffix}"
        elif atype == "type_string":
            text = action.get("text", "")
            preview = text[:28] + ("..." if len(text) > 28 else "")
            return f'Text: "{preview}"{suffix}'
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

    def _default_delay(self) -> int:
        try:
            return max(0, int(self.default_delay_var.get()))
        except (ValueError, AttributeError):
            return 100

    # ── Single-action trigger ────────────────────────────────────────────

    def _run_single_action(self, action: dict):
        MacroEngine().start([action], 1)

    # ── Per-action hotkeys ───────────────────────────────────────────────

    def _rebuild_action_hotkeys(self):
        self.action_hotkey_mgr.unregister_all()
        self._action_hids = []
        for action in self.actions:
            hk = action.get("hotkey", "")
            if hk:
                hid = self.action_hotkey_mgr.register(
                    hk, lambda a=action: self._run_single_action(a)
                )
                self._action_hids.append(hid)
            else:
                self._action_hids.append(-1)

    def _record_action_hotkey(self, index: int):
        action = self.actions[index]
        current = action.get("hotkey", "")

        dlg = ctk.CTkToplevel(self)
        dlg.title("Action Hotkey")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Press a key to assign, or clear:", font=("", 12)).pack(pady=(18, 6))
        display_var = ctk.StringVar(value=current if current else "— none —")
        ctk.CTkLabel(dlg, textvariable=display_var, font=("", 14, "bold")).pack(pady=4)

        captured = {"key": current}

        def start_capture():
            display_var.set("Press any key...")
            capture_btn.configure(state="disabled")

            def poll():
                time.sleep(0.15)
                for name, vk in VK_MAP.items():
                    if user32.GetAsyncKeyState(vk) & 0x8000:
                        captured["key"] = name
                        dlg.after(0, lambda n=name: display_var.set(n))
                        dlg.after(0, lambda: capture_btn.configure(state="normal"))
                        return
                threading.Thread(target=poll, daemon=True).start()

            threading.Thread(target=poll, daemon=True).start()

        btn_row = ctk.CTkFrame(dlg, fg_color="transparent")
        btn_row.pack(pady=10)

        capture_btn = ctk.CTkButton(btn_row, text="Record Key", width=110, command=start_capture)
        capture_btn.pack(side="left", padx=4)

        def save():
            self.actions[index]["hotkey"] = captured["key"]
            self._refresh_action_list()
            dlg.destroy()

        def clear():
            self.actions[index].pop("hotkey", None)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(btn_row, text="Save", width=70, command=save).pack(side="left", padx=4)
        ctk.CTkButton(btn_row, text="Clear", width=60, fg_color="#aa3333",
                       hover_color="#cc4444", command=clear).pack(side="left", padx=4)

    # ── Dialogs ──────────────────────────────────────────────────────────

    def _edit_action(self, index: int):
        atype = self.actions[index].get("type")
        dispatch = {
            "key": self._dlg_add_key,
            "combo": self._dlg_add_combo,
            "click": self._dlg_add_click,
            "delay": self._dlg_add_delay,
            "type_string": self._dlg_add_string,
        }
        fn = dispatch.get(atype)
        if fn:
            fn(edit_index=index)

    def _dlg_add_combo(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}
        ex_keys: list[str] = existing.get("keys", [])

        # Parse existing keys into modifiers + main key
        ex_mods = {k.upper() for k in ex_keys if k.upper() in _MODIFIER_NAMES}
        ex_main = next((k for k in ex_keys if k.upper() not in _MODIFIER_NAMES), "A")

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Combo" if editing else "Add Combo")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Modifiers:", anchor="w").pack(fill="x", padx=20, pady=(14, 4))

        mod_frame = ctk.CTkFrame(dlg, fg_color="transparent")
        mod_frame.pack(fill="x", padx=20)

        ctrl_var = ctk.BooleanVar(value=any(m in ex_mods for m in ("CTRL", "LCTRL", "RCTRL")))
        shift_var = ctk.BooleanVar(value=any(m in ex_mods for m in ("SHIFT", "LSHIFT", "RSHIFT")))
        alt_var = ctk.BooleanVar(value=any(m in ex_mods for m in ("ALT", "LALT", "RALT")))

        ctk.CTkCheckBox(mod_frame, text="Ctrl", variable=ctrl_var).pack(side="left", padx=(0, 12))
        ctk.CTkCheckBox(mod_frame, text="Shift", variable=shift_var).pack(side="left", padx=(0, 12))
        ctk.CTkCheckBox(mod_frame, text="Alt", variable=alt_var).pack(side="left")

        ctk.CTkLabel(dlg, text="Main key:", anchor="w").pack(fill="x", padx=20, pady=(14, 4))
        main_var = ctk.StringVar(value=ex_main)
        ctk.CTkComboBox(dlg, values=ALL_KEY_NAMES, variable=main_var, width=280).pack(padx=20)

        # Live preview
        preview_var = ctk.StringVar()

        def update_preview(*_):
            parts = []
            if ctrl_var.get():
                parts.append("Ctrl")
            if shift_var.get():
                parts.append("Shift")
            if alt_var.get():
                parts.append("Alt")
            parts.append(main_var.get().upper())
            preview_var.set("+".join(parts))

        ctrl_var.trace_add("write", update_preview)
        shift_var.trace_add("write", update_preview)
        alt_var.trace_add("write", update_preview)
        main_var.trace_add("write", update_preview)
        update_preview()

        ctk.CTkLabel(dlg, textvariable=preview_var, font=("", 14, "bold"),
                      text_color="#4ade80").pack(pady=8)

        ctk.CTkLabel(dlg, text="Repeat:", anchor="w").pack(fill="x", padx=20)
        repeat_var = ctk.StringVar(value=str(existing.get("repeat", 1)))
        ctk.CTkEntry(dlg, textvariable=repeat_var, width=280).pack(padx=20, pady=4)

        ctk.CTkLabel(dlg, text="Delay after (ms):", anchor="w").pack(fill="x", padx=20)
        delay_var = ctk.StringVar(value=str(existing.get("delay", self._default_delay())))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=280).pack(padx=20, pady=4)

        def submit():
            keys = []
            if ctrl_var.get():
                keys.append("CTRL")
            if shift_var.get():
                keys.append("SHIFT")
            if alt_var.get():
                keys.append("ALT")
            keys.append(main_var.get().upper())
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 50
            try:
                repeat = max(1, int(repeat_var.get()))
            except ValueError:
                repeat = 1
            new_action = {"type": "combo", "keys": keys, "delay": max(0, delay), "repeat": repeat}
            if editing:
                if existing.get("hotkey"):
                    new_action["hotkey"] = existing["hotkey"]
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=10)

    def _dlg_add_key(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Key Press" if editing else "Add Key Press")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        captured = {"key": existing.get("key", "")}

        # Key capture area
        ctk.CTkLabel(dlg, text="Key:").pack(pady=(15, 0))
        key_display = ctk.CTkLabel(
            dlg, text=captured["key"] if captured["key"] else "— none —",
            font=("", 14, "bold"), width=200,
        )
        key_display.pack(pady=(4, 2))

        record_btn = ctk.CTkButton(dlg, text="Press a Key to Record", width=200)
        record_btn.pack(pady=(0, 8))

        def start_key_capture():
            record_btn.configure(text="Listening...", state="disabled")
            key_display.configure(text="Press any key...")

            def poll():
                time.sleep(0.15)
                for name, vk in VK_MAP.items():
                    if user32.GetAsyncKeyState(vk) & 0x8000:
                        captured["key"] = name
                        dlg.after(0, lambda n=name: key_display.configure(text=n))
                        dlg.after(0, lambda: record_btn.configure(
                            text="Press a Key to Record", state="normal"))
                        return
                threading.Thread(target=poll, daemon=True).start()

            threading.Thread(target=poll, daemon=True).start()

        record_btn.configure(command=start_key_capture)

        ctk.CTkLabel(dlg, text="Action:").pack()
        action_var = ctk.StringVar(value=existing.get("action", "tap"))
        ctk.CTkComboBox(dlg, values=["tap", "press", "release"],
                         variable=action_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Repeat:").pack()
        repeat_var = ctk.StringVar(value=str(existing.get("repeat", 1)))
        ctk.CTkEntry(dlg, textvariable=repeat_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay after (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", self._default_delay())))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            if not captured["key"]:
                return
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 100
            try:
                repeat = max(1, int(repeat_var.get()))
            except ValueError:
                repeat = 1
            new_action = {
                "type": "key", "key": captured["key"],
                "action": action_var.get(), "delay": max(0, delay), "repeat": repeat,
            }
            if editing and existing.get("hotkey"):
                new_action["hotkey"] = existing["hotkey"]
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
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        coord_frame = ctk.CTkFrame(dlg, fg_color="transparent")
        coord_frame.pack(pady=(15, 5))

        ctk.CTkLabel(coord_frame, text="X:").pack(side="left", padx=(0, 5))
        x_var = ctk.StringVar(value=str(existing.get("x", 0)))
        ctk.CTkEntry(coord_frame, textvariable=x_var, width=70).pack(side="left", padx=(0, 15))
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

        ctk.CTkButton(dlg, text="Pick from Screen", command=pick_position).pack(pady=5)

        ctk.CTkLabel(dlg, text="Button:").pack()
        btn_var = ctk.StringVar(value=existing.get("button", "left"))
        ctk.CTkComboBox(dlg, values=["left", "right", "middle"],
                         variable=btn_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Repeat:").pack()
        repeat_var = ctk.StringVar(value=str(existing.get("repeat", 1)))
        ctk.CTkEntry(dlg, textvariable=repeat_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay after (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", self._default_delay())))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            try:
                x, y = int(x_var.get()), int(y_var.get())
                delay = int(delay_var.get())
            except ValueError:
                x, y, delay = 0, 0, 200
            try:
                repeat = max(1, int(repeat_var.get()))
            except ValueError:
                repeat = 1
            new_action = {
                "type": "click", "x": x, "y": y,
                "button": btn_var.get(), "delay": max(0, delay), "repeat": repeat,
            }
            if editing and existing.get("hotkey"):
                new_action["hotkey"] = existing["hotkey"]
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
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Repeat:").pack(pady=(20, 0))
        repeat_var = ctk.StringVar(value=str(existing.get("repeat", 1)))
        ctk.CTkEntry(dlg, textvariable=repeat_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", self._default_delay())))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 500
            try:
                repeat = max(1, int(repeat_var.get()))
            except ValueError:
                repeat = 1
            new_action = {"type": "delay", "delay": max(0, delay), "repeat": repeat}
            if editing and existing.get("hotkey"):
                new_action["hotkey"] = existing["hotkey"]
            if editing:
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=10)

    def _dlg_add_string(self, edit_index: int | None = None):
        editing = edit_index is not None
        existing = self.actions[edit_index] if editing else {}

        dlg = ctk.CTkToplevel(self)
        dlg.title("Edit Text" if editing else "Add Text")
        dlg.resizable(False, False)
        dlg.transient(self)
        dlg.grab_set()

        ctk.CTkLabel(dlg, text="Text to type:").pack(pady=(15, 0))
        text_box = ctk.CTkTextbox(dlg, width=340, height=80)
        text_box.pack(pady=5, padx=20)
        text_box.insert("0.0", existing.get("text", ""))

        ctk.CTkLabel(dlg, text="Repeat:").pack()
        repeat_var = ctk.StringVar(value=str(existing.get("repeat", 1)))
        ctk.CTkEntry(dlg, textvariable=repeat_var, width=200).pack(pady=5)

        ctk.CTkLabel(dlg, text="Delay after (ms):").pack()
        delay_var = ctk.StringVar(value=str(existing.get("delay", self._default_delay())))
        ctk.CTkEntry(dlg, textvariable=delay_var, width=200).pack(pady=5)

        def submit():
            text = text_box.get("0.0", "end").rstrip("\n")
            try:
                delay = int(delay_var.get())
            except ValueError:
                delay = 0
            try:
                repeat = max(1, int(repeat_var.get()))
            except ValueError:
                repeat = 1
            new_action = {"type": "type_string", "text": text, "delay": max(0, delay), "repeat": repeat}
            if editing and existing.get("hotkey"):
                new_action["hotkey"] = existing["hotkey"]
            if editing:
                self.actions[edit_index] = new_action
            else:
                self.actions.append(new_action)
            self._refresh_action_list()
            dlg.destroy()

        ctk.CTkButton(dlg, text="Save" if editing else "Add", command=submit).pack(pady=8)

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
        self.after(0, self._append_recorded_action, action)

    def _append_recorded_action(self, action: dict):
        if action.get("type") == "key" and action.get("key", "").upper() == "F8":
            self._stop_input_recording()
            return
        self.actions.append(action)
        self._refresh_action_list()

    def _on_infinite_toggle(self):
        self.repeat_entry.configure(
            state="disabled" if self.infinite_var.get() else "normal"
        )

    def _start_hotkey_recording(self):
        self._recording_hotkey = True
        self.hotkey_mgr.stop()
        self.record_hotkey_btn.configure(text="...", state="disabled")
        self.hotkey_label.configure(text="Press a key...")

        def poll_for_key():
            time.sleep(0.2)
            while self._recording_hotkey:
                for name, vk in VK_MAP.items():
                    if user32.GetAsyncKeyState(vk) & 0x8000:
                        self.after(0, self._finish_hotkey_recording, name)
                        return
                time.sleep(0.05)

        threading.Thread(target=poll_for_key, daemon=True).start()

    def _finish_hotkey_recording(self, name: str):
        self._recording_hotkey = False
        self.hotkey = name
        self.hotkey_label.configure(text=name)
        self.record_hotkey_btn.configure(text="Record", state="normal")
        self.start_btn.configure(text=f"Start ({name})")
        self.hotkey_mgr.set_hotkey(name)

    def _on_engine_status(self, status: str):
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

    # ── Overlay ───────────────────────────────────────────────────────────

    OV_DISPLAY = 72
    OV_SCALE = 4
    OV_RENDER = OV_DISPLAY * OV_SCALE
    OV_RING_WIDTH = 5
    OV_STEPS = 24
    OV_FRAME_MS = 18

    def _ov_render_base(self) -> Image.Image:
        S = self.OV_RENDER
        img = Image.new("RGBA", (S, S), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        rw = self.OV_RING_WIDTH * self.OV_SCALE
        gap = 2 * self.OV_SCALE
        draw.ellipse([gap, gap, S - gap, S - gap],
                      fill=None, outline=(20, 20, 20, 230), width=rw)
        return img.resize((self.OV_DISPLAY, self.OV_DISPLAY), Image.LANCZOS)

    def _ov_render_dot(self, angle_deg: int) -> Image.Image:
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
        self._overlay.geometry(f"{D}x{D}+830+26")
        self._overlay.configure(fg_color=TRANS_COLOR)

        self._overlay.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(self._overlay.winfo_id())
        style = ctypes.windll.user32.GetWindowLongW(hwnd, -20)
        ctypes.windll.user32.SetWindowLongW(hwnd, -20, style | 0x80000 | 0x20)

        self._ov_canvas = tk.Canvas(
            self._overlay, width=D, height=D, bg=TRANS_COLOR, highlightthickness=0,
        )
        self._ov_canvas.pack()

        self._ov_base = self._ov_render_base()
        self._ov_tk_img = ImageTk.PhotoImage(self._ov_base)
        self._ov_img_id = self._ov_canvas.create_image(D // 2, D // 2, image=self._ov_tk_img)

        step = 360 // self.OV_STEPS
        self._ov_dot_frames = {i: self._ov_render_dot(i * step) for i in range(self.OV_STEPS)}
        self._ov_active_dots: list[int] = []
        self._ov_ticking = False

    def _update_overlay(self, is_running: bool):
        pass

    def _on_engine_action(self):
        self.after(0, self._spawn_dot)

    def _spawn_dot(self):
        if not hasattr(self, "_ov_canvas"):
            return
        self._ov_active_dots.append(0)
        if not self._ov_ticking:
            self._ov_ticking = True
            self._ov_tick()

    def _ov_tick(self):
        new_dots = [s + 1 for s in self._ov_active_dots if s + 1 < self.OV_STEPS]
        self._ov_active_dots = new_dots

        S = self.OV_RENDER
        if new_dots:
            composite = Image.new("RGBA", (S, S), (0, 0, 0, 0))
            for s in new_dots:
                composite = Image.alpha_composite(composite, self._ov_dot_frames[s])
            small = composite.resize((self.OV_DISPLAY, self.OV_DISPLAY), Image.LANCZOS)
            combined = self._ov_base.copy()
            combined.paste(small, (0, 0), small)
        else:
            combined = self._ov_base.copy()

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
        self.action_hotkey_mgr.stop()
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
    log_file = os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), "automacro.log")

    if not is_admin():
        import subprocess
        try:
            result = subprocess.run(
                ["py", "-c", "import sys; print(sys.executable)"],
                capture_output=True, text=True, timeout=5,
            )
            python_exe = result.stdout.strip()
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

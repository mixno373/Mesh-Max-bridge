"""
MeshCore ⇄ MAX Bridge
GUI на CustomTkinter. Привязка канал → MAX-чат (с комментарием),
очередь отправки, rate-limit, radio-probe, анимации, персистентность.
Зависимости: customtkinter, pyserial, maxapi, meshcore
"""

import asyncio
import json
import os, sys
import queue
import threading
import time
from datetime import datetime, timedelta
from collections import deque
from typing import Optional, Dict, Tuple

import customtkinter as ctk
from serial.tools import list_ports

from maxapi import Bot, Dispatcher
from maxapi.types import MessageCreated
from meshcore import MeshCore, EventType

# ============================ НАСТРОЙКИ ============================
BAUD_RATE = 115200
DEFAULT_CHAT_ID = -68054901276784
MAX_QUEUE_SIZE = 50
SEND_TIMEOUT = 15.0
STATS_TIMEOUT = 10.0

COLOR_GREEN  = "#2ecc71"
COLOR_YELLOW = "#f1c40f"
COLOR_ORANGE = "#e67e22"
COLOR_RED    = "#e74c3c"
COLOR_GRAY   = "#555555"
COLOR_IDLE   = ("gray70", "gray30")

NEG_INF = float("-inf")


# ============================ CONFIG ============================
def load_config() -> dict:
    try:
        with open("mesh_max_config.json", "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}


def save_config(data: dict) -> Optional[str]:
    try:
        with open("mesh_max_config.json", "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        return None
    except OSError as e:
        return str(e)


# ============================ QUEUED MESSAGE ============================
class QueuedMessage:
    __slots__ = ("channel", "text", "user_id", "user_name", "source_label",
                 "release_at", "enqueued_at")

    def __init__(self, channel, text, user_id, user_name, source_label, release_at):
        self.channel = channel
        self.text = text
        self.user_id = user_id
        self.user_name = user_name
        self.source_label = source_label
        self.release_at = release_at
        self.enqueued_at = time.monotonic()


# ============================ RATE LIMITER ============================
class RateLimiter:
    def __init__(self):
        self.global_seconds = 2.0
        self.per_user_seconds = 30.0
        self.tx_seconds = 1.0
        self.priority_users: set = set()
        self._last_tx = NEG_INF
        self._last_global = NEG_INF
        self._per_user: Dict[str, float] = {}
        self.allowed = 0
        self.queued = 0
        self.dropped = 0

    def configure(self, g, u, t, priority=""):
        self.global_seconds = max(0.0, float(g))
        self.per_user_seconds = max(0.0, float(u))
        self.tx_seconds = max(0.0, float(t))
        self.priority_users = {x.strip() for x in priority.split(",") if x.strip()}

    def schedule(self, user_id: str) -> Tuple[bool, float]:
        now = time.monotonic()
        if user_id in self.priority_users:
            self.allowed += 1
            return True, now
        release = max(
            now,
            self._last_tx + self.tx_seconds,
            self._last_global + self.global_seconds,
            self._per_user.get(user_id, NEG_INF) + self.per_user_seconds,
        )
        self._last_tx = release
        self._last_global = release
        self._per_user[user_id] = release
        can_now = release <= now + 0.01
        if can_now:
            self.allowed += 1
        else:
            self.queued += 1
        return can_now, release

    def reset_counters(self):
        self.allowed = 0
        self.queued = 0
        self.dropped = 0


# ============================ RADIO MONITOR ============================
class RadioMonitor:
    def __init__(self):
        self.interval = 300.0
        self.fail_threshold = 3
        self.consecutive_fails = 0
        self.zombie = False
        self.total_probes = 0
        self.failed_probes = 0

    def configure(self, interval, threshold):
        self.interval = max(30.0, float(interval))
        self.fail_threshold = max(1, int(threshold))

    def record_success(self):
        self.consecutive_fails = 0
        self.zombie = False
        self.total_probes += 1

    def record_failure(self) -> bool:
        self.consecutive_fails += 1
        self.failed_probes += 1
        self.total_probes += 1
        if not self.zombie and self.consecutive_fails >= self.fail_threshold:
            self.zombie = True
            return True
        return False


def _resource_path(rel: str) -> str:
    try:
        base = sys._MEIPASS
    except AttributeError:
        base = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base, rel)

# ============================ GUI ============================
class MeshMaxApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        icon = _resource_path("icon.ico")
        if os.path.exists(icon):
            try:
                self.iconbitmap(icon)
            except Exception:
                pass
        self.title("MeshCore ⇄ MAX Bridge")
        self.geometry("1000x860")
        self.minsize(920, 720)
        ctk.set_appearance_mode("dark")
        ctk.set_default_color_theme("blue")

        self.event_queue: queue.Queue = queue.Queue()
        self.mc: Optional[MeshCore] = None
        self.max_bot: Optional[Bot] = None
        self.dp: Optional[Dispatcher] = None
        self.loop: Optional[asyncio.AbstractEventLoop] = None
        self.async_thread: Optional[threading.Thread] = None
        self.running = False

        self._polling_task = None
        self._stats_task = None
        self._probe_task = None
        self._queue_task = None
        self._mesh_lock: Optional[asyncio.Lock] = None
        self._stop_event: Optional[asyncio.Event] = None

        self.config = load_config()
        # channel_bindings: {канал: {"max": chat_id, "comment": "..."}}
        self.channel_bindings: Dict[int, Dict] = self._load_bindings()
        self.binding_rows: list = []
        self.message_queue: list[QueuedMessage] = []

        self.msg_timestamps_mesh: deque = deque()
        self.msg_timestamps_max: deque = deque()
        self.mesh_connected = False
        self.max_connected = False

        self.rate_limiter = RateLimiter()
        self.radio_monitor = RadioMonitor()
        self._pulses = {"mesh": False, "max": False}

        self._battery_mv: Optional[int] = None
        self._uptime_s: Optional[int] = None
        self._rssi: Optional[int] = None
        self._snr: Optional[float] = None
        self._queue_len: Optional[int] = None
        self._rx_total: Optional[int] = None
        self._tx_total: Optional[int] = None

        self._build_ui()
        self._refresh_ports()
        self._restore_saved_settings()
        self._poll_queue()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    # ==================== Конфиг ====================
    def _load_bindings(self) -> Dict[int, Dict]:
        """
        Загружает привязки. Поддерживает:
          - новый формат: {"0": {"max": int, "comment": "..."}}
          - старый плоский: {"0": int}        → comment=""
          - старый с tg: {"0": {"max": int, "tg": ...}} → tg игнорируется
        """
        raw = self.config.get("channel_bindings", {})
        result: Dict[int, Dict] = {}
        if isinstance(raw, dict):
            for k, v in raw.items():
                try:
                    ch = int(k)
                except (ValueError, TypeError):
                    continue
                if isinstance(v, int):
                    result[ch] = {"max": v, "comment": ""}
                elif isinstance(v, dict):
                    mx = v.get("max")
                    cm = v.get("comment", "")
                    if mx not in (None, "", 0):
                        try:
                            result[ch] = {"max": int(mx), "comment": str(cm)}
                        except (ValueError, TypeError):
                            pass
        if not result:
            result = {0: {"max": DEFAULT_CHAT_ID, "comment": ""}}
        return result

    def _restore_saved_settings(self):
        self.max_token_var.set(str(self.config.get("max_bot_token", "")))

        rate = self.config.get("rate", {})
        if isinstance(rate, dict):
            if "global" in rate: self.rate_global_var.set(str(rate["global"]))
            if "per_user" in rate: self.rate_user_var.set(str(rate["per_user"]))
            if "tx" in rate: self.rate_tx_var.set(str(rate["tx"]))
            if "priority" in rate: self.priority_var.set(str(rate["priority"]))

        probe = self.config.get("probe", {})
        if isinstance(probe, dict):
            if "interval" in probe: self.probe_interval_var.set(str(probe["interval"]))
            if "threshold" in probe: self.probe_threshold_var.set(str(probe["threshold"]))

        try:
            self.rate_limiter.configure(
                float(self.rate_global_var.get()),
                float(self.rate_user_var.get()),
                float(self.rate_tx_var.get()),
                self.priority_var.get(),
            )
        except ValueError:
            pass
        try:
            self.radio_monitor.configure(
                float(self.probe_interval_var.get()),
                int(self.probe_threshold_var.get()),
            )
        except ValueError:
            pass

        last_port = self.config.get("last_port", "")
        if last_port and last_port in list(self.port_combo.cget("values") or []):
            self.port_var.set(last_port)
            self._log(f"Восстановлен последний COM-порт: {last_port}")

        self._log("Конфигурация загружена из mesh_max_config.json")

    def _collect_config(self) -> dict:
        return {
            "max_bot_token": self.max_token_var.get(),
            "channel_bindings": {
                str(ch): {
                    "max": int(b["max"]),
                    "comment": str(b.get("comment", "")),
                }
                for ch, b in self.channel_bindings.items()
            },
            "rate": {
                "global": self.rate_global_var.get(),
                "per_user": self.rate_user_var.get(),
                "tx": self.rate_tx_var.get(),
                "priority": self.priority_var.get(),
            },
            "probe": {
                "interval": self.probe_interval_var.get(),
                "threshold": self.probe_threshold_var.get(),
            },
            "last_port": self.port_var.get() if self.port_var.get() else "",
        }

    def _save_config(self):
        err = save_config(self._collect_config())
        if err:
            self._log(f"⚠ Ошибка сохранения конфига: {err}", "WARN")
        else:
            self._log("💾 Конфиг сохранён.")

    def _on_close(self):
        self._save_config()
        self.running = False
        if self.loop and self.loop.is_running() and self._stop_event is not None:
            try:
                self.loop.call_soon_threadsafe(self._stop_event.set)
            except Exception:
                pass

        start = time.time()

        def _wait_and_destroy():
            if self.async_thread and self.async_thread.is_alive():
                if time.time() - start > 8.0:
                    self._log("⚠ Поток не завершился за 8 с — принудительный выход", "WARN")
                    try:
                        self.destroy()
                    except Exception:
                        pass
                    os._exit(0)
                    return
                self.after(200, _wait_and_destroy)
            else:
                self.destroy()

        self.after(200, _wait_and_destroy)

    # ==================== UI ====================
    def _build_ui(self):
        self.port_var = ctk.StringVar()
        self.max_token_var = ctk.StringVar()
        self.rate_global_var = ctk.StringVar(value="2.0")
        self.rate_user_var = ctk.StringVar(value="30.0")
        self.rate_tx_var = ctk.StringVar(value="1.0")
        self.priority_var = ctk.StringVar(value="")
        self.probe_interval_var = ctk.StringVar(value="300")
        self.probe_threshold_var = ctk.StringVar(value="3")

        self._build_top_bar()
        self._build_led_row()
        self._build_stats_cards()
        self._build_tabview()
        self._build_summary_row()
        self._build_log_box()

        self.after(2000, self._update_stats_ui)

    def _build_top_bar(self):
        top = ctk.CTkFrame(self, fg_color="transparent")
        top.pack(fill="x", padx=8, pady=(6, 2))

        ctk.CTkLabel(top, text="COM:", font=("", 11)).pack(side="left")
        self.port_combo = ctk.CTkComboBox(top, variable=self.port_var, width=220, height=26)
        self.port_combo.pack(side="left", padx=3)
        ctk.CTkButton(top, text="⟳", width=32, height=26,
                      command=self._refresh_ports).pack(side="left", padx=2)

        self.btn_stop = ctk.CTkButton(top, text="Стоп", width=80, height=26,
                                      state="disabled", command=self._stop_bridge)
        self.btn_stop.pack(side="right", padx=2)
        self.btn_start = ctk.CTkButton(top, text="Старт", width=80, height=26,
                                       command=self._start_bridge)
        self.btn_start.pack(side="right", padx=2)

    def _build_led_row(self):
        led_frame = ctk.CTkFrame(self, fg_color="transparent")
        led_frame.pack(fill="x", padx=8, pady=2)
        self.mesh_led = self._make_led(led_frame, "Mesh")
        self.mesh_led.pack(side="left", padx=(4, 12), pady=2)
        self.max_led = self._make_led(led_frame, "MAX")
        self.max_led.pack(side="left", padx=(0, 12), pady=2)
        ctk.CTkLabel(led_frame, text="эфир:",
                     font=("", 10)).pack(side="left", padx=(4, 2))
        self._build_activity(led_frame)

    def _make_led(self, parent, label: str) -> ctk.CTkFrame:
        frame = ctk.CTkFrame(parent, fg_color="transparent")
        led = ctk.CTkFrame(frame, width=14, height=14, corner_radius=7, fg_color=COLOR_GRAY)
        led.pack(side="left", padx=(0, 4))
        led.pack_propagate(False)
        ctk.CTkLabel(frame, text=label, font=("", 11)).pack(side="left")
        frame._led = led
        return frame

    def _set_led(self, led_frame, color: str):
        try:
            led_frame._led.configure(fg_color=color)
        except Exception:
            pass

    def _start_pulse(self, key, led_frame):
        if self._pulses.get(key): return
        self._pulses[key] = True
        base = (46, 204, 113)
        steps, delay = 40, 30

        def tick(step=0, direction=1):
            if not self._pulses.get(key) or not led_frame.winfo_exists(): return
            t = step / steps
            factor = 0.55 + 0.45 * (1 - abs(1 - 2 * t))
            r, g, b = (int(c * factor) for c in base)
            try:
                led_frame._led.configure(fg_color=f"#{r:02x}{g:02x}{b:02x}")
            except Exception:
                return
            nxt = step + direction
            if nxt > steps:
                direction, nxt = -1, steps - 1
            elif nxt < 0:
                direction, nxt = 1, 1
            led_frame.after(delay, lambda: tick(nxt, direction))
        tick()

    def _stop_pulse(self, key):
        self._pulses[key] = False

    def _update_mesh_led(self):
        if not self.mesh_connected:
            self._stop_pulse("mesh"); self._set_led(self.mesh_led, COLOR_GRAY)
        elif self.radio_monitor.zombie:
            self._stop_pulse("mesh"); self._set_led(self.mesh_led, COLOR_ORANGE)
        else:
            if not self._pulses["mesh"]: self._start_pulse("mesh", self.mesh_led)

    def _update_max_led(self):
        if self.max_connected:
            if not self._pulses["max"]: self._start_pulse("max", self.max_led)
        else:
            self._stop_pulse("max"); self._set_led(self.max_led, COLOR_GRAY)

    def _build_activity(self, parent):
        self.activity_bars = []
        for _ in range(5):
            b = ctk.CTkFrame(parent, width=3, height=12, corner_radius=1, fg_color=COLOR_IDLE)
            b.pack(side="left", padx=1); b.pack_propagate(False)
            self.activity_bars.append(b)

    def _flash_activity(self):
        for b in self.activity_bars:
            try: b.configure(fg_color=COLOR_GREEN)
            except Exception: return
        self.after(180, self._reset_activity)

    def _reset_activity(self):
        for b in self.activity_bars:
            try: b.configure(fg_color=COLOR_IDLE)
            except Exception: return

    def _build_stats_cards(self):
        frame = ctk.CTkFrame(self, fg_color="transparent")
        frame.pack(fill="x", padx=8, pady=2)
        self.card_battery = self._make_battery_card(frame)
        self.card_uptime  = self._make_card(frame, "Uptime", "—")
        self.card_rssi    = self._make_card(frame, "RSSI", "—")
        self.card_snr     = self._make_card(frame, "SNR", "—")
        self.card_queue_hw = self._make_card(frame, "Оч. ноды", "—")
        self.card_packets = self._make_card(frame, "Пакеты", "—")
        for c in (self.card_battery, self.card_uptime, self.card_rssi,
                  self.card_snr, self.card_queue_hw, self.card_packets):
            c.pack(side="left", padx=3, pady=2, fill="x", expand=True)

    def _make_card(self, parent, title, value) -> ctk.CTkFrame:
        card = ctk.CTkFrame(parent, corner_radius=6, fg_color=("gray90", "gray20"))
        ctk.CTkLabel(card, text=title, font=("", 10),
                     text_color=("gray40", "gray70")).pack(pady=(3, 0))
        val = ctk.CTkLabel(card, text=value, font=("Consolas", 13, "bold"))
        val.pack(pady=(0, 3))
        card._value = val
        return card

    def _make_battery_card(self, parent) -> ctk.CTkFrame:
        card = ctk.CTkFrame(parent, corner_radius=6, fg_color=("gray90", "gray20"))
        ctk.CTkLabel(card, text="Батарея", font=("", 10),
                     text_color=("gray40", "gray70")).pack(pady=(3, 0))
        bar = ctk.CTkProgressBar(card, width=70, height=8, corner_radius=4)
        bar.pack(pady=2); bar.set(0)
        lbl = ctk.CTkLabel(card, text="—", font=("Consolas", 11, "bold"))
        lbl.pack(pady=(0, 3))
        card._bar = bar; card._lbl = lbl
        return card

    def _set_card(self, card, text, color=None):
        card._value.configure(text=text)
        if color: card._value.configure(text_color=color)

    def _set_battery(self, mv):
        if mv is None:
            self.card_battery._bar.set(0)
            self.card_battery._lbl.configure(text="—"); return
        ratio = max(0.0, min(1.0, (mv - 3000) / 1200))
        self.card_battery._bar.set(ratio)
        color = COLOR_GREEN if ratio > 0.5 else COLOR_YELLOW if ratio > 0.2 else COLOR_RED
        self.card_battery._bar.configure(progress_color=color)
        self.card_battery._lbl.configure(text=f"{mv}мВ", text_color=color)

    def _build_tabview(self):
        self.tabs = ctk.CTkTabview(self, height=260)
        self.tabs.pack(fill="x", padx=8, pady=2)

        tab_settings = self.tabs.add("Настройки")
        self._build_settings_content(tab_settings)

        tab_bind = self.tabs.add("Привязки")
        self._build_bindings_content(tab_bind)

    def _build_settings_content(self, parent):
        row0 = ctk.CTkFrame(parent, fg_color="transparent")
        row0.pack(fill="x", padx=4, pady=(2, 4))
        ctk.CTkLabel(row0, text="MAX Bot Token:",
                     font=("", 11, "bold")).pack(side="left", padx=(0, 6))
        ctk.CTkEntry(row0, textvariable=self.max_token_var,
                     width=340, height=24, show="*").pack(side="left")
        ctk.CTkLabel(row0, text="(пусто → только Mesh, без пересылки)",
                     font=("", 9), text_color=("gray40", "gray70")).pack(side="left", padx=6)

        row1 = ctk.CTkFrame(parent, fg_color="transparent")
        row1.pack(fill="x", padx=4, pady=2)
        ctk.CTkLabel(row1, text="Задержки (с):",
                     font=("", 11, "bold")).pack(side="left", padx=(0, 8))
        ctk.CTkLabel(row1, text="общая:", font=("", 10)).pack(side="left")
        ctk.CTkEntry(row1, textvariable=self.rate_global_var, width=50, height=24).pack(side="left", padx=3)
        ctk.CTkLabel(row1, text="на юзера:", font=("", 10)).pack(side="left")
        ctk.CTkEntry(row1, textvariable=self.rate_user_var, width=50, height=24).pack(side="left", padx=3)
        ctk.CTkLabel(row1, text="TX:", font=("", 10)).pack(side="left")
        ctk.CTkEntry(row1, textvariable=self.rate_tx_var, width=50, height=24).pack(side="left", padx=3)
        ctk.CTkLabel(row1, text="priority:", font=("", 10)).pack(side="left", padx=(8, 2))
        ctk.CTkEntry(row1, textvariable=self.priority_var, width=150, height=24).pack(side="left")

        row2 = ctk.CTkFrame(parent, fg_color="transparent")
        row2.pack(fill="x", padx=4, pady=2)
        ctk.CTkLabel(row2, text="Radio-probe (с):",
                     font=("", 11, "bold")).pack(side="left", padx=(0, 8))
        ctk.CTkEntry(row2, textvariable=self.probe_interval_var, width=50, height=24).pack(side="left", padx=3)
        ctk.CTkLabel(row2, text="порог:", font=("", 10)).pack(side="left", padx=(6, 2))
        ctk.CTkEntry(row2, textvariable=self.probe_threshold_var, width=40, height=24).pack(side="left", padx=3)

        row3 = ctk.CTkFrame(parent, fg_color="transparent")
        row3.pack(fill="x", padx=4, pady=(6, 2))
        ctk.CTkButton(row3, text="Применить", width=100, height=26,
                      command=self._apply_limits).pack(side="left", padx=2)
        ctk.CTkButton(row3, text="Сброс счётчиков", width=130, height=26,
                      command=self._reset_counters).pack(side="left", padx=2)
        ctk.CTkButton(row3, text="Очистить очередь", width=130, height=26,
                      fg_color="#c0392b", hover_color="#e74c3c",
                      command=self._clear_message_queue).pack(side="left", padx=2)

    def _build_bindings_content(self, parent):
        header = ctk.CTkFrame(parent, fg_color="transparent")
        header.pack(fill="x", padx=4, pady=(2, 2))
        ctk.CTkLabel(header, text="Канал MeshCore ↔ MAX-чат",
                     font=("", 11, "bold")).pack(side="left")
        ctk.CTkButton(header, text="Применить", width=100, height=24,
                      command=self._apply_bindings).pack(side="right", padx=2)
        ctk.CTkButton(header, text="+ Добавить", width=90, height=24,
                      command=self._add_binding_row).pack(side="right", padx=2)
        self.lbl_bindings_info = ctk.CTkLabel(
            header, text="", font=("", 10), text_color=("gray40", "gray70"))
        self.lbl_bindings_info.pack(side="right", padx=8)

        # Строка-заголовок колонок
        columns = ctk.CTkFrame(parent, fg_color="transparent")
        columns.pack(fill="x", padx=6, pady=(0, 1))
        ctk.CTkLabel(columns, text="Канал", width=60, font=("", 9, "bold"),
                     text_color=("gray40", "gray70"), anchor="w").pack(side="left", padx=2)
        ctk.CTkLabel(columns, text="MAX chat_id", width=245, font=("", 9, "bold"),
                     text_color=("gray40", "gray70"), anchor="w").pack(side="left", padx=(4, 2))
        ctk.CTkLabel(columns, text="Комментарий", width=240, font=("", 9, "bold"),
                     text_color=("gray40", "gray70"), anchor="w").pack(side="left", padx=(12, 2))

        self.bindings_frame = ctk.CTkScrollableFrame(parent, height=150)
        self.bindings_frame.pack(fill="x", padx=4, pady=2)

        for ch, b in sorted(self.channel_bindings.items()):
            self._add_binding_row(
                default_chan=str(ch),
                default_max=str(b["max"]),
                default_comment=b.get("comment", ""),
            )
        self._update_bindings_info()

    def _build_summary_row(self):
        stats2 = ctk.CTkFrame(self, fg_color="transparent")
        stats2.pack(fill="x", padx=8, pady=2)
        self.lbl_rate = ctk.CTkLabel(stats2, text="Rate-limit: OK",
                                     font=("", 10), anchor="w")
        self.lbl_rate.pack(side="left", padx=4)
        self.lbl_radio = ctk.CTkLabel(stats2, text="Radio: OK",
                                      font=("", 10), anchor="w")
        self.lbl_radio.pack(side="left", padx=4)

    def _build_log_box(self):
        log_frame = ctk.CTkFrame(self)
        log_frame.pack(fill="both", expand=True, padx=8, pady=(2, 8))

        ctk.CTkLabel(log_frame, text="Лог событий:",
                     font=("", 11, "bold"), anchor="w").pack(fill="x", padx=4, pady=(4, 0))
        self.log_box = ctk.CTkTextbox(log_frame, wrap="word",
                                      state="disabled", height=180,
                                      font=("Consolas", 11))
        self.log_box.pack(fill="both", expand=True, padx=4, pady=4)

    # ==================== Прочие UI-хелперы ====================
    def _apply_limits(self):
        try:
            g = float(self.rate_global_var.get())
            u = float(self.rate_user_var.get())
            t = float(self.rate_tx_var.get())
            self.rate_limiter.configure(g, u, t, self.priority_var.get())
            pi = float(self.probe_interval_var.get())
            pt = int(self.probe_threshold_var.get())
            self.radio_monitor.configure(pi, pt)
            self._log(f"Лимиты: global={g}s, per-user={u}s, tx={t}s, "
                      f"probe={pi}s, threshold={pt}, priority=[{self.priority_var.get()}]")
            self._save_config()
        except ValueError as e:
            self._log(f"Некорректное значение лимита: {e}", "ERROR")

    def _reset_counters(self):
        self.rate_limiter.reset_counters()
        self.radio_monitor.total_probes = 0
        self.radio_monitor.failed_probes = 0
        self.msg_timestamps_mesh.clear()
        self.msg_timestamps_max.clear()
        self._log("Счётчики сброшены.")

    def _clear_message_queue(self):
        n = len(self.message_queue)
        self.message_queue.clear()
        if n: self._log(f"Очередь очищена ({n} сообщений)", "WARN")

    def _add_binding_row(self, default_chan="", default_max="", default_comment=""):
        row = ctk.CTkFrame(self.bindings_frame, fg_color="transparent")
        row.pack(fill="x", pady=1)

        chan_var = ctk.StringVar(value=default_chan)
        ctk.CTkEntry(row, textvariable=chan_var, width=60, height=22).pack(side="left", padx=2)

        max_var = ctk.StringVar(value=default_max)
        ctk.CTkEntry(row, textvariable=max_var, width=240, height=22).pack(side="left", padx=2)

        cmt_var = ctk.StringVar(value=default_comment)
        ctk.CTkEntry(row, textvariable=cmt_var, width=240, height=22,
                     placeholder_text="напр. 'чат Казань', 'дом'…").pack(side="left", padx=(10, 2))

        entry = {
            "chan_var": chan_var,
            "max_var": max_var,
            "cmt_var": cmt_var,
            "frame": row,
        }

        def remove():
            try: row.destroy()
            except Exception: pass
            if entry in self.binding_rows:
                self.binding_rows.remove(entry)

        ctk.CTkButton(row, text="✕", width=26, height=22, fg_color="#c0392b",
                      hover_color="#e74c3c", command=remove).pack(side="left", padx=6)
        self.binding_rows.append(entry)

    def _apply_bindings(self):
        bindings: Dict[int, Dict] = {}
        try:
            for entry in self.binding_rows:
                chan_s = entry["chan_var"].get().strip()
                max_s  = entry["max_var"].get().strip()
                cmt_s  = entry["cmt_var"].get().strip()
                if not chan_s and not max_s and not cmt_s:
                    continue
                if not chan_s:
                    raise ValueError("укажите номер канала")
                if not max_s:
                    raise ValueError(f"укажите MAX chat_id для канала {chan_s}")
                chan = int(chan_s)
                if chan < 0:
                    raise ValueError(f"канал должен быть >= 0 (получено {chan})")
                mx = int(max_s)
                if chan in bindings:
                    self._log(f"⚠ Канал {chan} перезаписан", "WARN")
                bindings[chan] = {"max": mx, "comment": cmt_s}
        except ValueError as e:
            self._log(f"Ошибка привязки: {e}", "ERROR")
            return

        self.channel_bindings = bindings
        self._update_bindings_info()

        if not bindings:
            self._log("⚠ Нет привязок — пересылка работать не будет", "WARN")
        else:
            parts = []
            for ch, b in sorted(bindings.items()):
                mx = b["max"]
                cmt = b.get("comment", "")
                suffix = f" ({cmt})" if cmt else ""
                parts.append(f"ch{ch}→MAX[{mx}]{suffix}")
            self._log("Привязки: " + ", ".join(parts))

            # Проверка дубликатов chat_id
            seen = {}
            for ch, b in bindings.items():
                mx = b["max"]
                if mx in seen:
                    self._log(f"⚠ MAX chat {mx} привязан к каналам "
                              f"{seen[mx]} и {ch} — обратный маршрут по первому",
                              "WARN")
                else:
                    seen[mx] = ch
        self._save_config()

    def _update_bindings_info(self):
        n = len(self.channel_bindings)
        if n == 0:
            self.lbl_bindings_info.configure(text="нет привязок", text_color=COLOR_YELLOW)
        else:
            self.lbl_bindings_info.configure(text=f"активно: {n}", text_color=COLOR_GREEN)

    def _refresh_ports(self):
        ports = [p.device for p in list_ports.comports()]
        if ports:
            self.port_combo.configure(values=ports)
            if self.port_var.get() not in ports:
                self.port_var.set(ports[0])
        else:
            self.port_combo.configure(values=["— нет портов —"])
            self.port_var.set("— нет портов —")
        self._log("Список COM-портов обновлён.")

    def _log(self, text, level="INFO"):
        ts = datetime.now().strftime("%H:%M:%S")
        self.event_queue.put(("log", f"[{ts}] {level:<5} {text}\n"))

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.event_queue.get_nowait()
                if kind == "log":
                    self.log_box.configure(state="normal")
                    self.log_box.insert("end", payload)
                    self.log_box.see("end")
                    self.log_box.configure(state="disabled")
                elif kind == "mesh_status":
                    self.mesh_connected = payload; self._update_mesh_led()
                elif kind == "max_status":
                    self.max_connected = payload; self._update_max_led()
                elif kind == "radio_zombie":
                    self.radio_monitor.zombie = bool(payload); self._update_mesh_led()
                elif kind == "stats":
                    self._battery_mv = payload.get("battery_mv", self._battery_mv)
                    self._uptime_s   = payload.get("uptime_s", self._uptime_s)
                    self._rssi       = payload.get("rssi", self._rssi)
                    self._snr        = payload.get("snr", self._snr)
                    self._queue_len  = payload.get("queue", self._queue_len)
                    self._rx_total   = payload.get("rx", self._rx_total)
                    self._tx_total   = payload.get("tx", self._tx_total)
                elif kind == "flash":
                    self._flash_activity()
                elif kind == "bridge_stopped":
                    self.btn_start.configure(state="normal")
                    self.btn_stop.configure(state="disabled", text="Стоп")
        except queue.Empty:
            pass
        self.after(100, self._poll_queue)

    # ==================== Управление ====================
    def _start_bridge(self):
        port = self.port_var.get()
        if not port or "нет" in port:
            self._log("Не выбран COM-порт.", "ERROR"); return
        if self.async_thread and self.async_thread.is_alive():
            self._log("Предыдущий поток ещё завершается, подождите…", "WARN"); return
        if not self.channel_bindings:
            self._log("⚠ Нет привязок каналов", "WARN")
        self._apply_limits()
        self._save_config()
        self.message_queue.clear()
        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal", text="Стоп")
        self._log(f"Запуск моста на {port} …")
        self.running = True
        self.async_thread = threading.Thread(
            target=self._run_asyncio_loop, args=(port,), daemon=True)
        self.async_thread.start()

    def _stop_bridge(self):
        self._log("Остановка моста …")
        self.running = False
        self.btn_stop.configure(state="disabled", text="Остановка…")
        if self.loop and self.loop.is_running() and self._stop_event is not None:
            try:
                self.loop.call_soon_threadsafe(self._stop_event.set)
            except Exception as e:
                self._log(f"Ошибка сигнала остановки: {e}", "WARN")

    # ==================== asyncio ====================
    def _run_asyncio_loop(self, port):
        self.loop = asyncio.new_event_loop()
        asyncio.set_event_loop(self.loop)
        try:
            self.loop.run_until_complete(self._async_main(port))
        except Exception as e:
            self._log(f"Критическая ошибка asyncio: {e}", "ERROR")
        finally:
            try:
                pending = asyncio.all_tasks(self.loop)
                for p in pending:
                    p.cancel()
                if pending:
                    self.loop.run_until_complete(
                        asyncio.gather(*pending, return_exceptions=True))
            except Exception:
                pass
            self.loop.close()
            self._log("Async-цикл завершён.")
            self.event_queue.put(("bridge_stopped", None))

    async def _async_main(self, port):
        self._mesh_lock = asyncio.Lock()
        self._stop_event = asyncio.Event()

        try:
            # --- MeshCore ---
            try:
                self._log(f"Подключение к MeshCore на {port} …")
                self.mc = await MeshCore.create_serial(port, BAUD_RATE, debug=False)
                try:
                    self.mc.subscribe(EventType.CHANNEL_MSG_RECV,
                                      self._on_mesh_channel_message)
                except Exception as e:
                    self._log(f"CHANNEL_MSG_RECV subscribe: {e}", "WARN")
                for name, cb in (("CONNECTED", self._on_mesh_connected),
                                 ("DISCONNECTED", self._on_mesh_disconnected)):
                    try:
                        self.mc.subscribe(getattr(EventType, name), cb)
                    except Exception:
                        pass
                await self.mc.start_auto_message_fetching()
                self.event_queue.put(("mesh_status", True))
                self._log("MeshCore подключён.")
                self._stats_task = asyncio.create_task(self._stats_poller())
                self._probe_task = asyncio.create_task(self._radio_probe_loop())
                self._queue_task = asyncio.create_task(self._queue_processor())
            except Exception as e:
                self._log(f"Ошибка подключения MeshCore: {e}", "ERROR")
                self.event_queue.put(("mesh_status", False))
                return

            # --- MAX ---
            max_token = self.max_token_var.get().strip()
            if max_token:
                try:
                    self.max_bot = Bot(token=max_token)
                    self.dp = Dispatcher()
                    self.dp.message_created()(self._on_max_message)
                    try:
                        await self.max_bot.delete_webhook()
                    except Exception:
                        pass
                    self._log("MAX-бот: запуск polling …")
                    self.event_queue.put(("max_status", True))
                    self._polling_task = asyncio.create_task(
                        self.dp.start_polling(self.max_bot))
                except Exception as e:
                    self._log(f"Ошибка MAX-бота: {e}", "ERROR")
                    self.event_queue.put(("max_status", False))
            else:
                self._log("MAX: токен не задан — пересылка в MAX отключена", "WARN")
                self.event_queue.put(("max_status", False))

            await self._stop_event.wait()
            self._log("Получен сигнал остановки, освобождаю ресурсы…")

        except asyncio.CancelledError:
            self._log("Основная задача отменена, освобождаю ресурсы…")

        finally:
            for name, t in (("polling", self._polling_task),
                            ("stats",   self._stats_task),
                            ("probe",   self._probe_task),
                            ("queue",   self._queue_task)):
                if t and not t.done():
                    t.cancel()
                    try:
                        await asyncio.wait_for(t, timeout=5)
                    except (asyncio.CancelledError, asyncio.TimeoutError, Exception):
                        pass

            if self.message_queue:
                self._log(f"Очищено {len(self.message_queue)} сообщений из очереди", "WARN")
                self.message_queue.clear()

            if self.mc:
                try:
                    await asyncio.wait_for(
                        self.mc.stop_auto_message_fetching(), timeout=5)
                except Exception:
                    pass
                try:
                    await asyncio.wait_for(self.mc.disconnect(), timeout=5)
                    self._log("MeshCore отключён.")
                except Exception as e:
                    self._log(f"Ошибка отключения MeshCore: {e}", "WARN")
                self.mc = None
                await asyncio.sleep(0.5)
                self._log(f"COM-порт {port} освобождён.")

            self.event_queue.put(("mesh_status", False))
            self.event_queue.put(("max_status", False))

    # ==================== Mesh callbacks ====================
    async def _on_mesh_connected(self, event):
        self.event_queue.put(("mesh_status", True))
        self.radio_monitor.zombie = False
        self._log("MeshCore: соединение установлено.")

    async def _on_mesh_disconnected(self, event):
        self.event_queue.put(("mesh_status", False))
        self._log("MeshCore: соединение потеряно.", "WARN")

    async def _on_mesh_channel_message(self, event):
        try:
            payload = event.payload or {}
            text = payload.get("text", "")
            if not text: return
            chan_raw = (payload.get("channel_idx") or payload.get("chan_idx")
                        or payload.get("channel") or payload.get("chan"))
            chan: Optional[int] = None
            if chan_raw is not None:
                try: chan = int(chan_raw)
                except (ValueError, TypeError): chan = None
            if chan is None:
                if len(self.channel_bindings) == 1:
                    chan = next(iter(self.channel_bindings))
                else:
                    self._log(f"Канал не определён; поля: {list(payload.keys())}", "WARN")
                    return
            binding = self.channel_bindings.get(chan)
            if not binding:
                self._log(f"Нет привязки для канала {chan}", "WARN"); return
            chat_id = binding.get("max")
            if chat_id is None:
                self._log(f"Для канала {chan} не задан MAX chat_id", "WARN"); return
            comment = binding.get("comment", "")
            cmt_str = f" ({comment})" if comment else ""

            self.msg_timestamps_mesh.append(datetime.now())
            self.event_queue.put(("flash", None))
            max_ok = False

            if self.max_bot and self.max_connected:
                try:
                    await asyncio.wait_for(
                        self.max_bot.send_message(
                            chat_id=chat_id, text=f"📡{text}"),
                        timeout=SEND_TIMEOUT)
                    max_ok = True
                except Exception as e:
                    self._log(f"MAX ({chat_id}{cmt_str}): {type(e).__name__}: {e}", "WARN")
            else:
                self._log(f"MAX ({chat_id}{cmt_str}): бот не подключён — не ушло", "WARN")

            dest_str = f"MAX[{chat_id}]{cmt_str}" if max_ok else "не отправлено"
            self._log(f"Mesh[ch{chan}] → {dest_str}: {text[:60]}…")
        except Exception as e:
            self._log(f"Ошибка обработки Mesh-сообщения: {e}", "ERROR")

    # ---------- MAX → Mesh ----------
    async def _on_max_message(self, event: MessageCreated):
        try:
            chat_id = event.message.recipient.chat_id
        except Exception:
            return
        target_chan = None
        for ch, b in list(self.channel_bindings.items()):
            if b.get("max") == chat_id:
                target_chan = ch; break
        if target_chan is None: return
        text = event.message.body.text if event.message.body else None
        if not text: return
        sender = event.message.sender
        user_id = "unknown"; name = "Unknown"
        if sender:
            user_id = str(getattr(sender, "user_id", None)
                          or getattr(sender, "id", None)
                          or getattr(sender, "username", "unknown"))
            name = (getattr(sender, "first_name", None)
                    or getattr(sender, "username", None) or "Unknown")
            text = f"{name}: {text}"
        text = text[:139]
        await self._handle_send_to_mesh(
            target_chan, text, f"max:{user_id}", name, f"MAX[{chat_id}]")

    # ---------- Общий путь отправки в Mesh ----------
    async def _handle_send_to_mesh(self, channel, text, user_id, user_name, source_label):
        if not self.mc:
            self._log(f"{source_label}: Mesh не подключён — отброшено", "WARN"); return
        if len(self.message_queue) >= MAX_QUEUE_SIZE:
            self.rate_limiter.dropped += 1
            self._log(f"🚫 Очередь переполнена — отброшено от {user_name}: {text[:40]}…", "WARN")
            return
        can_now, release_at = self.rate_limiter.schedule(user_id)
        if can_now:
            await self._send_to_mesh(channel, text, source_label, user_id)
        else:
            delay = max(0.0, release_at - time.monotonic())
            qm = QueuedMessage(channel, text, user_id, user_name, source_label, release_at)
            self.message_queue.append(qm)
            self._log(f"⏳ В очередь #{len(self.message_queue)} (~{delay:.0f}с) "
                      f"от {user_name}: {text[:50]}…")

    async def _send_to_mesh(self, channel, text, source_label, user_id):
        try:
            async with self._mesh_lock:
                result = await asyncio.wait_for(
                    self.mc.commands.send_chan_msg(channel, text),
                    timeout=SEND_TIMEOUT)
            if result.type == EventType.ERROR:
                self._log(f"Mesh ошибка (ch{channel}): {result.payload}", "ERROR")
                return
            self.msg_timestamps_max.append(datetime.now())
            self.event_queue.put(("flash", None))
            self._log(f"{source_label} → Mesh[ch{channel}]: {text[:60]}…")
        except asyncio.TimeoutError:
            self._log(f"⏱ Таймаут отправки в Mesh (ch{channel})", "ERROR")
        except Exception as e:
            self._log(f"Ошибка отправки в Mesh: {e}", "ERROR")

    async def _queue_processor(self):
        self._log("✅ Обработчик очереди запущен.")
        while self.running:
            try:
                if not self.message_queue:
                    await asyncio.sleep(0.2); continue
                now = time.monotonic()
                sendable_idx = None
                next_release = None
                for i, qm in enumerate(self.message_queue):
                    if qm.release_at <= now + 0.01:
                        sendable_idx = i; break
                    if next_release is None or qm.release_at < next_release:
                        next_release = qm.release_at
                if sendable_idx is None:
                    wait = 1.0
                    if next_release is not None:
                        wait = min(1.0, max(0.05, next_release - now))
                    await asyncio.sleep(wait); continue
                qm = self.message_queue.pop(sendable_idx)
                delay = time.monotonic() - qm.enqueued_at
                await self._send_to_mesh(qm.channel, qm.text, qm.source_label, qm.user_id)
                if delay > 0.5:
                    self._log(f"⏱ Из очереди (+{delay:.0f}с): {qm.text[:40]}…")
            except asyncio.CancelledError:
                break
            except Exception as e:
                self._log(f"Ошибка обработчика очереди: {e}", "ERROR")
                await asyncio.sleep(1.0)
        self._log("Обработчик очереди остановлен.")

    async def _stats_poller(self):
        while self.running and self.mc:
            try:
                async with self._mesh_lock:
                    core = await asyncio.wait_for(
                        self.mc.commands.get_stats_core(), timeout=STATS_TIMEOUT)
                    radio = await asyncio.wait_for(
                        self.mc.commands.get_stats_radio(), timeout=STATS_TIMEOUT)
                payload = {}
                if core and core.type != EventType.ERROR:
                    p = core.payload
                    payload["battery_mv"] = p.get("battery_mv")
                    payload["uptime_s"]   = p.get("uptime_secs")
                    payload["queue"]      = p.get("queue_len")
                if radio and radio.type != EventType.ERROR:
                    p = radio.payload
                    payload["rssi"] = p.get("last_rssi")
                    snr_raw = p.get("last_snr")
                    payload["snr"] = round(snr_raw / 4.0, 1) if snr_raw is not None else None
                if payload:
                    self.event_queue.put(("stats", payload))
            except asyncio.TimeoutError:
                self._log("Таймаут stats Mesh", "WARN")
            except asyncio.CancelledError:
                break
            except Exception as e:
                self._log(f"Ошибка stats Mesh: {e}", "WARN")
            await asyncio.sleep(30)

    async def _radio_probe_loop(self):
        while self.running and self.mc:
            await asyncio.sleep(self.radio_monitor.interval)
            if not self.mc or not self.running: break
            try:
                async with self._mesh_lock:
                    result = await asyncio.wait_for(
                        self.mc.commands.get_stats_core(), timeout=STATS_TIMEOUT)
                if result and result.type != EventType.ERROR:
                    was = self.radio_monitor.zombie
                    self.radio_monitor.record_success()
                    if was:
                        self._log("✅ Нода Mesh восстановилась")
                        self.event_queue.put(("radio_zombie", False))
                else:
                    if self.radio_monitor.record_failure():
                        self._log(f"🚨 Нода Mesh ZOMBIE "
                                  f"({self.radio_monitor.consecutive_fails} отказов)", "ERROR")
                        self.event_queue.put(("radio_zombie", True))
            except asyncio.TimeoutError:
                if self.radio_monitor.record_failure():
                    self._log("🚨 Таймаут probe — ZOMBIE", "ERROR")
                    self.event_queue.put(("radio_zombie", True))
            except asyncio.CancelledError:
                break
            except Exception as e:
                if self.radio_monitor.record_failure():
                    self._log(f"🚨 Ошибка probe ({e}) — ZOMBIE", "ERROR")
                    self.event_queue.put(("radio_zombie", True))

    # ==================== UI update ====================
    def _update_stats_ui(self):
        cutoff = datetime.now() - timedelta(hours=24)
        while self.msg_timestamps_mesh and self.msg_timestamps_mesh[0] < cutoff:
            self.msg_timestamps_mesh.popleft()
        while self.msg_timestamps_max and self.msg_timestamps_max[0] < cutoff:
            self.msg_timestamps_max.popleft()

        self._set_battery(self._battery_mv)

        if self._uptime_s is not None:
            d, rem = divmod(self._uptime_s, 86400)
            h, rem = divmod(rem, 3600)
            m, _ = divmod(rem, 60)
            self._set_card(self.card_uptime, f"{d}д {h:02d}:{m:02d}")
        else:
            self._set_card(self.card_uptime, "—")

        if self._rssi is not None:
            color = COLOR_GREEN if self._rssi > -90 else COLOR_YELLOW if self._rssi > -110 else COLOR_RED
            self._set_card(self.card_rssi, f"{self._rssi}", color)
        else:
            self._set_card(self.card_rssi, "—")

        if self._snr is not None:
            color = COLOR_GREEN if self._snr > 5 else COLOR_YELLOW if self._snr > -5 else COLOR_RED
            self._set_card(self.card_snr, f"{self._snr}", color)
        else:
            self._set_card(self.card_snr, "—")

        if self._queue_len is not None:
            color = COLOR_RED if self._queue_len > 10 else None
            self._set_card(self.card_queue_hw, str(self._queue_len), color)
        else:
            self._set_card(self.card_queue_hw, "—")

        if self._rx_total is not None or self._tx_total is not None:
            rx = self._rx_total if self._rx_total is not None else "?"
            tx = self._tx_total if self._tx_total is not None else "?"
            self._set_card(self.card_packets, f"↓{rx} ↑{tx}")
        else:
            self._set_card(self.card_packets, "—")

        rl = self.rate_limiter
        q_size = len(self.message_queue)
        self.lbl_rate.configure(
            text=f"Rate: ✓{rl.allowed} ⏳{rl.queued} ✗{rl.dropped} "
                 f"очередь:{q_size}/{MAX_QUEUE_SIZE} | "
                 f"Mesh→MAX: {len(self.msg_timestamps_mesh)} "
                 f"MAX→Mesh: {len(self.msg_timestamps_max)}"
        )
        self.lbl_rate.configure(text_color=COLOR_YELLOW if q_size else ("gray20", "gray80"))

        rm = self.radio_monitor
        self.lbl_radio.configure(
            text=f"Radio: {'ZOMBIE' if rm.zombie else 'OK'} "
                 f"probes:{rm.total_probes} fail:{rm.failed_probes}")

        self.after(2000, self._update_stats_ui)


# ============================ ЗАПУСК ============================
if __name__ == "__main__":
    app = MeshMaxApp()
    app.mainloop()
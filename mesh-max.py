"""
MeshCore ⇄ MAX ⇄ Telegram Bridge GUI.

Маршрутизация:
    Mesh     -> MAX + Telegram
    MAX      -> Mesh + Telegram
    Telegram -> Mesh + MAX

MAX и Telegram:
    полный текст; длинные сообщения разбиваются на части.

Mesh:
    первые 139 символов, включая имя отправителя.

Функции:
    CustomTkinter GUI;
    тройные привязки канал Mesh / чат MAX / чат Telegram;
    очередь отправки в Mesh;
    rate-limit общей отправки, по пользователю и TX;
    приоритетные пользователи;
    radio-probe и восстановление соединения;
    индикация активности;
    сохранение настроек;
    защита от повторной обработки и собственных эхо-сообщений;
    Telegram через Telethon, напрямую или через MTProto-прокси.

Передаётся текст сообщения / текстовая подпись.
Вложения между сервисами не копируются.

Зависимости:
    pip install customtkinter pyserial maxapi meshcore telethon

Опционально:
    pip install TelethonFakeTLS
"""

import asyncio
import base64
import inspect
import json
import math
import os
import queue
import threading
import time

from collections import deque
from datetime import datetime
from typing import Any, Dict, Optional

import customtkinter as ctk

from serial.tools import list_ports

from maxapi import Bot, Dispatcher
from maxapi.types import MessageCreated

from meshcore import MeshCore, EventType

from telethon import TelegramClient, events
from telethon.network import (
    ConnectionTcpFull,
    ConnectionTcpMTProxyAbridged,
    ConnectionTcpMTProxyIntermediate,
    ConnectionTcpMTProxyRandomizedIntermediate,
)

try:
    from TelethonFakeTLS import ConnectionTcpMTProxyFakeTLS

    FAKETLS_AVAILABLE = True
except ImportError:
    try:
        from telethon.network.connection.tcpmtproxyfaketls import (
            ConnectionTcpMTProxyFakeTLS,
        )

        FAKETLS_AVAILABLE = True
    except ImportError:
        ConnectionTcpMTProxyFakeTLS = None
        FAKETLS_AVAILABLE = False


# ============================ НАСТРОЙКИ ============================

CONFIG_FILE = "mesh_max_config.json"

BAUD_RATE = 115200
DEFAULT_CHAT_ID = -68054901276784

MESH_TEXT_LIMIT = 139
MAX_TEXT_LIMIT = 4000
TG_TEXT_LIMIT = 4096

MAX_QUEUE_SIZE = 50

SEND_TIMEOUT = 15.0
CONNECT_TIMEOUT = 25.0
STATS_TIMEOUT = 10.0

TG_INIT_TIMEOUT = 30.0
TG_SEND_TIMEOUT = 15.0
TG_HEALTH_INTERVAL = 30.0
TG_SESSION_NAME = "bot_session"

RECONNECT_INTERVAL = 10.0

DEFAULT_PROXY_SERVER = "95.217.135.241"
DEFAULT_PROXY_PORT = "443"
DEFAULT_PROXY_SECRET = (
    "7pJZSUjIp-43RmluNUkNmWNkbnMuZ29vZ2xlLmNvbQ=="
)

COLOR_GREEN = "#2ecc71"
COLOR_YELLOW = "#f1c40f"
COLOR_ORANGE = "#e67e22"
COLOR_RED = "#e74c3c"
COLOR_GRAY = "#555555"

NEG_INF = float("-inf")


# ============================ ВСПОМОГАТЕЛЬНЫЕ ФУНКЦИИ ============================

def load_config() -> dict:
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as file:
            data = json.load(file)

        return data if isinstance(data, dict) else {}
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {}


def save_config(data: dict) -> None:
    temporary = CONFIG_FILE + ".tmp"

    with open(temporary, "w", encoding="utf-8") as file:
        json.dump(data, file, ensure_ascii=False, indent=2)

    os.replace(temporary, CONFIG_FILE)


def obj_get(obj: Any, key: str, default=None):
    if obj is None:
        return default

    if isinstance(obj, dict):
        return obj.get(key, default)

    return getattr(obj, key, default)


def first_value(obj: Any, *keys, default=None):
    for key in keys:
        value = obj_get(obj, key)
        if value is not None:
            return value

    return default


def int_or_none(value) -> Optional[int]:
    if value is None:
        return None

    value = str(value).strip()
    if value in ("", "-", "—", "None", "null"):
        return None

    return int(value)


def as_bool(value) -> bool:
    if isinstance(value, str):
        return value.strip().lower() in (
            "1", "true", "yes", "on", "да",
        )

    return bool(value)


def normalize_bindings(raw) -> Dict[int, dict]:
    result = {}

    if not isinstance(raw, dict):
        return result

    for channel, binding in raw.items():
        try:
            channel = int(channel)

            if not 0 <= channel <= 255:
                continue

            if not isinstance(binding, dict):
                continue

            result[channel] = {
                "max": int_or_none(binding.get("max")),
                "tg": int_or_none(binding.get("tg")),
            }
        except (TypeError, ValueError):
            continue

    return result


def normalize_proxy_secret(secret: str) -> str:
    """
    Преобразует hex или base64/base64url в hex.

    EE-секрет FakeTLS сохраняется целиком:
    EE + 16 байт секрета + домен.
    """
    value = secret.strip()

    if not value:
        raise ValueError("Не указан секрет MTProto-прокси.")

    try:
        raw = bytes.fromhex(value)
    except ValueError:
        try:
            padded = value + "=" * (-len(value) % 4)
            raw = base64.b64decode(
                padded,
                altchars=b"-_",
                validate=True,
            )
        except Exception as exc:
            raise ValueError(
                "Секрет прокси должен быть hex или base64/base64url."
            ) from exc

    if not raw:
        raise ValueError("Секрет прокси пуст.")

    if raw[0] == 0xEE:
        if len(raw) <= 17:
            raise ValueError(
                "FakeTLS EE-секрет должен содержать домен."
            )
    elif raw[0] == 0xDD and len(raw) == 17:
        pass
    elif len(raw) != 16:
        raise ValueError(
            "Ожидается 16-байтовый секрет, DD-секрет "
            "или EE-секрет с доменом."
        )

    return raw.hex()


def split_full_text(text: str, limit: int):
    """
    Делит текст без удаления пробелов, переводов строк
    и без добавления многоточий.

    Для совместимости лимит считается консервативно:
    символы вне BMP занимают две UTF-16 единицы.
    """
    if not text:
        return []

    parts = []
    buffer = []
    length = 0

    for character in text:
        size = 2 if ord(character) > 0xFFFF else 1

        if buffer and length + size > limit:
            parts.append("".join(buffer))
            buffer = []
            length = 0

        buffer.append(character)
        length += size

    if buffer:
        parts.append("".join(buffer))

    return parts


async def maybe_await(value):
    if inspect.isawaitable(value):
        return await value

    return value


async def close_max_bot(bot):
    """
    Разные версии maxapi могут по-разному
    предоставлять HTTP-сессию.
    """
    if bot is None:
        return

    for name in ("close", "aclose"):
        method = getattr(bot, name, None)

        if callable(method):
            await maybe_await(method())
            return

    for name in ("session", "_session"):
        session = getattr(bot, name, None)
        method = getattr(session, "close", None)

        if callable(method):
            await maybe_await(method())
            return


# ============================ КЭШИ ============================

class ExpiringCache:
    def __init__(self, capacity=4096):
        self.capacity = capacity
        self.items = {}

    def _prune(self, now):
        expired = [
            key
            for key, deadline in self.items.items()
            if deadline <= now
        ]

        for key in expired:
            self.items.pop(key, None)

        while len(self.items) >= self.capacity:
            oldest = next(iter(self.items))
            self.items.pop(oldest, None)

    def remember(self, key, ttl=180.0):
        now = time.monotonic()
        self._prune(now)

        # Переносим обновляемый элемент в конец.
        self.items.pop(key, None)
        self.items[key] = now + ttl

    def contains(self, key):
        deadline = self.items.get(key)

        if deadline is None:
            return False

        if deadline <= time.monotonic():
            self.items.pop(key, None)
            return False

        return True

    def seen(self, key, ttl=600.0):
        if self.contains(key):
            return True

        self.remember(key, ttl)
        return False

    def clear(self):
        self.items.clear()


# ============================ RATE LIMIT ============================

class RateLimiter:
    """
    Используется только для отправки в Mesh.

    MAX <-> Telegram не блокируется очередью Mesh.
    Приоритет отменяет пользовательскую задержку,
    но не отменяет общую задержку и TX.
    """

    def __init__(self):
        self.global_delay = 1.0
        self.user_delay = 3.0
        self.tx_delay = 1.0

        self.priority_users = set()

        self.last_global = NEG_INF
        self.last_tx = NEG_INF
        self.last_by_user = {}

        self.allowed = 0
        self.queued = 0
        self.dropped = 0

    def configure(
        self,
        global_delay,
        user_delay,
        tx_delay,
        priority,
    ):
        self.global_delay = max(0.0, float(global_delay))
        self.user_delay = max(0.0, float(user_delay))
        self.tx_delay = max(0.0, float(tx_delay))

        self.priority_users = {
            item.strip().casefold()
            for item in str(priority).split(",")
            if item.strip()
        }

    def is_priority(self, user_id: str, name: str) -> bool:
        user_id = str(user_id).casefold()
        name = str(name).casefold()

        plain_id = user_id.partition(":")[2]

        return (
            user_id in self.priority_users
            or plain_id in self.priority_users
            or name in self.priority_users
        )

    def delay_for(self, user_id, name, now=None):
        if now is None:
            now = time.monotonic()

        deadline = max(
            self.last_global + self.global_delay,
            self.last_tx + self.tx_delay,
        )

        if not self.is_priority(user_id, name):
            deadline = max(
                deadline,
                self.last_by_user.get(user_id, NEG_INF)
                + self.user_delay,
            )

        return max(0.0, deadline - now)

    def record_attempt(self, user_id):
        now = time.monotonic()

        self.last_global = now
        self.last_tx = now
        self.last_by_user[user_id] = now
        self.allowed += 1

        # Не храним пользователей бесконечно.
        if len(self.last_by_user) > 10000:
            cutoff = now - max(self.user_delay, 3600.0)

            self.last_by_user = {
                key: timestamp
                for key, timestamp in self.last_by_user.items()
                if timestamp >= cutoff
            }

    def reset_counters(self):
        self.allowed = 0
        self.queued = 0
        self.dropped = 0


class RadioMonitor:
    def __init__(self):
        self.interval = 20.0
        self.threshold = 3

        self.zombie = False
        self.consecutive_failures = 0

        self.total_probes = 0
        self.failed_probes = 0

    def configure(self, interval, threshold):
        self.interval = max(2.0, float(interval))
        self.threshold = max(1, int(threshold))

    def success(self):
        self.consecutive_failures = 0
        self.zombie = False

    def failure(self):
        self.failed_probes += 1
        self.consecutive_failures += 1

        if self.consecutive_failures >= self.threshold:
            self.zombie = True

    def reset_counters(self):
        self.total_probes = 0
        self.failed_probes = 0


# ============================ ПРИЛОЖЕНИЕ ============================

class MeshMaxApp(ctk.CTk):
    def __init__(self):
        super().__init__()

        self.title("MeshCore ⇄ MAX ⇄ Telegram")
        self.geometry("1100x920")
        self.minsize(930, 760)

        ctk.set_appearance_mode("dark")

        self.config_data = load_config()

        self.event_queue = queue.Queue()
        self._settings_lock = threading.Lock()
        self._settings = {}

        self._thread = None
        self._loop = None
        self._stop_event = None
        self._stop_requested = threading.Event()

        self._running = False
        self._closing = False
        self._accepting = False

        self.mc = None
        self.bot = None
        self.tg_client = None

        self._max_own_id = None
        self._tg_own_id = None
        self._tg_ready = False

        self.mesh_connected = False
        self.max_connected = False
        self.tg_connected = False
        self.radio_zombie = False

        self._pulses = {
            "mesh": False,
            "max": False,
            "tg": False,
        }

        self.rate_limiter = RateLimiter()
        self.radio_monitor = RadioMonitor()

        self.message_queue = deque()

        self._jobs = set()
        self._service_tasks = []

        self._received = ExpiringCache()
        self._outbound = ExpiringCache(capacity=10000)

        self.msg_timestamps_mesh = deque()
        self.msg_timestamps_max = deque()
        self.msg_timestamps_tg = deque()

        self._make_variables()
        self._build_ui()

        self.protocol("WM_DELETE_WINDOW", self._on_close)

        self._refresh_ports(log=False)
        self._load_bindings_into_ui()
        self._refresh_proxy_ui()

        # Читаем настройки в обычные Python-структуры.
        # Фоновый поток никогда не читает Tkinter-переменные.
        self._apply_settings(save=False, log=False)

        self.after(100, self._poll_queue)

        self._log(
            "Готово. Укажите привязки, настройки "
            "и нажмите «Запустить»."
        )

    # ============================ ПЕРЕМЕННЫЕ GUI ============================

    def _make_variables(self):
        cfg = self.config_data

        self.port_var = ctk.StringVar(
            value=str(cfg.get("last_port", ""))
        )

        self.max_token_var = ctk.StringVar(
            value=str(
                cfg.get("max_token", cfg.get("token", ""))
            )
        )

        self.tg_token_var = ctk.StringVar(
            value=str(
                cfg.get("tg_token", cfg.get("tg_bot_token", ""))
            )
        )

        self.tg_api_id_var = ctk.StringVar(
            value=str(cfg.get("tg_api_id", ""))
        )
        self.tg_api_hash_var = ctk.StringVar(
            value=str(cfg.get("tg_api_hash", ""))
        )

        self.tg_session_var = ctk.StringVar(
            value=str(
                cfg.get("tg_session", TG_SESSION_NAME)
            )
        )

        default_connection = (
            "FakeTLS"
            if FAKETLS_AVAILABLE
            else "RandomizedIntermediate"
        )

        self.tg_connection_var = ctk.StringVar(
            value=str(
                cfg.get("tg_connection", default_connection)
            )
        )

        self.tg_use_proxy_var = ctk.BooleanVar(
            value=as_bool(cfg.get("tg_use_proxy", True))
        )

        self.tg_proxy_server_var = ctk.StringVar(
            value=str(
                cfg.get("tg_proxy_server", DEFAULT_PROXY_SERVER)
            )
        )
        self.tg_proxy_port_var = ctk.StringVar(
            value=str(
                cfg.get("tg_proxy_port", DEFAULT_PROXY_PORT)
            )
        )
        self.tg_proxy_secret_var = ctk.StringVar(
            value=str(
                cfg.get("tg_proxy_secret", DEFAULT_PROXY_SECRET)
            )
        )

        self.rate_global_var = ctk.StringVar(
            value=str(cfg.get("rate_global", 1.0))
        )
        self.rate_user_var = ctk.StringVar(
            value=str(cfg.get("rate_user", 3.0))
        )
        self.rate_tx_var = ctk.StringVar(
            value=str(cfg.get("rate_tx", 1.0))
        )
        self.priority_var = ctk.StringVar(
            value=str(cfg.get("priority", ""))
        )

        self.probe_interval_var = ctk.StringVar(
            value=str(cfg.get("probe_interval", 20.0))
        )
        self.probe_threshold_var = ctk.StringVar(
            value=str(cfg.get("probe_threshold", 3))
        )

    # ============================ ПОСТРОЕНИЕ GUI ============================

    def _build_ui(self):
        header = ctk.CTkFrame(self)
        header.pack(fill="x", padx=8, pady=(8, 4))

        ctk.CTkLabel(
            header,
            text="MeshCore ⇄ MAX ⇄ Telegram",
            font=("", 21, "bold"),
        ).pack(side="left", padx=12, pady=10)

        self.btn_start = ctk.CTkButton(
            header,
            text="Запустить",
            width=115,
            command=self._start,
        )
        self.btn_start.pack(side="right", padx=(4, 10))

        self.btn_stop = ctk.CTkButton(
            header,
            text="Остановить",
            width=115,
            fg_color="#c0392b",
            hover_color=COLOR_RED,
            state="disabled",
            command=self._stop,
        )
        self.btn_stop.pack(side="right", padx=4)

        self._build_led_row()

        self.tabs = ctk.CTkTabview(self, height=340)
        self.tabs.pack(fill="x", padx=8, pady=4)

        self.tabs.add("Подключения")
        self.tabs.add("Привязки")
        self.tabs.add("Лимиты")
        self.tabs.add("Telegram")

        self._build_connections(self.tabs.tab("Подключения"))
        self._build_bindings(self.tabs.tab("Привязки"))
        self._build_limits(self.tabs.tab("Лимиты"))
        self._build_telegram(self.tabs.tab("Telegram"))

        self._build_cards()
        self._build_summary()
        self._build_log()

    def _row(self, parent):
        row = ctk.CTkFrame(parent, fg_color="transparent")
        row.pack(fill="x", padx=5, pady=5)
        return row

    def _label(self, parent, text, width=None):
        options = {"text": text, "font": ("", 11)}
        if width is not None:
            options["width"] = width

        label = ctk.CTkLabel(parent, **options)
        label.pack(side="left", padx=(2, 5))
        return label

    def _entry(self, parent, variable, width=200, secret=False):
        entry = ctk.CTkEntry(
            parent,
            textvariable=variable,
            width=width,
            height=27,
            show="*" if secret else "",
        )
        entry.pack(side="left", padx=4)
        return entry

    def _build_connections(self, parent):
        row = self._row(parent)

        self._label(row, "Mesh COM-порт:", 110)

        self.port_combo = ctk.CTkComboBox(
            row,
            variable=self.port_var,
            values=["— нет портов —"],
            width=220,
        )
        self.port_combo.pack(side="left", padx=4)

        ctk.CTkButton(
            row,
            text="Обновить",
            width=105,
            command=self._refresh_ports,
        ).pack(side="left", padx=5)

        self._label(row, f"Baud: {BAUD_RATE}")

        row = self._row(parent)
        self._label(row, "MAX Bot Token:", 110)
        self._entry(
            row,
            self.max_token_var,
            width=600,
            secret=True,
        )

        row = self._row(parent)
        ctk.CTkButton(
            row,
            text="Применить и сохранить",
            width=190,
            command=self._apply_settings,
        ).pack(side="left", padx=4)

        ctk.CTkLabel(
            parent,
            text=(
                "Изменения токенов, COM-порта и подключения Telegram "
                "применяются после остановки и повторного запуска.\n"
                "Привязки и лимиты можно менять во время работы."
            ),
            justify="left",
            anchor="w",
            font=("", 11),
            text_color=COLOR_YELLOW,
        ).pack(fill="x", padx=9, pady=12)

        ctk.CTkLabel(
            parent,
            text=(
                "Необязательные подключения можно оставить пустыми. "
                "Без Mesh MAX ⇄ Telegram продолжает работать."
            ),
            justify="left",
            anchor="w",
            font=("", 11),
        ).pack(fill="x", padx=9, pady=6)

    def _build_bindings(self, parent):
        ctk.CTkLabel(
            parent,
            text=(
                "Одна строка: канал Mesh ; ID чата MAX ; ID чата Telegram\n"
                "Пустое поле или «-» отключает соответствующее направление."
            ),
            justify="left",
            anchor="w",
        ).pack(fill="x", padx=8, pady=(4, 8))

        self.bindings_box = ctk.CTkTextbox(
            parent,
            height=140,
            font=("Consolas", 12),
        )
        self.bindings_box.pack(fill="x", padx=8, pady=4)

        row = self._row(parent)

        ctk.CTkButton(
            row,
            text="Применить привязки",
            width=180,
            command=self._apply_settings,
        ).pack(side="left", padx=4)

        self.lbl_bindings_info = ctk.CTkLabel(
            row,
            text="нет привязок",
        )
        self.lbl_bindings_info.pack(side="left", padx=10)

        ctk.CTkLabel(
            parent,
            text=(
                "Пример: 0 ; -68054901276784 ; -1001234567890\n"
                "Канал 0 поддерживается. Один чат может быть "
                "привязан к нескольким каналам Mesh."
            ),
            justify="left",
            anchor="w",
            font=("", 10),
        ).pack(fill="x", padx=8, pady=5)

    def _build_limits(self, parent):
        row = self._row(parent)

        self._label(row, "Задержки Mesh, с:")
        self._label(row, "общая:")
        self._entry(row, self.rate_global_var, width=65)
        self._label(row, "на пользователя:")
        self._entry(row, self.rate_user_var, width=65)
        self._label(row, "TX:")
        self._entry(row, self.rate_tx_var, width=65)

        row = self._row(parent)
        self._label(row, "Приоритет:")
        self._entry(row, self.priority_var, width=640)

        ctk.CTkLabel(
            parent,
            text=(
                "Через запятую: имя, max:12345, tg:12345 "
                "или просто числовой ID.\n"
                "Приоритет отменяет задержку пользователя, "
                "но сохраняет общую задержку и TX."
            ),
            justify="left",
            anchor="w",
            font=("", 10),
        ).pack(fill="x", padx=8, pady=3)

        row = self._row(parent)
        self._label(row, "Radio-probe, с:")
        self._entry(row, self.probe_interval_var, width=75)
        self._label(row, "Порог ошибок:")
        self._entry(row, self.probe_threshold_var, width=65)

        row = self._row(parent)

        ctk.CTkButton(
            row,
            text="Применить",
            width=115,
            command=self._apply_settings,
        ).pack(side="left", padx=4)

        ctk.CTkButton(
            row,
            text="Сброс счётчиков",
            width=155,
            command=self._reset_counters,
        ).pack(side="left", padx=4)

        ctk.CTkButton(
            row,
            text="Очистить очередь",
            width=155,
            fg_color="#c0392b",
            hover_color=COLOR_RED,
            command=self._clear_message_queue,
        ).pack(side="left", padx=4)

        ctk.CTkLabel(
            parent,
            text=(
                f"Очередь Mesh: {MAX_QUEUE_SIZE} сообщений. "
                f"В Mesh: не более {MESH_TEXT_LIMIT} символов.\n"
                "Переполнение или задержка очереди Mesh "
                "не блокирует пересылку между MAX и Telegram."
            ),
            justify="left",
            anchor="w",
            font=("", 11),
        ).pack(fill="x", padx=8, pady=7)

    def _build_telegram(self, parent):
        row = self._row(parent)

        self._label(row, "Bot Token:")
        self._entry(row, self.tg_token_var, width=390, secret=True)
        self._label(row, "API ID:")
        self._entry(row, self.tg_api_id_var, width=100)

        row = self._row(parent)

        self._label(row, "API Hash:")
        self._entry(
            row,
            self.tg_api_hash_var,
            width=320,
            secret=True,
        )
        self._label(row, "Сессия:")
        self._entry(row, self.tg_session_var, width=200)

        row = self._row(parent)

        self.btn_proxy_toggle = ctk.CTkButton(
            row,
            text="Прокси",
            width=150,
            command=self._toggle_proxy,
        )
        self.btn_proxy_toggle.pack(side="left", padx=4)

        self._label(row, "Тип:")

        self._conn_combo = ctk.CTkComboBox(
            row,
            values=[
                "FakeTLS",
                "RandomizedIntermediate",
                "Intermediate",
                "Abridged",
            ],
            variable=self.tg_connection_var,
            width=200,
        )
        self._conn_combo.pack(side="left", padx=4)

        row = self._row(parent)

        self._label(row, "Сервер:")
        self.proxy_server_entry = self._entry(
            row,
            self.tg_proxy_server_var,
            width=245,
        )

        self._label(row, "Порт:")
        self.proxy_port_entry = self._entry(
            row,
            self.tg_proxy_port_var,
            width=75,
        )

        row = self._row(parent)

        self._label(row, "Секрет:")
        self.proxy_secret_entry = self._entry(
            row,
            self.tg_proxy_secret_var,
            width=670,
            secret=True,
        )

        row = self._row(parent)

        ctk.CTkButton(
            row,
            text="Применить",
            width=115,
            command=self._apply_settings,
        ).pack(side="left", padx=4)

        ctk.CTkLabel(
            row,
            text=(
                "API ID / Hash: my.telegram.org. "
                "Прокси ВЫКЛ — прямое подключение / VPN."
            ),
            font=("", 10),
        ).pack(side="left", padx=8)

    def _build_led_row(self):
        row = self._row(self)

        self.mesh_led = self._make_led(row, "Mesh")
        self.max_led = self._make_led(row, "MAX")
        self.tg_led = self._make_led(row, "Telegram")

        for led in (self.mesh_led, self.max_led, self.tg_led):
            led.pack(side="left", padx=(5, 14))

        self._label(row, "Активность:")

        self.activity_bars = []

        activity_frame = ctk.CTkFrame(
            row,
            fg_color="transparent",
            height=22,
        )
        activity_frame.pack(side="left", padx=5)

        for _ in range(12):
            bar = ctk.CTkFrame(
                activity_frame,
                width=5,
                height=5,
                corner_radius=2,
                fg_color=COLOR_GRAY,
            )
            bar.pack(side="left", padx=2, anchor="s")
            self.activity_bars.append(bar)

        ctk.CTkLabel(
            row,
            text=f"Mesh ≤ {MESH_TEXT_LIMIT} символов",
            font=("", 11),
        ).pack(side="right", padx=8)

    def _make_led(self, parent, label):
        frame = ctk.CTkFrame(parent, fg_color="transparent")

        frame._led = ctk.CTkFrame(
            frame,
            width=14,
            height=14,
            corner_radius=7,
            fg_color=COLOR_GRAY,
        )
        frame._led.pack(side="left", padx=(0, 5))
        frame._led.pack_propagate(False)

        ctk.CTkLabel(
            frame,
            text=label,
            font=("", 11),
        ).pack(side="left")

        return frame

    def _build_cards(self):
        row = ctk.CTkFrame(self, fg_color="transparent")
        row.pack(fill="x", padx=8, pady=5)

        self.cards = {}

        for key, label in (
            ("battery", "Батарея"),
            ("uptime", "Uptime"),
            ("rssi", "RSSI"),
            ("snr", "SNR"),
            ("hw_queue", "Очередь радио"),
            ("packets", "RX / TX"),
        ):
            card = ctk.CTkFrame(row)
            card.pack(
                side="left",
                fill="x",
                expand=True,
                padx=3,
            )

            ctk.CTkLabel(
                card,
                text=label,
                font=("", 10),
            ).pack(pady=(5, 0))

            value = ctk.CTkLabel(
                card,
                text="—",
                font=("", 16, "bold"),
            )
            value.pack(pady=(0, 5))
            self.cards[key] = value

    def _build_summary(self):
        frame = ctk.CTkFrame(self, fg_color="transparent")
        frame.pack(fill="x", padx=8, pady=2)

        self.lbl_rate = ctk.CTkLabel(
            frame,
            text="Rate-limit: ожидание",
            anchor="w",
            font=("", 10),
        )
        self.lbl_rate.pack(fill="x", padx=4)

        row = ctk.CTkFrame(frame, fg_color="transparent")
        row.pack(fill="x")

        self.lbl_radio = ctk.CTkLabel(
            row,
            text="Radio: ожидание",
            font=("", 10),
        )
        self.lbl_radio.pack(side="left", padx=4)

        self.lbl_tg = ctk.CTkLabel(
            row,
            text="Telegram: выкл",
            font=("", 10),
        )
        self.lbl_tg.pack(side="left", padx=15)

    def _build_log(self):
        frame = ctk.CTkFrame(self)
        frame.pack(
            fill="both",
            expand=True,
            padx=8,
            pady=(5, 8),
        )

        ctk.CTkLabel(
            frame,
            text="Лог событий",
            anchor="w",
            font=("", 11, "bold"),
        ).pack(fill="x", padx=8, pady=(5, 0))

        self.log_box = ctk.CTkTextbox(
            frame,
            state="disabled",
            wrap="word",
            font=("Consolas", 11),
            height=170,
        )
        self.log_box.pack(
            fill="both",
            expand=True,
            padx=6,
            pady=6,
        )

    # ============================ НАСТРОЙКИ И ПРИВЯЗКИ ============================

    def _load_bindings_into_ui(self):
        raw = self.config_data.get(
            "channel_bindings",
            self.config_data.get("bindings"),
        )

        if raw is None:
            bindings = {
                0: {
                    "max": DEFAULT_CHAT_ID,
                    "tg": None,
                }
            }
        else:
            bindings = normalize_bindings(raw)

        lines = []

        for channel, binding in sorted(bindings.items()):
            max_id = binding.get("max")
            tg_id = binding.get("tg")

            lines.append(
                f"{channel} ; "
                f"{max_id if max_id is not None else '-'} ; "
                f"{tg_id if tg_id is not None else '-'}"
            )

        self.bindings_box.delete("1.0", "end")
        self.bindings_box.insert("1.0", "\n".join(lines))

    def _parse_bindings(self):
        result = {}

        text = self.bindings_box.get("1.0", "end")

        for line_number, line in enumerate(text.splitlines(), 1):
            line = line.strip()

            if not line or line.startswith("#"):
                continue

            parts = [part.strip() for part in line.split(";")]

            if len(parts) != 3:
                raise ValueError(
                    f"Привязка, строка {line_number}: "
                    "ожидается канал ; MAX ; Telegram."
                )

            channel = int(parts[0])

            if not 0 <= channel <= 255:
                raise ValueError(
                    f"Строка {line_number}: "
                    "канал Mesh должен быть от 0 до 255."
                )

            if channel in result:
                raise ValueError(
                    f"Канал Mesh {channel} указан несколько раз."
                )

            result[channel] = {
                "max": int_or_none(parts[1]),
                "tg": int_or_none(parts[2]),
            }

        return result

    def _read_form(self):
        bindings = self._parse_bindings()

        global_delay = float(self.rate_global_var.get())
        user_delay = float(self.rate_user_var.get())
        tx_delay = float(self.rate_tx_var.get())

        probe_interval = float(self.probe_interval_var.get())
        probe_threshold = int(self.probe_threshold_var.get())

        numeric_values = (
            global_delay,
            user_delay,
            tx_delay,
            probe_interval,
        )

        if not all(math.isfinite(value) for value in numeric_values):
            raise ValueError("Задержки должны быть конечными числами.")

        if min(global_delay, user_delay, tx_delay) < 0:
            raise ValueError("Задержки не могут быть отрицательными.")

        if probe_interval < 2:
            raise ValueError("Radio-probe: минимум 2 секунды.")

        if probe_threshold < 1:
            raise ValueError("Порог ошибок должен быть не меньше 1.")

        port = self.port_var.get().strip()

        if port.startswith("—"):
            port = ""

        settings = {
            "last_port": port,
            "max_token": self.max_token_var.get().strip(),
            "tg_token": self.tg_token_var.get().strip(),
            "tg_api_id": self.tg_api_id_var.get().strip(),
            "tg_api_hash": self.tg_api_hash_var.get().strip(),
            "tg_session": (
                self.tg_session_var.get().strip()
                or TG_SESSION_NAME
            ),
            "tg_use_proxy": bool(self.tg_use_proxy_var.get()),
            "tg_connection": self.tg_connection_var.get(),
            "tg_proxy_server": self.tg_proxy_server_var.get().strip(),
            "tg_proxy_port": self.tg_proxy_port_var.get().strip(),
            "tg_proxy_secret": self.tg_proxy_secret_var.get().strip(),
            "rate_global": global_delay,
            "rate_user": user_delay,
            "rate_tx": tx_delay,
            "priority": self.priority_var.get().strip(),
            "probe_interval": probe_interval,
            "probe_threshold": probe_threshold,
            "bindings": bindings,
        }

        if settings["tg_token"]:
            api_id = int(settings["tg_api_id"])

            if api_id <= 0:
                raise ValueError("Telegram API ID должен быть положительным.")

            if not settings["tg_api_hash"]:
                raise ValueError("Не указан Telegram API Hash.")

            if settings["tg_use_proxy"]:
                if not settings["tg_proxy_server"]:
                    raise ValueError("Не указан сервер прокси.")

                proxy_port = int(settings["tg_proxy_port"])

                if not 1 <= proxy_port <= 65535:
                    raise ValueError("Некорректный порт прокси.")

                normalize_proxy_secret(settings["tg_proxy_secret"])

                if (
                    settings["tg_connection"] == "FakeTLS"
                    and not FAKETLS_AVAILABLE
                ):
                    raise ValueError(
                        "FakeTLS недоступен. Установите TelethonFakeTLS "
                        "или выберите другой тип подключения."
                    )

        return settings

    def _apply_settings(self, save=True, log=True):
        try:
            settings = self._read_form()

            with self._settings_lock:
                self._settings = settings

            count = len(settings["bindings"])

            self.lbl_bindings_info.configure(
                text=f"активно: {count}" if count else "нет привязок",
                text_color=COLOR_GREEN if count else COLOR_YELLOW,
            )

            if save:
                config = dict(self.config_data)

                config.update({
                    key: value
                    for key, value in settings.items()
                    if key != "bindings"
                })

                config["channel_bindings"] = {
                    str(channel): dict(binding)
                    for channel, binding in settings["bindings"].items()
                }

                save_config(config)
                self.config_data = config

            if self._running:
                self._call_in_loop(self._apply_live_limits)

            if log:
                self._log(
                    "Настройки применены"
                    + (" и сохранены." if save else ".")
                )

                if self._running:
                    self._log(
                        "Привязки и лимиты обновлены. "
                        "Изменения подключений — после перезапуска.",
                        "WARN",
                    )

                if not count:
                    self._log(
                        "Нет привязок: пересылка отключена.",
                        "WARN",
                    )

            return True

        except Exception as exc:
            self._log(f"Ошибка настроек: {exc}", "ERROR")
            return False

    def _snapshot_settings(self):
        with self._settings_lock:
            settings = dict(self._settings)

            settings["bindings"] = {
                channel: dict(binding)
                for channel, binding in self._settings.get(
                    "bindings", {}
                ).items()
            }

            return settings

    def _apply_live_limits(self):
        settings = self._snapshot_settings()

        self.rate_limiter.configure(
            settings["rate_global"],
            settings["rate_user"],
            settings["rate_tx"],
            settings["priority"],
        )

        self.radio_monitor.configure(
            settings["probe_interval"],
            settings["probe_threshold"],
        )

    def _toggle_proxy(self):
        self.tg_use_proxy_var.set(
            not self.tg_use_proxy_var.get()
        )
        self._refresh_proxy_ui()
        self._apply_settings()

    def _refresh_proxy_ui(self):
        enabled = bool(self.tg_use_proxy_var.get())

        self.btn_proxy_toggle.configure(
            text="Прокси: ВКЛ" if enabled else "Прокси: ВЫКЛ",
            fg_color=COLOR_GREEN if enabled else COLOR_GRAY,
            hover_color="#27ae60" if enabled else "#666666",
        )

        state = "normal" if enabled else "disabled"

        for widget in (
            self._conn_combo,
            self.proxy_server_entry,
            self.proxy_port_entry,
            self.proxy_secret_entry,
        ):
            widget.configure(state=state)

    def _refresh_ports(self, log=True):
        try:
            ports = [port.device for port in list_ports.comports()]
        except Exception as exc:
            self._log(f"Ошибка поиска COM-портов: {exc}", "ERROR")
            ports = []

        selected = self.port_var.get().strip()

        # Сохраняем вручную заданный или сохранённый порт:
        # устройство может появиться после запуска программы.
        if selected and not selected.startswith("—") and selected not in ports:
            ports.append(selected)

        if ports:
            self.port_combo.configure(values=ports)

            if selected not in ports:
                self.port_var.set(ports[0])
        else:
            self.port_combo.configure(values=["— нет портов —"])
            self.port_var.set("— нет портов —")

        if log:
            self._log("Список COM-портов обновлён.")

    # ============================ ЛОГ И СОБЫТИЯ GUI ============================

    def _log(self, text, level="INFO"):
        timestamp = datetime.now().strftime("%H:%M:%S")

        self.event_queue.put((
            "log",
            f"[{timestamp}] {level:<5} {text}\n",
        ))

    def _poll_queue(self):
        try:
            # Ограничение защищает GUI от зависания
            # при большом потоке событий.
            for _ in range(300):
                kind, payload = self.event_queue.get_nowait()

                if kind == "log":
                    self.log_box.configure(state="normal")
                    self.log_box.insert("end", payload)

                    line_count = int(
                        self.log_box.index("end-1c").split(".")[0]
                    )

                    if line_count > 3000:
                        self.log_box.delete(
                            "1.0",
                            f"{line_count - 2500}.0",
                        )

                    self.log_box.see("end")
                    self.log_box.configure(state="disabled")

                elif kind == "mesh_status":
                    self.mesh_connected = bool(payload)
                    self._update_leds()

                elif kind == "max_status":
                    self.max_connected = bool(payload)
                    self._update_leds()

                elif kind == "tg_status":
                    self.tg_connected = bool(payload)
                    self._update_leds()

                elif kind == "radio_zombie":
                    self.radio_zombie = bool(payload)
                    self._update_leds()

                elif kind == "flash":
                    self._flash_activity()

                elif kind == "telemetry":
                    self._update_cards(payload)

                elif kind == "summary":
                    self._update_summary(payload)

                elif kind == "stopped":
                    self._running = False
                    self.btn_start.configure(state="normal")
                    self.btn_stop.configure(state="disabled")

        except queue.Empty:
            pass

        if not self._closing:
            self.after(100, self._poll_queue)

    def _start_pulse(self, key, frame):
        if self._pulses[key]:
            return

        self._pulses[key] = True

        def tick(step=0):
            if (
                self._closing
                or not self._pulses.get(key)
                or not frame.winfo_exists()
            ):
                return

            factor = 0.60 + 0.40 * (
                0.5 + 0.5 * math.sin(step / 8.0)
            )

            red = int(46 * factor)
            green = int(204 * factor)
            blue = int(113 * factor)

            frame._led.configure(
                fg_color=f"#{red:02x}{green:02x}{blue:02x}"
            )

            self.after(40, lambda: tick(step + 1))

        tick()

    def _update_leds(self):
        values = (
            (
                "mesh",
                self.mesh_led,
                self.mesh_connected and not self.radio_zombie,
                COLOR_ORANGE if self.radio_zombie else COLOR_GRAY,
            ),
            ("max", self.max_led, self.max_connected, COLOR_GRAY),
            ("tg", self.tg_led, self.tg_connected, COLOR_GRAY),
        )

        for key, frame, connected, idle_color in values:
            if connected:
                self._start_pulse(key, frame)
            else:
                self._pulses[key] = False
                frame._led.configure(fg_color=idle_color)

    def _flash_activity(self):
        if self._closing:
            return

        def tick(step=0):
            if self._closing:
                return

            for index, bar in enumerate(self.activity_bars):
                if step < 8:
                    height = 5 + int(
                        15 * abs(math.sin(index * 0.8 + step * 0.9))
                    )
                    bar.configure(
                        height=height,
                        fg_color=COLOR_GREEN,
                    )
                else:
                    bar.configure(
                        height=5,
                        fg_color=COLOR_GRAY,
                    )

            if step < 8:
                self.after(55, lambda: tick(step + 1))

        tick()

    def _update_cards(self, data):
        if data.get("battery_mv") is not None:
            self.cards["battery"].configure(
                text=f'{float(data["battery_mv"]) / 1000:.2f} V'
            )

        if data.get("uptime_s") is not None:
            seconds = int(data["uptime_s"])
            days, remainder = divmod(seconds, 86400)
            hours, remainder = divmod(remainder, 3600)
            minutes, _ = divmod(remainder, 60)

            self.cards["uptime"].configure(
                text=f"{days}д {hours:02}:{minutes:02}"
            )

        if data.get("rssi") is not None:
            self.cards["rssi"].configure(
                text=f'{data["rssi"]} dBm'
            )

        if data.get("snr") is not None:
            self.cards["snr"].configure(
                text=f'{data["snr"]} dB'
            )

        if data.get("queue") is not None:
            value = int(data["queue"])

            self.cards["hw_queue"].configure(
                text=str(value),
                text_color=(
                    COLOR_RED if value > 10 else ("gray10", "gray90")
                ),
            )

        if data.get("rx") is not None:
            self._display_rx = data["rx"]

        if data.get("tx") is not None:
            self._display_tx = data["tx"]

        if hasattr(self, "_display_rx") or hasattr(self, "_display_tx"):
            self.cards["packets"].configure(
                text=(
                    f"↓{getattr(self, '_display_rx', '?')} "
                    f"↑{getattr(self, '_display_tx', '?')}"
                )
            )

    def _update_summary(self, data):
        size = data["queue"]

        self.lbl_rate.configure(
            text=(
                f'Rate: ✓{data["allowed"]} '
                f'⏳{data["queued"]} ✗{data["dropped"]} '
                f"очередь:{size}/{MAX_QUEUE_SIZE} | "
                f'за час: Mesh RX:{data["mesh_rx"]} '
                f'MAX→Mesh:{data["max_tx"]} '
                f'TG→Mesh:{data["tg_tx"]}'
            ),
            text_color=(
                COLOR_YELLOW if size else ("gray20", "gray80")
            ),
        )

        self.lbl_radio.configure(
            text=(
                f'Radio: {"ZOMBIE" if data["zombie"] else "OK"} '
                f'probes:{data["probes"]} '
                f'fail:{data["failed"]}'
            ),
            text_color=(
                COLOR_ORANGE
                if data["zombie"]
                else ("gray20", "gray80")
            ),
        )

        if data["tg_ready"]:
            mode = "прокси" if data["tg_proxy"] else "прямо/VPN"

            self.lbl_tg.configure(
                text=f"Telegram: подключён ({mode})",
                text_color=COLOR_GREEN,
            )
        elif data["tg_enabled"]:
            self.lbl_tg.configure(
                text="Telegram: подключение / ошибка",
                text_color=COLOR_YELLOW,
            )
        else:
            self.lbl_tg.configure(
                text="Telegram: выкл",
                text_color=("gray40", "gray70"),
            )

    # ============================ ЗАПУСК И ОСТАНОВКА ============================

    def _call_in_loop(self, callback):
        loop = self._loop

        if loop is not None and loop.is_running():
            try:
                loop.call_soon_threadsafe(callback)
                return True
            except RuntimeError:
                pass

        return False

    def _start(self):
        if self._running:
            return

        if not self._apply_settings():
            return

        settings = self._snapshot_settings()

        if not (
            settings["last_port"]
            or settings["max_token"]
            or settings["tg_token"]
        ):
            self._log(
                "Не настроено ни одного подключения.",
                "ERROR",
            )
            return

        self._running = True
        self._stop_requested.clear()

        self.btn_start.configure(state="disabled")
        self.btn_stop.configure(state="normal")

        for card in self.cards.values():
            card.configure(text="—")

        for attribute in ("_display_rx", "_display_tx"):
            if hasattr(self, attribute):
                delattr(self, attribute)

        self._thread = threading.Thread(
            target=self._thread_main,
            args=(settings,),
            daemon=True,
            name="BridgeAsyncThread",
        )
        self._thread.start()

    def _stop(self):
        if not self._running:
            return

        self._stop_requested.set()
        self.btn_stop.configure(state="disabled")

        stop_event = self._stop_event

        if stop_event is not None:
            self._call_in_loop(stop_event.set)

        self._log("Остановка моста…")

    def _thread_main(self, settings):
        try:
            asyncio.run(self._async_main(settings))
        except Exception as exc:
            self._log(f"Ошибка основного цикла: {exc}", "ERROR")
        finally:
            self._loop = None
            self._stop_event = None

            self.event_queue.put(("mesh_status", False))
            self.event_queue.put(("max_status", False))
            self.event_queue.put(("tg_status", False))
            self.event_queue.put(("radio_zombie", False))
            self.event_queue.put(("stopped", None))

    async def _async_main(self, settings):
        self._loop = asyncio.get_running_loop()
        self._stop_event = asyncio.Event()

        self._run_settings = settings

        self._mesh_lock = asyncio.Lock()
        self._max_send_lock = asyncio.Lock()
        self._tg_send_lock = asyncio.Lock()

        self._jobs = set()
        self._service_tasks = []

        self.message_queue.clear()

        self._received.clear()
        self._outbound.clear()

        self.msg_timestamps_mesh.clear()
        self.msg_timestamps_max.clear()
        self.msg_timestamps_tg.clear()

        self.rate_limiter = RateLimiter()
        self.radio_monitor = RadioMonitor()
        self._apply_live_limits()

        self._max_own_id = None
        self._tg_own_id = None
        self._tg_ready = False

        self._accepting = True

        if self._stop_requested.is_set():
            self._stop_event.set()

        try:
            self._service_tasks = [
                asyncio.create_task(
                    self._mesh_manager(),
                    name="mesh-manager",
                ),
                asyncio.create_task(
                    self._mesh_queue_worker(),
                    name="mesh-queue",
                ),
                asyncio.create_task(
                    self._stats_loop(),
                    name="mesh-stats",
                ),
                asyncio.create_task(
                    self._summary_loop(),
                    name="summary",
                ),
            ]

            if settings["max_token"]:
                self._service_tasks.append(
                    asyncio.create_task(
                        self._max_manager(),
                        name="max-manager",
                    )
                )

            if settings["tg_token"]:
                self._service_tasks.append(
                    asyncio.create_task(
                        self._telegram_manager(),
                        name="telegram-manager",
                    )
                )

            self._log(
                "Мост запущен. "
                "Mesh → MAX + TG; MAX → Mesh + TG; TG → Mesh + MAX."
            )

            await self._stop_event.wait()

        finally:
            self._accepting = False

            tasks = [
                task
                for task in self._service_tasks + list(self._jobs)
                if not task.done()
            ]

            for task in tasks:
                task.cancel()

            if tasks:
                try:
                    await asyncio.wait_for(
                        asyncio.gather(
                            *tasks,
                            return_exceptions=True,
                        ),
                        timeout=10.0,
                    )
                except asyncio.TimeoutError:
                    self._log(
                        "Таймаут завершения фоновых задач.",
                        "WARN",
                    )

            if self.message_queue:
                self._log(
                    f"При остановке удалено "
                    f"{len(self.message_queue)} сообщений очереди Mesh.",
                    "WARN",
                )
                self.message_queue.clear()

            await self._disconnect_mesh()

            if self.tg_client is not None:
                client = self.tg_client
                self.tg_client = None

                try:
                    await asyncio.wait_for(
                        client.disconnect(),
                        timeout=5.0,
                    )
                except Exception as exc:
                    self._log(
                        f"Ошибка отключения Telegram: {exc}",
                        "WARN",
                    )

            if self.bot is not None:
                bot = self.bot
                self.bot = None

                try:
                    await asyncio.wait_for(
                        close_max_bot(bot),
                        timeout=5.0,
                    )
                except Exception as exc:
                    self._log(
                        f"Ошибка закрытия MAX: {exc}",
                        "WARN",
                    )

            self._tg_ready = False
            self._log("Мост остановлен.")

    async def _pause(self, seconds):
        try:
            await asyncio.wait_for(
                self._stop_event.wait(),
                timeout=max(0.01, seconds),
            )
        except asyncio.TimeoutError:
            pass

    def _spawn(self, coroutine):
        """
        Обработчики транспорта не ждут сетевой пересылки.

        Это особенно важно для MeshCore:
        чтение ответов радио не должно блокироваться отправкой
        сообщений в MAX / Telegram.
        """
        if not self._accepting:
            coroutine.close()
            return

        task = asyncio.create_task(coroutine)
        self._jobs.add(task)

        def done(completed):
            self._jobs.discard(completed)

            if completed.cancelled():
                return

            error = completed.exception()

            if error is not None:
                self._log(
                    f"Ошибка обработки сообщения: {error}",
                    "ERROR",
                )

        task.add_done_callback(done)

    def _on_close(self):
        if self._closing:
            return

        self._apply_settings()
        self._closing = True

        if self._running:
            self._stop()

        def wait_for_thread():
            if self._thread is not None and self._thread.is_alive():
                self.after(100, wait_for_thread)
            else:
                self.destroy()

        wait_for_thread()

    # ============================ MESH: ПОДКЛЮЧЕНИЕ ============================

    async def _connect_mesh(self):
        port = self._run_settings["last_port"]

        if not port:
            return False

        self._log(f"Подключение Mesh: {port}, {BAUD_RATE} baud…")

        mc = await asyncio.wait_for(
            MeshCore.create_serial(port, BAUD_RATE),
            timeout=CONNECT_TIMEOUT,
        )

        if mc is None:
            raise RuntimeError("MeshCore не вернул соединение.")

        try:
            mc.subscribe(
                EventType.CHANNEL_MSG_RECV,
                self._on_mesh_channel_message,
            )

            self.mc = mc

            method = getattr(
                mc,
                "start_auto_message_fetching",
                None,
            )

            if callable(method):
                await asyncio.wait_for(
                    maybe_await(method()),
                    timeout=SEND_TIMEOUT,
                )

            self.event_queue.put(("mesh_status", True))
            self._log("Mesh подключён.")
            return True

        except BaseException:
            if self.mc is mc:
                self.mc = None

            try:
                await asyncio.wait_for(
                    maybe_await(mc.disconnect()),
                    timeout=5.0,
                )
            except Exception:
                pass

            raise

    async def _disconnect_mesh(self):
        mc = self.mc
        self.mc = None

        self.event_queue.put(("mesh_status", False))

        if mc is None:
            return

        try:
            async with self._mesh_lock:
                await asyncio.wait_for(
                    maybe_await(mc.disconnect()),
                    timeout=5.0,
                )
        except Exception as exc:
            self._log(
                f"Ошибка отключения Mesh: {exc}",
                "WARN",
            )

    def _check_mesh_result(self, result):
        if result is None:
            raise RuntimeError("MeshCore вернул пустой ответ.")

        if obj_get(result, "type") == EventType.ERROR:
            raise RuntimeError(
                f"MeshCore: {obj_get(result, 'payload')}"
            )

        return result

    async def _mesh_command(self, method_name):
        async with self._mesh_lock:
            mc = self.mc

            if mc is None:
                raise RuntimeError("Mesh не подключён.")

            method = getattr(mc.commands, method_name, None)

            if not callable(method):
                raise AttributeError(
                    f"Версия meshcore не поддерживает {method_name}()."
                )

            result = await asyncio.wait_for(
                maybe_await(method()),
                timeout=STATS_TIMEOUT,
            )

            return self._check_mesh_result(result)

    async def _mesh_manager(self):
        if not self._run_settings["last_port"]:
            return

        while not self._stop_event.is_set():
            monitor = self.radio_monitor
            monitor.total_probes += 1

            try:
                if self.mc is None:
                    await self._connect_mesh()

                result = await self._mesh_command("get_bat")
                payload = obj_get(result, "payload", {}) or {}

                self._emit_telemetry(payload)

                was_zombie = monitor.zombie
                monitor.success()

                self.event_queue.put(("radio_zombie", False))
                self.event_queue.put(("mesh_status", True))

                if was_zombie:
                    self._log("Radio-probe: радио восстановлено.")

            except asyncio.CancelledError:
                raise

            except Exception as exc:
                monitor.failure()

                self._log(
                    f"Radio-probe: {exc}; "
                    f"ошибок подряд: {monitor.consecutive_failures}",
                    "WARN",
                )

                self.event_queue.put((
                    "radio_zombie",
                    monitor.zombie,
                ))

                if monitor.zombie and self.mc is not None:
                    self._log(
                        "Радио не отвечает. Переподключение Mesh…",
                        "WARN",
                    )
                    await self._disconnect_mesh()

            delay = (
                min(monitor.interval, RECONNECT_INTERVAL)
                if self.mc is None
                else monitor.interval
            )

            await self._pause(delay)

    # ============================ MESH: ПОЛУЧЕНИЕ ============================

    async def _on_mesh_channel_message(self, event):
        self._spawn(self._process_mesh_message(event))

    async def _process_mesh_message(self, event):
        payload = obj_get(event, "payload", {}) or {}

        text = obj_get(payload, "text", "")
        if not isinstance(text, str) or not text:
            return

        # Не используем "a or b": индекс канала 0 — корректный.
        channel = first_value(
            payload,
            "channel_idx",
            "chan_idx",
            "channel",
            "chan",
        )

        if channel is None:
            self._log(
                f"Mesh RX: не найден индекс канала: {payload}",
                "WARN",
            )
            return

        channel = int(channel)

        # Mesh обычно не даёт универсального ID отправителя.
        # Используется кратковременная память отправленного текста.
        if self._outbound.contains(("mesh", channel, text)):
            return

        # Некоторые прошивки добавляют перед текстом имя узла.
        _, separator, without_sender = text.partition(": ")

        if (
            separator
            and self._outbound.contains(
                ("mesh", channel, without_sender)
            )
        ):
            return

        timestamp = first_value(
            payload,
            "sender_timestamp",
            "timestamp",
            "time",
        )

        sender = first_value(
            payload,
            "sender",
            "sender_name",
            "pubkey_prefix",
            default="",
        )

        key = (
            "mesh-rx",
            channel,
            str(timestamp),
            str(sender),
            text,
        )

        # Без timestamp защита только от близких повторов,
        # чтобы не подавлять одинаковые сообщения навсегда.
        ttl = 600.0 if timestamp is not None else 2.0

        if self._received.seen(key, ttl=ttl):
            return

        self._emit_telemetry(payload)
        self.msg_timestamps_mesh.append(time.monotonic())

        await self._route_message(
            source="mesh",
            source_id=channel,
            full_text=text,
            user_id=f"mesh:{sender}",
            name=str(sender or "Mesh"),
        )

    # ============================ MAX: ПОДКЛЮЧЕНИЕ ============================

    async def _max_manager(self):
        token = self._run_settings["max_token"]

        while not self._stop_event.is_set():
            bot = None

            try:
                self._log("Подключение MAX…")

                bot = Bot(token=token)

                me = await asyncio.wait_for(
                    bot.get_me(),
                    timeout=CONNECT_TIMEOUT,
                )

                own_id = first_value(me, "user_id", "id")

                if own_id is None:
                    user = obj_get(me, "user")
                    own_id = first_value(user, "user_id", "id")

                self._max_own_id = (
                    str(own_id) if own_id is not None else None
                )

                dispatcher = Dispatcher()
                dispatcher.message_created()(self._on_max_message)

                self.bot = bot
                self.event_queue.put(("max_status", True))
                self._log("MAX подключён.")

                await dispatcher.start_polling(bot)

                if not self._stop_event.is_set():
                    self._log(
                        "Polling MAX завершился. Повторное подключение.",
                        "WARN",
                    )

            except asyncio.CancelledError:
                raise

            except Exception as exc:
                self._log(
                    f"Ошибка MAX: {exc}",
                    "ERROR",
                )

            finally:
                if self.bot is bot:
                    self.bot = None

                self.event_queue.put(("max_status", False))

                if bot is not None:
                    try:
                        await asyncio.wait_for(
                            close_max_bot(bot),
                            timeout=5.0,
                        )
                    except Exception as exc:
                        self._log(
                            f"Ошибка закрытия сессии MAX: {exc}",
                            "WARN",
                        )

            await self._pause(RECONNECT_INTERVAL)

    # ============================ MAX: ПОЛУЧЕНИЕ ============================

    async def _on_max_message(self, event: MessageCreated):
        self._spawn(self._process_max_message(event))

    async def _process_max_message(self, event):
        message = obj_get(event, "message")

        if message is None:
            return

        recipient = obj_get(message, "recipient")
        chat_id = obj_get(recipient, "chat_id")

        if chat_id is None:
            return

        chat_id = int(chat_id)

        body = obj_get(message, "body")
        text = obj_get(body, "text")

        if not isinstance(text, str) or not text:
            return

        sender = obj_get(message, "sender")
        sender_id = first_value(sender, "user_id", "id")

        # Игнорируем именно собственного бота.
        # Сообщения других ботов автоматически не запрещаем.
        if (
            self._max_own_id is not None
            and sender_id is not None
            and str(sender_id) == self._max_own_id
        ):
            return

        if self._outbound.contains(("max", chat_id, text)):
            return

        message_id = first_value(
            body,
            "mid",
            "message_id",
            "id",
        )

        if message_id is None:
            message_id = first_value(
                message,
                "message_id",
                "id",
            )

        if message_id is not None:
            key = ("max-rx", chat_id, str(message_id))
            ttl = 600.0
        else:
            key = (
                "max-rx",
                chat_id,
                str(sender_id),
                str(obj_get(message, "timestamp", "")),
                text,
            )
            ttl = 2.0

        if self._received.seen(key, ttl=ttl):
            return

        first_name = obj_get(sender, "first_name", "") or ""
        last_name = obj_get(sender, "last_name", "") or ""

        name = (
            f"{first_name} {last_name}".strip()
            or obj_get(sender, "name")
            or obj_get(sender, "username")
            or "MAX User"
        )

        name = str(name).replace("\r", " ").replace("\n", " ")

        # Не обрезаем полный текст.
        full_text = f"{name}: {text}"

        await self._route_message(
            source="max",
            source_id=chat_id,
            full_text=full_text,
            user_id=f"max:{sender_id if sender_id is not None else 'unknown'}",
            name=name,
        )

    # ============================ TELEGRAM: ПОДКЛЮЧЕНИЕ ============================

    def _make_telegram_client(self):
        settings = self._run_settings

        kwargs = {
            "timeout": 10,
            "connection_retries": 2,
            "request_retries": 1,
            "retry_delay": 2,
            "auto_reconnect": True,
            # FloodWait будет обработан как ошибка отправки,
            # а не скрытая многоминутная блокировка.
            "flood_sleep_threshold": 0,
        }

        if settings["tg_use_proxy"]:
            secret_hex = normalize_proxy_secret(
                settings["tg_proxy_secret"]
            )
            raw_secret = bytes.fromhex(secret_hex)
            connection_name = settings["tg_connection"]

            connection_classes = {
                "FakeTLS": ConnectionTcpMTProxyFakeTLS,
                "RandomizedIntermediate": (
                    ConnectionTcpMTProxyRandomizedIntermediate
                ),
                "Intermediate": ConnectionTcpMTProxyIntermediate,
                "Abridged": ConnectionTcpMTProxyAbridged,
            }

            connection_class = connection_classes.get(
                connection_name
            )

            if connection_class is None:
                raise RuntimeError(
                    f"Тип подключения {connection_name} недоступен."
                )

            if connection_name == "FakeTLS":
                if not FAKETLS_AVAILABLE:
                    raise RuntimeError(
                        "Для FakeTLS установите TelethonFakeTLS."
                    )

                if raw_secret[0] != 0xEE:
                    raise ValueError(
                        "FakeTLS требует EE-секрет с доменом."
                    )

            elif raw_secret[0] == 0xEE:
                # Для обычных MTProxy-соединений используется
                # базовый 16-байтовый секрет без EE и домена.
                secret_hex = raw_secret[1:17].hex()

                self._log(
                    "EE-секрет используется без FakeTLS: "
                    "взят базовый 16-байтовый секрет. "
                    "Прокси может требовать именно FakeTLS.",
                    "WARN",
                )

            elif raw_secret[0] == 0xDD and len(raw_secret) == 17:
                secret_hex = raw_secret[1:].hex()

            kwargs["connection"] = connection_class

            kwargs["proxy"] = (
                settings["tg_proxy_server"],
                int(settings["tg_proxy_port"]),
                secret_hex,
            )

        else:
            kwargs["connection"] = ConnectionTcpFull

        return TelegramClient(
            settings["tg_session"],
            int(settings["tg_api_id"]),
            settings["tg_api_hash"],
            **kwargs,
        )

    async def _telegram_manager(self):
        while not self._stop_event.is_set():
            client = None

            try:
                self._log("Подключение Telegram…")

                client = self._make_telegram_client()

                await asyncio.wait_for(
                    client.start(
                        bot_token=self._run_settings["tg_token"]
                    ),
                    timeout=TG_INIT_TIMEOUT,
                )

                me = await asyncio.wait_for(
                    client.get_me(),
                    timeout=STATS_TIMEOUT,
                )

                if me is None or not obj_get(me, "bot", False):
                    raise RuntimeError(
                        "Файл сессии авторизован не как бот. "
                        "Укажите другое имя сессии."
                    )

                expected_id = self._run_settings["tg_token"].split(
                    ":", 1
                )[0]

                if (
                    expected_id.isdigit()
                    and int(expected_id) != int(me.id)
                ):
                    raise RuntimeError(
                        "Сессия принадлежит другому Telegram-боту. "
                        "Укажите новое имя сессии."
                    )

                self._tg_own_id = int(me.id)

                client.add_event_handler(
                    self._on_telegram_message,
                    events.NewMessage(
                        incoming=True,
                        outgoing=False,
                    ),
                )

                self.tg_client = client
                self._tg_ready = True

                self.event_queue.put(("tg_status", True))

                self._log(
                    f"Telegram подключён: "
                    f"@{obj_get(me, 'username', '') or me.id}"
                )

                while not self._stop_event.is_set():
                    await self._pause(TG_HEALTH_INTERVAL)

                    if self._stop_event.is_set():
                        break

                    if not client.is_connected():
                        raise ConnectionError(
                            "Telegram-соединение разорвано."
                        )

                    health = await asyncio.wait_for(
                        client.get_me(),
                        timeout=STATS_TIMEOUT,
                    )

                    if health is None:
                        raise ConnectionError(
                            "Telegram не ответил на проверку."
                        )

            except asyncio.CancelledError:
                raise

            except Exception as exc:
                self._log(
                    f"Ошибка Telegram: {exc}",
                    "ERROR",
                )

            finally:
                self._tg_ready = False
                self.event_queue.put(("tg_status", False))

                if self.tg_client is client:
                    self.tg_client = None

                if client is not None:
                    try:
                        await asyncio.wait_for(
                            client.disconnect(),
                            timeout=5.0,
                        )
                    except Exception as exc:
                        self._log(
                            f"Ошибка закрытия Telegram: {exc}",
                            "WARN",
                        )

            await self._pause(RECONNECT_INTERVAL)

    # ============================ TELEGRAM: ПОЛУЧЕНИЕ ============================

    async def _on_telegram_message(self, event):
        self._spawn(self._process_telegram_message(event))

    async def _process_telegram_message(self, event):
        chat_id = event.chat_id

        if chat_id is None:
            return

        chat_id = int(chat_id)

        if event.out:
            return

        if (
            self._tg_own_id is not None
            and event.sender_id == self._tg_own_id
        ):
            return

        text = event.raw_text

        if not isinstance(text, str) or not text:
            return

        if self._outbound.contains(("tg", chat_id, text)):
            return

        if self._received.seen(
            ("tg-rx", chat_id, event.id),
            ttl=600.0,
        ):
            return

        sender = None

        try:
            sender = await asyncio.wait_for(
                event.get_sender(),
                timeout=5.0,
            )
        except Exception:
            pass

        first_name = obj_get(sender, "first_name", "") or ""
        last_name = obj_get(sender, "last_name", "") or ""

        name = (
            f"{first_name} {last_name}".strip()
            or obj_get(sender, "title")
            or obj_get(sender, "username")
            or "TG User"
        )

        name = str(name).replace("\r", " ").replace("\n", " ")

        # Не обрезаем полный текст.
        full_text = f"{name}: {text}"

        await self._route_message(
            source="tg",
            source_id=chat_id,
            full_text=full_text,
            user_id=f"tg:{event.sender_id}",
            name=name,
        )

    # ============================ ТРОЙНАЯ МАРШРУТИЗАЦИЯ ============================

    async def _route_message(
        self,
        source,
        source_id,
        full_text,
        user_id,
        name,
    ):
        settings = self._snapshot_settings()
        bindings = settings["bindings"]

        targets = set()

        for channel, binding in bindings.items():
            max_id = binding.get("max")
            tg_id = binding.get("tg")

            matches = (
                (source == "mesh" and channel == source_id)
                or (source == "max" and max_id == source_id)
                or (source == "tg" and tg_id == source_id)
            )

            if not matches:
                continue

            if source != "mesh":
                targets.add(("mesh", channel))

            if source != "max" and max_id is not None:
                targets.add(("max", max_id))

            if source != "tg" and tg_id is not None:
                targets.add(("tg", tg_id))

        if not targets:
            return

        source_label = {
            "mesh": f"Mesh[ch{source_id}]",
            "max": f"MAX[{source_id}]",
            "tg": f"TG[{source_id}]",
        }[source]

        self._log(
            f"{source_label} RX: {len(full_text)} символов."
        )
        self.event_queue.put(("flash", None))

        network_tasks = []

        for transport, destination in sorted(
            targets,
            key=lambda item: (item[0], item[1]),
        ):
            if transport == "mesh":
                # Очередь содержит полный текст.
                # Обрезка делается только в _send_to_mesh().
                self._enqueue_mesh(
                    channel=destination,
                    text=full_text,
                    source=source,
                    source_label=source_label,
                    user_id=user_id,
                    name=name,
                )

            elif transport == "max":
                network_tasks.append(
                    self._send_to_max(
                        destination,
                        full_text,
                        source_label,
                    )
                )

            elif transport == "tg":
                network_tasks.append(
                    self._send_to_telegram(
                        destination,
                        full_text,
                        source_label,
                    )
                )

        if network_tasks:
            # Ошибка одного направления не отменяет остальные.
            results = await asyncio.gather(
                *network_tasks,
                return_exceptions=True,
            )

            for result in results:
                if isinstance(result, Exception):
                    self._log(
                        f"Ошибка независимой пересылки: {result}",
                        "ERROR",
                    )

    # ============================ MAX: ОТПРАВКА ПОЛНОГО ТЕКСТА ============================

    async def _send_to_max(
        self,
        chat_id,
        full_text,
        source_label="Bridge",
    ):
        parts = split_full_text(full_text, MAX_TEXT_LIMIT)

        if not parts:
            return False

        sent_count = 0

        try:
            async with self._max_send_lock:
                bot = self.bot

                if bot is None:
                    self._log(
                        f"{source_label} → MAX[{chat_id}]: "
                        "MAX не подключён.",
                        "WARN",
                    )
                    return False

                for part in parts:
                    # Запоминаем до запроса: эхо может прийти
                    # раньше ответа send_message().
                    self._outbound.remember(
                        ("max", chat_id, part),
                        ttl=180.0,
                    )

                    await asyncio.wait_for(
                        bot.send_message(
                            chat_id=chat_id,
                            text=part,
                        ),
                        timeout=SEND_TIMEOUT,
                    )

                    sent_count += 1

            self._log(
                f"{source_label} → MAX[{chat_id}]: "
                f"полный текст, {len(full_text)} символов, "
                f"частей: {sent_count}."
            )
            self.event_queue.put(("flash", None))
            return True

        except asyncio.CancelledError:
            raise

        except Exception as exc:
            self._log(
                f"{source_label} → MAX[{chat_id}]: {exc}; "
                f"подтверждено частей {sent_count}/{len(parts)}.",
                "ERROR",
            )
            return False

    # ============================ TELEGRAM: ОТПРАВКА ПОЛНОГО ТЕКСТА ============================

    async def _send_to_telegram(
        self,
        chat_id,
        full_text,
        source_label="Bridge",
    ):
        parts = split_full_text(full_text, TG_TEXT_LIMIT)

        if not parts:
            return False

        sent_count = 0

        try:
            async with self._tg_send_lock:
                client = self.tg_client

                if (
                    client is None
                    or not self._tg_ready
                    or not client.is_connected()
                ):
                    self._log(
                        f"{source_label} → TG[{chat_id}]: "
                        "Telegram не подключён.",
                        "WARN",
                    )
                    return False

                for part in parts:
                    self._outbound.remember(
                        ("tg", chat_id, part),
                        ttl=180.0,
                    )

                    await asyncio.wait_for(
                        client.send_message(
                            entity=chat_id,
                            message=part,
                            parse_mode=None,
                            formatting_entities=[],
                            link_preview=False,
                        ),
                        timeout=TG_SEND_TIMEOUT,
                    )

                    sent_count += 1

            self._log(
                f"{source_label} → TG[{chat_id}]: "
                f"полный текст, {len(full_text)} символов, "
                f"частей: {sent_count}."
            )
            self.event_queue.put(("flash", None))
            return True

        except asyncio.CancelledError:
            raise

        except Exception as exc:
            self._log(
                f"{source_label} → TG[{chat_id}]: {exc}; "
                f"подтверждено частей {sent_count}/{len(parts)}.",
                "ERROR",
            )
            return False

    # ============================ MESH: ОЧЕРЕДЬ ============================

    def _enqueue_mesh(
        self,
        channel,
        text,
        source,
        source_label,
        user_id,
        name,
    ):
        if len(self.message_queue) >= MAX_QUEUE_SIZE:
            self.rate_limiter.dropped += 1

            self._log(
                f"{source_label} → Mesh[ch{channel}]: "
                "очередь заполнена. "
                "Пересылка в другой мессенджер не отменяется.",
                "WARN",
            )
            return False

        self.message_queue.append({
            "channel": channel,
            "text": text,
            "source": source,
            "source_label": source_label,
            "user_id": str(user_id),
            "name": str(name),
        })

        self.rate_limiter.queued += 1
        return True

    async def _mesh_queue_worker(self):
        while not self._stop_event.is_set():
            if (
                not self.message_queue
                or self.mc is None
                or self.radio_monitor.zombie
            ):
                await self._pause(0.25)
                continue

            now = time.monotonic()

            ready = []
            shortest_delay = None

            for index, item in enumerate(self.message_queue):
                delay = self.rate_limiter.delay_for(
                    item["user_id"],
                    item["name"],
                    now=now,
                )

                if shortest_delay is None or delay < shortest_delay:
                    shortest_delay = delay

                if delay <= 0:
                    priority = self.rate_limiter.is_priority(
                        item["user_id"],
                        item["name"],
                    )

                    ready.append((
                        0 if priority else 1,
                        index,
                    ))

            if not ready:
                await self._pause(
                    min(
                        max(shortest_delay or 0.05, 0.05),
                        0.5,
                    )
                )
                continue

            _, index = min(ready)

            item = self.message_queue[index]
            del self.message_queue[index]

            # Общая задержка и TX учитывают также неудачные попытки.
            self.rate_limiter.record_attempt(item["user_id"])

            await self._send_to_mesh(
                channel=item["channel"],
                text=item["text"],
                source=item["source"],
                source_label=item["source_label"],
                user_id=item["user_id"],
            )

    # ============================ MESH: ОТПРАВКА С ЛИМИТОМ 139 ============================

    async def _send_to_mesh(
        self,
        channel,
        text,
        source,
        source_label,
        user_id,
    ):
        # Единственное место, где сокращается текст сообщения.
        mesh_text = text[:MESH_TEXT_LIMIT]

        if not mesh_text:
            return False

        if len(text) > MESH_TEXT_LIMIT:
            self._log(
                f"{source_label} → Mesh[ch{channel}]: "
                f"текст сокращён с {len(text)} "
                f"до {len(mesh_text)} символов."
            )

        try:
            async with self._mesh_lock:
                mc = self.mc

                if mc is None:
                    self._log(
                        f"{source_label} → Mesh[ch{channel}]: "
                        "соединение отсутствует.",
                        "WARN",
                    )
                    return False

                self._outbound.remember(
                    ("mesh", channel, mesh_text),
                    ttl=180.0,
                )

                result = await asyncio.wait_for(
                    mc.commands.send_chan_msg(
                        channel,
                        mesh_text,
                    ),
                    timeout=SEND_TIMEOUT,
                )

                self._check_mesh_result(result)

            timestamp = time.monotonic()

            if source == "max":
                self.msg_timestamps_max.append(timestamp)
            elif source == "tg":
                self.msg_timestamps_tg.append(timestamp)

            self._log(
                f"{source_label} → Mesh[ch{channel}]: "
                f"отправлено {len(mesh_text)} символов."
            )

            self.event_queue.put(("flash", None))
            return True

        except asyncio.CancelledError:
            raise

        except asyncio.TimeoutError:
            # Не повторяем автоматически:
            # радио могло принять сообщение до таймаута.
            self._log(
                f"{source_label} → Mesh[ch{channel}]: "
                "таймаут. Автоповтор отключён, "
                "чтобы не создавать дубликаты.",
                "ERROR",
            )
            return False

        except Exception as exc:
            self._log(
                f"{source_label} → Mesh[ch{channel}]: {exc}",
                "ERROR",
            )
            return False

    # ============================ СТАТИСТИКА РАДИО ============================

    def _emit_telemetry(self, payload):
        if not isinstance(payload, dict):
            return

        mappings = {
            "battery_mv": (
                "battery_mv",
                "batt_mv",
                "battery",
            ),
            "uptime_s": (
                "uptime_s",
                "uptime_secs",
                "uptime",
            ),
            "rssi": (
                "rssi",
                "last_rssi",
            ),
            "snr": (
                "snr",
                "last_snr",
            ),
            "queue": (
                "queue",
                "queue_len",
                "tx_queue_len",
            ),
            "rx": (
                "rx",
                "rx_total",
                "rx_packets",
                "recv_packets",
            ),
            "tx": (
                "tx",
                "tx_total",
                "tx_packets",
                "sent_packets",
            ),
        }

        data = {}

        for target, keys in mappings.items():
            value = first_value(payload, *keys)

            if isinstance(value, (int, float)):
                data[target] = value

        if data:
            self.event_queue.put(("telemetry", data))

    async def _stats_loop(self):
        # Эти команды зависят от версии библиотеки и прошивки.
        # Если команда отсутствует, соответствующая карточка
        # остаётся без значения.
        unsupported = set()

        while not self._stop_event.is_set():
            if (
                self.mc is not None
                and not self.radio_monitor.zombie
            ):
                for name in (
                    "get_stats_core",
                    "get_stats_radio",
                ):
                    if name in unsupported:
                        continue

                    try:
                        result = await self._mesh_command(name)
                        payload = obj_get(
                            result,
                            "payload",
                            {},
                        ) or {}

                        self._emit_telemetry(payload)

                    except AttributeError:
                        unsupported.add(name)

                    except asyncio.CancelledError:
                        raise

                    except Exception as exc:
                        self._log(
                            f"Статистика {name}: {exc}",
                            "WARN",
                        )

            await self._pause(20.0)

    async def _summary_loop(self):
        while not self._stop_event.is_set():
            cutoff = time.monotonic() - 3600.0

            for timestamps in (
                self.msg_timestamps_mesh,
                self.msg_timestamps_max,
                self.msg_timestamps_tg,
            ):
                while timestamps and timestamps[0] < cutoff:
                    timestamps.popleft()

            limiter = self.rate_limiter
            monitor = self.radio_monitor

            self.event_queue.put((
                "summary",
                {
                    "queue": len(self.message_queue),
                    "allowed": limiter.allowed,
                    "queued": limiter.queued,
                    "dropped": limiter.dropped,
                    "mesh_rx": len(self.msg_timestamps_mesh),
                    "max_tx": len(self.msg_timestamps_max),
                    "tg_tx": len(self.msg_timestamps_tg),
                    "zombie": monitor.zombie,
                    "probes": monitor.total_probes,
                    "failed": monitor.failed_probes,
                    "tg_ready": self._tg_ready,
                    "tg_enabled": bool(
                        self._run_settings["tg_token"]
                    ),
                    "tg_proxy": self._run_settings["tg_use_proxy"],
                },
            ))

            await self._pause(2.0)

    # ============================ ОЧИСТКА И СЧЁТЧИКИ ============================

    def _clear_message_queue(self):
        def clear():
            count = len(self.message_queue)
            self.message_queue.clear()

            self._log(
                f"Очередь Mesh очищена: {count} сообщений.",
                "WARN",
            )

        if not self._call_in_loop(clear):
            self.message_queue.clear()
            self._log("Очередь Mesh пуста.")

    def _reset_counters(self):
        def reset():
            self.rate_limiter.reset_counters()
            self.radio_monitor.reset_counters()

            self.msg_timestamps_mesh.clear()
            self.msg_timestamps_max.clear()
            self.msg_timestamps_tg.clear()

            self._log("Счётчики сброшены.")

        if not self._call_in_loop(reset):
            reset()


# ============================ ЗАПУСК ============================

if __name__ == "__main__":
    app = MeshMaxApp()
    app.mainloop()
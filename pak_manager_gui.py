#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
UE Pak Tool v3.1 с улучшенной производительностью и интерфейсом

Основные улучшения:
• Оптимизированная работа с большими файлами
• Добавлен прогресс-бар для длительных операций
• Улучшенное управление памятью
• Поддержка новых форматов UE5
• Улучшенный интерфейс с темами оформления
• Расширенные возможности поиска
• Улучшенная обработка ошибок
• Дополнительные проверки безопасности

Разработчик: Greshnyy
Версия с улучшениями: 3.1
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
import tkinter.font as tkFont
import subprocess
import os
import zipfile
import platform
import configparser
import threading
import tempfile
import stat
import codecs
import difflib
import traceback
import sys
import glob
from datetime import datetime
from pathlib import Path
from typing import Optional, Tuple, Dict, Any, List, Union
import webbrowser
import requests
from packaging import version
import hashlib
from concurrent.futures import ThreadPoolExecutor, as_completed
import io

# Если установлен tkinterdnd2, используем его для drag-and-drop
try:
    from tkinterdnd2 import DND_FILES, TkinterDnD
    USE_DND = True
except ImportError:
    USE_DND = False
    print("Библиотека tkinterdnd2 не найдена. Drag-and-Drop будет недоступен.")

APP_NAME = "UE Pak Tool"
APP_VERSION = "3.1"
GITHUB_REPO = "Greshnyy/ue-pak-tool"  # Для проверки обновлений

# Конфигурационные константы
CONFIG_FILE = 'ue_pak_tool_config.ini'
CONFIG_SECTION_PATHS = 'Paths'
CONFIG_SECTION_LASTDIRS = 'LastDirs'
CONFIG_SECTION_UI = 'UI'
CONFIG_SECTION_PERFORMANCE = 'Performance'

# Ключи конфигурации
KEY_UNREALPAK_PATH = 'UnrealPakPath'

# Ключи для последних директорий
KEY_LAST_DIRS = [
    'LastUnpackSourceDir', 'LastUnpackDestDir',
    'LastPackSourceDir', 'LastPackDestDir',
    'LastOpenFileDir', 'LastIniViewDir',
    'LastPakUtilDir', 'LastAnalyzeDir',
    'LastCompareFile1Dir', 'LastCompareFile2Dir'
]

KEY_CUSTOM_COMPRESS_PARAMS = 'CustomCompressParams'
KEY_EXTERNAL_DIFF_TOOL = 'ExternalDiffTool'
KEY_THEME = 'Theme'  # 'dark' или 'light'
KEY_THREADS = 'MaxThreads'
KEY_CACHE_SIZE = 'CacheSizeMB'

# Фильтры для UE5-ассетов
UE5_ASSET_EXTENSIONS = [("UE5 Assets", "*.pak *.ucas *.utoc *.uasset *.umap"), ("Все файлы", "*.*")]

# Расширения файлов
EDITABLE_EXTENSIONS = ['.txt', '.ini', '.cfg', '.xml', '.json', '.log', '.csv', '.py', '.lua', '.yaml', '.yml']
INI_EXTENSIONS = [("INI files", "*.ini"), ("Все файлы", "*.*")]
COMPARABLE_EXTENSIONS = [
    ("Конф. файлы", "*.ini *.cfg *.xml *.json *.yaml *.yml"),
    ("Лог-файлы", "*.log"),
    ("Текстовые файлы", "*.txt"),
    ("Все файлы", "*.*")
]
PAK_EXTENSIONS = [("Pak архивы", "*.pak"), ("Все файлы", "*.*")]
ARCHIVE_EXTENSIONS = [("Архивы (pak, zip)", "*.pak *.zip"), ("Pak архивы", "*.pak"), ("Zip архивы", "*.zip"), ("Все файлы", "*.*")]
TEXT_LIKE_EXTENSIONS = [("Текст/Конфиги", "*.txt *.ini *.cfg *.xml *.json *.log *.csv *.py *.lua *.yaml *.yml"), ("Все файлы", "*.*")]

class FileCache:
    """Класс для кэширования файловых операций"""
    def __init__(self, max_size_mb: int = 100):
        self.max_size = max_size_mb * 1024 * 1024  # Конвертируем в байты
        self.cache = {}
        self.current_size = 0
        self.lock = threading.Lock()

    def get(self, filepath: str) -> Optional[bytes]:
        """Получает содержимое файла из кэша"""
        key = self._get_cache_key(filepath)
        with self.lock:
            if key in self.cache:
                # Обновляем время доступа для LRU
                data = self.cache.pop(key)
                self.cache[key] = data
                return data[0]
        return None

    def put(self, filepath: str, data: bytes) -> None:
        """Добавляет данные в кэш"""
        key = self._get_cache_key(filepath)
        size = len(data)
        
        with self.lock:
            # Освобождаем место, если нужно
            while self.current_size + size > self.max_size and self.cache:
                oldest_key = next(iter(self.cache))
                oldest_data = self.cache.pop(oldest_key)
                self.current_size -= len(oldest_data[0])
            
            # Добавляем новые данные
            self.cache[key] = (data, datetime.now())
            self.current_size += size

    def _get_cache_key(self, filepath: str) -> str:
        """Создает уникальный ключ для файла"""
        file_stat = os.stat(filepath)
        return f"{filepath}:{file_stat.st_size}:{file_stat.st_mtime}"

class UpdateChecker:
    @staticmethod
    def check_for_updates(current_version: str) -> Tuple[bool, str, str]:
        """Проверяет наличие обновлений на GitHub.
        Возвращает (is_update_available, latest_version, release_url)"""
        try:
            api_url = f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest"
            response = requests.get(api_url, timeout=5)
            response.raise_for_status()
            release_info = response.json()
            latest_version = release_info['tag_name'].lstrip('v')
            
            if version.parse(latest_version) > version.parse(current_version):
                return True, latest_version, release_info['html_url']
        except Exception as e:
            print(f"Ошибка при проверке обновлений: {e}")
        return False, "", ""

class CreateToolTip:
    """Создает всплывающую подсказку для виджета Tkinter."""
    def __init__(self, widget, text='widget info'):
        self.widget = widget
        self.text = text
        self.waittime = 500  # мс до появления
        self.wraplength = 250  # максимальная ширина текста
        self._after_id = None
        self._tooltip_window = None
        self.widget.bind("<Enter>", self._enter, add='+')
        self.widget.bind("<Leave>", self._leave, add='+')
        self.widget.bind("<ButtonPress>", self._leave, add='+')

    def _enter(self, event=None):
        self._schedule()

    def _leave(self, event=None):
        self._unschedule()
        self._hidetip()

    def _schedule(self):
        self._unschedule()
        self._after_id = self.widget.after(self.waittime, self._showtip)

    def _unschedule(self):
        if self._after_id:
            try:
                self.widget.after_cancel(self._after_id)
            except Exception:
                pass
            self._after_id = None

    def _showtip(self):
        if self._tooltip_window or not self.widget.winfo_exists():
            return

        try:
            x, y, _, _ = self.widget.bbox("insert")
            x += self.widget.winfo_rootx() + 25
            y += self.widget.winfo_rooty() + 20
        except (tk.TclError, TypeError):
            x = self.widget.winfo_pointerx() + 10
            y = self.widget.winfo_pointery() + 10

        self._tooltip_window = tw = tk.Toplevel(self.widget)
        tw.wm_overrideredirect(True)
        tw.wm_geometry(f"+{x}+{y}")
        label = tk.Label(tw, text=self.text, justify='left', background="#ffffe0",
                         relief='solid', borderwidth=1, wraplength=self.wraplength,
                         font=("tahoma", 8, "normal"))
        label.pack(ipadx=1)

    def _hidetip(self):
        if self._tooltip_window:
            try:
                self._tooltip_window.destroy()
            except Exception:
                pass
            self._tooltip_window = None

class UEPakToolApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title(f"{APP_NAME} v{APP_VERSION}")
        self._load_initial_config()
        self.root.geometry("900x750")
        
        # Инициализация кэша
        self.file_cache = FileCache()
        
        # Инициализация переменных
        self.theme_var = tk.StringVar(value=self.config_data.get(KEY_THEME, 'dark'))
        self.compress_pak_var = tk.BooleanVar(value=False)
        self.status_var = tk.StringVar(value="Готово.")
        self.progress_var = tk.DoubleVar()
        
        # Настройка стилей
        self._setup_styles_and_fonts()
        self._create_header()

        # Инициализация виджетов
        self.log_text: Optional[scrolledtext.ScrolledText] = None
        self.status_bar: Optional[ttk.Label] = None
        self.progress_bar: Optional[ttk.Progressbar] = None
        self.action_buttons: list = []
        self.ini_viewer_text: Optional[scrolledtext.ScrolledText] = None
        self.ini_filepath_label_var = tk.StringVar(value="Файл не загружен")
        self.progress_window = None
        self.diff_file1: Optional[str] = None
        self.diff_file2: Optional[str] = None
        self.diff_text: Optional[scrolledtext.ScrolledText] = None
        self.asset_analysis_text: Optional[scrolledtext.ScrolledText] = None
        self.notebook: Optional[ttk.Notebook] = None
        self.search_entry: Optional[ttk.Entry] = None
        self.search_results: List[str] = []

        # Создание интерфейса
        self._create_widgets()
        self._log_initial_config()

        # Настройка Drag-and-Drop
        if USE_DND:
            self._create_drag_and_drop_area()
            self.log_message("Drag-and-Drop активен (библиотека tkinterdnd2 найдена).")
        else:
            self.log_message("Drag-and-Drop недоступен (библиотека tkinterdnd2 не найдена).")
            
        # Первичная проверка пути к UnrealPak (тихая)
        self.root.after(100, lambda: self._check_unrealpak_path(silent=True))
        # Проверка обновлений (в фоне)
        self.root.after(1000, self._check_updates_background)

    def _save_log_to_file(self):
        """Сохраняет содержимое лога в файл."""
        if not self.log_text:
            return
        
        last_dir = self._get_last_dir('LastOpenFileDir', os.path.expanduser("~"))
        
        file_path = filedialog.asksaveasfilename(
            title="Сохранить лог как...",
            initialdir=last_dir,
            filetypes=[("Текстовые файлы", "*.txt"), ("Все файлы", "*.*")],
            defaultextension=".txt",
            parent=self.root
        )
        
        if file_path:
            try:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(self.log_text.get(1.0, tk.END))
                
                self.log_message(f"Лог сохранен в файл: {file_path}")
                self._save_config_value('LastOpenFileDir', str(Path(file_path).parent))
            except Exception as e:
                messagebox.showerror("Ошибка", f"Не удалось сохранить лог: {e}", parent=self.root)

    def _load_initial_config(self):
        """Загружает конфигурацию из файла."""
        config = configparser.ConfigParser()
        config_data = {
            KEY_UNREALPAK_PATH: None,
            KEY_CUSTOM_COMPRESS_PARAMS: "",
            KEY_EXTERNAL_DIFF_TOOL: "",
            KEY_THEME: "dark",
            KEY_THREADS: str(min(32, (os.cpu_count() or 1) + 4)),
            KEY_CACHE_SIZE: "100"  # 100 MB по умолчанию
        }
        
        # Добавляем ключи для последних директорий
        for key in KEY_LAST_DIRS:
            config_data[key] = None

        if os.path.exists(CONFIG_FILE):
            try:
                config.read(CONFIG_FILE, encoding='utf-8')
                
                # Загрузка секции Paths
                if config.has_section(CONFIG_SECTION_PATHS):
                    for key in [KEY_UNREALPAK_PATH, KEY_CUSTOM_COMPRESS_PARAMS, KEY_EXTERNAL_DIFF_TOOL]:
                        if key in config_data:
                            config_data[key] = config.get(CONFIG_SECTION_PATHS, key, fallback=config_data[key])
                
                # Загрузка секции LastDirs
                if config.has_section(CONFIG_SECTION_LASTDIRS):
                    for key in KEY_LAST_DIRS:
                        loaded = config.get(CONFIG_SECTION_LASTDIRS, key, fallback=None)
                        config_data[key] = loaded if (loaded and os.path.isdir(loaded)) else None
                
                # Загрузка секции UI
                if config.has_section(CONFIG_SECTION_UI):
                    config_data[KEY_THEME] = config.get(CONFIG_SECTION_UI, KEY_THEME, fallback="dark")
                
                # Загрузка секции Performance
                if config.has_section(CONFIG_SECTION_PERFORMANCE):
                    config_data[KEY_THREADS] = config.get(CONFIG_SECTION_PERFORMANCE, KEY_THREADS, fallback=config_data[KEY_THREADS])
                    config_data[KEY_CACHE_SIZE] = config.get(CONFIG_SECTION_PERFORMANCE, KEY_CACHE_SIZE, fallback=config_data[KEY_CACHE_SIZE])
                
            except Exception as e:
                print(f"Error loading config: {e}\n{traceback.format_exc()}")

        self.config_data = config_data
        # Обновляем размер кэша
        self.file_cache = FileCache(max_size_mb=int(self.config_data[KEY_CACHE_SIZE]))

    def _save_config_value(self, key: str, value: Any):
        """Сохраняет значение в конфиг и в файл."""
        if key in self.config_data:
            self.config_data[key] = value
            
            config = configparser.ConfigParser()
            if os.path.exists(CONFIG_FILE):
                try:
                    config.read(CONFIG_FILE, encoding='utf-8')
                except Exception:
                    pass

            # Определяем секцию для ключа
            if key in [KEY_UNREALPAK_PATH, KEY_CUSTOM_COMPRESS_PARAMS, KEY_EXTERNAL_DIFF_TOOL]:
                section = CONFIG_SECTION_PATHS
            elif key in KEY_LAST_DIRS:
                section = CONFIG_SECTION_LASTDIRS
            elif key == KEY_THEME:
                section = CONFIG_SECTION_UI
            elif key in [KEY_THREADS, KEY_CACHE_SIZE]:
                section = CONFIG_SECTION_PERFORMANCE
            else:
                section = None

            if section:
                if not config.has_section(section):
                    config.add_section(section)
                config.set(section, key, str(value) if value is not None else '')

            try:
                with open(CONFIG_FILE, 'w', encoding='utf-8') as f:
                    config.write(f)
            except Exception as e:
                print(f"Error saving config: {e}")

    def _setup_styles_and_fonts(self):
        """Настраивает стили и шрифты в зависимости от выбранной темы."""
        self.style = ttk.Style()
        
        # Пробуем использовать тему 'clam'
        try:
            self.style.theme_use("clam")
        except tk.TclError:
            pass

        families = tkFont.families()
        default_font_family = "Segoe UI" if "Segoe UI" in families else "Helvetica"
        consolas_family = "Consolas" if "Consolas" in families else "Courier"

        # Базовые шрифты
        self.default_font = (default_font_family, 9)
        self.bold_font = (default_font_family, 9, "bold")
        self.small_font = (default_font_family, 8)
        self.log_font = (consolas_family, 9)
        self.large_button_font = (default_font_family, 10, "bold")
        self.tab_font = (default_font_family, 10, "bold")

        # Цвета для тем
        if self.theme_var.get() == 'light':
            self._setup_light_theme()
        else:
            self._setup_dark_theme()

    def _setup_dark_theme(self):
        """Настраивает темную тему."""
        bg_color = "#2C3E50"
        fg_color = "#ECF0F1"
        btn_bg = "#34495E"
        btn_active_bg = "#2980B9"
        header_bg = "#1ABC9C"
        status_bg = "#34495E"
        filepath_fg = "#BDC3C7"
        text_bg = "#1C2833"
        text_fg = "#EAECEE"
        select_bg = "#0078D7"
        entry_bg = "#34495E"
        entry_fg = "#ECF0F1"
        entry_highlight = "#2980B9"

        self.style.configure('.', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.configure('TButton', background=btn_bg, foreground=fg_color, font=self.default_font, padding=5)
        self.style.map('TButton', background=[('active', btn_active_bg)])
        self.style.configure('Large.TButton', font=self.large_button_font, padding=8)
        self.style.configure('Small.TButton', font=self.default_font, padding=3)
        self.style.configure('TLabel', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.configure('Status.TLabel', background=status_bg, foreground=fg_color, font=self.small_font)
        self.style.configure('FilePath.TLabel', background=bg_color, foreground=filepath_fg, font=self.small_font)
        self.style.configure('TNotebook', background=bg_color, borderwidth=0)
        self.style.configure('TNotebook.Tab', background=btn_bg, foreground=fg_color, padding=[10, 5], font=self.tab_font, borderwidth=1)
        self.style.map('TNotebook.Tab', background=[('selected', btn_active_bg), ('active', '#4E647A')])
        self.style.configure('TFrame', background=bg_color)
        self.style.configure('TLabelframe', background=bg_color, foreground=fg_color, font=self.bold_font)
        self.style.configure('TLabelframe.Label', background=bg_color, foreground=fg_color, font=self.bold_font)
        self.style.configure('TCheckbutton', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.map('TCheckbutton', indicatorcolor=[('selected', header_bg), ('!selected', fg_color)],
                       background=[('active', '#3E5164')])
        self.style.configure("Note.TLabel", background="#4A617A", foreground="#FFFFFF")
        self.style.configure("Header.TFrame", background=self.style.lookup('TNotebook.Tab', 'background', ('selected',)))
        self.style.configure("Header.TLabel", background=self.style.lookup('Header.TFrame', 'background'),
                             foreground="#FFFFFF", font=("Segoe UI", 16, "bold"))
        self.style.configure('TEntry', fieldbackground=entry_bg, foreground=entry_fg, insertcolor=entry_fg)
        self.style.map('TEntry', fieldbackground=[('focus', entry_bg)], highlightcolor=[('focus', entry_highlight)])

        # Настройки для текстовых виджетов
        self.text_bg = text_bg
        self.text_fg = text_fg
        self.select_bg = select_bg

    def ask_and_save_unrealpak_path(self):
        """Запрашивает у пользователя путь к UnrealPak.exe и сохраняет его в конфиг."""
        last_dir = os.path.dirname(self.config_data.get(KEY_UNREALPAK_PATH, "")) or os.path.expanduser("~")
        
        file_path = filedialog.askopenfilename(
            title="Укажите путь к UnrealPak.exe",
            initialdir=last_dir,
            filetypes=[("Executable files", "*.exe"), ("All files", "*.*")],
            parent=self.root
        )
        
        if file_path:
            self._save_config_value(KEY_UNREALPAK_PATH, file_path)
            self.log_message(f"Путь к UnrealPak сохранен: {file_path}")
            self._check_unrealpak_path(silent=False)

    def _show_about_info(self):
        """Показывает информацию о программе."""
        about_text = f"""
        {APP_NAME} v{APP_VERSION}
        
        Инструмент для работы с архивами Unreal Engine (.pak, .ucas, .utoc)
        
        Основные функции:
        - Распаковка и упаковка .pak архивов
        - Просмотр содержимого архивов
        - Анализ UE5-ассетов
        - Сравнение файлов
        
        Разработчик: Greshnyy
        Лицензия: MIT
        
        GitHub: https://github.com/{GITHUB_REPO}
        """
        
        messagebox.showinfo("О программе", about_text.strip(), parent=self.root)
        self.log_message("Открыто окно 'О программе'")

    def _select_file_and_unpack(self):
        """Выбирает файл архива и распаковывает его."""
        last_dir = self._get_last_dir('LastUnpackSourceDir', os.path.expanduser("~"))
        
        file_path = filedialog.askopenfilename(
            title="Выберите архив для распаковки",
            initialdir=last_dir,
            filetypes=ARCHIVE_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastUnpackSourceDir', str(Path(file_path).parent))
            
            default_dir = Path(file_path).parent / f"{Path(file_path).stem}_unpacked"
            dir_path = filedialog.askdirectory(
                title="Выберите папку для распаковки",
                initialdir=str(default_dir),
                parent=self.root
            )
            
            if dir_path:
                self._save_config_value('LastUnpackDestDir', dir_path)
                self._unpack_archive(file_path, dir_path)

    def _unpack_archive(self, archive_path: str, output_dir: str):
        """Распаковывает архив с отображением прогресса."""
        self._show_progress_window("Распаковка архива", f"Распаковка {Path(archive_path).name}...")
        
        try:
            if Path(archive_path).suffix.lower() == '.zip':
                self._unpack_zip(archive_path, output_dir)
            else:
                self._unpack_pak(archive_path, output_dir)
                
            messagebox.showinfo("Готово", "Архив успешно распакован.", parent=self.root)
            self.log_message(f"Архив распакован: {archive_path} → {output_dir}")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось распаковать архив:\n{e}", parent=self.root)
            self.log_message(f"Ошибка распаковки: {e}")
        finally:
            self._hide_progress_window()

    def _unpack_zip(self, zip_path: str, output_dir: str):
        """Распаковывает ZIP архив."""
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            total_files = len(zip_ref.infolist())
            for i, file in enumerate(zip_ref.infolist(), 1):
                zip_ref.extract(file, output_dir)
                self._update_progress(int(i / total_files * 100))
                self._update_progress_window(
                    "Распаковка ZIP",
                    f"Распаковка {Path(zip_path).name}\nФайл {i} из {total_files}"
                )

    def _unpack_pak(self, pak_path: str, output_dir: str):
        """Распаковывает PAK архив с помощью UnrealPak."""
        if not self._check_unrealpak_path(silent=True):
            raise Exception("Путь к UnrealPak не настроен или неверен")
        
        args = [
            pak_path,
            "-Extract",
            output_dir
        ]
        
        stdout, stderr = self._run_unrealpak_command(args, "Распаковка PAK")
        
        if "error" in stderr.lower():
            raise Exception(f"Ошибка распаковки: {stderr}")

    def _configure_compression_settings(self):
        """Настраивает параметры сжатия."""
        current_params = self.config_data.get(KEY_CUSTOM_COMPRESS_PARAMS, "")
        
        new_params = simpledialog.askstring(
            "Параметры сжатия",
            "Введите дополнительные параметры сжатия (например, -compressionformat=Zlib):",
            initialvalue=current_params,
            parent=self.root
        )
        
        if new_params is not None:
            self._save_config_value(KEY_CUSTOM_COMPRESS_PARAMS, new_params)
            self.log_message(f"Параметры сжатия обновлены: {new_params}")

    def _configure_external_diff_tool(self):
        """Настраивает внешний инструмент для сравнения файлов."""
        last_dir = os.path.dirname(self.config_data.get(KEY_EXTERNAL_DIFF_TOOL, "")) or os.path.expanduser("~")
        
        file_path = filedialog.askopenfilename(
            title="Укажите путь к внешнему Diff Tool",
            initialdir=last_dir,
            filetypes=[("Executable files", "*.exe"), ("All files", "*.*")],
            parent=self.root
        )
        
        if file_path:
            self._save_config_value(KEY_EXTERNAL_DIFF_TOOL, file_path)
            self.log_message(f"Внешний Diff Tool сохранен: {file_path}")

    def _check_unrealpak_path(self, silent=True):
        """Проверяет, установлен ли путь к UnrealPak и доступен ли он."""
        unrealpak = self.config_data.get(KEY_UNREALPAK_PATH)
        
        if not unrealpak:
            if not silent:
                messagebox.showwarning("Внимание", "Путь к UnrealPak не настроен.", parent=self.root)
            return False
        
        if not os.path.isfile(unrealpak):
            if not silent:
                messagebox.showerror("Ошибка", f"Файл UnrealPak не найден по указанному пути:\n{unrealpak}", parent=self.root)
            return False
        
        if not silent:
            messagebox.showinfo("Проверка", f"UnrealPak найден:\n{unrealpak}", parent=self.root)
            self.log_message(f"Проверка UnrealPak: файл существует ({unrealpak})")
        
        return True

    def _check_updates_background(self):
        """Проверяет обновления в фоновом режиме."""
        def check():
            try:
                has_update, latest_version, url = UpdateChecker.check_for_updates(APP_VERSION)
                if has_update:
                    self.root.after(0, lambda: self._show_update_available(latest_version, url))
            except Exception as e:
                self.log_message(f"Ошибка при проверке обновлений: {e}")

        threading.Thread(target=check, daemon=True).start()

    def _check_updates_manual(self):
        """Проверяет обновления по запросу пользователя."""
        self.log_message("Проверка обновлений...")
        self.set_status("Проверка обновлений...")
        
        try:
            has_update, latest_version, url = UpdateChecker.check_for_updates(APP_VERSION)
            if has_update:
                self._show_update_available(latest_version, url)
            else:
                messagebox.showinfo("Обновления", "У вас установлена последняя версия.", parent=self.root)
                self.log_message("Обновлений не найдено.")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось проверить обновления:\n{e}", parent=self.root)
            self.log_message(f"Ошибка проверки обновлений: {e}")
        finally:
            self.set_status("Готово.")

    def _show_update_available(self, version: str, url: str):
        """Показывает сообщение о доступном обновлении."""
        msg = f"Доступна новая версия {version} (у вас {APP_VERSION}).\nХотите перейти на страницу загрузки?"
        if messagebox.askyesno("Доступно обновление", msg, parent=self.root):
            webbrowser.open(url)
            self.log_message(f"Открыта страница загрузки: {url}")

    def _setup_light_theme(self):
        """Настраивает светлую тему."""
        bg_color = "#F5F5F5"
        fg_color = "#333333"
        btn_bg = "#E0E0E0"
        btn_active_bg = "#64B5F6"
        header_bg = "#4CAF50"
        status_bg = "#E0E0E0"
        filepath_fg = "#666666"
        text_bg = "#FFFFFF"
        text_fg = "#000000"
        select_bg = "#2196F3"
        entry_bg = "#FFFFFF"
        entry_fg = "#000000"
        entry_highlight = "#64B5F6"

        self.style.configure('.', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.configure('TButton', background=btn_bg, foreground=fg_color, font=self.default_font, padding=5)
        self.style.map('TButton', background=[('active', btn_active_bg)])
        self.style.configure('Large.TButton', font=self.large_button_font, padding=8)
        self.style.configure('Small.TButton', font=self.default_font, padding=3)
        self.style.configure('TLabel', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.configure('Status.TLabel', background=status_bg, foreground=fg_color, font=self.small_font)
        self.style.configure('FilePath.TLabel', background=bg_color, foreground=filepath_fg, font=self.small_font)
        self.style.configure('TNotebook', background=bg_color, borderwidth=0)
        self.style.configure('TNotebook.Tab', background=btn_bg, foreground=fg_color, padding=[10, 5], font=self.tab_font, borderwidth=1)
        self.style.map('TNotebook.Tab', background=[('selected', btn_active_bg), ('active', '#BBDEFB')])
        self.style.configure('TFrame', background=bg_color)
        self.style.configure('TLabelframe', background=bg_color, foreground=fg_color, font=self.bold_font)
        self.style.configure('TLabelframe.Label', background=bg_color, foreground=fg_color, font=self.bold_font)
        self.style.configure('TCheckbutton', background=bg_color, foreground=fg_color, font=self.default_font)
        self.style.map('TCheckbutton', indicatorcolor=[('selected', header_bg), ('!selected', fg_color)],
                       background=[('active', '#E0E0E0')])
        self.style.configure("Note.TLabel", background="#CFD8DC", foreground="#000000")
        self.style.configure("Header.TFrame", background=self.style.lookup('TNotebook.Tab', 'background', ('selected',)))
        self.style.configure("Header.TLabel", background=self.style.lookup('Header.TFrame', 'background'),
                             foreground="#FFFFFF", font=("Segoe UI", 16, "bold"))
        self.style.configure('TEntry', fieldbackground=entry_bg, foreground=entry_fg, insertcolor=entry_fg)
        self.style.map('TEntry', fieldbackground=[('focus', entry_bg)], highlightcolor=[('focus', entry_highlight)])

        # Настройки для текстовых виджетов
        self.text_bg = text_bg
        self.text_fg = text_fg
        self.select_bg = select_bg

    def _toggle_theme(self):
        """Переключает между темной и светлой темой."""
        new_theme = 'light' if self.theme_var.get() == 'dark' else 'dark'
        self.theme_var.set(new_theme)
        self._save_config_value(KEY_THEME, new_theme)
        self._setup_styles_and_fonts()
        self._update_widgets_colors()

    def _update_widgets_colors(self):
        """Обновляет цвета виджетов при смене темы."""
        # Текстовые виджеты
        if self.log_text and hasattr(self.log_text, 'winfo_exists') and self.log_text.winfo_exists():
            self.log_text.config(bg=self.text_bg, fg=self.text_fg, selectbackground=self.select_bg)
        if self.ini_viewer_text and hasattr(self.ini_viewer_text, 'winfo_exists') and self.ini_viewer_text.winfo_exists():
            self.ini_viewer_text.config(bg=self.text_bg, fg=self.text_fg, selectbackground=self.select_bg)
        if self.diff_text and hasattr(self.diff_text, 'winfo_exists') and self.diff_text.winfo_exists():
            self.diff_text.config(bg=self.text_bg, fg=self.text_fg, selectbackground=self.select_bg)
        if self.asset_analysis_text and hasattr(self.asset_analysis_text, 'winfo_exists') and self.asset_analysis_text.winfo_exists():
            self.asset_analysis_text.config(bg=self.text_bg, fg=self.text_fg, selectbackground=self.select_bg)
        
        # Поле поиска
        if self.search_entry and hasattr(self.search_entry, 'winfo_exists') and self.search_entry.winfo_exists():
            self.search_entry.config(style='TEntry')

    def _create_header(self):
        """Создает заголовок приложения с кнопкой переключения темы."""
        header_frame = ttk.Frame(self.root, style="Header.TFrame", height=50)
        header_frame.pack(fill=tk.X, side=tk.TOP)
        
        # Левая часть - название
        title_frame = ttk.Frame(header_frame)
        title_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        title_label = ttk.Label(title_frame, text=f"{APP_NAME} v{APP_VERSION}",
                              style="Header.TLabel", anchor="center")
        title_label.pack(pady=10)
        
        # Правая часть - кнопка темы
        theme_frame = ttk.Frame(header_frame)
        theme_frame.pack(side=tk.RIGHT, padx=10)
        
        theme_btn = ttk.Button(theme_frame, text="☀️" if self.theme_var.get() == 'dark' else "🌙",
                             command=self._toggle_theme, style='Small.TButton', width=3)
        theme_btn.pack(pady=5)
        CreateToolTip(theme_btn, "Переключить тему (темная/светлая)")

    def _create_widgets(self):
        """Создает основные виджеты интерфейса."""
        menu_bar = tk.Menu(self.root)

        # Меню "Файл"
        file_menu = tk.Menu(menu_bar, tearoff=0)
        file_menu.add_command(label="Сохранить лог в файл...", command=self._save_log_to_file)
        file_menu.add_separator()
        file_menu.add_command(label="Выход", command=self.root.quit)
        menu_bar.add_cascade(label="Файл", menu=file_menu)

        # Меню "Настройки"
        settings_menu = tk.Menu(menu_bar, tearoff=0)
        settings_menu.add_command(label="Указать путь к UnrealPak.exe...", command=self.ask_and_save_unrealpak_path)
        settings_menu.add_command(label="Параметры сжатия...", command=self._configure_compression_settings)
        settings_menu.add_command(label="Указать внешний Diff Tool...", command=self._configure_external_diff_tool)
        settings_menu.add_separator()
        settings_menu.add_command(label="Настройки производительности...", command=self._configure_performance_settings)
        settings_menu.add_separator()
        settings_menu.add_command(label="Проверить путь к UnrealPak", command=lambda: self._check_unrealpak_path(silent=False))
        menu_bar.add_cascade(label="Настройки", menu=settings_menu)

        # Меню "Справка"
        help_menu = tk.Menu(menu_bar, tearoff=0)
        help_menu.add_command(label="Проверить обновления", command=self._check_updates_manual)
        help_menu.add_separator()
        help_menu.add_command(label="О программе", command=self._show_about_info)
        menu_bar.add_cascade(label="Справка", menu=help_menu)

        self.root.config(menu=menu_bar)

        # Основная область с вкладками
        self.notebook = ttk.Notebook(self.root, padding="5")
        self.notebook.pack(pady=10, padx=10, expand=True, fill="both")

        self.action_buttons = []

        # Создаем вкладки
        self._create_archive_tab()
        self._create_open_file_tab()
        self._create_ini_viewer_tab()
        self._create_batch_tab()
        self._create_diff_tab()
        self._create_asset_analyzer_tab()

        self._collect_action_buttons()

        # Область логов
        log_frame = ttk.LabelFrame(self.root, text="Лог операций", padding="10")
        log_frame.pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        # Добавляем поиск в лог
        search_frame = ttk.Frame(log_frame)
        search_frame.pack(fill=tk.X, pady=(0, 5))
        
        self.search_entry = ttk.Entry(search_frame)
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        self.search_entry.bind("<Return>", lambda e: self._search_in_log())
        
        search_btn = ttk.Button(search_frame, text="Поиск", command=self._search_in_log, style="Small.TButton")
        search_btn.pack(side=tk.RIGHT)

        self.log_text = scrolledtext.ScrolledText(log_frame, wrap=tk.WORD, state=tk.DISABLED, height=10, 
                                                 font=self.log_font, bg=self.text_bg, fg=self.text_fg, 
                                                 relief=tk.FLAT, borderwidth=2, selectbackground=self.select_bg)
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self._setup_text_widget_context_menu(self.log_text, read_only=True)

        # Строка статуса и прогресс-бар
        status_frame = ttk.Frame(self.root)
        status_frame.pack(side=tk.BOTTOM, fill=tk.X)
        
        self.progress_bar = ttk.Progressbar(status_frame, variable=self.progress_var, maximum=100, mode='determinate')
        self.progress_bar.pack(fill=tk.X, side=tk.TOP)
        
        self.status_bar = ttk.Label(status_frame, textvariable=self.status_var, relief=tk.SUNKEN, 
                                   anchor=tk.W, padding="2 5", style='Status.TLabel')
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM)
        self.set_status("Готово.")

    def _search_in_log(self):
        """Выполняет поиск текста в логе."""
        search_text = self.search_entry.get()
        if not search_text:
            return
            
        self.log_text.tag_remove('search', '1.0', tk.END)
        self.log_text.tag_config('search', background='yellow', foreground='black')
        
        count = 0
        idx = '1.0'
        while True:
            idx = self.log_text.search(search_text, idx, nocase=True, stopindex=tk.END)
            if not idx:
                break
                
            lastidx = f"{idx}+{len(search_text)}c"
            self.log_text.tag_add('search', idx, lastidx)
            count += 1
            idx = lastidx
            
        if count > 0:
            self.set_status(f"Найдено {count} совпадений для '{search_text}'")
        else:
            self.set_status(f"Текст '{search_text}' не найден")

    def _configure_performance_settings(self):
        """Настраивает параметры производительности."""
        self.log_message("Запрос параметров производительности...")
        
        current_threads = self.config_data.get(KEY_THREADS, str(min(32, (os.cpu_count() or 1) + 4)))
        current_cache = self.config_data.get(KEY_CACHE_SIZE, "100")
        
        settings_window = tk.Toplevel(self.root)
        settings_window.title("Настройки производительности")
        settings_window.transient(self.root)
        settings_window.grab_set()
        
        ttk.Label(settings_window, text="Макс. потоков:").grid(row=0, column=0, padx=5, pady=5, sticky="e")
        threads_entry = ttk.Entry(settings_window)
        threads_entry.insert(0, current_threads)
        threads_entry.grid(row=0, column=1, padx=5, pady=5, sticky="w")
        
        ttk.Label(settings_window, text="Размер кэша (MB):").grid(row=1, column=0, padx=5, pady=5, sticky="e")
        cache_entry = ttk.Entry(settings_window)
        cache_entry.insert(0, current_cache)
        cache_entry.grid(row=1, column=1, padx=5, pady=5, sticky="w")
        
        def save_settings():
            try:
                threads = int(threads_entry.get())
                cache = int(cache_entry.get())
                
                if threads < 1 or threads > 64:
                    raise ValueError("Количество потоков должно быть от 1 до 64")
                if cache < 10 or cache > 1024:
                    raise ValueError("Размер кэша должен быть от 10 до 1024 MB")
                
                self._save_config_value(KEY_THREADS, str(threads))
                self._save_config_value(KEY_CACHE_SIZE, str(cache))
                self.file_cache = FileCache(max_size_mb=cache)
                
                self.log_message(f"Настройки производительности обновлены: потоки={threads}, кэш={cache}MB")
                settings_window.destroy()
                messagebox.showinfo("Сохранено", "Настройки производительности сохранены.", parent=self.root)
            except ValueError as e:
                messagebox.showerror("Ошибка", str(e), parent=settings_window)

        ttk.Button(settings_window, text="Сохранить", command=save_settings).grid(row=2, column=0, columnspan=2, pady=10)

    def _update_progress(self, value: int):
        """Обновляет значение прогресс-бара."""
        def update():
            if self.progress_bar and hasattr(self.progress_bar, 'winfo_exists') and self.progress_bar.winfo_exists():
                self.progress_var.set(value)
                
        if self.root and hasattr(self.root, 'winfo_exists') and self.root.winfo_exists():
            self.root.after_idle(update)

    def _show_progress_window(self, title: str, message: str):
        """Показывает окно с индикатором выполнения."""
        if self.progress_window is not None and hasattr(self.progress_window, 'winfo_exists') and self.progress_window.winfo_exists():
            self._update_progress_window(title, message)
            return

        self.progress_window = pw = tk.Toplevel(self.root)
        pw.title(title)
        pw.geometry("400x120")
        pw.resizable(False, False)
        pw.transient(self.root)
        pw.protocol("WM_DELETE_WINDOW", lambda: None)

        root_x = self.root.winfo_x()
        root_y = self.root.winfo_y()
        root_w = self.root.winfo_width()
        root_h = self.root.winfo_height()
        pw_w = 400
        pw_h = 120
        x = root_x + (root_w - pw_w) // 2
        y = root_y + (root_h - pw_h) // 2
        pw.geometry(f"+{x}+{y}")

        self.progress_label = ttk.Label(pw, text=message, anchor="center", wraplength=380)
        self.progress_label.pack(pady=10, padx=10, fill=tk.X)

        self.progress_window_bar = ttk.Progressbar(pw, variable=self.progress_var, maximum=100, mode='determinate')
        self.progress_window_bar.pack(fill=tk.X, padx=20, pady=(5,15))
        pw.grab_set()

    def _update_progress_window(self, title: str, message: str):
        """Обновляет окно прогресса."""
        if self.progress_window and hasattr(self.progress_window, 'winfo_exists') and self.progress_window.winfo_exists():
            self.progress_window.title(title)
            if hasattr(self, 'progress_label') and self.progress_label and hasattr(self.progress_label, 'winfo_exists') and self.progress_label.winfo_exists():
                self.progress_label.config(text=message)

    def _hide_progress_window(self):
        """Скрывает окно с индикатором выполнения."""
        if self.progress_window and hasattr(self.progress_window, 'winfo_exists') and self.progress_window.winfo_exists():
            try:
                self.progress_window.grab_release()
                self.progress_window.destroy()
            except Exception as e:
                self.log_message(f"Ошибка скрытия окна прогресса: {e}")
            self.progress_window = None
            self.progress_label = None
            self.progress_window_bar = None

    def _run_unrealpak_command(self, args: list, operation_desc: str) -> Tuple[str, str]:
        """Запускает команду UnrealPak и возвращает stdout и stderr."""
        unrealpak = self.config_data.get(KEY_UNREALPAK_PATH)
        if not unrealpak:
            raise Exception("Путь к UnrealPak не настроен.")
            
        cmd = [unrealpak] + args
        
        self.log_message(f"Команда ({operation_desc}): {' '.join(map(str, cmd))}")
        self.set_status(f"Выполняется: {operation_desc}...")
        
        stdout_str, stderr_str = "", ""
        
        try:
            startupinfo = None
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE

            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  startupinfo=startupinfo,
                                  creationflags=subprocess.CREATE_NO_WINDOW if platform.system() == "Windows" else 0,
                                  text=True, encoding='utf-8', errors='replace')

            # Чтение вывода в реальном времени с обновлением прогресса
            while True:
                output = proc.stdout.readline()
                if output == '' and proc.poll() is not None:
                    break
                if output:
                    stdout_str += output
                    self.log_message(output.strip())
                    
                    # Попытка извлечь прогресс из вывода (если есть)
                    if '%' in output:
                        try:
                            percent = int(output.split('%')[0].split()[-1])
                            self._update_progress(percent)
                        except (ValueError, IndexError):
                            pass

            stderr_str = proc.stderr.read()
            
            if stderr_str.strip():
                self.log_message(f"stderr:\n---\n{stderr_str.strip()}\n---")

            if proc.returncode != 0:
                raise subprocess.CalledProcessError(proc.returncode, cmd, output=stdout_str, stderr=stderr_str)

            return stdout_str, stderr_str
        except Exception as e:
            self.log_message(f"Ошибка запуска UnrealPak: {e}")
            raise e

    def _batch_process_with_progress(self, items: List[Tuple[str, str]], process_func: callable, operation_name: str):
        """Обрабатывает несколько элементов с отображением прогресса."""
        total = len(items)
        self._show_progress_window(f"Пакетная обработка ({operation_name})", f"Обработка 1 из {total}...")
        
        try:
            max_threads = int(self.config_data.get(KEY_THREADS, min(32, (os.cpu_count() or 1) + 4)))
            with ThreadPoolExecutor(max_workers=max_threads) as executor:
                futures = []
                for i, (src, dst) in enumerate(items, 1):
                    futures.append(executor.submit(process_func, src, dst))
                    
                    # Обновляем прогресс после добавления каждой задачи
                    self.root.after(0, lambda i=i: self._update_progress_window(
                        f"Пакетная обработка ({operation_name})",
                        f"Обработка {i} из {total}..."
                    ))
                    self.root.after(0, lambda i=i: self._update_progress(int((i / total) * 100)))
                
                for future in as_completed(futures):
                    try:
                        future.result()
                    except Exception as e:
                        self.log_message(f"Ошибка при пакетной обработке: {e}")
                        
        finally:
            self._hide_progress_window()
            self._update_progress(0)

    def _calculate_file_hash(self, filepath: str) -> str:
        """Вычисляет хеш файла для проверки целостности."""
        hash_sha256 = hashlib.sha256()
        with open(filepath, "rb") as f:
            for chunk in iter(lambda: f.read(4096), b""):
                hash_sha256.update(chunk)
        return hash_sha256.hexdigest()

    def _verify_file_integrity(self, filepath: str, expected_hash: Optional[str] = None) -> bool:
        """Проверяет целостность файла."""
        if not os.path.exists(filepath):
            return False
            
        if expected_hash:
            current_hash = self._calculate_file_hash(filepath)
            return current_hash == expected_hash
            
        # Если хеш не предоставлен, выполняем базовую проверку
        try:
            with open(filepath, 'rb') as f:
                f.read(1)
            return True
        except IOError:
            return False

    def _optimize_file_handling(self, filepath: str, mode: str = 'r') -> Union[io.TextIOWrapper, io.BufferedReader]:
        """Оптимизированное открытие файла с учетом кэширования."""
        if 'b' in mode:
            # Для бинарных файлов используем кэш
            cached_data = self.file_cache.get(filepath)
            if cached_data is not None:
                return io.BytesIO(cached_data)
                
            with open(filepath, 'rb') as f:
                data = f.read()
                self.file_cache.put(filepath, data)
                return io.BytesIO(data)
        else:
            # Для текстовых файлов просто открываем
            return open(filepath, mode, encoding='utf-8', errors='replace')

    def _create_archive_tab(self):
        """Создает вкладку для работы с архивами с улучшенным интерфейсом."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="Архивы (.pak, .zip)")
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=1)

        # Основные кнопки
        frame_main = ttk.Frame(tab)
        frame_main.grid(row=0, column=0, columnspan=2, sticky="ew", pady=(0,10))
        frame_main.columnconfigure(0, weight=1)
        frame_main.columnconfigure(1, weight=1)

        self.unpack_button = ttk.Button(frame_main, text="Распаковать архив...", 
                                      command=self._select_file_and_unpack, style="Large.TButton")
        self.unpack_button.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        CreateToolTip(self.unpack_button, "Выберите .pak или .zip архив для распаковки.")

        self.pack_button = ttk.Button(frame_main, text="Упаковать папку в .pak...", 
                                    command=self._select_folder_and_pack, style="Large.TButton")
        self.pack_button.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        CreateToolTip(self.pack_button, "Выберите папку для упаковки в .pak архив.")

        # Опции
        options_frame = ttk.Frame(tab)
        options_frame.grid(row=1, column=1, sticky="e", padx=5, pady=(0,10))
        self.compress_check = ttk.Checkbutton(options_frame, text="Сжатие", variable=self.compress_pak_var)
        self.compress_check.pack(side=tk.LEFT)
        CreateToolTip(self.compress_check, "Включить сжатие (флаг -compress).")

        # Утилиты
        utils_frame = ttk.LabelFrame(tab, text="Утилиты для .pak", padding="10")
        utils_frame.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(10,10))
        utils_frame.columnconfigure(0, weight=1)
        utils_frame.columnconfigure(1, weight=1)

        self.list_pak_button = ttk.Button(utils_frame, text="Содержимое .pak...", 
                                        command=self._select_and_list_pak, style="Small.TButton")
        self.list_pak_button.grid(row=0, column=0, padx=5, pady=5, sticky="ew")
        CreateToolTip(self.list_pak_button, "Показать список файлов внутри архива.")

        self.test_pak_button = ttk.Button(utils_frame, text="Проверить .pak...", 
                                        command=self._select_and_test_pak, style="Small.TButton")
        self.test_pak_button.grid(row=0, column=1, padx=5, pady=5, sticky="ew")
        CreateToolTip(self.test_pak_button, "Проверить целостность архива.")

        # Примечание
        note_label = ttk.Label(tab, 
                              text="Примечание: для IO Store (.ucas/.utoc) используйте вкладку 'Анализ UE5-ассетов'.",
                              wraplength=750, justify=tk.LEFT, relief=tk.RIDGE, padding=10, 
                              font=self.small_font, style="Note.TLabel")
        note_label.grid(row=3, column=0, columnspan=2, pady=10, padx=5, sticky="ew")

    def _unpack_archive_task(self, archive_path: str, output_dir: str, operation_name: str):
        """Задача для распаковки архива с улучшенной обработкой."""
        archive_path = Path(archive_path)
        output_dir = Path(output_dir)
        
        # Проверка свободного места
        required_space = archive_path.stat().st_size * 2  # Оценочно
        free_space = self._get_free_space(output_dir)
        
        if free_space < required_space:
            raise Exception(f"Недостаточно свободного места. Требуется: {required_space/1024/1024:.2f} MB, доступно: {free_space/1024/1024:.2f} MB")
        
        # Проверка целостности архива
        if not self._verify_file_integrity(str(archive_path)):
            raise Exception("Файл архива поврежден или недоступен для чтения")
        
        if archive_path.suffix.lower() == ".zip":
            self._unpack_zip(archive_path, output_dir)
        else:
            self._unpack_pak(archive_path, output_dir)
            
        # Проверка целостности распакованных файлов
        self._verify_unpacked_files(output_dir)

    def _get_free_space(self, path: Path) -> int:
        """Возвращает количество свободного места в байтах."""
        if platform.system() == "Windows":
            import ctypes
            free_bytes = ctypes.c_ulonglong(0)
            ctypes.windll.kernel32.GetDiskFreeSpaceExW(ctypes.c_wchar_p(str(path)), None, None, ctypes.pointer(free_bytes))
            return free_bytes.value
        else:
            statvfs = os.statvfs(str(path))
            return statvfs.f_bavail * statvfs.f_frsize

    def _verify_unpacked_files(self, directory: Path):
        """Проверяет целостность распакованных файлов."""
        self.set_status("Проверка целостности файлов...")
        verified = 0
        errors = 0
        
        for root, _, files in os.walk(directory):
            for file in files:
                filepath = Path(root) / file
                if not self._verify_file_integrity(str(filepath)):
                    self.log_message(f"Ошибка проверки: {filepath}")
                    errors += 1
                else:
                    verified += 1
                    
                # Обновляем прогресс
                if (verified + errors) % 100 == 0:
                    self._update_progress(int((verified + errors) / (verified + errors + 1) * 100))
        
        self.log_message(f"Проверка завершена. Успешно: {verified}, ошибок: {errors}")

    def _pack_folder_to_pak_task(self, folder_path: str, pak_path: str, operation_name: str):
        """Задача для упаковки папки с улучшенной обработкой."""
        if not self._check_unrealpak_path(silent=True):
            raise Exception("Путь к UnrealPak не настроен или неверен.")
        
        folder_path = Path(folder_path)
        pak_path = Path(pak_path)
        
        # Проверка свободного места
        required_space = sum(f.stat().st_size for f in folder_path.glob('**/*') if f.is_file()) * 1.5  # Оценочно
        free_space = self._get_free_space(pak_path.parent)
        
        if free_space < required_space:
            raise Exception(f"Недостаточно свободного места. Требуется: {required_space/1024/1024:.2f} MB, доступно: {free_space/1024/1024:.2f} MB")
        
        if pak_path.exists():
            pak_path.unlink()
        
        
        args = [
            pak_path,
            "-Create=" + str(folder_path),
            "-compress" if self.compress_pak_var.get() else "",
            self.config_data.get(KEY_CUSTOM_COMPRESS_PARAMS, ""),
        ]
        
        # Удаляем пустые аргументы
        args = [arg for arg in args if arg]
        
        self._run_unrealpak_command(args, "Упаковка PAK архива")
        
        # Проверка целостности созданного архива
        if not self._verify_file_integrity(str(pak_path)):
            raise Exception("Созданный архив поврежден")

    def _select_files_and_batch_unpack(self):
        """Выбирает несколько архивов для пакетной распаковки с улучшенным интерфейсом."""
        last_dir = self._get_last_dir('LastUnpackSourceDir')
        
        file_paths = filedialog.askopenfilenames(
            title="Выберите архивы для распаковки",
            initialdir=last_dir,
            filetypes=ARCHIVE_EXTENSIONS,
            parent=self.root
        )
        
        if file_paths:
            self._save_config_value('LastUnpackSourceDir', str(Path(file_paths[0]).parent))
            
            default_out = Path(file_paths[0]).parent / "batch_unpacked"
            dir_path = filedialog.askdirectory(
                title="Выберите папку для распаковки",
                initialdir=str(default_out),
                parent=self.root
            )
            
            if dir_path:
                self._save_config_value('LastUnpackDestDir', dir_path)
                
                items = []
                for file_path in file_paths:
                    archive_name = Path(file_path).stem
                    output_dir = Path(dir_path) / archive_name
                    items.append((file_path, str(output_dir)))
                
                # Используем пакетную обработку с прогрессом
                self._batch_process_with_progress(items, self._unpack_archive_task, "Batch Unpack")

    def _select_folders_and_batch_pack(self):
        """Выбирает родительскую папку для пакетной упаковки с улучшенным интерфейсом."""
        last_dir = self._get_last_dir('LastPackSourceDir')
        
        parent_dir = filedialog.askdirectory(
            title="Выберите родительскую папку с папками для упаковки",
            initialdir=last_dir,
            parent=self.root
        )
        
        if parent_dir:
            self._save_config_value('LastPackSourceDir', parent_dir)
            
            default_out = Path(parent_dir) / "batch_packed"
            output_dir = filedialog.askdirectory(
                title="Выберите папку для сохранения PAK архивов",
                initialdir=str(default_out),
                parent=self.root
            )
            
            if output_dir:
                self._save_config_value('LastPackDestDir', output_dir)
                
                parent_path = Path(parent_dir)
                output_path = Path(output_dir)
                
                items = []
                for folder in parent_path.iterdir():
                    if folder.is_dir():
                        pak_path = output_path / f"{folder.name}.pak"
                        items.append((str(folder), str(pak_path)))
                
                # Используем пакетную обработку с прогрессом
                self._batch_process_with_progress(items, self._pack_folder_to_pak_task, "Batch Pack")

    def _create_drag_and_drop_area(self):
        """Создает улучшенную область для drag-and-drop."""
        try:
            dnd_frame = ttk.LabelFrame(self.root, text="Перетащите файлы/папки сюда", padding="10")
            dnd_frame.pack(fill=tk.X, padx=10, pady=5, side=tk.BOTTOM)

            instruction_label = ttk.Label(dnd_frame, 
                                         text="Перетащите архивы (.pak, .zip) или папки для упаковки", 
                                         anchor="center", justify=tk.CENTER, style="DND.TLabel")
            self.style.configure("DND.TLabel", 
                                background=self.style.lookup("TLabelframe", "background"), 
                                foreground=self.style.lookup("TLabelframe", "foreground"), 
                                font=self.small_font)
            instruction_label.pack(fill=tk.X, expand=True, pady=5)

            dnd_frame.drop_target_register(DND_FILES)
            dnd_frame.dnd_bind("<<Drop>>", self._dnd_drop_event)
            CreateToolTip(dnd_frame, "Поддерживается перетаскивание архивов для распаковки или папок для упаковки.")
        except Exception as e:
            self.log_message(f"Ошибка создания области Drag-and-Drop: {e}")

    def _dnd_drop_event(self, event):
        """Обрабатывает событие перетаскивания файлов."""
        try:
            files = self.root.tk.splitlist(event.data)
            for file in files:
                if os.path.isfile(file) and file.lower().endswith(('.pak', '.zip')):
                    self._handle_dropped_archive(file)
                elif os.path.isdir(file):
                    self._handle_dropped_folder(file)
        except Exception as e:
            self.log_message(f"Ошибка обработки перетаскивания: {e}")

    def _handle_dropped_archive(self, file_path):
        """Обрабатывает перетаскивание архива."""
        default_dir = Path(file_path).parent / f"{Path(file_path).stem}_unpacked"
        dir_path = filedialog.askdirectory(
            title="Выберите папку для распаковки",
            initialdir=str(default_dir),
            parent=self.root
        )
        
        if dir_path:
            self._unpack_archive(file_path, dir_path)

    def _handle_dropped_folder(self, folder_path):
        """Обрабатывает перетаскивание папки."""
        default_pak = Path(folder_path).parent / f"{Path(folder_path).name}.pak"
        pak_path = filedialog.asksaveasfilename(
            title="Сохранить PAK архив как...",
            initialdir=str(default_pak.parent),
            initialfile=default_pak.name,
            filetypes=PAK_EXTENSIONS,
            defaultextension=".pak",
            parent=self.root
        )
        
        if pak_path:
            self._pack_folder_to_pak(folder_path, pak_path)

    def _pack_folder_to_pak(self, folder_path: str, pak_path: str):
        """Упаковывает папку в PAK архив."""
        self._show_progress_window("Упаковка PAK", f"Упаковка {Path(folder_path).name}...")
        
        try:
            self._pack_folder_to_pak_task(folder_path, pak_path, "Упаковка PAK")
            messagebox.showinfo("Готово", "PAK архив успешно создан.", parent=self.root)
            self.log_message(f"PAK архив создан: {folder_path} → {pak_path}")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось создать PAK архив:\n{e}", parent=self.root)
            self.log_message(f"Ошибка упаковки: {e}")
        finally:
            self._hide_progress_window()

    def _select_and_list_pak(self):
        """Выбирает PAK архив и показывает его содержимое."""
        last_dir = self._get_last_dir('LastPakUtilDir')
        
        file_path = filedialog.askopenfilename(
            title="Выберите PAK архив",
            initialdir=last_dir,
            filetypes=PAK_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastPakUtilDir', str(Path(file_path).parent))
            self._list_pak_contents(file_path)

    def _list_pak_contents(self, pak_path: str):
        """Показывает содержимое PAK архива."""
        if not self._check_unrealpak_path(silent=True):
            return
            
        args = [pak_path, "-List"]
        
        try:
            stdout, stderr = self._run_unrealpak_command(args, "Список файлов в PAK")
            
            # Создаем окно для отображения содержимого
            list_window = tk.Toplevel(self.root)
            list_window.title(f"Содержимое: {Path(pak_path).name}")
            list_window.geometry("800x600")
            
            text = scrolledtext.ScrolledText(list_window, wrap=tk.WORD, font=self.log_font,
                                           bg=self.text_bg, fg=self.text_fg, selectbackground=self.select_bg)
            text.pack(fill=tk.BOTH, expand=True)
            
            text.insert(tk.END, stdout)
            text.config(state=tk.DISABLED)
            
            self._setup_text_widget_context_menu(text, read_only=True)
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось получить список файлов:\n{e}", parent=self.root)
            self.log_message(f"Ошибка получения списка файлов: {e}")

    def _select_and_test_pak(self):
        """Выбирает PAK архив и проверяет его целостность."""
        last_dir = self._get_last_dir('LastPakUtilDir')
        
        file_path = filedialog.askopenfilename(
            title="Выберите PAK архив для проверки",
            initialdir=last_dir,
            filetypes=PAK_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastPakUtilDir', str(Path(file_path).parent))
            self._test_pak_integrity(file_path)

    def _test_pak_integrity(self, pak_path: str):
        """Проверяет целостность PAK архива."""
        if not self._check_unrealpak_path(silent=True):
            return
            
        args = [pak_path, "-Test"]
        
        try:
            self._show_progress_window("Проверка PAK", f"Проверка {Path(pak_path).name}...")
            stdout, stderr = self._run_unrealpak_command(args, "Проверка PAK")
            
            if "error" not in stderr.lower():
                messagebox.showinfo("Проверка завершена", "PAK архив не содержит ошибок.", parent=self.root)
                self.log_message(f"PAK архив проверен: {pak_path} - ошибок не найдено")
            else:
                messagebox.showerror("Ошибка", "PAK архив содержит ошибки.", parent=self.root)
                self.log_message(f"PAK архив содержит ошибки: {pak_path}\n{stderr}")
                
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось проверить PAK архив:\n{e}", parent=self.root)
            self.log_message(f"Ошибка проверки PAK архива: {e}")
        finally:
            self._hide_progress_window()

    def _select_folder_and_pack(self):
        """Выбирает папку для упаковки в PAK архив."""
        last_dir = self._get_last_dir('LastPackSourceDir', os.path.expanduser("~"))
        
        folder_path = filedialog.askdirectory(
            title="Выберите папку для упаковки",
            initialdir=last_dir,
            parent=self.root
        )
        
        if folder_path:
            self._save_config_value('LastPackSourceDir', folder_path)
            
            default_pak = Path(folder_path).parent / f"{Path(folder_path).name}.pak"
            pak_path = filedialog.asksaveasfilename(
                title="Сохранить PAK архив как...",
                initialdir=str(default_pak.parent),
                initialfile=default_pak.name,
                filetypes=PAK_EXTENSIONS,
                defaultextension=".pak",
                parent=self.root
            )
            
            if pak_path:
                self._save_config_value('LastPackDestDir', str(Path(pak_path).parent))
                self._pack_folder_to_pak(folder_path, pak_path)

    def _create_open_file_tab(self):
        """Создает вкладку для открытия и редактирования файлов."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="Открыть файл")
        tab.columnconfigure(0, weight=1)
        
        # Кнопка открытия файла
        open_frame = ttk.Frame(tab)
        open_frame.grid(row=0, column=0, sticky="ew", pady=(0,10))
        
        self.open_button = ttk.Button(open_frame, text="Открыть файл...", 
                                    command=self._select_and_open_file, style="Large.TButton")
        self.open_button.pack(fill=tk.X)
        CreateToolTip(self.open_button, "Открыть текстовый файл для просмотра и редактирования.")
        
        # Область для отображения содержимого файла
        self.file_content_text = scrolledtext.ScrolledText(tab, wrap=tk.WORD, state=tk.DISABLED,
                                                         font=self.log_font, bg=self.text_bg, fg=self.text_fg,
                                                         selectbackground=self.select_bg)
        self.file_content_text.grid(row=1, column=0, sticky="nsew")
        tab.rowconfigure(1, weight=1)
        
        self._setup_text_widget_context_menu(self.file_content_text, read_only=False)
        
        # Кнопки для работы с файлом
        button_frame = ttk.Frame(tab)
        button_frame.grid(row=2, column=0, sticky="ew", pady=(10,0))
        
        self.save_button = ttk.Button(button_frame, text="Сохранить", state=tk.DISABLED,
                                    command=self._save_opened_file, style="Small.TButton")
        self.save_button.pack(side=tk.LEFT, padx=5)
        CreateToolTip(self.save_button, "Сохранить изменения в файле.")
        
        self.reload_button = ttk.Button(button_frame, text="Перезагрузить", state=tk.DISABLED,
                                      command=self._reload_opened_file, style="Small.TButton")
        self.reload_button.pack(side=tk.LEFT, padx=5)
        CreateToolTip(self.reload_button, "Перезагрузить файл (отменить изменения).")

    def _select_and_open_file(self):
        """Выбирает файл для открытия."""
        last_dir = self._get_last_dir('LastOpenFileDir', os.path.expanduser("~"))
        
        file_path = filedialog.askopenfilename(
            title="Выберите файл для открытия",
            initialdir=last_dir,
            filetypes=TEXT_LIKE_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastOpenFileDir', str(Path(file_path).parent))
            self._open_file(file_path)

    def _open_file(self, file_path: str):
        """Открывает файл для просмотра и редактирования."""
        try:
            with self._optimize_file_handling(file_path, 'r') as f:
                content = f.read()
                
            self.current_file_path = file_path
            self.file_content_text.config(state=tk.NORMAL)
            self.file_content_text.delete(1.0, tk.END)
            self.file_content_text.insert(tk.END, content)
            self.file_content_text.edit_modified(False)
            self.file_content_text.config(state=tk.NORMAL)
            
            self.save_button.config(state=tk.DISABLED)
            self.reload_button.config(state=tk.NORMAL)
            
            self.root.title(f"{APP_NAME} v{APP_VERSION} - {Path(file_path).name}")
            self.log_message(f"Файл открыт: {file_path}")
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось открыть файл:\n{e}", parent=self.root)
            self.log_message(f"Ошибка открытия файла: {e}")

    def _save_opened_file(self):
        """Сохраняет изменения в открытом файле."""
        if not hasattr(self, 'current_file_path') or not self.current_file_path:
            return
            
        try:
            content = self.file_content_text.get(1.0, tk.END)
            
            # Создаем резервную копию
            backup_path = f"{self.current_file_path}.bak"
            if os.path.exists(self.current_file_path):
                os.replace(self.current_file_path, backup_path)
            
            with open(self.current_file_path, 'w', encoding='utf-8') as f:
                f.write(content)
                
            self.file_content_text.edit_modified(False)
            self.save_button.config(state=tk.DISABLED)
            
            self.log_message(f"Файл сохранен: {self.current_file_path}")
            messagebox.showinfo("Сохранено", "Файл успешно сохранен.", parent=self.root)
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось сохранить файл:\n{e}", parent=self.root)
            self.log_message(f"Ошибка сохранения файла: {e}")

    def _reload_opened_file(self):
        """Перезагружает открытый файл, отменяя изменения."""
        if hasattr(self, 'current_file_path') and self.current_file_path:
            self._open_file(self.current_file_path)

    def _create_ini_viewer_tab(self):
        """Создает вкладку для просмотра INI файлов."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="INI Viewer")
        tab.columnconfigure(0, weight=1)
        
        # Верхняя панель с кнопками
        top_frame = ttk.Frame(tab)
        top_frame.grid(row=0, column=0, sticky="ew", pady=(0,10))
        top_frame.columnconfigure(1, weight=1)
        
        self.open_ini_button = ttk.Button(top_frame, text="Открыть INI...", 
                                        command=self._select_and_open_ini, style="Small.TButton")
        self.open_ini_button.grid(row=0, column=0, padx=(0,5), sticky="w")
        CreateToolTip(self.open_ini_button, "Открыть INI файл для просмотра.")
        
        self.ini_filepath_label = ttk.Label(top_frame, textvariable=self.ini_filepath_label_var,
                                           style="FilePath.TLabel")
        self.ini_filepath_label.grid(row=0, column=1, sticky="ew")
        
        # Область для отображения INI
        self.ini_viewer_text = scrolledtext.ScrolledText(tab, wrap=tk.WORD, state=tk.DISABLED,
                                                        font=self.log_font, bg=self.text_bg, fg=self.text_fg,
                                                        selectbackground=self.select_bg)
        self.ini_viewer_text.grid(row=1, column=0, sticky="nsew")
        tab.rowconfigure(1, weight=1)
        
        self._setup_text_widget_context_menu(self.ini_viewer_text, read_only=True)

    def _select_and_open_ini(self):
        """Выбирает INI файл для просмотра."""
        last_dir = self._get_last_dir('LastIniViewDir', os.path.expanduser("~"))
        
        file_path = filedialog.askopenfilename(
            title="Выберите INI файл",
            initialdir=last_dir,
            filetypes=INI_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastIniViewDir', str(Path(file_path).parent))
            self._open_ini_file(file_path)

    def _open_ini_file(self, file_path: str):
        """Открывает и отображает INI файл."""
        try:
            config = configparser.ConfigParser()
            config.read(file_path, encoding='utf-8')
            
            output = io.StringIO()
            config.write(output)
            content = output.getvalue()
            output.close()
            
            self.ini_viewer_text.config(state=tk.NORMAL)
            self.ini_viewer_text.delete(1.0, tk.END)
            self.ini_viewer_text.insert(tk.END, content)
            self.ini_viewer_text.config(state=tk.DISABLED)
            
            self.ini_filepath_label_var.set(Path(file_path).name)
            self.log_message(f"INI файл открыт: {file_path}")
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось открыть INI файл:\n{e}", parent=self.root)
            self.log_message(f"Ошибка открытия INI файла: {e}")

    def _create_batch_tab(self):
        """Создает вкладку для пакетной обработки."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="Пакетная обработка")
        tab.columnconfigure(0, weight=1)
        tab.columnconfigure(1, weight=1)
        
        # Пакетная распаковка
        unpack_frame = ttk.LabelFrame(tab, text="Пакетная распаковка", padding="10")
        unpack_frame.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        unpack_frame.columnconfigure(0, weight=1)
        
        ttk.Label(unpack_frame, text="Распаковать несколько архивов в одну папку:").grid(row=0, column=0, sticky="w")
        
        self.batch_unpack_button = ttk.Button(unpack_frame, text="Выбрать архивы...",
                                            command=self._select_files_and_batch_unpack, style="Small.TButton")
        self.batch_unpack_button.grid(row=1, column=0, sticky="ew", pady=(5,0))
        CreateToolTip(self.batch_unpack_button, "Выберите несколько архивов для распаковки.")
        
        # Пакетная упаковка
        pack_frame = ttk.LabelFrame(tab, text="Пакетная упаковка", padding="10")
        pack_frame.grid(row=0, column=1, sticky="nsew", padx=5, pady=5)
        pack_frame.columnconfigure(0, weight=1)
        
        ttk.Label(pack_frame, text="Упаковать несколько папок в PAK архивы:").grid(row=0, column=0, sticky="w")
        
        self.batch_pack_button = ttk.Button(pack_frame, text="Выбрать папки...",
                                          command=self._select_folders_and_batch_pack, style="Small.TButton")
        self.batch_pack_button.grid(row=1, column=0, sticky="ew", pady=(5,0))
        CreateToolTip(self.batch_pack_button, "Выберите родительскую папку с папками для упаковки.")
        
        # Примечание
        note_frame = ttk.Frame(tab)
        note_frame.grid(row=1, column=0, columnspan=2, sticky="ew", pady=(10,0))
        
        note_label = ttk.Label(note_frame, 
                              text="Примечание: для каждой папки будет создан отдельный PAK архив с именем папки.",
                              wraplength=750, justify=tk.LEFT, relief=tk.RIDGE, padding=10, 
                              font=self.small_font, style="Note.TLabel")
        note_label.pack(fill=tk.X)

    def _create_diff_tab(self):
        """Создает вкладку для сравнения файлов."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="Сравнение файлов")
        tab.columnconfigure(0, weight=1)
        
        # Верхняя панель с кнопками
        top_frame = ttk.Frame(tab)
        top_frame.grid(row=0, column=0, sticky="ew", pady=(0,10))
        
        self.select_diff_file1_button = ttk.Button(top_frame, text="Файл 1...",
                                                command=lambda: self._select_diff_file(1), style="Small.TButton")
        self.select_diff_file1_button.pack(side=tk.LEFT, padx=(0,5))
        CreateToolTip(self.select_diff_file1_button, "Выберите первый файл для сравнения.")
        
        self.select_diff_file2_button = ttk.Button(top_frame, text="Файл 2...",
                                                command=lambda: self._select_diff_file(2), style="Small.TButton")
        self.select_diff_file2_button.pack(side=tk.LEFT, padx=(0,5))
        CreateToolTip(self.select_diff_file2_button, "Выберите второй файл для сравнения.")
        
        self.compare_button = ttk.Button(top_frame, text="Сравнить", state=tk.DISABLED,
                                       command=self._compare_files, style="Small.TButton")
        self.compare_button.pack(side=tk.LEFT, padx=(0,5))
        CreateToolTip(self.compare_button, "Сравнить выбранные файлы.")
        
        self.external_diff_button = ttk.Button(top_frame, text="Внешнее сравнение", state=tk.DISABLED,
                                             command=self._run_external_diff, style="Small.TButton")
        self.external_diff_button.pack(side=tk.LEFT)
        CreateToolTip(self.external_diff_button, "Сравнить файлы во внешнем инструменте.")
        
        # Область для отображения различий
        self.diff_text = scrolledtext.ScrolledText(tab, wrap=tk.WORD, state=tk.DISABLED,
                                                 font=self.log_font, bg=self.text_bg, fg=self.text_fg,
                                                 selectbackground=self.select_bg)
        self.diff_text.grid(row=1, column=0, sticky="nsew")
        tab.rowconfigure(1, weight=1)
        
        self._setup_text_widget_context_menu(self.diff_text, read_only=True)

    def _select_diff_file(self, file_num: int):
        """Выбирает файл для сравнения."""
        last_dir_key = f'LastCompareFile{file_num}Dir'
        last_dir = self._get_last_dir(last_dir_key, os.path.expanduser("~"))
        
        file_path = filedialog.askopenfilename(
            title=f"Выберите файл {file_num} для сравнения",
            initialdir=last_dir,
            filetypes=COMPARABLE_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value(last_dir_key, str(Path(file_path).parent))
            
            if file_num == 1:
                self.diff_file1 = file_path
            else:
                self.diff_file2 = file_path
                
            self._update_diff_buttons_state()

    def _update_diff_buttons_state(self):
        """Обновляет состояние кнопок сравнения в зависимости от выбранных файлов."""
        if self.diff_file1 and self.diff_file2:
            self.compare_button.config(state=tk.NORMAL)
            self.external_diff_button.config(state=tk.NORMAL)
        else:
            self.compare_button.config(state=tk.DISABLED)
            self.external_diff_button.config(state=tk.DISABLED)

    def _compare_files(self):
        """Сравнивает два файла и показывает различия."""
        if not self.diff_file1 or not self.diff_file2:
            return
            
        try:
            with open(self.diff_file1, 'r', encoding='utf-8') as f1:
                lines1 = f1.readlines()
                
            with open(self.diff_file2, 'r', encoding='utf-8') as f2:
                lines2 = f2.readlines()
                
            diff = difflib.unified_diff(
                lines1, lines2,
                fromfile=Path(self.diff_file1).name,
                tofile=Path(self.diff_file2).name,
                lineterm=''
            )
            
            diff_text = '\n'.join(diff)
            
            self.diff_text.config(state=tk.NORMAL)
            self.diff_text.delete(1.0, tk.END)
            self.diff_text.insert(tk.END, diff_text)
            self.diff_text.config(state=tk.DISABLED)
            
            self.log_message(f"Сравнение файлов: {self.diff_file1} ↔ {self.diff_file2}")
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось сравнить файлы:\n{e}", parent=self.root)
            self.log_message(f"Ошибка сравнения файлов: {e}")

    def _run_external_diff(self):
        """Запускает внешний инструмент для сравнения файлов."""
        if not self.diff_file1 or not self.diff_file2:
            return
            
        diff_tool = self.config_data.get(KEY_EXTERNAL_DIFF_TOOL)
        if not diff_tool:
            messagebox.showwarning("Внимание", "Внешний Diff Tool не настроен.", parent=self.root)
            return
            
        try:
            subprocess.Popen([diff_tool, self.diff_file1, self.diff_file2])
            self.log_message(f"Запущен внешний Diff Tool: {diff_tool}")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось запустить Diff Tool:\n{e}", parent=self.root)
            self.log_message(f"Ошибка запуска Diff Tool: {e}")

    def _create_asset_analyzer_tab(self):
        """Создает вкладку для анализа UE5 ассетов."""
        tab = ttk.Frame(self.notebook, padding="10")
        self.notebook.add(tab, text="Анализ UE5-ассетов")
        tab.columnconfigure(0, weight=1)
        
        # Верхняя панель с кнопками
        top_frame = ttk.Frame(tab)
        top_frame.grid(row=0, column=0, sticky="ew", pady=(0,10))
        
        self.open_asset_button = ttk.Button(top_frame, text="Открыть ассет...",
                                          command=self._select_and_analyze_asset, style="Small.TButton")
        self.open_asset_button.pack(side=tk.LEFT, padx=(0,5))
        CreateToolTip(self.open_asset_button, "Выберите UE5 ассет для анализа (.uasset, .umap, .pak, .ucas, .utoc).")
        
        # Область для отображения анализа
        self.asset_analysis_text = scrolledtext.ScrolledText(tab, wrap=tk.WORD, state=tk.DISABLED,
                                                            font=self.log_font, bg=self.text_bg, fg=self.text_fg,
                                                            selectbackground=self.select_bg)
        self.asset_analysis_text.grid(row=1, column=0, sticky="nsew")
        tab.rowconfigure(1, weight=1)
        
        self._setup_text_widget_context_menu(self.asset_analysis_text, read_only=True)

    def _select_and_analyze_asset(self):
        """Выбирает UE5 ассет для анализа."""
        last_dir = self._get_last_dir('LastAnalyzeDir', os.path.expanduser("~"))
        
        file_path = filedialog.askopenfilename(
            title="Выберите UE5 ассет для анализа",
            initialdir=last_dir,
            filetypes=UE5_ASSET_EXTENSIONS,
            parent=self.root
        )
        
        if file_path:
            self._save_config_value('LastAnalyzeDir', str(Path(file_path).parent))
            self._analyze_asset(file_path)

    def _analyze_asset(self, file_path: str):
        """Анализирует UE5 ассет и показывает информацию."""
        try:
            file_size = os.path.getsize(file_path)
            file_ext = Path(file_path).suffix.lower()
            
            info = [
                f"Файл: {Path(file_path).name}",
                f"Размер: {file_size / 1024 / 1024:.2f} MB",
                f"Тип: {file_ext}",
                "\nЗаголовок файла (первые 64 байта):"
            ]
            
            with open(file_path, 'rb') as f:
                header = f.read(64)
                hex_dump = ' '.join(f'{b:02X}' for b in header)
                ascii_dump = ''.join(chr(b) if 32 <= b <= 126 else '.' for b in header)
                
                info.append(hex_dump)
                info.append(ascii_dump)
            
            if file_ext in ('.pak', '.ucas', '.utoc'):
                info.append("\nДополнительная информация:")
                
                if file_ext == '.pak':
                    info.append("Это PAK архив Unreal Engine.")
                    if self._check_unrealpak_path(silent=True):
                        args = [file_path, "-List"]
                        stdout, stderr = self._run_unrealpak_command(args, "Анализ PAK")
                        info.append("\nСодержимое архива:")
                        info.append(stdout)
                
                elif file_ext in ('.ucas', '.utoc'):
                    info.append("Это файл IO Store Unreal Engine 5.")
                    if file_ext == '.ucas':
                        info.append("Файл данных (UCAS).")
                    else:
                        info.append("Файл таблицы содержимого (UTOC).")
            
            self.asset_analysis_text.config(state=tk.NORMAL)
            self.asset_analysis_text.delete(1.0, tk.END)
            self.asset_analysis_text.insert(tk.END, '\n'.join(info))
            self.asset_analysis_text.config(state=tk.DISABLED)
            
            self.log_message(f"Анализ ассета: {file_path}")
            
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось проанализировать ассет:\n{e}", parent=self.root)
            self.log_message(f"Ошибка анализа ассета: {e}")

    def _collect_action_buttons(self):
        """Собирает все кнопки действий для управления состоянием."""
        self.action_buttons = [
            self.unpack_button, self.pack_button, 
            self.list_pak_button, self.test_pak_button,
            self.open_button, self.save_button, self.reload_button,
            self.open_ini_button,
            self.batch_unpack_button, self.batch_pack_button,
            self.select_diff_file1_button, self.select_diff_file2_button,
            self.compare_button, self.external_diff_button,
            self.open_asset_button
        ]

    def _setup_text_widget_context_menu(self, text_widget: tk.Text, read_only: bool = True):
        """Настраивает контекстное меню для текстового виджета."""
        context_menu = tk.Menu(text_widget, tearoff=0)
        
        context_menu.add_command(label="Копировать", command=lambda: text_widget.event_generate("<<Copy>>"))
        
        if not read_only:
            context_menu.add_separator()
            context_menu.add_command(label="Вставить", command=lambda: text_widget.event_generate("<<Paste>>"))
            context_menu.add_command(label="Вырезать", command=lambda: text_widget.event_generate("<<Cut>>"))
        
        def show_context_menu(event):
            try:
                context_menu.tk_popup(event.x_root, event.y_root)
            finally:
                context_menu.grab_release()
        
        text_widget.bind("<Button-3>", show_context_menu)

    def _get_last_dir(self, key: str, default: str = None) -> str:
        """Возвращает последнюю использованную директорию для указанного ключа."""
        return self.config_data.get(key, default) if default else self.config_data.get(key)

    def log_message(self, message: str):
        """Добавляет сообщение в лог с временной меткой."""
        timestamp = datetime.now().strftime("[%H:%M:%S]")
        full_message = f"{timestamp} {message}\n"
        
        if self.log_text and hasattr(self.log_text, 'winfo_exists') and self.log_text.winfo_exists():
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, full_message)
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        
        print(full_message.strip())

    def set_status(self, message: str):
        """Устанавливает статус в строке состояния."""
        if hasattr(self, 'status_var'):
            self.status_var.set(message)

    def _log_initial_config(self):
        """Логирует начальную конфигурацию при запуске."""
        self.log_message(f"Запуск {APP_NAME} v{APP_VERSION}")
        self.log_message(f"Тема интерфейса: {self.theme_var.get()}")
        
        if self.config_data.get(KEY_UNREALPAK_PATH):
            self.log_message(f"Путь к UnrealPak: {self.config_data[KEY_UNREALPAK_PATH]}")
        else:
            self.log_message("Путь к UnrealPak не настроен")
            
        self.log_message(f"Макс. потоков: {self.config_data.get(KEY_THREADS, 'по умолчанию')}")
        self.log_message(f"Размер кэша: {self.config_data.get(KEY_CACHE_SIZE, '100')} MB")

    def run(self):
        """Запускает главный цикл приложения с улучшенной обработкой ошибок."""
        try:
            self.set_status("Приложение готово.")
            self.root.mainloop()
        except Exception as e:
            self.log_message(f"Критическая ошибка: {traceback.format_exc()}")
            messagebox.showerror("Критическая ошибка", 
                               f"Произошла критическая ошибка:\n{e}\n\nСм. лог для подробностей.",
                               parent=self.root)
            sys.exit(1)

if __name__ == "__main__":
    RootClass = TkinterDnD.Tk if USE_DND else tk.Tk
    root = RootClass()
    try:
        app = UEPakToolApp(root)
        app.run()
    except Exception as e:
        messagebox.showerror("Ошибка запуска", f"Не удалось запустить приложение:\n{e}")
        sys.exit(1)
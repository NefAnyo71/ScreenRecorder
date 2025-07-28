import psutil
import tkinter as tk
from tkinter import messagebox, filedialog, ttk
import threading
import cv2
import numpy as np
import mss
import time
import pyautogui
import os
import subprocess
from PIL import Image, ImageTk
import logging
import pyaudio
import wave
import json
try:
    import win32gui
    import win32con
    WIN32_AVAILABLE = True
except ImportError:
    WIN32_AVAILABLE = False
    print("win32gui modülü bulunamadı. Pencere seçimi özelliği sınırlı olacak.")

# Loglama ayarları
logging.basicConfig(
    filename="screen_record_log.txt",
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s"
)

def log_print(message, level="info"):
    """Konsola çıktı veren ve log dosyasına yazan yardımcı fonksiyon."""
    print(message)
    if level == "error":
        logging.error(message)
    elif level == "warning":
        logging.warning(message)
    else:
        logging.info(message)

# MSS objesini thread'ler arasında güvenli bir şekilde paylaşmak için
thread_local_data = threading.local()

class ScreenRecorderApp:
    def __init__(self, master):
        try:
            self.master = master
            self.preview_thread = None
            master.title("Better Than OBS")

            # Tam ekranı kapat, pencereyi ekranı kaplayacak şekilde ayarla
            screen_w = master.winfo_screenwidth()
            screen_h = master.winfo_screenheight()
            # %90 oranında ekranı kaplasın
            window_w = int(screen_w * 0.9)
            window_h = int(screen_h * 0.9)
            x = (screen_w - window_w) // 2
            y = (screen_h - window_h) // 2
            master.geometry(f"{window_w}x{window_h}+{x}+{y}")
            master.resizable(True, True)
            # master.attributes("-fullscreen", False)  # Tam ekranı kapalı tut

            # Menü çubuğunu oluştur
            menubar = tk.Menu(master)
            # Dosya menüsü
            filemenu = tk.Menu(menubar, tearoff=0)
            filemenu.add_command(label="Kayıt Başlat", command=self.start_recording)
            filemenu.add_command(label="Kayıt Durdur", command=self.stop_recording)
            filemenu.add_separator()
            filemenu.add_command(label="Çıkış", command=self.on_closing)
            menubar.add_cascade(label="Dosya", menu=filemenu)

            # Yardım menüsü
            helpmenu = tk.Menu(menubar, tearoff=0)
            helpmenu.add_command(label="Ayarlar", command=self.open_settings)
            helpmenu.add_command(label="Tam Ekran Aç/Kapat", command=self.toggle_fullscreen)
            helpmenu.add_separator()
            helpmenu.add_command(label="Yardım Merkezi", command=self.show_advanced_help)
            helpmenu.add_command(
                label="Hata Bildir / Geri Bildirim",
                command=lambda: messagebox.showinfo(
                    "Geri Bildirim",
                    "Herhangi bir hata veya öneri için lütfen aşağıdaki e-posta adresine ulaşın:\n\narifkerem71@gmail.com"
                )
            )
            menubar.add_cascade(label="Yardım", menu=helpmenu)
            
            # Ayarlar menüsü (ayrı olarak)
            menubar.add_command(label="Ayarlar", command=self.show_settings_panel)

            master.config(menu=menubar)

            self.recording = False
            self.output_directory = os.path.join(os.path.expanduser("~"), "EkranKayitlari")
            self.fps = 20
            self.record_thread = None
            self.audio_record_thread = None
            self.out = None
            self.audio_frames = []
            self.audio_stream = None
            self.p = None # PyAudio instance

            # Ses kayıt ayarları
            self.audio_format = pyaudio.paInt16
            self.audio_channels = 2 # Stereo
            self.audio_rate = 44100 # Örnekleme oranı (Hz)
            self.audio_chunk_size = 1024 # Ses verisi boyutu

            self.monitor_region = {"top": 0, "left": 0, "width": pyautogui.size().width, "height": pyautogui.size().height}
            self.is_selecting_region = False
            self.selection_rect_id = None
            self.start_x, self.start_y = None, None
            self.current_x, self.current_y = None, None

            self.paused = False  # Duraklatma durumu
            
            # Eksik değişkenler
            self.format_var = tk.StringVar(value="mp4")
            self.current_record_filename_video = ""
            self.current_record_filename_audio = ""
            
            # Disk alanı takibi
            self.disk_warning_label = None
            self.disk_check_thread = None
            self.estimated_time_left = 0

            # Multi-monitor ve pencere seçimi için değişkenler
            self.available_monitors = []
            self.available_windows = []
            self.current_target = {'type': 'monitor', 'index': 0}  # Varsayılan: ilk monitor
            self.monitor_previews = []  # Önizleme canvas'ları için
            self.preview_update_thread = None
            
            # Kayıt dizinini varsayılan olarak ayarla
            self.output_directory = os.path.join(os.path.expanduser("~"), "EkranKayitlari")
            if not os.path.exists(self.output_directory):
                os.makedirs(self.output_directory)

            # Varlıkları yükle
            self._load_assets()
            # Arayüz bileşenlerini oluştur
            self._create_widgets()
            # Monitor ve pencereleri tespit et
            self._update_available_targets()
            # Seçim UI'sini güncelle
            self._update_selection_ui()
            # Önizleme thread'ini başlat
            self._start_preview_thread()

            master.protocol("WM_DELETE_WINDOW", self.on_closing)

            # Uygulama simgesi ayarı (icon.ico dosyası ile aynı dizinde olmalı)
            try:
                master.iconbitmap('icon.ico')
            except Exception:
                pass
        
        except Exception as e:
            log_print(f"ScreenRecorderApp başlatılırken hata oluştu: {e}", level="error")
            messagebox.showerror("Başlatma Hatası", f"Uygulama başlatılırken hata oluştu: {e}")

    def _detect_monitors(self):
        """Tüm monitörleri tespit eder."""
        try:
            with mss.mss() as sct:
                self.available_monitors = []
                for i, monitor in enumerate(sct.monitors[1:], 1):  # İlk monitor (0) tüm ekranlar
                    self.available_monitors.append({
                        'index': i,
                        'name': f'Monitor {i}',
                        'region': monitor,
                        'type': 'monitor'
                    })
                log_print(f"Tespit edilen monitor sayısı: {len(self.available_monitors)}")
        except Exception as e:
            log_print(f"Monitor tespitinde hata: {e}", level="error")
            # Varsayılan monitor ekle
            self.available_monitors = [{
                'index': 1,
                'name': 'Monitor 1',
                'region': {'top': 0, 'left': 0, 'width': pyautogui.size().width, 'height': pyautogui.size().height},
                'type': 'monitor'
            }]

    def _detect_windows(self):
        """Açık pencereleri tespit eder."""
        self.available_windows = []
        if not WIN32_AVAILABLE:
            log_print("win32gui modülü yok, pencere tespiti yapılamıyor", level="warning")
            return
        
        def enum_windows_callback(hwnd, windows):
            if win32gui.IsWindowVisible(hwnd) and win32gui.GetWindowText(hwnd):
                try:
                    rect = win32gui.GetWindowRect(hwnd)
                    window_title = win32gui.GetWindowText(hwnd)
                    
                    # Çok küçük pencereleri ve kendi uygulamamızı filtrele
                    width = rect[2] - rect[0]
                    height = rect[3] - rect[1]
                    if width > 100 and height > 100 and "Better Than OBS" not in window_title:
                        windows.append({
                            'hwnd': hwnd,
                            'name': window_title[:50] + ("..." if len(window_title) > 50 else ""),
                            'region': {'top': rect[1], 'left': rect[0], 'width': width, 'height': height},
                            'type': 'window'
                        })
                except Exception as e:
                    pass  # Bazı pencereler erişim hatası verebilir
            return True
        
        try:
            win32gui.EnumWindows(enum_windows_callback, self.available_windows)
            log_print(f"Tespit edilen pencere sayısı: {len(self.available_windows)}")
        except Exception as e:
            log_print(f"Pencere tespitinde hata: {e}", level="error")

    def _refresh_targets(self):
        """Hedefleri yeniler ve UI'yi günceller."""
        self._update_available_targets()
        self._update_selection_ui()
        log_print("Kayıt hedefleri yenilendi.")
    
    def _update_available_targets(self):
        """Mevcut monitör ve pencereleri günceller."""
        try:
            self._detect_monitors()
            self._detect_windows()
        except Exception as e:
            log_print(f"Hedefleri güncellerken hata oluştu: {e}", level="error")

    def _capture_target_thumbnail(self, target):
        """Hedef için küçük önizleme görüntüsü yakalar."""
        try:
            region = target['region']
            
            if target['type'] == 'window' and WIN32_AVAILABLE:
                # Pencere için özel yakalama
                try:
                    hwnd = target['hwnd']
                    # Pencereyi öne getir (isteğe bağlı)
                    # win32gui.SetForegroundWindow(hwnd)
                    pass
                except:
                    pass
            
            # Ekran görüntüsü yakala
            with mss.mss() as sct:
                screenshot = sct.grab(region)
                img = Image.frombytes("RGB", screenshot.size, screenshot.bgra, "raw", "BGRX")
                
                # Daha büyük ve net önizleme (120x90 piksel)
                img.thumbnail((120, 90), Image.LANCZOS)
                
                # Çerçeve ekle
                bordered_img = Image.new('RGB', (124, 94), color='#4a5568')
                bordered_img.paste(img, (2, 2))
                
                # Tkinter için PhotoImage'e çevir
                return ImageTk.PhotoImage(bordered_img)
                
        except Exception as e:
            log_print(f"Thumbnail yakalama hatası ({target['name']}): {e}", level="warning")
            # Hata durumunda placeholder görsel oluştur
            placeholder = Image.new('RGB', (124, 94), color='#2d3748')
            # Placeholder içinde ikon çiz
            from PIL import ImageDraw, ImageFont
            draw = ImageDraw.Draw(placeholder)
            icon = "🖥️" if target['type'] == 'monitor' else "🪟"
            # Basit metin ekleme
            draw.text((62, 47), icon, fill='white', anchor='mm')
            return ImageTk.PhotoImage(placeholder)

    def _update_selection_ui(self):
        """Monitor ve pencere seçim UI'sini günceller."""
        try:
            # Önceki öğeleri temizle
            for widget in self.selection_items_frame.winfo_children():
                widget.destroy()
        
            all_targets = self.available_monitors + self.available_windows
            
            for i, target in enumerate(all_targets):
                # Her hedef için bir frame oluştur (koyu tema) - sadece metin için
                target_frame = tk.Frame(self.selection_items_frame, bg="#2a2a2a", 
                                      relief=tk.FLAT, bd=1, padx=8, pady=6)
                target_frame.pack(side=tk.LEFT, padx=4, pady=4)
                
                # Hedef türüne göre ikon ve ad (tam isim)
                icon = "🖥️" if target['type'] == 'monitor' else "🪟"
                name_text = target['name']
                
                # Ana isim label'ı (daha büyük)
                name_label = tk.Label(target_frame, text=f"{icon} {name_text}", 
                                    font=("Segoe UI", 10, "bold"), fg="white", bg="#2a2a2a",
                                    cursor="hand2", wraplength=120)
                name_label.pack(pady=(2, 4))
                
                # Boyut bilgisi
                region = target['region']
                size_text = f"{region['width']}x{region['height']}"
                size_label = tk.Label(target_frame, text=size_text, 
                                    font=("Segoe UI", 8), fg="#888888", bg="#2a2a2a",
                                    cursor="hand2")
                size_label.pack()
                
                # Tıklama olaylarını tüm bileşenlere ekle
                def make_click_handler(t):
                    return lambda e: self._select_target(t)
                
                # Eksik değişkenleri tanımla
                icon_label = name_label  # Geçici çözüm
                status_label = size_label  # Geçici çözüm
                
                click_handler = make_click_handler(target)
                target_frame.bind("<Button-1>", click_handler)
                name_label.bind("<Button-1>", click_handler)
                size_label.bind("<Button-1>", click_handler)
                
                # Seçili hedefi vurgula
                is_selected = (self.current_target['type'] == target['type'] and 
                              ((target['type'] == 'monitor' and self.current_target.get('index') == target.get('index')) or
                               (target['type'] == 'window' and self.current_target.get('hwnd') == target.get('hwnd'))))
                
                if is_selected:
                    target_frame.config(bg="#3498db", relief=tk.SUNKEN, bd=3)
                    name_label.config(bg="#3498db")
                    size_label.config(bg="#3498db")
                else:
                    # Modern hover efekti
                    def on_enter(e, frame=target_frame, name=name_label, size=size_label):
                        if not is_selected:
                            frame.config(bg="#4a6741")
                            name.config(bg="#4a6741")
                            size.config(bg="#4a6741")
                    
                    def on_leave(e, frame=target_frame, name=name_label, size=size_label):
                        if not is_selected:
                            frame.config(bg="#2a2a2a")
                            name.config(bg="#2a2a2a")
                            size.config(bg="#2a2a2a")
                    
                    target_frame.bind("<Enter>", on_enter)
                    target_frame.bind("<Leave>", on_leave)
                    name_label.bind("<Enter>", on_enter)
                    name_label.bind("<Leave>", on_leave)
                    size_label.bind("<Enter>", on_enter)
                    size_label.bind("<Leave>", on_leave)
            
            # Canvas scroll bölgesini güncelle
            self.selection_items_frame.update_idletasks()
            self.selection_canvas.configure(scrollregion=self.selection_canvas.bbox("all"))
        except Exception as e:
            log_print(f"Seçim UI'si güncellenirken hata oluştu: {e}", level="error")
    
    def _select_target(self, target):
        """Kayıt hedefini seçer."""
        if target['type'] == 'monitor':
            self.current_target = {'type': 'monitor', 'index': target['index']}
            self.monitor_region = target['region']
        else:  # window
            self.current_target = {'type': 'window', 'hwnd': target['hwnd']}
            self.monitor_region = target['region']
        
        log_print(f"Yeni kayıt hedefi seçildi: {target['name']} - Region: {target['region']}")
        
        # Seçim UI'sini güncelle
        self._update_selection_ui()
        
        # Ana önizlemeyi de güncelle (bu önemli!)
        self._update_preview_for_new_target()

    def _update_preview_for_new_target(self):
        """Seçilen hedefe göre ana önizlemeyi günceller."""
        # Önizleme thread'inin yeni hedefi kullanmasını sağlar
        log_print(f"Ana önizleme güncellendi: {self.current_target}, region: {self.monitor_region}")
        
        # Eğer pencere seçildiyse ve win32gui varsa, pencereyi aktif hale getir
        if self.current_target['type'] == 'window' and WIN32_AVAILABLE:
            try:
                hwnd = self.current_target['hwnd']
                # Pencereyi görünür hale getir (minimize durumundan çıkar)
                if win32gui.IsIconic(hwnd):
                    win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
            except Exception as e:
                log_print(f"Pencere aktifleştirme hatası: {e}", level="warning")
        
        # Önizleme thread'ini yeniden başlat
        if hasattr(self, 'preview_thread') and self.preview_thread and self.preview_thread.is_alive():
            # Mevcut thread'i durdurmak için bir flag ekleyelim
            self.stop_preview = True
            time.sleep(0.1)  # Kısa bekleme
        
        self.stop_preview = False
        self._start_preview_thread()

    def _add_button_hover_effect(self, button, hover_color, normal_color):
        """Butonlara hover efekti ekler."""
        def on_enter(e):
            button.config(bg=hover_color)
        
        def on_leave(e):
            button.config(bg=normal_color)
        
        button.bind("<Enter>", on_enter)
        button.bind("<Leave>", on_leave)

    def _load_assets(self):
        """Görsel varlıkları (resimler) yükler."""
        assets_path = os.path.join(os.path.dirname(__file__), "assets", "images")
        
        # Arka plan görselini yükle
        try:
            bg_image_path = os.path.join(assets_path, "background.png")
            self.bg_image_pil = Image.open(bg_image_path)
            # Pencere boyutuna uyması için yeniden boyutlandır
            self.bg_image_pil = self.bg_image_pil.resize((self.master.winfo_width(), self.master.winfo_height()), Image.LANCZOS)
            self.bg_image_tk = ImageTk.PhotoImage(self.bg_image_pil)
            log_print(f"Arka plan görseli yüklendi: {bg_image_path}")
        except FileNotFoundError:
            log_print(f"Hata: background.png bulunamadı. Beklenen yol: {bg_image_path}", level="error")
            self.bg_image_tk = None
        except Exception as e:
            log_print(f"Arka plan görseli yüklenirken hata: {e}", level="error")
            self.bg_image_tk = None



    def _create_widgets(self):
        frame_bg_color = "#23272f"

        # Ana frame (tüm pencereyi kaplar)
        main_frame = tk.Frame(self.master, bg=frame_bg_color)
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Sol panel
        control_frame = tk.Frame(main_frame, bd=2, relief=tk.GROOVE, padx=20, pady=20, bg=frame_bg_color)
        control_frame.pack(side=tk.LEFT, fill=tk.Y, padx=10, pady=10)

        # Sağ panel (önizleme ve ayarlar)
        preview_frame = tk.Frame(main_frame, bd=2, relief=tk.GROOVE, padx=10, pady=10, bg=frame_bg_color)
        preview_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=10, pady=10)

        # Ana önizleme Canvas
        self.preview_canvas = tk.Canvas(preview_frame, bg="black", bd=0, highlightthickness=0)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True)
        
        # Önizleme canvas'ının içinde, üst kısmında seçim alanı oluştur
        # Seçim alanı için frame (canvas içinde)
        self.selection_frame = tk.Frame(self.preview_canvas, bg="#1a1a1a", height=260)
        self.selection_frame.pack_propagate(False)
        
        # Seçim başlığı ve yenile butonu
        header_frame = tk.Frame(self.selection_frame, bg="#1a1a1a")
        header_frame.pack(fill=tk.X, pady=(5, 8))
        
        selection_label = tk.Label(header_frame, text="🎯 Kayıt Hedefi Seçin", 
                                 font=("Segoe UI", 12, "bold"), fg="#3498db", bg="#1a1a1a")
        selection_label.pack(side=tk.LEFT, padx=(10, 0))
        
        # Yenile butonu
        refresh_btn = tk.Button(header_frame, text="🔄", font=("Segoe UI", 10), 
                               bg="#2c3e50", fg="white", relief=tk.FLAT, bd=0,
                               cursor="hand2", width=3, height=1,
                               command=self._refresh_targets)
        refresh_btn.pack(side=tk.RIGHT, padx=(0, 10))
        
        # Hover efekti
        def on_enter(e): refresh_btn.config(bg="#34495e")
        def on_leave(e): refresh_btn.config(bg="#2c3e50")
        refresh_btn.bind("<Enter>", on_enter)
        refresh_btn.bind("<Leave>", on_leave)
        
        # Kaydırılabilir seçim alanı
        self.selection_canvas = tk.Canvas(self.selection_frame, bg="#1a1a1a", height=230, 
                                        bd=0, highlightthickness=0)
        self.selection_scrollbar = tk.Scrollbar(self.selection_frame, orient="horizontal", 
                                              command=self.selection_canvas.xview)
        self.selection_canvas.configure(xscrollcommand=self.selection_scrollbar.set)
        
        self.selection_canvas.pack(side=tk.TOP, fill=tk.X, expand=True, padx=5)
        self.selection_scrollbar.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(0, 3))
        
        # Seçim öğeleri için frame
        self.selection_items_frame = tk.Frame(self.selection_canvas, bg="#1a1a1a")
        self.selection_canvas.create_window((0, 0), window=self.selection_items_frame, anchor="nw")
        
        # Seçim frame'ini canvas'a yerleştir (üst kısımda)
        self.selection_window_id = self.preview_canvas.create_window(0, 0, window=self.selection_frame, anchor="nw")
        
        # Canvas boyutu değiştiğinde seçim alanını yeniden boyutlandır
        def on_canvas_configure(event):
            canvas_width = event.width
            canvas_height = event.height
            # Seçim frame'ini canvas'ın tam genişliğine ayarla
            self.selection_frame.config(width=canvas_width)
            # Seçim frame'ini canvas'ın üst kısmına yerleştir
            self.preview_canvas.coords(self.selection_window_id, 0, 0)
            # Ana önizleme alanının konumunu ayarla (seçim alanının altında)
            self.main_preview_y_offset = 260
            
        self.preview_canvas.bind('<Configure>', on_canvas_configure)
        
        # İlk boyutlandırma için canvas genişliğini al
        self.preview_canvas.update_idletasks()
        initial_width = self.preview_canvas.winfo_width() if self.preview_canvas.winfo_width() > 1 else 850
        self.selection_frame.config(width=initial_width)

        tk.Label(control_frame, text="Better Than OBS", font=("Helvetica", 18, "bold"), fg="white", bg=frame_bg_color).pack(pady=10)

        self.label = tk.Label(control_frame, text="Hazır", font=("Helvetica", 18), fg="black", bg=frame_bg_color)
        self.label.pack(pady=15)

        button_width = 24
        button_pady = 10
        button_style = {
            "font": ("Segoe UI", 12, "bold"),
            "relief": tk.FLAT,
            "bd": 0,
            "activebackground": "#555555",
            "activeforeground": "white",
            "width": button_width,
            "cursor": "hand2",
            "pady": 12,
            "borderwidth": 2,
            "highlightthickness": 0
        }

        self.start_button = tk.Button(control_frame, text="🎬 Kaydı Başlat", command=self.start_recording,
                                      bg="#2E7D32", fg="white", **button_style)
        self.start_button.pack(pady=button_pady)
        self._add_button_hover_effect(self.start_button, "#4CAF50", "#2E7D32")

        self.stop_button = tk.Button(control_frame, text="⏹️ Kaydı Durdur", command=self.stop_recording,
                                     bg="#C62828", fg="white", **button_style, state=tk.DISABLED)
        self.stop_button.pack(pady=button_pady)
        self._add_button_hover_effect(self.stop_button, "#f44336", "#C62828")
        
        self.pause_button = tk.Button(control_frame, text="⏸️ Duraklat", command=self.toggle_pause,
                                      bg="#F57C00", fg="white", **button_style, state=tk.DISABLED)
        self.pause_button.pack(pady=10)
        self._add_button_hover_effect(self.pause_button, "#FF9800", "#F57C00")

        # FPS ayarı
        tk.Label(control_frame, text="FPS (Kare/Saniye):", font=("Helvetica", 13), bg=frame_bg_color).pack(pady=10)
        fps_options = (30, 60, 100, 120)
        self.fps_var = tk.IntVar(value=60)  # Otomatik 60 FPS
        self.fps_spinbox = tk.Spinbox(
            control_frame,
            values=fps_options,
            textvariable=self.fps_var,
            font=("Helvetica", 13),
            width=5,
            justify="center",
            state="readonly"
        )
        self.fps_spinbox.pack(pady=5)
        tk.Label(control_frame, text="Önerilen: 30 FPS", font=("Helvetica", 11), fg="gray", bg=frame_bg_color).pack(pady=(0, 10))

        # Mikrofon seçimi
        tk.Label(control_frame, text="Mikrofon Seçimi:", font=("Helvetica", 13), bg=frame_bg_color).pack(pady=10)
        self.microphone_var = tk.StringVar()
        self.microphone_options = self._get_audio_devices()
        if self.microphone_options:
            self.microphone_var.set(self.microphone_options[0])
        else:
            self.microphone_var.set("Mikrofon Bulunamadı")
            log_print("Uyarı: Hiçbir mikrofon bulunamadı.", level="warning")

        self.microphone_combobox = ttk.Combobox(control_frame, textvariable=self.microphone_var,
                                               values=self.microphone_options, state="readonly", font=("Helvetica", 11), width=35)
        self.microphone_combobox.pack(pady=5)

        # Kayıt dizini ayarı
        tk.Label(control_frame, text="Kayıt Dizini:", font=("Helvetica", 13), bg=frame_bg_color).pack(pady=10)
        self.dir_entry = tk.Entry(control_frame, font=("Helvetica", 12), width=40)
        self.dir_entry.insert(0, self.output_directory)
        self.dir_entry.pack(pady=5)
        dir_button = tk.Button(control_frame, text="📁 Dizin Seç", command=self._select_output_directory_from_main, 
                              font=("Segoe UI", 10, "bold"), bg="#1976D2", fg="white", 
                              relief=tk.FLAT, bd=0, cursor="hand2", pady=8, highlightthickness=0)
        dir_button.pack(pady=5)
        self._add_button_hover_effect(dir_button, "#2196F3", "#1976D2")

        self.status_label = tk.Label(control_frame, text=f"Kayıt Dizini: {self.output_directory}", font=("Helvetica", 11), fg="gray", wraplength=400, bg=frame_bg_color)
        self.status_label.pack(pady=10)
        
        self.region_info_label = tk.Label(control_frame, text="Kayıt Alanı: Tüm Ekran", font=("Helvetica", 11), fg="purple", wraplength=400, bg=frame_bg_color)
        self.region_info_label.pack(pady=5)

        self.select_region_button = tk.Button(control_frame, text="🎯 Kayıt Alanı Seç", command=self.start_region_selection,
                                            bg="#F57C00", fg="white", **button_style)
        self.select_region_button.pack(pady=button_pady)
        self._add_button_hover_effect(self.select_region_button, "#FFC107", "#F57C00")

        self.reset_region_button = tk.Button(control_frame, text="🖥️ Tüm Ekranı Kaydet", command=self.reset_recording_region,
                                             bg="#616161", fg="white", **button_style)
        self.reset_region_button.pack(pady=button_pady)
        self._add_button_hover_effect(self.reset_region_button, "#9E9E9E", "#616161")



        # Sağ panel: Canlı önizleme
        tk.Label(preview_frame, text="Canlı Önizleme", font=("Helvetica", 16, "bold"), bg=frame_bg_color).pack(pady=10)

        self.canvas_width = 850
        self.canvas_height = 700
        self.preview_canvas = tk.Canvas(preview_frame, width=self.canvas_width, height=self.canvas_height, bg="black", bd=0, highlightthickness=0)
        self.preview_canvas.pack(expand=True, fill=tk.BOTH)

        monitor_list = []
        with mss.mss() as sct:
            for idx, monitor in enumerate(sct.monitors[1:], start=1):
                monitor_list.append(f"Ekran {idx}: {monitor['width']}x{monitor['height']}")

        self.selected_monitor_var = tk.StringVar()
        if monitor_list:
            self.selected_monitor_var.set(monitor_list[0])
        else:
            self.selected_monitor_var.set("Ekran bulunamadı")

        monitor_frame = tk.Frame(preview_frame, bg=frame_bg_color)
        monitor_frame.pack(fill=tk.X, pady=(10, 0))

        tk.Label(monitor_frame, text="Kayıt Alınacak Ekran:", font=("Helvetica", 13), bg=frame_bg_color).pack(side=tk.LEFT, padx=5)
        monitor_combobox = ttk.Combobox(monitor_frame, textvariable=self.selected_monitor_var, values=monitor_list, state="readonly", font=("Helvetica", 11), width=30)
        monitor_combobox.pack(side=tk.LEFT, padx=10)

        def set_selected_monitor(event=None):
            idx = monitor_combobox.current() + 1  # mss.monitors[1] ana ekran, [2] ikinci ekran vs.
            with mss.mss() as sct:
                monitor = sct.monitors[idx]
                self.monitor_region = {
                    "top": monitor["top"],
                    "left": monitor["left"],
                    "width": monitor["width"],
                    "height": monitor["height"]
                }
            self.region_info_label.config(text=f"Kayıt Alanı: Ekran {idx} ({monitor['width']}x{monitor['height']})", fg="purple")
            log_print(f"Kayıt alınacak ekran değiştirildi: {self.monitor_region}")

        monitor_combobox.bind("<<ComboboxSelected>>", set_selected_monitor)

        self.preview_canvas.bind("<ButtonPress-1>", self._on_canvas_mouse_press)
        self.preview_canvas.bind("<B1-Motion>", self._on_canvas_mouse_drag)
        self.preview_canvas.bind("<ButtonRelease-1>", self._on_canvas_mouse_release)
        self.master.bind("<Escape>", self._cancel_canvas_selection)

    def _get_audio_devices(self):
        """Sistemdeki mevcut ses giriş cihazlarını (mikrofonları) listeler."""
        devices = []
        try:
            self.p = pyaudio.PyAudio()
            info = self.p.get_host_api_info_by_index(0)
            num_devices = info.get("deviceCount")
            for i in range(num_devices):
                device_info = self.p.get_device_info_by_host_api_device_index(0, i)
                if device_info.get("maxInputChannels") > 0:
                    devices.append(device_info.get("name"))
            log_print(f"Bulunan mikrofonlar: {devices}")
        except Exception as e:
            log_print(f"Mikrofonlar listelenirken hata oluştu: {e}", level="error")
            self.master.after(0, lambda: messagebox.showerror("Ses Hatası", f"Mikrofonlar listelenirken hata oluştu: {e}"))
        finally:
            # PyAudio instance'ı uygulamanın ömrü boyunca açık kalmalı, burada terminate etme
            pass 
        return devices

    def _get_microphone_index(self, mic_name):
        """Mikrofon adına göre indeksini döndürür."""
        try:
            if not self.p:
                self.p = pyaudio.PyAudio()
            info = self.p.get_host_api_info_by_index(0)
            num_devices = info.get("deviceCount")
            for i in range(num_devices):
                device_info = self.p.get_device_info_by_host_api_device_index(0, i)
                if device_info.get("maxInputChannels") > 0 and device_info.get("name") == mic_name:
                    return i
        except Exception as e:
            log_print(f"Mikrofon indeksi alınırken hata: {e}", level="error")
        return -1

    def _ensure_output_directory_exists(self):
        """Kayıt dizininin varlığını kontrol eder, yoksa oluşturur."""
        if not os.path.exists(self.output_directory):
            try:
                os.makedirs(self.output_directory)
                log_print(f"Kayıt dizini oluşturuldu: {self.output_directory}")
            except OSError as e:
                messagebox.showerror("Dizin Hatası", f"Kayıt dizini oluşturulamadı: {self.output_directory}\nHata: {e}")
                self.output_directory = os.path.expanduser("~")
                log_print(f"Kayıt dizini hata nedeniyle varsayılana döndürüldü: {self.output_directory}", level="error")

    def _start_preview_thread(self):
        """Canlı önizleme thread'ini başlatır."""
        if hasattr(self, 'preview_thread') and self.preview_thread and self.preview_thread.is_alive():
            log_print("Önizleme thread'i zaten çalışıyor.")
            return
        
        self.stop_preview = False
        self.preview_thread = threading.Thread(target=self._screen_preview_loop)
        self.preview_thread.daemon = True
        self.preview_thread.start()
        log_print("Önizleme thread'i başlatıldı.")

    def _screen_preview_loop(self):
        """Ekranın canlı önizlemesini Canvas üzerinde gösteren döngü."""
        try:
            if not hasattr(thread_local_data, 'sct'):
                thread_local_data.sct = mss.mss()
            sct = thread_local_data.sct
        except Exception as e:
            log_print(f"Önizleme thread'inde MSS başlatılırken hata: {e}", level="error")
            self.master.after(0, lambda err_msg=str(e): self.status_label.config(text=f"Önizleme hatası: {err_msg}", fg="red"))
            return

        while True:
            if not self.master.winfo_exists():
                log_print("Ana pencere kapandı, önizleme thread'i durduruluyor.")
                break

            try:
                # Pencere boyutlandığında Canvas boyutlarını güncelle
                self.canvas_width = self.preview_canvas.winfo_width()
                self.canvas_height = self.preview_canvas.winfo_height()

                # Seçilen hedefi kullan (tüm ekran yerine)
                sct_img = sct.grab(self.monitor_region)
                img = np.array(sct_img)
                img = cv2.cvtColor(img, cv2.COLOR_RGBA2BGR)

                img_h, img_w, _ = img.shape
                aspect_ratio = img_w / img_h

                if self.canvas_width / self.canvas_height > aspect_ratio:
                    new_h = self.canvas_height
                    new_w = int(new_h * aspect_ratio)
                else:
                    new_w = self.canvas_width
                    new_h = int(new_w / aspect_ratio)

                preview_img = cv2.resize(img, (new_w, new_h), interpolation=cv2.INTER_AREA)

                img_rgb = cv2.cvtColor(preview_img, cv2.COLOR_BGR2RGB)
                img_pil = Image.fromarray(img_rgb)
                img_tk = ImageTk.PhotoImage(image=img_pil)

                self.master.after(0, self._update_canvas, img_tk)

                time.sleep(1 / self.fps)

            except mss.exception.ScreenShotError as e:
                log_print(f"Önizleme ekranı yakalama hatası: {e}", level="error")
                self.master.after(0, lambda err_msg=str(e): self.status_label.config(text=f"Önizleme hatası: {err_msg}", fg="red"))
                break
            except Exception as e:
                log_print(f"Beklenmeyen önizleme hatası: {e}", level="error")
                self.master.after(0, lambda err_msg=str(e): self.status_label.config(text=f"Önizleme hatası: {err_msg}", fg="red"))
                break
        
        if hasattr(thread_local_data, 'sct'):
            thread_local_data.sct.close()
            del thread_local_data.sct
        log_print("Önizleme thread'i sonlandı.")

    def _update_canvas(self, img_tk):
        """Canvas üzerindeki görüntüyü günceller."""
        if not self.master.winfo_exists():
            return
        
        # Sadece ana önizleme görüntüsünü sil, seçim alanını koru
        self.preview_canvas.delete("preview_image")
        self.preview_canvas.delete("selection_rect")
        
        self.preview_canvas.image = img_tk
        
        # Ana önizleme görüntüsünü seçim alanının altına yerleştir
        selection_height = 260
        available_height = self.canvas_height - selection_height
        
        x_offset = (self.canvas_width - img_tk.width()) // 2
        y_offset = selection_height + max(-150, (available_height - img_tk.height()) // 2)
        
        # Ana önizleme görüntüsünü oluştur
        self.preview_canvas.create_image(x_offset, y_offset, image=img_tk, anchor=tk.NW, tags="preview_image")
        
        # Disk uyarısını sağ üste ekle
        if hasattr(self, 'disk_warning_label') and self.disk_warning_label:
            self.preview_canvas.coords(self.disk_warning_label, self.canvas_width - 10, 10)
        
        # Seçim frame'ini tekrar üste getir (eğer kayıp olduysa)
        if hasattr(self, 'selection_window_id'):
            self.preview_canvas.coords(self.selection_window_id, 0, 0)

        # Eğer alan seçimi yapılıyorsa, Canvas üzerinde dikdörtgeni çiz
        if self.is_selecting_region and self.start_x is not None and self.current_x is not None:
            self.selection_rect_id = self.preview_canvas.create_rectangle(
                self.start_x, self.start_y, self.current_x, self.current_y, 
                outline="blue", width=2, dash=(5, 2), tags="selection_rect"
            )

    def _record_audio_thread(self, audio_filename, input_device_index):
        """Mikrofondan ses kaydını yürüten thread fonksiyonu."""
        log_print(f"Ses kaydı başlatılıyor: {audio_filename} (Cihaz Indeksi: {input_device_index})")
        self.audio_frames = []
        try:
            # PyAudio instance'ı zaten ana thread'de başlatıldı, burada tekrar başlatmaya gerek yok.
            # Ancak thread-safe olması için PyAudio objesini burada da kontrol edelim.
            # Eğer self.p ana thread'de başlatıldıysa, bu thread'de de kullanılabilir olmalı.
            # Bazı durumlarda PyAudio objesi thread'ler arasında doğrudan paylaşım sorunları yaşatabilir.
            # En güvenli yol, her thread'in kendi PyAudio objesini oluşturmasıdır,
            # ancak bu da kaynak tüketimini artırabilir.
            # Şu anki thread_local_data yaklaşımı MSS için, PyAudio için de benzer bir durum olabilir.
            # PyAudio'nun kendisi thread-safe olmayabilir.
            # Basitlik adına, ana thread'deki self.p'yi kullanmaya devam edelim ve sorun çıkarsa değiştirelim.
            
            # Alternatif: Her thread kendi PyAudio objesini oluşturup kapatır
            # p_local = pyaudio.PyAudio()
            # stream_local = p_local.open(...)
            # ...
            # stream_local.close()
            # p_local.terminate()

            self.audio_stream = self.p.open(format=self.audio_format,
                                            channels=self.audio_channels,
                                            rate=self.audio_rate,
                                            input=True,
                                            frames_per_buffer=self.audio_chunk_size,
                                            input_device_index=input_device_index)
            
            while self.recording:
                if self.paused:
                    time.sleep(0.1)
                    continue
                data = self.audio_stream.read(self.audio_chunk_size)
                self.audio_frames.append(data)
            
            log_print("Ses akışı durduruldu.")
            self.audio_stream.stop_stream()
            self.audio_stream.close()

            # Ses dosyasını kaydet
            wf = wave.open(audio_filename, 'wb')
            wf.setnchannels(self.audio_channels)
            wf.setsampwidth(self.p.get_sample_size(self.audio_format))
            wf.setframerate(self.audio_rate)
            wf.writeframes(b''.join(self.audio_frames))
            wf.close()
            log_print(f"Ses dosyası kaydedildi: {audio_filename}")

        except Exception as e:
            log_print(f"Ses kaydı sırasında hata oluştu: {e}", level="error")
            self.master.after(0, lambda: messagebox.showerror("Ses Kayıt Hatası", f"Ses kaydı sırasında hata oluştu: {e}"))
            self.recording = False # Ses hatası olursa kaydı durdur
        finally:
            # Ses kaydı thread'i sonlandığında akışı kapat
            try:
                if self.audio_stream and hasattr(self.audio_stream, 'is_active') and self.audio_stream.is_active():
                    self.audio_stream.stop_stream()
                    self.audio_stream.close()
            except:
                pass
            log_print("Ses kayıt thread'i sonlandı.")


    def start_recording(self):
        if not self.recording:
            self.fps = self.fps_var.get()
            log_print(f"Kayıt FPS ayarı: {self.fps}")

            selected_mic_name = self.microphone_var.get()
            microphone_index = -1
            if selected_mic_name != "Mikrofon Bulunamadı":
                microphone_index = self._get_microphone_index(selected_mic_name)

            if microphone_index == -1 and selected_mic_name != "Mikrofon Bulunamadı":
                messagebox.showerror("Mikrofon Hatası", f"Seçilen mikrofon bulunamadı: '{selected_mic_name}'. Lütfen geçerli bir mikrofon seçin.")
                return
            elif not self.microphone_options:
                messagebox.showwarning("Ses Kaydı Uyarısı", "Sistemde mikrofon bulunamadı. Sadece ekran kaydedilecek.")
                microphone_index = -1

            self.recording = True
            self._update_button_states_on_record_start()
            self.label.config(text="Kayıt Yapılıyor...", fg="red")

            timestamp = time.strftime("%Y%m%d_%H%M%S")
            ext = self.format_var.get()
            self.current_record_filename_video = os.path.join(self.output_directory, f"ekran_kaydi_{timestamp}.{ext}")  # .mp4 uzantısı!
            self.current_record_filename_audio = os.path.join(self.output_directory, f"ses_kaydi_{timestamp}.wav")
            
            self.status_label.config(text=f"Video kaydediliyor: '{os.path.basename(self.current_record_filename_video)}'", fg="blue")
            log_print(f"Video kaydı başlatılıyor: {self.current_record_filename_video}")

            if hasattr(self, "selected_monitors") and self.selected_monitors:
                for idx in self.selected_monitors:
                    with mss.mss() as sct:
                        monitor = sct.monitors[idx]
                        # Her monitör için ayrı dosya adı oluştur
                        video_filename = os.path.join(self.output_directory, f"ekran_kaydi_monitor{idx}_{timestamp}.{ext}")
                        # Her monitör için ayrı thread başlat
                        threading.Thread(target=self._record_screen_thread, args=(monitor, video_filename)).start()
            else:
                # Tek monitör için eski sistem
                self.record_thread = threading.Thread(target=self._record_screen_thread, args=(self.monitor_region, self.current_record_filename_video))
                self.record_thread.start()

            if microphone_index != -1:
                log_print(f"Ses kaydı başlatılıyor: {self.current_record_filename_audio}")
                self.audio_record_thread = threading.Thread(target=self._record_audio_thread, args=(self.current_record_filename_audio, microphone_index))
                self.audio_record_thread.start()
            else:
                self.audio_record_thread = None # Ses kaydı yapılmayacaksa thread'i None yap

            # Kayıt süresi ayarı (varsa)
            if hasattr(self, 'record_duration_var') and self.record_duration_var.get() > 0:
                threading.Timer(self.record_duration_var.get(), self.stop_recording).start()

        else:
            messagebox.showwarning("Uyarı", "Kayıt zaten devam ediyor!")

    def stop_recording(self):
        if self.recording:
            self.recording = False
            self.label.config(text="Durduruluyor...", fg="orange")
            self.status_label.config(text="Lütfen bekleyiniz, kayıtlar sonlandırılıyor...", fg="orange")
            log_print("Kayıt durdurma sinyali gönderildi.")

            # Video thread'inin bitmesini bekle
            if self.record_thread and self.record_thread.is_alive():
                log_print("Video kayıt thread'inin bitmesi bekleniyor...")
                self.record_thread.join(timeout=10)
                if self.record_thread.is_alive():
                    log_print("Uyarı: Video kayıt thread'i zaman aşımına uğradı.", level="warning")
                else:
                    log_print("Video kayıt thread'i başarıyla sonlandı.")

            # Ses thread'inin bitmesini bekle
            if self.audio_record_thread and self.audio_record_thread.is_alive():
                log_print("Ses kayıt thread'inin bitmesi bekleniyor...")
                self.audio_record_thread.join(timeout=10)
                if self.audio_record_thread.is_alive():
                    log_print("Uyarı: Ses kayıt thread'i zaman aşımına uğradı.", level="warning")
                else:
                    log_print("Ses kayıt thread'i başarıyla sonlandı.")

            # Video ve ses dosyalarını birleştir
            if (hasattr(self, 'current_record_filename_video') and self.current_record_filename_video and 
                hasattr(self, 'current_record_filename_audio') and self.current_record_filename_audio and 
                os.path.exists(self.current_record_filename_video) and os.path.exists(self.current_record_filename_audio)):
                
                self.status_label.config(text="Video ve ses birleştiriliyor...", fg="orange")
                log_print("Video ve ses dosyaları birleştiriliyor...")
                
                # Birleştirme işlemini ayrı thread'de yap
                threading.Thread(target=self._merge_audio_video_thread).start()
            else:
                self._finalize_recording()
        else:
            messagebox.showwarning("Uyarı", "Zaten kayıt yapılmıyor!")

    def _merge_audio_video_thread(self):
        """Video ve ses dosyalarını birleştiren thread fonksiyonu."""
        try:
            video_path = self.current_record_filename_video
            audio_path = self.current_record_filename_audio
            
            # Geçici dosya adı oluştur
            base_name = os.path.splitext(video_path)[0]
            temp_output = base_name + "_temp.mp4"
            
            # FFmpeg komutu
            cmd = [
                'ffmpeg',
                '-i', video_path,  # Video girişi
                '-i', audio_path,  # Ses girişi
                '-c:v', 'copy',    # Video codec'ini kopyala (yeniden encode etme)
                '-c:a', 'aac',     # Ses codec'i AAC
                '-strict', 'experimental',
                '-y',              # Dosya varsa üzerine yaz
                temp_output
            ]
            
            log_print(f"FFmpeg komutu çalıştırılıyor: {' '.join(cmd)}")
            
            # FFmpeg'i çalıştır
            result = subprocess.run(cmd, capture_output=True, text=True, creationflags=subprocess.CREATE_NO_WINDOW)
            
            if result.returncode == 0:
                # Başarılı - orijinal video dosyasını sil ve temp dosyayı yeniden adlandır
                if os.path.exists(video_path):
                    os.remove(video_path)
                os.rename(temp_output, video_path)
                
                # Ses dosyasını sil
                if os.path.exists(audio_path):
                    os.remove(audio_path)
                    log_print(f"Geçici ses dosyası silindi: {audio_path}")
                
                log_print(f"Video ve ses başarıyla birleştirildi: {video_path}")
                self.master.after(0, self._finalize_recording)
            else:
                # Hata durumunda
                log_print(f"FFmpeg hatası: {result.stderr}", level="error")
                # Temp dosyayı sil
                if os.path.exists(temp_output):
                    os.remove(temp_output)
                
                # Kullanıcıya hata bildir ve ayrı dosyaları koru
                self.master.after(0, lambda: messagebox.showwarning(
                    "Birleştirme Hatası", 
                    f"Video ve ses birleştirilemedi. Dosyalar ayrı ayrı kaydedildi.\n\n"
                    f"Video: {os.path.basename(video_path)}\n"
                    f"Ses: {os.path.basename(audio_path)}\n\n"
                    f"FFmpeg hatası: {result.stderr[:200]}..."
                ))
                self.master.after(0, self._finalize_recording)
                
        except FileNotFoundError:
            log_print("FFmpeg bulunamadı. Lütfen FFmpeg'in sistem PATH'inde olduğundan emin olun.", level="error")
            self.master.after(0, lambda: messagebox.showerror(
                "FFmpeg Bulunamadı", 
                "FFmpeg bulunamadı. Video ve ses ayrı dosyalar olarak kaydedildi.\n\n"
                "FFmpeg'i indirmek için: https://ffmpeg.org/download.html"
            ))
            self.master.after(0, self._finalize_recording)
        except Exception as e:
            log_print(f"Birleştirme sırasında beklenmeyen hata: {e}", level="error")
            self.master.after(0, lambda: messagebox.showerror(
                "Birleştirme Hatası", 
                f"Video ve ses birleştirilemedi: {e}\n\n"
                f"Dosyalar ayrı ayrı kaydedildi."
            ))
            self.master.after(0, self._finalize_recording)
    
    def _finalize_recording(self):
        """Kayıt işlemini sonlandırır ve kullanıcıya bilgi verir."""
        self._update_button_states_on_record_stop()
        self.label.config(text="Hazır", fg="black")
        
        # Disk takibini durdur
        if hasattr(self, 'disk_warning_label') and self.disk_warning_label:
            self.preview_canvas.delete(self.disk_warning_label)
            self.disk_warning_label = None
        
        # Kullanıcıya dosyanın kaydedildiğini bildir
        if hasattr(self, 'current_record_filename_video') and self.current_record_filename_video:
            if hasattr(self, 'current_record_filename_audio') and os.path.exists(self.current_record_filename_audio):
                # Ses dosyası hala varsa, birleştirme başarısız olmuş
                final_message = (f"Ekran kaydı tamamlandı.\n\n"
                               f"Video: {os.path.basename(self.current_record_filename_video)}\n"
                               f"Ses: {os.path.basename(self.current_record_filename_audio)}")
            else:
                # Ses dosyası yoksa, başarıyla birleştirilmiş
                final_message = f"Ekran kaydı tamamlandı.\n\nVideo (ses dahil): {os.path.basename(self.current_record_filename_video)}"
        else:
            final_message = "Ekran kaydı tamamlandı."

        self.status_label.config(text="Kayıt tamamlandı. Dosyalar kaydedildi.", fg="green")
        messagebox.showinfo("Kayıt Tamamlandı", final_message)

    def _start_disk_monitoring(self):
        """Disk alanı takibini başlatır."""
        if self.disk_check_thread and self.disk_check_thread.is_alive():
            return
        
        self.disk_check_thread = threading.Thread(target=self._disk_monitor_loop)
        self.disk_check_thread.daemon = True
        self.disk_check_thread.start()
    
    def _disk_monitor_loop(self):
        """Disk alanını takip eder ve tahmini süre hesaplar."""
        import shutil
        
        while self.recording:
            try:
                # Disk alanını kontrol et
                free_space = shutil.disk_usage(self.output_directory).free
                
                # Tahmini dosya boyutu (MB/saniye)
                estimated_mb_per_sec = (self.monitor_region['width'] * self.monitor_region['height'] * 3 * self.fps) / (1024 * 1024)
                
                # Tahmini kalan süre (saniye)
                self.estimated_time_left = int(free_space / (estimated_mb_per_sec * 1024 * 1024))
                
                # Uyarı mesajını güncelle
                if self.estimated_time_left < 300:  # 5 dakikadan az
                    warning_text = f"⚠️ Disk Dolacak: {self.estimated_time_left//60}:{self.estimated_time_left%60:02d}"
                    color = "red"
                else:
                    warning_text = f"💾 Tahmini Süre: {self.estimated_time_left//60}:{self.estimated_time_left%60:02d}"
                    color = "yellow"
                
                self.master.after(0, self._update_disk_warning, warning_text, color)
                
                time.sleep(5)  # 5 saniyede bir kontrol et
            except:
                break
    
    def _update_disk_warning(self, text, color):
        """Disk uyarısını canvas üzerinde günceller."""
        if hasattr(self, 'disk_warning_label') and self.disk_warning_label:
            self.preview_canvas.delete(self.disk_warning_label)
        
        self.disk_warning_label = self.preview_canvas.create_text(
            self.canvas_width - 10, 10, text=text, fill=color, 
            font=("Arial", 12, "bold"), anchor="ne", tags="disk_warning"
        )

    def _record_screen_thread(self, monitor_to_record, video_filename):
        """Kayıt işlemini yürüten thread fonksiyonu."""
        try:
            if not hasattr(thread_local_data, 'sct'):
                thread_local_data.sct = mss.mss()
            sct = thread_local_data.sct
        except Exception as e:
            log_print(f"Kayıt thread'inde MSS başlatılırken hata: {e}", level="error")
            messagebox.showerror("Kayıt Hatası", f"MSS başlatılırken hata oluştu: {e}. Kayıt başlatılamadı.")
            self.recording = False
            self.master.after(0, self._update_button_states_on_record_stop)
            self.master.after(0, lambda: self.label.config(text="Hata!", fg="red"))
            self.master.after(0, lambda: self.status_label.config(text="Kayıt başlatılamadı.", fg="red"))
            return

        monitor_to_record = self.monitor_region
        
        video_width = monitor_to_record['width']
        video_height = monitor_to_record['height']

        if video_width <= 0 or video_height <= 0:
            log_print(f"Hata: Geçersiz kayıt alanı boyutları: Genişlik={video_width}, Yükseklik={video_height}", level="error")
            messagebox.showerror("Kayıt Hatası", "Geçersiz kayıt alanı boyutları. Kayıt başlatılamadı.")
            self.recording = False
            self.master.after(0, self._update_button_states_on_record_stop)
            self.master.after(0, lambda: self.label.config(text="Hata!", fg="red"))
            self.master.after(0, lambda: self.status_label.config(text="Kayıt başlatılamadı (geçersiz alan).", fg="red"))
            return

        ext = self.format_var.get()
        if ext == 'mp4':
            fourcc = cv2.VideoWriter_fourcc(*'mp4v')
        else:
            fourcc = cv2.VideoWriter_fourcc(*'XVID')
        
        # Ses ile birlikte kayıt için fourcc ayarla
        try:
            self.out = cv2.VideoWriter(video_filename, fourcc, self.fps, (video_width, video_height), True)
        except Exception as e:
            log_print(f"Video yazıcısı oluşturulurken hata: {e}", level="error")
            messagebox.showerror("Kayıt Hatası", f"Video yazıcısı oluşturulurken hata oluştu: {e}\nDosya yolu veya codec sorunu olabilir.")
            self.recording = False
            self.master.after(0, self._update_button_states_on_record_stop)
            self.master.after(0, lambda: self.label.config(text="Hata!", fg="red"))
            self.master.after(0, lambda: self.status_label.config(text="Kayıt başlatılamadı.", fg="red"))
            return

        if not self.out.isOpened():
            log_print(f"Hata: Video yazıcısı açılamadı. Dosya: {self.current_record_filename_video}", level="error")
            messagebox.showerror("Kayıt Hatası", f"Video yazıcısı açılamadı. '{self.current_record_filename_video}' yazılabilir mi veya codec destekleniyor mu?")
            self.recording = False
            self.master.after(0, self._update_button_states_on_record_stop)
            self.master.after(0, lambda: self.label.config(text="Hata!", fg="red"))
            self.master.after(0, lambda: self.status_label.config(text="Kayıt başlatılamadı.", fg="red"))
            return
        
        log_print("Video yazıcısı başarıyla açıldı.")

        while self.recording:
            if self.paused:
                time.sleep(0.1)
                continue
            try:
                # Pencere seçildiyse pencere konumunu güncelle
                if self.current_target['type'] == 'window' and WIN32_AVAILABLE:
                    try:
                        hwnd = self.current_target['hwnd']
                        if win32gui.IsWindow(hwnd):
                            rect = win32gui.GetWindowRect(hwnd)
                            monitor_to_record = {
                                'top': rect[1], 
                                'left': rect[0], 
                                'width': rect[2] - rect[0], 
                                'height': rect[3] - rect[1]
                            }
                    except:
                        pass
                
                sct_img = sct.grab(monitor_to_record)
                img = np.array(sct_img)
                img = cv2.cvtColor(img, cv2.COLOR_RGBA2BGR)
                self.out.write(img)
                time.sleep(1 / self.fps)
            except mss.exception.ScreenShotError as e:
                log_print(f"Ekran yakalama hatası (kayıt thread): {e}", level="error")
                messagebox.showerror("Hata", f"Ekran yakalama hatası: {e}. Kayıt durduruldu.")
                self.recording = False
                self.master.after(0, self.stop_recording)
                break
            except Exception as e:
                log_print(f"Beklenmeyen hata (kayıt thread): {e}", level="error")
                messagebox.showerror("Hata", f"Beklenmeyen hata oluştu: {e}. Kayıt durduruldu.")
                self.recording = False
                self.master.after(0, self.stop_recording)
                break

        if self.out:
            self.out.release()
            self.out = None
            log_print("Video yazıcısı serbest bırakıldı.")
        
        if hasattr(thread_local_data, 'sct'):
            thread_local_data.sct.close()
            del thread_local_data.sct
        log_print("Kayıt thread'i sonlandı.")

    # Kayıt dizini seçme işlemi ana ekrana taşındığı için bu fonksiyonun adı değişti.
    def _select_output_directory_from_main(self):
        """Kayıt dizinini değiştirmek için dosya diyaloğu açar (ana ekrandan)."""
        new_directory = filedialog.askdirectory(initialdir=self.output_directory, title="Kayıt Dizini Seç")
        if new_directory:
            self.output_directory = new_directory
            self.dir_entry.delete(0, tk.END)
            self.dir_entry.insert(0, self.output_directory)
            self.status_label.config(text=f"Kayıt Dizini: {self.output_directory}", fg="blue")
            messagebox.showinfo("Dizin Değiştirildi", f"Kayıt dizini şuraya ayarlandı:\n{self.output_directory}")
            log_print(f"Kayıt dizini değiştirildi: {self.output_directory}")
        else:
            messagebox.showinfo("Bilgi", "Kayıt dizini değişikliği iptal edildi.")
            log_print("Kayıt dizini değişikliği iptal edildi.")

    def start_region_selection(self):
        """Kullanıcının canlı önizleme Canvas'ı üzerinde bir bölge seçmesini başlatır."""
        if self.recording:
            messagebox.showwarning("Uyarı", "Kayıt devam ederken alan seçemezsiniz.")
            return

        if self.is_selecting_region:
            messagebox.showinfo("Bilgi", "Zaten bir alan seçimi devam ediyor. Lütfen bitirin.")
            return
            
        self.is_selecting_region = True
        self.select_region_button.config(state=tk.DISABLED)
        self.reset_region_button.config(state=tk.DISABLED)
        self.status_label.config(text="Önizleme üzerinde kayıt alanını seçmek için sürükle bırak yapın veya ESC ile iptal edin.", fg="red")
        self.preview_canvas.config(cursor="cross")

        self.preview_canvas.delete("selection_rect")
        self.selection_rect_id = None
        self.start_x, self.start_y = None, None
        self.current_x, self.current_y = None, None
        log_print("Canvas üzerinde alan seçimi başlatıldı.")

    def _on_canvas_mouse_press(self, event):
        if not self.is_selecting_region:
            return
        self.start_x = event.x
        self.start_y = event.y
        self.current_x = event.x
        self.current_y = event.y
        self.preview_canvas.delete("selection_rect")
        self.selection_rect_id = self.preview_canvas.create_rectangle(
            self.start_x, self.start_y, self.current_x, self.current_y, 
            outline="blue", width=2, dash=(5, 2), tag="selection_rect"
        )
        # log_print(f"Canvas fare basıldı: ({self.start_x}, {self.start_y})")

    def _on_canvas_mouse_drag(self, event):
        if not self.is_selecting_region:
            return
        self.current_x = event.x
        self.current_y = event.y
        if self.selection_rect_id:
            self.preview_canvas.coords(self.selection_rect_id, self.start_x, self.start_y, self.current_x, self.current_y)

    def _on_canvas_mouse_release(self, event):
        if not self.is_selecting_region:
            return
        
        end_x, end_y = event.x, event.y
        log_print(f"Canvas fare bırakıldı: ({end_x}, {end_y})")

        full_screen_width, full_screen_height = pyautogui.size()
        
        temp_img_width = full_screen_width
        temp_img_height = full_screen_height
        aspect_ratio = temp_img_width / temp_img_height

        current_canvas_width = self.preview_canvas.winfo_width()
        current_canvas_height = self.preview_canvas.winfo_height()

        if current_canvas_width / current_canvas_height > aspect_ratio:
            rendered_h = current_canvas_height
            rendered_w = int(rendered_h * aspect_ratio)
        else:
            rendered_w = current_canvas_width
            rendered_h = int(rendered_w / aspect_ratio)

        x_offset_canvas = (current_canvas_width - rendered_w) // 2
        y_offset_canvas = (current_canvas_height - rendered_h) // 2

        selected_canvas_x1 = max(0, min(self.start_x, end_x) - x_offset_canvas)
        selected_canvas_y1 = max(0, min(self.start_y, end_y) - y_offset_canvas)
        selected_canvas_x2 = max(0, max(self.start_x, end_x) - x_offset_canvas)
        selected_canvas_y2 = max(0, max(self.start_y, end_y) - y_offset_canvas)
        
        selected_canvas_x1 = min(max(0, selected_canvas_x1), rendered_w)
        selected_canvas_y1 = min(max(0, selected_canvas_y1), rendered_h)
        selected_canvas_x2 = min(max(0, selected_canvas_x2), rendered_w)
        selected_canvas_y2 = min(max(0, selected_canvas_y2), rendered_h)

        scale_factor_x = full_screen_width / rendered_w
        scale_factor_y = full_screen_height / rendered_h

        real_x1 = int(selected_canvas_x1 * scale_factor_x)
        real_y1 = int(selected_canvas_y1 * scale_factor_y)
        real_x2 = int(selected_canvas_x2 * scale_factor_x)
        real_y2 = int(selected_canvas_y2 * scale_factor_y)

        width = real_x2 - real_x1
        height = real_y2 - real_y1
        
        min_dim = 10
        if width < min_dim or height < min_dim:
            messagebox.showwarning("Geçersiz Seçim", f"Seçilen alan çok küçük (min. {min_dim}x{min_dim} piksel). Tüm ekran kaydedilmeye devam edecek.")
            self.reset_recording_region()
            log_print("Geçersiz seçim (boyut çok küçük), kayıt alanı tüm ekrana sıfırlandı.", level="warning")
        elif width > 0 and height > 0:
            self.monitor_region = {"top": real_y1, "left": real_x1, "width": width, "height": height}
            self.region_info_label.config(text=f"Kayıt Alanı: Sol: {real_x1}, Üst: {real_y1}, Genişlik: {width}, Yükseklik: {height}", fg="purple")
            messagebox.showinfo("Kayıt Alanı", f"Ekran kayıt alanı seçildi:\nSol: {real_x1}, Üst: {real_y1}\nGenişlik: {width}, Yükseklik: {height}")
            log_print(f"Seçilen gerçek kayıt alanı: {self.monitor_region}")
        else:
            messagebox.showwarning("Geçersiz Seçim", "Geçerli bir kayıt alanı seçmediniz (genişlik veya yükseklik sıfır/negatif). Tüm ekran kaydedilmeye devam edecek.")
            self.reset_recording_region()
            log_print("Geçersiz seçim, kayıt alanı tüm ekrana sıfırlandı.", level="warning")

        self._finalize_canvas_selection()

    def _cancel_canvas_selection(self, event=None):
        """ESC tuşu ile Canvas üzerindeki seçimi iptal etme."""
        if self.is_selecting_region:
            messagebox.showinfo("Seçim İptal Edildi", "Kayıt alanı seçimi iptal edildi. Tüm ekran kaydedilmeye devam edecek.")
            self.reset_recording_region()
            self._finalize_canvas_selection()
            log_print("Canvas üzerindeki seçim iptal edildi.")

    def _finalize_canvas_selection(self):
        """Canvas üzerindeki seçim sonrası temizlik işlemleri."""
        self.is_selecting_region = False
        self.preview_canvas.delete("selection_rect")
        self.selection_rect_id = None
        self.preview_canvas.config(cursor="arrow")
        self.select_region_button.config(state=tk.NORMAL)
        self.reset_region_button.config(state=tk.NORMAL)
        self.status_label.config(text=f"Kayıt Dizini: {self.output_directory}", fg="gray")
        log_print("Canvas seçim işlemi tamamlandı.")

    def reset_recording_region(self):
        """Kayıt alanını tüm ekrana sıfırlar."""
        self.monitor_region = {"top": 0, "left": 0, "width": pyautogui.size().width, "height": pyautogui.size().height}
        self.region_info_label.config(text="Kayıt Alanı: Tüm Ekran", fg="purple")
        log_print("Kayıt alanı tüm ekrana sıfırlandı.")

    def _update_button_states_on_record_start(self):
        self.start_button.config(state=tk.DISABLED)
        self.stop_button.config(state=tk.NORMAL)
        self.pause_button.config(state=tk.NORMAL)  # Duraklat butonunu aktif et
        self.fps_spinbox.config(state=tk.DISABLED)
        self.microphone_combobox.config(state=tk.DISABLED)
        self.dir_entry.config(state=tk.DISABLED)
        try:
            parent = self.dir_entry.master
            for widget in parent.winfo_children():
                if isinstance(widget, tk.Button) and "Dizin Seç" in widget.cget("text"):
                    widget.config(state=tk.DISABLED)
        except:
            pass
        self.select_region_button.config(state=tk.DISABLED)
        self.reset_region_button.config(state=tk.DISABLED)

    def _update_button_states_on_record_stop(self):
        self.start_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)
        self.pause_button.config(state=tk.DISABLED)  # Duraklat butonunu pasif et
        self.fps_spinbox.config(state=tk.NORMAL)
        self.microphone_combobox.config(state="readonly")
        self.dir_entry.config(state=tk.NORMAL)
        try:
            parent = self.dir_entry.master
            for widget in parent.winfo_children():
                if isinstance(widget, tk.Button) and "Dizin Seç" in widget.cget("text"):
                    widget.config(state=tk.NORMAL)
        except:
            pass
        self.select_region_button.config(state=tk.NORMAL)
        self.reset_region_button.config(state=tk.NORMAL)

    def toggle_pause(self):
        self.paused = not self.paused
        if self.paused:
            self.pause_button.config(text="Devam Et", bg="#2196F3")
            self.label.config(text="Kayıt Duraklatıldı", fg="orange")
            self.status_label.config(text="Kayıt duraklatıldı.", fg="orange")
        else:
            self.pause_button.config(text="Duraklat", bg="#FF9800")
            self.label.config(text="Kayıt Yapılıyor...", fg="red")
            if hasattr(self, 'current_record_filename_video') and self.current_record_filename_video:
                self.status_label.config(text=f"Video kaydediliyor: '{os.path.basename(self.current_record_filename_video)}'", fg="blue")
            else:
                self.status_label.config(text="Video kaydediliyor...", fg="blue")

    def on_closing(self):
        log_print("Uygulama kapatılıyor...")
        if self.recording:
            if messagebox.askokcancel("Çıkış", "Kayıt devam ediyor. Çıkmak istiyor musunuz?"):
                self.recording = False
                if self.record_thread and self.record_thread.is_alive():
                    self.record_thread.join(timeout=2)
                if self.audio_record_thread and self.audio_record_thread.is_alive():
                    self.audio_record_thread.join(timeout=2)
                
                if self.p:
                    self.p.terminate()
                    log_print("PyAudio terminate edildi.")
                
                if hasattr(thread_local_data, 'sct'):
                    thread_local_data.sct.close()
                    del thread_local_data.sct
                self.master.destroy()
            else:
                return
        else:
            if self.p:
                self.p.terminate()
                log_print("PyAudio terminate edildi.")

            if hasattr(thread_local_data, 'sct'):
                thread_local_data.sct.close()
                del thread_local_data.sct
            self.master.destroy()
        log_print("Uygulama başarıyla kapatıldı.")

    def show_settings_panel(self):
        """Ana pencerede ayarlar panelini gösterir."""
        # Ayarlar paneli frame'i oluştur
        if hasattr(self, 'settings_panel') and self.settings_panel.winfo_exists():
            self.settings_panel.destroy()
        
        self.settings_panel = tk.Frame(self.master, bg="#2c3e50", relief=tk.RAISED, bd=2)
        self.settings_panel.place(x=50, y=50, width=400, height=500)
        
        # Başlık
        title_frame = tk.Frame(self.settings_panel, bg="#34495e", height=40)
        title_frame.pack(fill=tk.X)
        title_frame.pack_propagate(False)
        
        tk.Label(title_frame, text="⚙️ Ayarlar", font=("Segoe UI", 14, "bold"), 
                fg="white", bg="#34495e").pack(pady=8)
        
        # Kapat butonu
        close_btn = tk.Button(title_frame, text="✖", font=("Arial", 12, "bold"), 
                             fg="white", bg="#e74c3c", relief=tk.FLAT, bd=0,
                             command=lambda: self.settings_panel.destroy())
        close_btn.place(x=365, y=5, width=30, height=30)
        
        # İçerik alanı
        content_frame = tk.Frame(self.settings_panel, bg="#2c3e50")
        content_frame.pack(fill=tk.BOTH, expand=True, padx=15, pady=15)
        
        # FPS Ayarı
        tk.Label(content_frame, text="FPS (Kare/Saniye):", font=("Segoe UI", 11, "bold"), 
                fg="white", bg="#2c3e50").pack(anchor="w", pady=(0, 5))
        fps_frame = tk.Frame(content_frame, bg="#2c3e50")
        fps_frame.pack(fill=tk.X, pady=(0, 15))
        
        fps_options = [30, 60, 100, 120]
        self.fps_var = tk.IntVar(value=60)
        for fps in fps_options:
            tk.Radiobutton(fps_frame, text=str(fps), variable=self.fps_var, value=fps,
                          font=("Segoe UI", 10), fg="white", bg="#2c3e50", 
                          selectcolor="#3498db", activebackground="#2c3e50").pack(side=tk.LEFT, padx=10)
        
        # Format Ayarı
        tk.Label(content_frame, text="Kayıt Formatı:", font=("Segoe UI", 11, "bold"), 
                fg="white", bg="#2c3e50").pack(anchor="w", pady=(0, 5))
        format_frame = tk.Frame(content_frame, bg="#2c3e50")
        format_frame.pack(fill=tk.X, pady=(0, 15))
        
        self.format_var = tk.StringVar(value="mp4")
        formats = ["mp4", "avi", "mkv"]
        for fmt in formats:
            tk.Radiobutton(format_frame, text=fmt.upper(), variable=self.format_var, value=fmt,
                          font=("Segoe UI", 10), fg="white", bg="#2c3e50", 
                          selectcolor="#3498db", activebackground="#2c3e50").pack(side=tk.LEFT, padx=15)
        
        # Kısayol Ayarları
        tk.Label(content_frame, text="Klavye Kısayolları:", font=("Segoe UI", 11, "bold"), 
                fg="white", bg="#2c3e50").pack(anchor="w", pady=(10, 5))
        
        shortcut_frame = tk.Frame(content_frame, bg="#2c3e50")
        shortcut_frame.pack(fill=tk.X, pady=(0, 15))
        
        shortcuts = [
            ("Kayıt Başlat/Durdur:", "F9"),
            ("Mute/Unmute:", "F8"),
            ("Ekran Seçimi:", "F7")
        ]
        
        for i, (label, default) in enumerate(shortcuts):
            tk.Label(shortcut_frame, text=label, font=("Segoe UI", 9), 
                    fg="#bdc3c7", bg="#2c3e50").grid(row=i, column=0, sticky="w", pady=2)
            tk.Entry(shortcut_frame, width=8, font=("Segoe UI", 9), bg="#34495e", 
                    fg="white", insertbackground="white").grid(row=i, column=1, padx=(10, 0), pady=2)
        
        # Kaydet butonu
        save_btn = tk.Button(content_frame, text="💾 Ayarları Kaydet", 
                            font=("Segoe UI", 11, "bold"), bg="#27ae60", fg="white",
                            relief=tk.FLAT, bd=0, cursor="hand2", pady=8,
                            command=lambda: [messagebox.showinfo("Ayarlar", "Ayarlar kaydedildi!"), 
                                           self.settings_panel.destroy()])
        save_btn.pack(pady=20, fill=tk.X)
        
        # Hover efekti
        def on_enter(e): save_btn.config(bg="#2ecc71")
        def on_leave(e): save_btn.config(bg="#27ae60")
        save_btn.bind("<Enter>", on_enter)
        save_btn.bind("<Leave>", on_leave)

    def open_settings(self):
        settings_win = tk.Toplevel(self.master)
        settings_win.title("Ayarlar")
        settings_win.geometry("520x650")
        tk.Label(settings_win, text="Ayarlar", font=("Helvetica", 16, "bold")).pack(pady=10)

        # Uygulama sesi hariç tutma
        tk.Label(settings_win, text="Sesini Kayda Almayacağın Uygulamaları Seç:", font=("Helvetica", 12)).pack(pady=10)

        search_var = tk.StringVar()
        search_entry = tk.Entry(settings_win, textvariable=search_var, font=("Helvetica", 11), width=40, fg="gray")
        search_entry.pack(pady=5)
        search_entry.insert(0, "Uygulama Adı Ara...")

        def on_search_entry_click(event):
            if search_entry.get() == "Uygulama Adı Ara...":
                search_entry.delete(0, tk.END)
                search_entry.config(fg="black")

        search_entry.bind("<FocusIn>", on_search_entry_click)

        app_listbox = tk.Listbox(settings_win, selectmode=tk.MULTIPLE, width=60, height=10)
        app_listbox.pack(pady=5)

        apps = []
        for proc in psutil.process_iter(['pid', 'name']):
            if proc.info['name']:
                apps.append(proc.info['name'])
        apps = sorted(set(apps))

        def update_listbox(*args):
            search_term = search_var.get().lower()
            app_listbox.delete(0, tk.END)
            # Eğer arama kutusu boşsa veya placeholder ise tüm uygulamaları göster
            if not search_term or search_term == "uygulama adı ara...":
                for app in apps:
                    app_listbox.insert(tk.END, app)
            else:
                for app in apps:
                    if search_term in app.lower():
                        app_listbox.insert(tk.END, app)

        search_var.trace_add("write", update_listbox)
        update_listbox()  # Başlangıçta doldur

        # Kısayol ayarları
        tk.Label(settings_win, text="Klavye Kısayolları", font=("Helvetica", 13, "bold")).pack(pady=15)
        shortcut_frame = tk.Frame(settings_win)
        shortcut_frame.pack(pady=5)

        tk.Label(shortcut_frame, text="Kayıt Başlat/Durdur:", font=("Helvetica", 12)).grid(row=0, column=0, sticky="w")
        self.shortcut_record_var = tk.StringVar(value="F9")
        tk.Entry(shortcut_frame, textvariable=self.shortcut_record_var, width=10).grid(row=0, column=1, padx=5)

        tk.Label(shortcut_frame, text="Mute/Unmute:", font=("Helvetica", 12)).grid(row=1, column=0, sticky="w")
        self.shortcut_mute_var = tk.StringVar(value="F8")
        tk.Entry(shortcut_frame, textvariable=self.shortcut_mute_var, width=10).grid(row=1, column=1, padx=5)

        tk.Label(shortcut_frame, text="Ekran Seçimi:", font=("Helvetica", 12)).grid(row=2, column=0, sticky="w")
        self.shortcut_screen_var = tk.StringVar(value="F7")
        tk.Entry(shortcut_frame, textvariable=self.shortcut_screen_var, width=10).grid(row=2, column=1, padx=5)

        # Kayıt formatı ayarı
        tk.Label(settings_win, text="Kayıt Formatı:", font=("Helvetica", 12)).pack(pady=10)
        self.format_var = tk.StringVar(value="mp4")
        tk.OptionMenu(settings_win, self.format_var, "mp4", "avi", "mkv").pack(pady=5)

        def save_selection():
            selected_indices = app_listbox.curselection()
            self.excluded_apps = [app_listbox.get(i) for i in selected_indices]
            self.shortcut_record = self.shortcut_record_var.get()
            self.shortcut_mute = self.shortcut_mute_var.get()
            self.shortcut_screen = self.shortcut_screen_var.get()

            # Ayarları JSON olarak kaydet
            settings_data = {
                "excluded_apps": self.excluded_apps,
                "shortcut_record": self.shortcut_record,
                "shortcut_mute": self.shortcut_mute,
                "shortcut_screen": self.shortcut_screen,
                "record_duration": self.record_duration_var.get(),
                "format": self.format_var.get(),
                # "selected_monitors" removed - handled on main screen
            }
            settings_dir = os.path.join(os.path.dirname(__file__), "settings")
            os.makedirs(settings_dir, exist_ok=True)
            settings_path = os.path.join(settings_dir, "settings.json")
            with open(settings_path, "w", encoding="utf-8") as f:
                json.dump(settings_data, f, ensure_ascii=False, indent=4)

            messagebox.showinfo(
                "Ayarlar",
                f"Kayda alınmayacak uygulamalar ve tuş atamaları:\n{', '.join(self.excluded_apps)}\n\n"
                f"Kayıt Başlat/Durdur: {self.shortcut_record}\n"
                f"Mute/Unmute: {self.shortcut_mute}\n"
                f"Ekran Seçimi: {self.shortcut_screen}"
                f"\n\nKayıt süresi: {self.record_duration_var.get()} saniye\n"
                f"Kayıt Formatı: {self.format_var.get()}"
                f"\n\nAyarlar kaydedildi."
                f"\n\nNot: Kısayolları kullanabilmek için uygulamayı yeniden başlatmanız gerekebilir."
                f"\n\nAyarlar dosyası: {settings_path}"
                f"\n\nUygulama sesi hariç tutulan uygulamalar: {', '.join(self.excluded_apps) if self.excluded_apps else 'Yok'}"
                f"\n\nKayıt dizini: {self.output_directory}"
                f"\n\nKayıt alanı: Sol: {self.monitor_region['left']}, Üst: {self.monitor_region['top']}, "
                f"Genişlik: {self.monitor_region['width']}, Yükseklik: {self.monitor_region['height']}"
            )
            settings_win.destroy()

        save_button = tk.Button(settings_win, text="💾 Seçimi Kaydet", command=save_selection,
                               font=("Segoe UI", 11, "bold"), bg="#388E3C", fg="white",
                               relief=tk.FLAT, bd=0, cursor="hand2", pady=10, highlightthickness=0)
        save_button.pack(pady=15)
        self._add_button_hover_effect(save_button, "#4CAF50", "#388E3C")

        # Kısayolları ana pencerede bağla (örnek)
        def bind_shortcuts():
            self.master.bind(f"<{self.shortcut_record_var.get()}>", lambda e: self.start_recording() if not self.recording else self.stop_recording())
            self.master.bind(f"<{self.shortcut_mute_var.get()}>", lambda e: self.toggle_mute())
            self.master.bind(f"<{self.shortcut_screen_var.get()}>", lambda e: self.start_region_selection())
        settings_win.protocol("WM_DELETE_WINDOW", lambda: [bind_shortcuts(), settings_win.destroy()])

    # Mute/Unmute fonksiyonu örneği:
    def toggle_mute(self):
        # Burada mikrofonu mute/unmute yapacak kodu ekleyebilirsin
        messagebox.showinfo("Mute", "Mute/Unmute fonksiyonu tetiklendi.")

    def toggle_fullscreen(self):
        # Tam ekran/pencere modunu değiştirir
        current = self.master.attributes("-fullscreen")
        self.master.attributes("-fullscreen", not current)

    def show_advanced_help(self):
        help_window = tk.Toplevel()
        help_window.title("Ekran Kaydedici Yardım Merkezi")
        help_window.geometry("750x600")
        help_window.resizable(True, True)

        # Scrollbar
        scrollbar = tk.Scrollbar(help_window)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Yardım metni
        help_text_widget = tk.Text(help_window, wrap="word", font=("Helvetica", 12), yscrollcommand=scrollbar.set)
        help_text_widget.pack(expand=True, fill=tk.BOTH)

        help_text = """
📘 EKRAN KAYDEDİCİ YARDIM MERKEZİ

🟩 GENEL KULLANIM:
- 'Kaydı Başlat' ile ekran kaydı başlatılır.
- 'Kaydı Durdur' ile kayıt sonlandırılır.
- Ayarlar menüsünden FPS, mikrofon ve kayıt formatı gibi detaylar yapılandırılır.
- 'Kayıt Alanı Seç' ile sadece belirli bir ekran bölgesi kaydedilebilir.

🎯 SIK KARŞILAŞILAN HATALAR VE ÇÖZÜMLER:

1️⃣ Mikrofon Bulunamadı:
- Mikrofon sisteminizde tanımlı olmayabilir.
- Harici mikrofon kullanıyorsanız, takılı olduğundan emin olun.
- Ayarlar > Ses giriş cihazı listesinde "Mikrofon Bulunamadı" görünüyorsa, sadece ekran kaydedilir.

2️⃣ Kayıt Başlamıyor:
- Kayıt dizini mevcut değil veya yazma izni yok.
- Kayıt alanı geçersiz olabilir (örneğin 0x0 piksel).
- Kodlama biçimi (örneğin MP4) sistem tarafından desteklenmiyor olabilir.

3️⃣ Ses Kayıt Hataları:
- Seçili mikrofon sistemde devre dışıysa kayıt başlamaz.
- Ses aygıtı çalışırken çıkarılırsa hata alınır. Bu durumda kayıt durur.
- FFmpeg bulunamazsa video ve ses ayrı dosyalar olarak kaydedilir.

4️⃣ Önizleme Boş / Donmuş:
- Ekran kartı veya işletim sistemi MSS modülünün ekranı yakalamasını engelliyor olabilir.
- Ekran kapalı (örneğin dizüstü ekranı kapalı) ya da ekran paylaşımı aktif olabilir.

5️⃣ Video Dosyası Oluşturulamıyor:
- Belirttiğiniz kayıt dizinine yazılamıyor olabilir.
- Codec desteklenmiyor (örneğin MP4 için destekli codec yüklü değilse).

6️⃣ Video-Ses Birleştirme Hataları:
- FFmpeg sistem PATH'inde değilse birleştirme başarısız olur.
- FFmpeg indirmek için: https://ffmpeg.org/download.html
- Birleştirme başarısızsa video ve ses ayrı dosyalar olarak kalır.

📦 LOG DOSYASI:
- Uygulama olayları `screen_record_log.txt` dosyasına yazılır.
- Hata aldığınızda bu dosyayı geliştiriciye iletmeniz çözüm sürecini hızlandırır.

⚙️ AYARLAR HAKKINDA:
- 'Ayarlar' menüsünden kayıt süresi, format ve kısayol tuşlarını özelleştirebilirsiniz.
- Seçilen ayarlar `settings/settings.json` dosyasına kaydedilir.
- Kayıt dizinini değiştirmek için ana ekrandan 'Dizin Seç' butonunu kullanın.

💡 İPUÇLARI:
- Ekran kaydederken performansı artırmak için 60 FPS önerilir.
- Video ve ses otomatik olarak tek MP4 dosyasında birleştirilir (FFmpeg gereklidir).
- FFmpeg yoksa video ve ses ayrı dosyalar olarak kaydedilir.
- 'Duraklat' özelliği kayıt süresince istediğiniz zaman kullanılabilir.

📬 DESTEK VE GERİ BİLDİRİM:
E-posta: arifkerem71@gmail.com
Lütfen karşılaştığınız hataları ve ekran görüntülerini de ekleyin.

---

Teşekkür ederiz. Yazılımı daha iyi hale getirmek için geri bildirimleriniz değerlidir.
"""

        help_text_widget.insert(tk.END, help_text)
        help_text_widget.config(state=tk.DISABLED)
        scrollbar.config(command=help_text_widget.yview)

        close_button = tk.Button(help_window, text="❌ Kapat", command=help_window.destroy,
                                font=("Segoe UI", 11, "bold"), bg="#D32F2F", fg="white",
                                relief=tk.FLAT, bd=0, cursor="hand2", pady=8, highlightthickness=0)
        close_button.pack(pady=10)
        self._add_button_hover_effect(close_button, "#f44336", "#D32F2F")

if __name__ == "__main__":
    root = tk.Tk()
    app = ScreenRecorderApp(root)
    root.mainloop()
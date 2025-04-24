import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
import requests
from bs4 import BeautifulSoup
import os
import threading
import re
import urllib.parse
from urllib.parse import urlparse
from io import BytesIO
from PIL import Image, ImageTk
import json
import traceback
import webbrowser
import concurrent.futures  # 添加concurrent.futures用于线程池

# 定义应用程序颜色主题
class AppTheme:
    BG_COLOR = "#f5f5f7"  # 背景色，类似苹果的淡灰色
    PRIMARY_COLOR = "#0066cc"  # 主色调，更深的蓝色
    SECONDARY_COLOR = "#34c759"  # 绿色，用于成功消息
    TEXT_COLOR = "#1d1d1f"  # 文本主色
    LIGHT_TEXT = "#86868b"  # 浅色文本
    FRAME_BG = "#ffffff"  # 框架背景色
    CANVAS_BG = "#ffffff"  # 画布背景色
    HOVER_COLOR = "#0052a3"  # 悬停色，更深
    BORDER_COLOR = "#e6e6e6"  # 边框色

class ImageDownloader:
    def __init__(self, root):
        self.root = root
        self.root.title("URL图片批量下载器")
        
        # 先隐藏窗口，避免闪烁
        self.root.withdraw()
        
        self.root.geometry("1000x1000")  # 默认高度，确保所有功能完全可见
        self.root.minsize(800, 800)  # 最小高度，防止窗口缩小导致功能隐藏
        self.root.configure(bg=AppTheme.BG_COLOR)
        
        # 性能优化设置
        self.max_connections = 10  # 最大并发连接数
        self.connection_timeout = 15  # 连接超时（秒）
        self.max_image_size = 20 * 1024 * 1024  # 最大图片大小（20MB）
        self.chunk_size = 8192  # 文件下载分块大小
        self.memory_limit = 100 * 1024 * 1024  # 内存使用限制（100MB）
        
        # 初始化变量
        self.url_list = []  # URL列表
        self.is_downloading = False  # 是否正在下载
        self.preview_images = []  # 预览图片URL列表
        self.current_preview_index = 0  # 当前预览图片索引
        self.selected_images = set()  # 选中的图片集合
        
        # 文件名前缀变量
        self.prefix_var = tk.StringVar(value="image")  # 默认前缀为"image"
        
        # 图片缩放相关变量
        self.original_pil_img = None  # 存储原始PIL图片对象
        self.current_scale = 1.0  # 当前缩放比例
        self.base_scale = 1.0     # 基础缩放比例（适应画布的比例）
        
        # 分辨率筛选相关变量
        self.resolution_info_collected = False  # 标记是否已收集分辨率信息
        self.image_resolutions = {}  # 存储图片URL到分辨率的映射
        self.image_widths = {}      # 存储图片URL到宽度的映射
        self.image_heights = {}     # 存储图片URL到高度的映射
        self.original_preview_images = []  # 存储原始的图片URL列表（未筛选）
        
        # 设置现代化主题样式
        self.setup_styles()
        
        # 初始化变量
        self.images = []
        self.current_image_index = 0
        self.download_path = os.path.join(os.path.expanduser("~"), "Downloads")
        self.preview_image = None
        self.analyzing = False
        self.downloading = False
        self.log_window = None
        self.image_list_window = None
        
        # 创建UI
        self.setup_ui()
        self.setup_keybindings()
        
        # 存储当前预览的图片链接
        self.preview_images = []
        self.current_preview_index = 0
        
        # 存储下载状态
        self.is_downloading = False
        
        # 存储URL列表
        self.url_list = []
        
        # 调试日志
        self.debug_log = []
        
        # 分辨率信息缓存
        self.resolution_map = {}  # 完整分辨率映射 {url: "宽x高"}
        self.width_map = {}       # 宽度映射 {url: 宽}
        self.height_map = {}      # 高度映射 {url: 高}
        self.resolution_info_collected = False  # 标记是否已收集过分辨率信息
        
        # 设置应用图标
        try:
            icon_path = "icon.ico"
            if os.path.exists(icon_path):
                self.root.iconbitmap(icon_path)
                # 保存图标路径以供其他窗口使用
                self.icon_path = icon_path
                
                # 为Windows系统设置任务栏图标
                try:
                    import ctypes
                    ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("URL.ImageDownloader.1.2.0")
                except Exception as e:
                    print(f"设置Windows任务栏图标出错: {str(e)}")
        except Exception as e:
            print(f"设置图标出错: {str(e)}")
        
        # 确保所有布局计算完成
        self.root.update_idletasks()
        
        # 将主窗口居中显示
        self._center_window(self.root)
        
        # 显示窗口
        self.root.deiconify()
    
    def _center_window(self, window):
        """将窗口居中显示"""
        window.update_idletasks()
        width = window.winfo_width()
        height = window.winfo_height()
        x = (window.winfo_screenwidth() // 2) - (width // 2)
        y = (window.winfo_screenheight() // 2) - (height // 2)
        window.geometry(f'{width}x{height}+{x}+{y}')
    
    def setup_styles(self):
        """设置自定义现代化样式"""
        style = ttk.Style()
        
        # 定义主题颜色
        bg_color = "#f5f5f7"  # 背景色
        accent_color = "#0066cc"  # 主题色，调整为更深的蓝色
        accent_hover = "#0052a3"  # 悬停色，更深
        
        # 设置全局主题
        style.configure(".", 
                        font=("Microsoft YaHei UI", 9),
                        background=bg_color)
        
        # 主按钮样式
        style.configure("Primary.TButton", 
                        foreground="#ff0000",  # 改为红色文字
                        background=accent_color,
                        borderwidth=1,  # 添加边框
                        focusthickness=0,
                        padding=(10, 4))
        style.map("Primary.TButton",
                 background=[('active', accent_hover), ('pressed', accent_hover)])
        
        # 次要按钮样式
        style.configure("Secondary.TButton", 
                       foreground="#333333",  # 添加深灰色文本颜色
                       background="#ffffff",
                       borderwidth=0,
                       focusthickness=0,
                       padding=(8, 4))
        style.map("Secondary.TButton",
                 background=[('active', "#e6e6e6")])
        
        # 卡片样式
        style.configure("Card.TFrame", 
                       background="#ffffff",
                       relief="flat")
        
        # 标签框样式
        style.configure("Card.TLabelframe", 
                       background="#ffffff",
                       font=("Microsoft YaHei UI", 9, "bold"))
        style.configure("Card.TLabelframe.Label", 
                       background="#ffffff",
                       foreground=accent_color,
                       font=("Microsoft YaHei UI", 9, "bold"))
        
        # 复选框样式
        style.configure("TCheckbutton", 
                       background=bg_color)
        
        # 输入框样式
        style.configure("TEntry", 
                       padding=(5, 2))
        
    def setup_ui(self):
        """设置用户界面"""
        # 创建主框架
        self.main_frame = ttk.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 顶部菜单区域
        self.top_frame = ttk.Frame(self.main_frame)
        self.top_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 菜单按钮（左侧）
        self.menu_button = ttk.Button(self.top_frame, text="☰", width=3,
                                     style="Secondary.TButton",
                                     command=self.show_menu)
        self.menu_button.pack(side=tk.LEFT, padx=(0, 5))
        
        # 创建弹出菜单
        self.popup_menu = tk.Menu(self.root, tearoff=0)
        self.popup_menu.add_command(label="查看日志", command=self.show_log_window)
        self.popup_menu.add_command(label="图片列表", command=self.show_image_list)
        self.popup_menu.add_separator()
        self.popup_menu.add_command(label="帮助", command=self.show_help)
        self.popup_menu.add_command(label="关于", command=self.show_about)
        
        # 添加置顶选项
        self.always_on_top = tk.BooleanVar(value=False)
        self.popup_menu.add_checkbutton(label="窗口置顶", 
                                      variable=self.always_on_top,
                                      command=self._toggle_always_on_top)
        
        # 创建分隔面板 - 左侧控制区域和右侧预览区域
        self.paned_window = ttk.PanedWindow(self.main_frame, orient=tk.HORIZONTAL)
        self.paned_window.pack(fill=tk.BOTH, expand=True)
        
        # 左侧控制面板
        self.left_panel = ttk.Frame(self.paned_window)
        
        # 右侧预览面板
        self.right_panel = ttk.Frame(self.paned_window)
        
        # 添加到面板窗口
        self.paned_window.add(self.left_panel, weight=30)  # 左侧控制区占30%
        self.paned_window.add(self.right_panel, weight=70)  # 右侧预览区占70%
        
        # 在左侧面板添加控制区域
        self.setup_left_panel()
        
        # 在右侧面板添加预览区域
        self.setup_right_panel()
    
    def setup_left_panel(self):
        """设置左侧控制面板"""
        # 文件操作框架
        self.file_frame = ttk.LabelFrame(self.left_panel, text="文件操作", style="Card.TLabelframe")
        self.file_frame.pack(fill=tk.X, pady=(0, 10), padx=5)
        
        # 保存路径选择
        path_frame = ttk.Frame(self.file_frame)
        path_frame.pack(fill=tk.X, padx=5, pady=5)
        
        path_label = ttk.Label(path_frame, text="保存路径:")
        path_label.pack(side=tk.LEFT, padx=(0, 5))
        
        self.path_var = tk.StringVar(value=self.download_path)
        path_entry = ttk.Entry(path_frame, textvariable=self.path_var, width=25)
        path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))
        
        browse_button = ttk.Button(path_frame, text="浏览", style="Secondary.TButton",
                                  command=self.browse_path)
        browse_button.pack(side=tk.LEFT)
        
        # 文件名设置
        filename_frame = ttk.Frame(self.file_frame)
        filename_frame.pack(fill=tk.X, padx=5, pady=5)
        
        prefix_label = ttk.Label(filename_frame, text="文件名前缀:")
        prefix_label.pack(side=tk.LEFT, padx=(0, 5))
        
        self.prefix_var = tk.StringVar(value="image")
        prefix_entry = ttk.Entry(filename_frame, textvariable=self.prefix_var)
        prefix_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        # URL列表框架
        self.url_list_frame = ttk.LabelFrame(self.left_panel, text="URL输入区域", style="Card.TLabelframe")
        self.url_list_frame.pack(fill=tk.X, pady=(0, 10), padx=5)
        
        # URL输入提示
        url_tip_label = ttk.Label(self.url_list_frame, text="输入一个或多个URL，每行一个")
        url_tip_label.pack(anchor=tk.W, padx=5, pady=(5, 0))
        
        # 批量URL输入
        self.batch_text = tk.Text(self.url_list_frame, height=8, width=30, 
                                 font=("Microsoft YaHei UI", 9))
        self.batch_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        batch_button_frame = ttk.Frame(self.url_list_frame)
        batch_button_frame.pack(fill=tk.X, padx=5, pady=(0, 5))
        
        analyze_button = ttk.Button(batch_button_frame, text="分析URL", 
                                   style="Primary.TButton",
                                   command=self.batch_analyze)
        analyze_button.pack(side=tk.LEFT, padx=(0, 5))
        
        load_file_button = ttk.Button(batch_button_frame, text="从文件加载", 
                                     style="Secondary.TButton",
                                     command=self.load_urls_from_file)
        load_file_button.pack(side=tk.LEFT, padx=(0, 5))
        
        clear_button = ttk.Button(batch_button_frame, text="清空", 
                                 style="Secondary.TButton",
                                 command=lambda: self.batch_text.delete(1.0, tk.END))
        clear_button.pack(side=tk.LEFT)
        
        # URL列表区域
        url_list_label = ttk.Label(self.url_list_frame, text="已加载URL列表:")
        url_list_label.pack(anchor=tk.W, padx=5, pady=(10, 0))
        
        # URL文本区域和滚动条
        url_scroll = ttk.Scrollbar(self.url_list_frame)
        url_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.url_text = tk.Text(self.url_list_frame, height=6, width=30, 
                              font=("Microsoft YaHei UI", 9),
                              yscrollcommand=url_scroll.set)
        self.url_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        url_scroll.config(command=self.url_text.yview)
        
        # URL状态标签
        self.url_status = ttk.Label(self.url_list_frame, text="已加载 0 个URL")
        self.url_status.pack(anchor=tk.W, padx=5, pady=(0, 5))
        
        # 高级设置框架
        self.advanced_frame = ttk.LabelFrame(self.left_panel, text="高级设置", style="Card.TLabelframe")
        self.advanced_frame.pack(fill=tk.X, pady=(0, 10), padx=5)
        
        # 高级选项
        adv_option_frame = ttk.Frame(self.advanced_frame)
        adv_option_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.filter_small_var = tk.BooleanVar(value=True)
        filter_small_check = ttk.Checkbutton(adv_option_frame, text="过滤小图片",
                                            variable=self.filter_small_var)
        filter_small_check.pack(anchor=tk.W)
        
        self.filter_gif_var = tk.BooleanVar(value=False)
        filter_gif_check = ttk.Checkbutton(adv_option_frame, text="过滤GIF图片",
                                          variable=self.filter_gif_var)
        filter_gif_check.pack(anchor=tk.W)
        
        self.verify_images_var = tk.BooleanVar(value=True)
        verify_check = ttk.Checkbutton(adv_option_frame, text="验证图片有效性",
                                     variable=self.verify_images_var)
        verify_check.pack(anchor=tk.W)
        
        self.skip_small_images_var = tk.BooleanVar(value=True)
        skip_small_check = ttk.Checkbutton(adv_option_frame, text="跳过小图标",
                                         variable=self.skip_small_images_var)
        skip_small_check.pack(anchor=tk.W)
        
        # 分辨率筛选设置
        self.filter_resolution_var = tk.BooleanVar(value=False)
        filter_resolution_check = ttk.Checkbutton(adv_option_frame, text="按分辨率筛选",
                                                variable=self.filter_resolution_var,
                                                command=self._toggle_resolution_frame)
        filter_resolution_check.pack(anchor=tk.W)
        
        # 分辨率选择框架
        self.resolution_frame = ttk.Frame(self.advanced_frame)
        self.resolution_frame.pack(fill=tk.X, padx=5, pady=5)
        
        resolution_label = ttk.Label(self.resolution_frame, text="筛选方式:")
        resolution_label.pack(side=tk.LEFT, padx=(0, 5))
        
        # 创建筛选类型选择
        self.filter_type_var = tk.StringVar(value="分辨率")
        self.filter_type_combobox = ttk.Combobox(self.resolution_frame, textvariable=self.filter_type_var, 
                                               width=8, state="readonly")
        self.filter_type_combobox['values'] = ["分辨率", "宽度", "高度"]
        self.filter_type_combobox.pack(side=tk.LEFT, padx=(0, 5))
        self.filter_type_combobox.bind("<<ComboboxSelected>>", lambda e: self._on_filter_type_changed())
        
        # 创建分辨率下拉菜单
        self.resolution_var = tk.StringVar(value="全部")
        self.resolution_combobox = ttk.Combobox(self.resolution_frame, textvariable=self.resolution_var, 
                                               width=10, state="readonly")
        self.resolution_combobox['values'] = ["全部"]  # 初始值，后续会更新
        self.resolution_combobox.pack(side=tk.LEFT, padx=(0, 10))
        
        # 绑定下拉框选择事件
        self.resolution_combobox.bind("<<ComboboxSelected>>", lambda e: self._on_resolution_selected())
        
        # 添加应用筛选按钮
        apply_button = ttk.Button(self.resolution_frame, text="应用筛选", 
                                 style="Primary.TButton",
                                 command=self._apply_resolution_filter)
        apply_button.pack(side=tk.LEFT, padx=5)
        
        # 添加一个刷新按钮
        refresh_button = ttk.Button(self.resolution_frame, text="刷新列表", 
                                   style="Secondary.TButton",
                                   command=self._update_resolution_list)
        refresh_button.pack(side=tk.LEFT, padx=(0, 0))
        
        # 初始状态下隐藏分辨率框架
        self.resolution_frame.pack_forget()
        
        # 宽高设置
        size_frame = ttk.Frame(self.advanced_frame)
        size_frame.pack(fill=tk.X, padx=5, pady=5)
        
        min_width_label = ttk.Label(size_frame, text="最小宽度:")
        min_width_label.grid(row=0, column=0, sticky=tk.W, padx=(0, 5))
        
        self.min_width_var = tk.StringVar(value="100")
        min_width_entry = ttk.Entry(size_frame, textvariable=self.min_width_var, width=6)
        min_width_entry.grid(row=0, column=1, sticky=tk.W, padx=(0, 10))
        
        min_height_label = ttk.Label(size_frame, text="最小高度:")
        min_height_label.grid(row=0, column=2, sticky=tk.W, padx=(0, 5))
        
        self.min_height_var = tk.StringVar(value="100")
        min_height_entry = ttk.Entry(size_frame, textvariable=self.min_height_var, width=6)
        min_height_entry.grid(row=0, column=3, sticky=tk.W)
        
        # 下载设置框架
        self.download_frame = ttk.LabelFrame(self.left_panel, text="下载设置", style="Card.TLabelframe")
        self.download_frame.pack(fill=tk.X, pady=(0, 10), padx=5)
        
        # 下载按钮
        button_frame = ttk.Frame(self.download_frame)
        button_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 选择性下载复选框放在下载按钮上方，更加醒目
        self.selective_var = tk.BooleanVar(value=False)
        selective_check = ttk.Checkbutton(button_frame, text="选择性下载",
                                          variable=self.selective_var,
                                          command=self._sync_selective_checkboxes)
        selective_check.pack(side=tk.LEFT, padx=(0, 10))
        
        self.download_button = ttk.Button(button_frame, text="下载全部图片", 
                                         style="Primary.TButton",
                                         command=self.start_download)
        self.download_button.pack(side=tk.LEFT, padx=(0, 5))
        
        self.cancel_btn = ttk.Button(button_frame, text="取消", 
                                   style="Secondary.TButton",
                                   command=self.cancel_download,
                                   state=tk.DISABLED)
        self.cancel_btn.pack(side=tk.LEFT)
        
        self.download_current_button = ttk.Button(button_frame, text="下载当前图片", 
                                                style="Secondary.TButton",
                                                command=self.download_current)
        self.download_current_button.pack(side=tk.LEFT, padx=(5, 0))
    
    def setup_right_panel(self):
        """设置右侧预览面板"""
        # 预览框架
        self.preview_frame = ttk.LabelFrame(self.right_panel, text="图片预览", style="Card.TLabelframe")
        self.preview_frame.pack(fill=tk.BOTH, expand=True, padx=5)
        
        # 预览画布
        self.canvas_frame = ttk.Frame(self.preview_frame, style="Card.TFrame")
        self.canvas_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.preview_canvas = tk.Canvas(self.canvas_frame, bg="white", highlightthickness=0)
        self.preview_canvas.pack(fill=tk.BOTH, expand=True)
        
        # 绑定鼠标滚轮事件
        self.preview_canvas.bind("<MouseWheel>", self._on_mouse_wheel)  # Windows
        self.preview_canvas.bind("<Button-4>", self._on_mouse_wheel)    # Linux上滚
        self.preview_canvas.bind("<Button-5>", self._on_mouse_wheel)    # Linux下滚
        
        # 添加缩放指示标签
        self.zoom_label = ttk.Label(self.canvas_frame, text="缩放: 100%")
        self.zoom_label.place(relx=1.0, rely=0.0, anchor="ne", x=-10, y=10)
        self.zoom_label.lift()  # 确保标签在最上层
        
        # 导航控制
        nav_frame = ttk.Frame(self.preview_frame)
        nav_frame.pack(fill=tk.X, padx=5, pady=(0, 5))
        
        self.prev_button = ttk.Button(nav_frame, text="← 上一张", 
                                     style="Secondary.TButton",
                                     command=self.prev_image)
        self.prev_button.pack(side=tk.LEFT, padx=(0, 5))
        
        self.image_counter_label = ttk.Label(nav_frame, text="0/0")
        self.image_counter_label.pack(side=tk.LEFT, padx=5)
        
        self.next_button = ttk.Button(nav_frame, text="下一张 →", 
                                     style="Secondary.TButton",
                                     command=self.next_image)
        self.next_button.pack(side=tk.LEFT, padx=(5, 0))
        
        # 选择性下载复选框
        self.selected_var = tk.BooleanVar(value=True)
        self.select_check = ttk.Checkbutton(nav_frame, text="选中此图片",
                                           variable=self.selected_var,
                                           command=self.toggle_selection)
        self.select_check.pack(side=tk.RIGHT)
        
        # 跳转到指定图片框架
        goto_frame = ttk.Frame(self.preview_frame)
        goto_frame.pack(fill=tk.X, padx=5, pady=(0, 5))
        
        # 使用Grid布局以便对齐控件
        goto_frame.columnconfigure(1, weight=1)  # 让输入框占据更多空间
        
        # 图片跳转标签和输入框
        ttk.Label(goto_frame, text="图片编号:").grid(row=0, column=0, sticky=tk.W)
        
        self.goto_index = tk.StringVar()
        goto_entry = ttk.Entry(goto_frame, textvariable=self.goto_index, width=15)
        goto_entry.grid(row=0, column=1, sticky=tk.EW, padx=5)
        
        # 绑定回车键事件
        goto_entry.bind('<Return>', lambda e: self.goto_image())
        
        # 仅下载选中图片复选框 - 移除重复选项
        # self.only_checked_var = tk.BooleanVar(value=False)
        # ttk.Checkbutton(goto_frame, text="仅下载已选中的图片",
        #               variable=self.only_checked_var).grid(row=0, column=2, sticky=tk.E)
        
        # 添加跳转按钮
        ttk.Button(goto_frame, text="跳转", 
                  command=self.goto_image).grid(row=0, column=2, sticky=tk.E, padx=5)
        
        # 状态框架
        self.status_frame = ttk.Frame(self.right_panel)
        self.status_frame.pack(fill=tk.X, padx=5, pady=(5, 0))
        
        # 状态标签
        self.status_label = ttk.Label(self.status_frame, text="就绪")
        self.status_label.pack(side=tk.LEFT)
        
        # 进度条
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(self.status_frame, variable=self.progress_var,
                                           length=200, mode="determinate")
        self.progress_bar.pack(side=tk.RIGHT)
        
        # 添加下载控制区域到右侧面板底部
        download_control_frame = ttk.LabelFrame(self.right_panel, text="下载控制", style="Card.TLabelframe")
        download_control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # 创建下载控制选项
        control_options = ttk.Frame(download_control_frame)
        control_options.pack(fill=tk.X, padx=5, pady=5)
        
        # 添加选择性下载的帮助提示
        download_tip = ttk.Label(control_options, 
                               text="提示: 使用上方'选中此图片'复选框可选择需要下载的图片", 
                               font=("Microsoft YaHei UI", 8), 
                               foreground=AppTheme.LIGHT_TEXT)
        download_tip.pack(side=tk.BOTTOM, anchor=tk.W, pady=(3, 0))
        
        # 更新选择性下载选项的文本和样式
        self.select_download_var = tk.BooleanVar(value=self.selective_var.get())
        select_check = ttk.Checkbutton(control_options, 
                                    text="选择性下载（仅下载已选中的图片）",
                                    variable=self.select_download_var,
                                    command=self._sync_right_to_left)
        select_check.pack(side=tk.LEFT, padx=(0, 10))
                       
        # 添加保存当前图片按钮
        ttk.Button(control_options, text="保存当前图片", 
                  style="Secondary.TButton",
                  command=self.save_current_image).pack(side=tk.RIGHT)
    
    def show_menu(self):
        """显示菜单"""
        x = self.menu_button.winfo_rootx()
        y = self.menu_button.winfo_rooty() + self.menu_button.winfo_height()
        self.popup_menu.tk_popup(x, y)
    
    def setup_keybindings(self):
        """设置键盘快捷键"""
        # 左右箭头切换图片
        self.root.bind('<Left>', lambda e: self.prev_image())
        self.root.bind('<Right>', lambda e: self.next_image())
        
        # 回车键开始下载
        self.root.bind('<Return>', lambda e: self.start_download())
        
        # Esc键取消
        self.root.bind('<Escape>', lambda e: self.cancel_download())
        
        # F1显示帮助
        self.root.bind('<F1>', lambda e: self.show_help())
        
    def browse_path(self):
        path = filedialog.askdirectory()
        if path:
            self.path_var.set(path)
    
    def load_urls_from_file(self):
        file_path = filedialog.askopenfilename(
            title="选择URL文件",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")]
        )
        if not file_path:
            return
        
        # 开始加载前，显示加载状态
        self._update_status("正在加载URL文件...")
        self.progress_bar["value"] = 0
        self.root.update()
            
        # 使用线程加载文件，防止界面卡顿
        threading.Thread(target=self._load_urls_file_thread, args=(file_path,), daemon=True).start()
    
    def _load_urls_file_thread(self, file_path):
        """在后台线程中加载URL文件"""
        try:
            # 读取文件
            with open(file_path, "r", encoding="utf-8") as f:
                urls = [line.strip() for line in f.readlines() if line.strip()]
                
            if not urls:
                self.root.after(0, lambda: messagebox.showwarning("警告", "文件中未找到URL"))
                self.root.after(0, lambda: self._update_status("就绪"))
                return
            
            # 更新UI需要在主线程中进行
            self.root.after(0, lambda: self._update_loaded_urls(urls))
            
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("错误", f"读取文件时出错: {str(e)}"))
            self.root.after(0, lambda: self._update_status("就绪"))
    
    def _update_loaded_urls(self, urls):
        """更新加载的URL到UI（在主线程中调用）"""
        self.url_list = urls
        
        # 显示URLs到文本区域
        self.url_text.delete(1.0, tk.END)
        self.url_text.tag_configure("current", background="#e0e0e0")  # 定义高亮样式
        
        # 使用批处理更新文本，减少UI更新次数
        url_text = ""
        for i, url in enumerate(urls):
            url_text += f"{i+1}. {url}\n"
        
        self.url_text.insert(tk.END, url_text)
        
        # 更新URL状态
        self.url_status.config(text=f"已加载 {len(urls)} 个URL")
        
        # 将第一个URL显示在状态栏，提示用户可以开始分析
        self._update_status(f"已加载 {len(urls)} 个URL，可以开始分析")
        
        # 显示成功消息
        messagebox.showinfo("成功", f"已加载 {len(urls)} 个URL")
    
    def analyze_all_urls(self):
        if not self.url_list:
            messagebox.showwarning("警告", "没有可分析的URL")
            return
            
        self.status_label.config(text="批量分析中...")
        self.progress_bar["value"] = 0
        self.root.update()
        
        # 重置预览图片列表
        self.preview_images = []
        
        # 在新线程中处理，避免UI冻结
        self.is_downloading = True  # 重用此标志用于取消操作
        self.cancel_btn.config(state=tk.NORMAL)
        threading.Thread(target=self._analyze_all_urls_thread, daemon=True).start()
        
    def _analyze_all_urls_thread(self):
        total_urls = len(self.url_list)
        all_img_urls = []
        
        # 创建进度跟踪变量
        self.analyzed_count = 0
        self.analyzed_urls_lock = threading.Lock()
        
        # 创建一个线程池
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            # 保存所有future对象
            future_to_url = {executor.submit(self._analyze_single_url_parallel, url): url for url in self.url_list}
            
            # 更新进度和状态的定时器
            def update_progress():
                if not self.is_downloading:
                    return
                    
                with self.analyzed_urls_lock:
                    progress = (self.analyzed_count / total_urls) * 100
                    self._update_progress(progress, self.analyzed_count, total_urls, prefix="分析URL")
                
                # 每500毫秒更新一次进度
                if self.is_downloading:
                    self.root.after(500, update_progress)
                    
            # 启动进度更新定时器
            update_progress()
            
            # 收集结果
            for future in concurrent.futures.as_completed(future_to_url):
                if not self.is_downloading:  # 如果取消了分析
                    break
                    
                url = future_to_url[future]
                try:
                    img_urls = future.result()
                    if img_urls:
                        all_img_urls.extend(img_urls)
                        
                    # 更新已分析URL数量
                    with self.analyzed_urls_lock:
                        self.analyzed_count += 1
                        
                except Exception as e:
                    self.root.after(0, lambda url=url, e=str(e): 
                                  self._update_status(f"分析 {url} 时出错: {e}"))
                    
                    # 更新已分析URL数量
                    with self.analyzed_urls_lock:
                        self.analyzed_count += 1
        
        # 清除高亮
        self.root.after(0, self._clear_url_highlight)
        
        # 验证图片
        if self.verify_images_var.get() and all_img_urls:
            self.root.after(0, lambda: self._update_status("验证图片中..."))
            all_img_urls = self._verify_images(all_img_urls)
            
        # 更新UI必须在主线程进行
        self.root.after(0, lambda: self._update_preview(all_img_urls))
        
        # 重置下载状态
        self.is_downloading = False
        self.root.after(0, lambda: self.cancel_btn.config(state=tk.DISABLED))
    
    def _analyze_single_url_parallel(self, url):
        """并行分析单个URL的函数（供线程池使用）"""
        try:
            # 高亮当前处理的URL
            self.root.after(0, lambda i=self.url_list.index(url), url=url: 
                           self._highlight_current_url(i, url))
            
            # 显示当前处理的URL
            self.root.after(0, lambda url=url: self._update_status(f"分析: {url}"))
            
            # 检查URL是否直接指向图片
            if self._is_direct_image_url(url):
                return [url]
            
            # 提取网页中的图片
            img_urls = self._extract_images_from_url(url)
            
            # 记录提取结果
            count = len(img_urls)
            self.root.after(0, lambda url=url, count=count: 
                           self._update_status(f"从 {url} 提取到 {count} 张图片"))
            
            return img_urls
                
        except Exception as e:
            self.root.after(0, lambda url=url, e=str(e): 
                           self._update_status(f"分析 {url} 时出错: {e}"))
            return []
    
    def _verify_images(self, img_urls):
        """验证图片有效性并过滤尺寸"""
        valid_urls = []
        total = len(img_urls)
        
        # 图片分辨率映射字典，用于保存分辨率信息
        self.resolution_map = {}
        self.width_map = {}
        self.height_map = {}
        
        # 获取分辨率筛选设置
        filter_by_resolution = self.filter_resolution_var.get()
        selected_resolution = self.resolution_var.get()
        
        # 尝试获取最小尺寸设置
        try:
            min_width = int(self.min_width_var.get())
            min_height = int(self.min_height_var.get())
        except ValueError:
            min_width = 0
            min_height = 0
        
        skip_small = self.skip_small_images_var.get()
        
        # 创建线程安全的计数器和结果列表
        self.verified_count = 0
        self.verified_lock = threading.Lock()
        thread_safe_valid_urls = []
        thread_safe_resolution_map = {}
        thread_safe_width_map = {}
        thread_safe_height_map = {}
        
        # 定义验证单个图片的函数
        def verify_single_image(url, index):
            if not self.is_downloading:
                return None
                
            try:
                # 获取图片并检查尺寸
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                }
                response = requests.get(url, headers=headers, timeout=10, stream=True)
                
                # 只读取前几个字节来验证是否为有效图片
                content_type = response.headers.get('Content-Type', '')
                
                # 如果内容类型不是图片，跳过
                if not content_type.startswith('image/'):
                    return None
                
                # 获取完整图片并检查尺寸
                img_data = response.content
                image = Image.open(BytesIO(img_data))
                width, height = image.size
                
                # 记录图片分辨率信息
                resolution_str = f"{width}x{height}"
                
                # 存储分辨率信息到线程安全的字典
                with self.verified_lock:
                    thread_safe_resolution_map[url] = resolution_str
                    thread_safe_width_map[url] = width
                    thread_safe_height_map[url] = height
                
                # 跳过小图标
                if skip_small and (width < 50 or height < 50):
                    return None
                    
                # 检查最小尺寸
                if (min_width > 0 and width < min_width) or (min_height > 0 and height < min_height):
                    return None
                
                # 如果开启了分辨率筛选且选择了特定分辨率
                if filter_by_resolution and selected_resolution != "全部":
                    if resolution_str != selected_resolution:
                        return None
                
                # 图片验证通过，返回URL
                return url
                
            except Exception:
                # 如果验证失败，跳过这个URL
                return None
            finally:
                # 更新验证进度
                with self.verified_lock:
                    self.verified_count += 1
        
        # 更新进度的定时器函数
        def update_verify_progress():
            if not self.is_downloading:
                return
                
            with self.verified_lock:
                progress = (self.verified_count / total) * 100
                self._update_progress(progress, self.verified_count, total, prefix="验证图片")
            
            # 每500毫秒更新一次进度
            if self.is_downloading:
                self.root.after(500, update_verify_progress)
        
        # 开始进度更新
        update_verify_progress()
        
        # 使用线程池并行验证图片
        with concurrent.futures.ThreadPoolExecutor(max_workers=10) as executor:
            # 提交所有验证任务到线程池
            future_to_url = {executor.submit(verify_single_image, url, i): url 
                           for i, url in enumerate(img_urls)}
            
            # 收集验证结果
            for future in concurrent.futures.as_completed(future_to_url):
                if not self.is_downloading:
                    break
                    
                result = future.result()
                if result:
                    thread_safe_valid_urls.append(result)
        
        # 更新全局分辨率映射
        self.resolution_map = thread_safe_resolution_map
        self.width_map = thread_safe_width_map
        self.height_map = thread_safe_height_map
        
        return thread_safe_valid_urls
    
    def _extract_images_from_url(self, url):
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,image/apng,*/*;q=0.8',
            'Accept-Language': 'zh-CN,zh;q=0.9,en;q=0.8',
            'Referer': url
        }
        
        try:
            # 设置更长的超时时间，有些网站加载较慢
            response = requests.get(url, headers=headers, timeout=self.connection_timeout, stream=True)
            response.raise_for_status()
            
            # 检查内容大小
            content_length = int(response.headers.get('Content-Length', 0))
            if content_length > self.memory_limit:
                # 内容太大，只读取部分
                html_content = response.text[:self.memory_limit]
                self.root.after(0, lambda: self._update_status(f"警告: {url} 内容过大，只分析部分内容"))
            else:
                # 尝试检测网页编码
                if response.encoding == 'ISO-8859-1':
                    # 可能是错误检测，尝试使用apparent_encoding
                    response.encoding = response.apparent_encoding
                
                html_content = response.text
            
            # 使用更快速的HTML解析方法
            soup = BeautifulSoup(html_content, 'html.parser')
            base_url = '{uri.scheme}://{uri.netloc}'.format(uri=urlparse(url))
            
            # 查找所有图片链接
            img_urls = set()  # 使用集合避免重复
            
            # 1. 从常规img标签获取图片
            for img in soup.find_all('img'):
                # 检查多种可能的属性
                for attr in ['src', 'data-src', 'data-original', 'data-lazyload', 'data-lazy', 
                             'data-original-src', 'data-source', 'data-srcset', 'srcset',
                             'data-url', 'data-img', 'data-bg-src', 'data-image']:
                    src = img.get(attr)
                    if src:
                        # 处理srcset属性（包含多个URL）
                        if attr == 'srcset':
                            # 提取srcset中的所有URL
                            srcset_urls = re.findall(r'([^\s,]+)(?:\s+\d+[wx][^,]*)?(?:,|$)', src)
                            for srcset_url in srcset_urls:
                                self._add_url_to_set(img_urls, srcset_url, base_url, url)
                        else:
                            self._add_url_to_set(img_urls, src, base_url, url)
            
            # 2. 从a标签中寻找图片链接
            for a in soup.find_all('a'):
                href = a.get('href')
                if href and self._is_image_url(href):
                    self._add_url_to_set(img_urls, href, base_url, url)
                    
            # 3. 从style属性中提取背景图片
            for tag in soup.find_all(lambda tag: tag.has_attr('style')):
                style = tag['style']
                urls = re.findall(r'background(?:-image)?\s*:\s*url\s*\(\s*[\'"]?([^\'")]+)[\'"]?\s*\)', style)
                for bg_url in urls:
                    self._add_url_to_set(img_urls, bg_url, base_url, url)
            
            # 4. 从所有标签的data-background属性中查找
            for tag in soup.find_all():
                for attr in ['data-background', 'data-bg', 'data-original', 'data-src', 'data-url', 'data-img']:
                    bg_url = tag.get(attr)
                    if bg_url:
                        self._add_url_to_set(img_urls, bg_url, base_url, url)
            
            # 5. 从CSS文件中提取背景图片
            for link in soup.find_all('link', rel='stylesheet'):
                css_url = link.get('href')
                if css_url:
                    try:
                        css_full_url = urllib.parse.urljoin(url, css_url)
                        css_response = requests.get(css_full_url, headers=headers, timeout=10)
                        css_text = css_response.text
                        bg_urls = re.findall(r'background(?:-image)?\s*:\s*url\s*\(\s*[\'"]?([^\'")]+)[\'"]?\s*\)', css_text)
                        for bg_url in bg_urls:
                            self._add_url_to_set(img_urls, bg_url, base_url, css_full_url)
                    except Exception:
                        # 忽略CSS获取错误
                        pass
            
            # 6. 从meta标签中获取图片
            for meta in soup.find_all('meta'):
                if meta.get('property') in ['og:image', 'twitter:image', 'og:image:secure_url']:
                    content = meta.get('content')
                    if content:
                        self._add_url_to_set(img_urls, content, base_url, url)
            
            # 7. 从JSON数据中提取图片URL (针对一些使用JavaScript加载图片的网站)
            # 在script标签中查找可能的JSON数据
            for script in soup.find_all('script'):
                if script.string:
                    # 尝试在JavaScript中查找图片URL
                    urls = re.findall(r'(?:src|url|image|img|source)(?:["\']|\s*:\s*["\']\s*)([^"\']+\.(?:jpg|jpeg|png|gif|webp|bmp|svg))', script.string, re.IGNORECASE)
                    for img_url in urls:
                        self._add_url_to_set(img_urls, img_url, base_url, url)
                    
                    # 尝试查找JSON数据
                    json_objects = re.findall(r'({[^{]*"(?:url|src|image|img|source)"[^}]*})', script.string)
                    for json_obj in json_objects:
                        try:
                            # 提取JSON字符串并修复常见的JavaScript格式问题
                            fixed_json = re.sub(r'([{,])\s*(\w+):', r'\1"\2":', json_obj)
                            data = json.loads(fixed_json)
                            for key in ['url', 'src', 'image', 'img', 'source']:
                                if key in data and isinstance(data[key], str):
                                    self._add_url_to_set(img_urls, data[key], base_url, url)
                        except (json.JSONDecodeError, ValueError):
                            pass
            
            # 将集合转为列表
            img_urls_list = list(img_urls)
            
            if not img_urls_list:
                # 如果找不到图片，可能是因为网页使用了特殊的加载方式
                # 尝试更深入的搜索
                self._deep_search_images(soup, img_urls, base_url, url)
                img_urls_list = list(img_urls)
            
            # 在状态栏显示找到的图片数量
            self.root.after(0, lambda msg=f"从 {url} 找到 {len(img_urls_list)} 张图片": self._update_status(msg))
            
            return img_urls_list
            
        except Exception as e:
            self.root.after(0, lambda msg=f"处理URL时出错: {str(e)}": self._update_status(msg))
            return []
    
    def _deep_search_images(self, soup, img_urls, base_url, page_url):
        """更深入地搜索图片，针对特殊网站"""
        try:
            # 1. 查找所有可能包含图片URL的属性
            for tag in soup.find_all():
                for attr in tag.attrs:
                    if isinstance(tag[attr], str):
                        attr_value = tag[attr].lower()
                        # 检查属性值是否包含图片扩展名
                        if re.search(r'\.(jpg|jpeg|png|gif|webp|bmp|svg)(\?|$|#)', attr_value):
                            self._add_url_to_set(img_urls, tag[attr], base_url, page_url)
            
            # 2. 查找HTML中的所有URL模式
            html_text = str(soup)
            # 匹配各种URL格式的图片
            urls = re.findall(r'(?:https?:)?//[^/\s]+/\S+?\.(?:jpg|jpeg|png|gif|webp|bmp|svg)(?:\?[^\'"\s]*)?(?=[\'"\s])', html_text)
            for url in urls:
                self._add_url_to_set(img_urls, url, base_url, page_url)
                
        except Exception:
            pass
            
    def _add_url_to_set(self, url_set, src, base_url, page_url, check_is_image=True):
        """将URL添加到集合中，同时处理相对路径"""
        if not src:
            return
            
        # 忽略data URIs (base64编码的图片)，除非特别要求
        if src.startswith('data:'):
            return
            
        # 忽略javascript:和about:协议
        if src.startswith(('javascript:', 'about:')):
            return
            
        # 修复URL中的特殊字符
        src = src.replace(' ', '%20').replace('\\', '/')
            
        # 处理相对URL
        if not src.startswith(('http://', 'https://')):
            if src.startswith('//'):  # 协议相对URL
                parsed_url = urlparse(page_url)
                src = f"{parsed_url.scheme}:{src}"
            elif src.startswith('/'):  # 绝对路径
                src = base_url + src
            else:  # 相对路径
                src = urllib.parse.urljoin(page_url, src)
        
        # 检查是否为图片URL
        if check_is_image and not self._is_image_url(src):
            return
            
        url_set.add(src)
    
    def _is_image_url(self, url):
        """检查URL是否指向图片文件"""
        # 图片文件扩展名
        image_extensions = ['.jpg', '.jpeg', '.png', '.gif', '.bmp', '.webp', '.svg', '.ico', '.tiff']
        parsed_url = urlparse(url)
        path = parsed_url.path.lower()
        
        # 检查是否以图片扩展名结尾
        if any(path.endswith(ext) for ext in image_extensions):
            return True
            
        # 检查URL是否包含图片相关关键词
        if 'image' in path or 'img' in path or 'photo' in path or 'picture' in path:
            return True
            
        # 检查URL参数是否包含图片扩展名（如?file=image.jpg）
        query = parsed_url.query.lower()
        if any(ext[1:] in query for ext in image_extensions):  # ext[1:] 移除点号
            return True
            
        return False
    
    def _analyze_url_thread(self, url):
        try:
            self.root.after(0, lambda: self._update_status(f"正在分析: {url}"))
            print(f"开始分析URL: {url}")  # 调试信息
            
            # 检查URL是否直接指向图片文件
            if self._is_direct_image_url(url):
                print(f"检测到直接图片URL: {url}")  # 调试信息
                self.root.after(0, lambda: self._update_preview([url]))
                return
                
            img_urls = self._extract_images_from_url(url)
            print(f"从URL提取到 {len(img_urls)} 张图片")  # 调试信息
            
            # 验证图片
            if self.verify_images_var.get() and img_urls:
                self.root.after(0, lambda: self._update_status("验证图片中..."))
                print("开始验证图片...")  # 调试信息
                img_urls = self._verify_images(img_urls)
                print(f"验证后剩余 {len(img_urls)} 张有效图片")  # 调试信息
            
            # 更新UI必须在主线程进行
            self.root.after(0, lambda: self._update_preview(img_urls))
        except Exception as e:
            print(f"分析URL出错: {str(e)}")  # 调试信息
            traceback_info = traceback.format_exc()
            print(f"详细错误信息: {traceback_info}")  # 打印完整堆栈
            self.root.after(0, lambda: self._handle_error(f"分析URL时出错: {str(e)}"))
    
    def _is_direct_image_url(self, url):
        """检查URL是否直接指向图片文件"""
        try:
            # 首先检查URL格式
            if self._is_image_url(url):
                # 然后发送HEAD请求验证
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                }
                response = requests.head(url, headers=headers, timeout=10)
                content_type = response.headers.get('Content-Type', '')
                
                # 验证内容类型是否为图片
                return content_type.startswith('image/')
        except Exception:
            pass
            
        return False
    
    def _update_preview(self, img_urls):
        """更新预览区域显示新的图片列表"""
        print(f"更新预览，收到 {len(img_urls)} 张图片")  # 调试信息
        
        self.preview_images = img_urls
        self.current_preview_index = 0
        
        if not img_urls:
            self.status_label.config(text="未找到图片")
            self.image_counter_label.config(text="0/0")
            # 清空画布
            self.preview_canvas.delete("all")
            
            # 获取画布实际尺寸
            self.root.update_idletasks()
            canvas_width = self.preview_canvas.winfo_width()
            canvas_height = self.preview_canvas.winfo_height()
            
            if canvas_width <= 1:
                canvas_width = 500
                canvas_height = 400
                
            self.preview_canvas.create_text(
                canvas_width // 2,
                canvas_height // 2,
                text="未找到图片",
                fill="gray",
                font=("Arial", 16)
            )
            print("未找到图片，已更新UI")  # 调试信息
            return
            
        self.status_label.config(text=f"找到 {len(img_urls)} 张图片")
        
        print(f"预览图片列表更新，共 {len(img_urls)} 张图片")  # 调试信息
        if img_urls:
            print(f"第一张图片URL: {img_urls[0]}")  # 调试第一张图片
        
        # 确保画布准备好
        self.root.update_idletasks()
        
        # 加载第一张图片预览
        self.load_preview_image()
        
        # 标记分辨率信息为未收集
        self.resolution_info_collected = False
        
        # 如果有图片，自动更新分辨率列表
        if len(img_urls) > 0:
            # 使用延迟调用，确保UI更新完成后再执行分辨率收集
            self.root.after(1000, self._update_resolution_list)
    
    def load_preview_image(self):
        """加载当前索引的预览图片"""
        try:
            if not self.preview_images or len(self.preview_images) == 0:
                print("没有预览图片可加载")
                return
                
            if self.current_preview_index < 0 or self.current_preview_index >= len(self.preview_images):
                print(f"图片索引超出范围: {self.current_preview_index}, 总数: {len(self.preview_images)}")
                return
                
            # 获取画布实际尺寸
            self.root.update_idletasks()
            canvas_width = self.preview_canvas.winfo_width()
            canvas_height = self.preview_canvas.winfo_height()
            
            print(f"画布尺寸: {canvas_width} x {canvas_height}")  # 调试信息
            
            # 如果画布尺寸还未确定，使用默认尺寸
            if canvas_width <= 1 or canvas_height <= 1:
                canvas_width = 500
                canvas_height = 400
                print(f"使用默认画布尺寸: {canvas_width} x {canvas_height}")  # 调试信息
            
            # 清空画布并显示加载信息
            self.preview_canvas.delete("all")
            loading_text_id = self.preview_canvas.create_text(
                canvas_width // 2,
                canvas_height // 2,
                text="加载图片中...",
                fill="black",
                font=("Arial", 16)
            )
            self.root.update()  # 强制更新UI，确保加载文本立即显示
            
            # 更新预览标签
            self.image_counter_label.config(text=f"{self.current_preview_index + 1}/{len(self.preview_images)}")
            
            # 同时在状态栏也显示预览信息
            self._update_status(f"预览图片: {self.current_preview_index + 1}/{len(self.preview_images)}")
            
            # 获取当前索引的图片URL
            img_url = self.preview_images[self.current_preview_index]
            print(f"加载预览图片: {img_url}")  # 调试信息
            
            try:
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/58.0.3029.110 Safari/537.3'
                }
                
                # 添加错误处理和超时
                try:
                    response = requests.get(img_url, headers=headers, timeout=15, stream=True)
                    response.raise_for_status()  # 检查HTTP错误
                except requests.exceptions.RequestException as e:
                    print(f"请求图片出错: {str(e)}")  # 调试信息
                    self.preview_canvas.delete("all")
                    self.preview_canvas.create_text(
                        canvas_width // 2,
                        canvas_height // 2,
                        text=f"无法加载图片:\n{str(e)}",
                        fill="red",
                        font=("Arial", 14),
                        justify="center"
                    )
                    return
                
                # 使用BytesIO读取图片
                img_data = BytesIO(response.content)
                try:
                    pil_img = Image.open(img_data)
                    print(f"成功加载原始图片，尺寸: {pil_img.width} x {pil_img.height}")  # 调试信息
                    
                    # 保存原始图片对象以供缩放使用
                    self.original_pil_img = pil_img
                    self.current_scale = 1.0  # 重置缩放比例
                    
                except Exception as e:
                    print(f"无法解析图片数据: {str(e)}")
                    self.preview_canvas.delete("all")
                    self.preview_canvas.create_text(
                        canvas_width // 2,
                        canvas_height // 2,
                        text=f"无法解析图片数据:\n{str(e)}",
                        fill="red",
                        font=("Arial", 14),
                        justify="center"
                    )
                    return
                
                # 计算缩放比例以适应画布
                width_ratio = canvas_width / pil_img.width
                height_ratio = canvas_height / pil_img.height
                scale_ratio = min(width_ratio, height_ratio) * 0.9  # 留出一些边距
                
                # 对于非常大的图片，不要缩小太多
                if pil_img.width > canvas_width * 2 or pil_img.height > canvas_height * 2:
                    # 如果图片非常大，我们保持一定的最小尺寸，用户可以通过滚动查看
                    scale_ratio = max(scale_ratio, 0.5)  # 确保图片不会缩小太多
                
                # 保存基础缩放比例
                self.base_scale = scale_ratio
                
                # 计算缩放后的尺寸
                new_width = int(pil_img.width * scale_ratio)
                new_height = int(pil_img.height * scale_ratio)
                
                print(f"缩放比例: {scale_ratio}, 新尺寸: {new_width} x {new_height}")  # 调试信息
                
                if new_width <= 0 or new_height <= 0:
                    raise ValueError(f"计算的图片尺寸无效: {new_width}x{new_height}")
                    
                # 缩放图片
                pil_img = pil_img.resize((new_width, new_height), Image.LANCZOS)
                
                # 更新缩放指示器
                zoom_percentage = int(self.current_scale * 100)
                self.zoom_label.config(text=f"缩放: {zoom_percentage}%")
                
                # 转换为PhotoImage
                try:
                    img = ImageTk.PhotoImage(pil_img)
                except Exception as e:
                    print(f"创建PhotoImage失败: {str(e)}")
                    self.preview_canvas.delete("all")
                    self.preview_canvas.create_text(
                        canvas_width // 2,
                        canvas_height // 2,
                        text=f"无法创建图片预览:\n{str(e)}",
                        fill="red",
                        font=("Arial", 14),
                        justify="center"
                    )
                    return
                
                # 保存引用以防止垃圾回收
                self._photo_image = img
                
                # 计算居中位置
                x_center = canvas_width // 2
                y_center = canvas_height // 2
                
                # 清空画布并添加图像
                self.preview_canvas.delete("all")
                image_id = self.preview_canvas.create_image(
                    x_center, y_center,
                    image=img,
                    anchor="center"  # 使用中心点作为锚点
                )
                
                # 调整画布的滚动区域以适应图片
                self.preview_canvas.config(scrollregion=self.preview_canvas.bbox("all"))
                
                print(f"成功显示预览图片，ID: {image_id}")  # 调试信息
                
            except Exception as e:
                print(f"加载图片过程中出错: {str(e)}")  # 调试信息
                traceback_info = traceback.format_exc()
                print(f"详细错误信息: {traceback_info}")  # 打印完整堆栈
                self.preview_canvas.delete("all")
                self.preview_canvas.create_text(
                    canvas_width // 2,
                    canvas_height // 2,
                    text=f"加载图片失败:\n{str(e)}",
                    fill="red",
                    font=("Arial", 14),
                    justify="center"
                )
                
        except Exception as e:
            print(f"预览图片加载函数发生错误: {str(e)}")  # 调试信息
            traceback_info = traceback.format_exc()
            print(f"详细错误信息: {traceback_info}")  # 打印完整堆栈
            self.preview_canvas.delete("all")
            self.preview_canvas.create_text(
                canvas_width // 2 if 'canvas_width' in locals() else 200,
                canvas_height // 2 if 'canvas_height' in locals() else 100,
                text=f"发生错误:\n{str(e)}",
                fill="red",
                font=("Arial", 14),
                justify="center"
            )
    
    def prev_image(self):
        if not self.preview_images or len(self.preview_images) <= 1:
            return
            
        if self.current_preview_index > 0:
            self.current_preview_index -= 1
            self.load_preview_image()
            print(f"切换到前一张图片，当前索引: {self.current_preview_index}")  # 调试信息
    
    def next_image(self):
        if not self.preview_images or len(self.preview_images) <= 1:
            return
            
        if self.current_preview_index < len(self.preview_images) - 1:
            self.current_preview_index += 1
            self.load_preview_image()
            print(f"切换到后一张图片，当前索引: {self.current_preview_index}")  # 调试信息
    
    def start_download(self):
        # 检查是否有URL列表，如果有但还没分析过，先分析
        if self.url_list and not self.preview_images:
            self.analyze_all_urls()
            return
            
        if not self.preview_images:
            messagebox.showwarning("警告", "没有可下载的图片")
            return
            
        save_path = self.path_var.get().strip()
        if not save_path:
            messagebox.showwarning("警告", "请选择保存路径")
            return
            
        if not os.path.exists(save_path):
            try:
                os.makedirs(save_path)
            except Exception as e:
                messagebox.showerror("错误", f"创建保存目录失败: {str(e)}")
                return
        
        # 如果启用了选择性下载，只下载当前选中的图片
        if self.selective_var.get():
            if self.current_preview_index < 0 or self.current_preview_index >= len(self.preview_images):
                messagebox.showwarning("警告", "没有选中的图片")
                return
                
            if not self.selected_var.get():
                messagebox.showwarning("警告", "当前图片未被选中")
                return
                
            # 下载当前选中的图片
            self.download_current()
            return
        
        # 常规模式：下载所有图片
        self.is_downloading = True
        self.download_button.config(state=tk.DISABLED)
        self.cancel_btn.config(state=tk.NORMAL)
        
        # 开始下载线程
        threading.Thread(target=self._download_thread, args=(save_path,), daemon=True).start()
    
    def _download_thread(self, save_path):
        total = len(self.preview_images)
        success_count = 0
        
        # 获取文件名前缀
        prefix = self.prefix_var.get().strip()
        if not prefix:
            prefix = "image"  # 如果前缀为空，使用默认值
        
        for i, img_url in enumerate(self.preview_images):
            if not self.is_downloading:
                break
                
            try:
                # 更新进度
                progress = (i / total) * 100
                self.root.after(0, lambda p=progress, i=i, t=total: self._update_progress(p, i, t))
                
                # 下载图片
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                    'Referer': img_url
                }
                response = requests.get(img_url, headers=headers, timeout=15)
                response.raise_for_status()
                
                # 从URL或Content-Type获取文件扩展名
                filename = os.path.basename(urlparse(img_url).path)
                if filename and '.' in filename:
                    # 从URL提取文件名和扩展名
                    base_name, ext = os.path.splitext(filename)
                    # 确保扩展名是小写字母
                    ext = ext.lower()
                    # 在原文件名前添加前缀
                    filename = f"{prefix}_{base_name}{ext}"
                else:
                    # 从Content-Type确定文件扩展名
                    content_type = response.headers.get('Content-Type', '')
                    if 'jpeg' in content_type or 'jpg' in content_type:
                        ext = '.jpg'
                    elif 'png' in content_type:
                        ext = '.png'
                    elif 'gif' in content_type:
                        ext = '.gif'
                    elif 'webp' in content_type:
                        ext = '.webp'
                    elif 'bmp' in content_type:
                        ext = '.bmp'
                    elif 'svg' in content_type:
                        ext = '.svg'
                    else:
                        ext = '.jpg'  # 默认扩展名
                
                    # 使用前缀和序号生成文件名
                    filename = f"{prefix}_{i+1}{ext}"
                
                # 确保文件名合法
                filename = re.sub(r'[\\/*?:"<>|]', "_", filename)
                
                # 保存文件
                save_file_path = os.path.join(save_path, filename)
                
                # 检查是否存在同名文件
                if os.path.exists(save_file_path):
                    base_name, ext = os.path.splitext(filename)
                    counter = 1
                    while os.path.exists(os.path.join(save_path, f"{base_name}_{counter}{ext}")):
                        counter += 1
                    save_file_path = os.path.join(save_path, f"{base_name}_{counter}{ext}")
                
                with open(save_file_path, 'wb') as f:
                    f.write(response.content)
                
                success_count += 1
                
            except Exception as e:
                self.root.after(0, lambda msg=f"下载失败 ({i+1}/{total}): {str(e)}": self._update_status(msg))
        
        # 完成下载
        self.root.after(0, lambda sc=success_count, t=total: self._download_completed(sc, t))
    
    def _update_progress(self, progress, current, total, prefix="下载中"):
        self.progress_bar["value"] = progress
        self.status_label.config(text=f"{prefix} ({current+1}/{total})")
    
    def _update_status(self, message):
        """更新状态栏并记录日志"""
        self.status_label.config(text=message)
        # 保存日志
        self.debug_log.append(message)
        # 如果日志过长，保留最近的100条
        if len(self.debug_log) > 100:
            self.debug_log = self.debug_log[-100:]
        
        # 更新日志窗口，如果存在
        if hasattr(self, 'log_text') and self.log_text:
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, message + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
            
    def _download_completed(self, success_count, total):
        self.progress_bar["value"] = 100
        self.status_label.config(text=f"下载完成，成功: {success_count}/{total}")
        self.is_downloading = False
        self.download_button.config(state=tk.NORMAL)
        self.cancel_btn.config(state=tk.DISABLED)
    
    def cancel_download(self):
        self.is_downloading = False
        self.status_label.config(text="已取消下载")
    
    def _handle_error(self, message):
        self.status_label.config(text=message)
        messagebox.showerror("错误", message)

    def show_log_window(self):
        """显示日志窗口"""
        log_window = tk.Toplevel(self.root)
        log_window.title("调试日志")
        
        # 先隐藏窗口，避免闪烁
        log_window.withdraw()
        
        # 设置图标
        try:
            if hasattr(self, 'icon_path') and os.path.exists(self.icon_path):
                log_window.iconbitmap(self.icon_path)
        except Exception as e:
            print(f"设置日志窗口图标出错: {str(e)}")
        
        log_window.geometry("600x400")
        
        # 创建文本区域
        frame = ttk.Frame(log_window, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建带滚动条的文本区域
        scrollbar = ttk.Scrollbar(frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.log_text = tk.Text(frame, wrap=tk.WORD, yscrollcommand=scrollbar.set)
        self.log_text.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=self.log_text.yview)
        
        # 填充日志内容
        self.log_text.insert(tk.END, "\n".join(self.debug_log))
        self.log_text.config(state=tk.DISABLED)
        
        # 底部按钮
        button_frame = ttk.Frame(log_window, padding="10")
        button_frame.pack(fill=tk.X)
        
        ttk.Button(button_frame, text="清除日志", 
                  command=lambda: self.clear_log(self.log_text)).pack(side=tk.LEFT)
                  
        ttk.Button(button_frame, text="保存日志", 
                  command=self.save_log).pack(side=tk.LEFT, padx=(5, 0))
                  
        ttk.Button(button_frame, text="关闭", 
                  command=log_window.destroy).pack(side=tk.RIGHT)
        
        # 确保所有布局计算完成
        log_window.update_idletasks()
        
        # 居中显示
        self._center_window(log_window)
        
        # 显示窗口
        log_window.deiconify()
    
    def clear_log(self, text_widget):
        """清除日志"""
        self.debug_log = []
    def clear_log(self, text_widget):
        """清除日志"""
        self.debug_log = []
        text_widget.config(state=tk.NORMAL)
        text_widget.delete(1.0, tk.END)
        text_widget.config(state=tk.DISABLED)
        
    def save_log(self):
        """保存日志到文件"""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")],
            title="保存日志"
        )
        if file_path:
            try:
                with open(file_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(self.debug_log))
                messagebox.showinfo("成功", f"日志已保存到 {file_path}")
            except Exception as e:
                messagebox.showerror("错误", f"保存日志时出错: {str(e)}")

    def show_help(self):
        """显示帮助信息"""
        help_window = tk.Toplevel(self.root)
        help_window.title("使用帮助")
        
        # 先隐藏窗口，避免闪烁
        help_window.withdraw()
        
        # 设置图标
        try:
            if hasattr(self, 'icon_path') and os.path.exists(self.icon_path):
                help_window.iconbitmap(self.icon_path)
        except Exception as e:
            print(f"设置帮助窗口图标出错: {str(e)}")
        
        help_window.geometry("600x500")
        
        frame = ttk.Frame(help_window, padding="20")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建带滚动条的文本区域
        scrollbar = ttk.Scrollbar(frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        text = tk.Text(frame, wrap=tk.WORD, yscrollcommand=scrollbar.set)
        text.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=text.yview)
        
        # 插入帮助内容
        help_text = """URL图片批量下载器使用帮助：

1. 添加URL：
   - 在左侧"URL输入区域"中输入一个或多个URL，每行一个
   - 或者点击"从文件加载"按钮从文本文件导入URL列表

2. 分析URL：
   - 点击"分析URL"按钮开始分析URL中的图片
   - 程序将从网页中提取图片链接并显示在右侧预览区

3. 预览图片：
   - 使用"上一张"和"下一张"按钮浏览提取到的图片
   - 使用鼠标滚轮可以缩放图片
   - 勾选"选中此图片"可以标记需要下载的图片

4. 下载设置：
   - 选择保存路径：点击"浏览"按钮选择图片保存的目录
   - 设置文件名前缀：在"文件名前缀"输入框中设置下载文件的前缀
   - 高级设置：可以设置过滤小图片、GIF图片等选项
   - 分辨率筛选：可以按照分辨率、宽度或高度筛选图片

5. 下载图片：
   - 勾选"选择性下载"可以只下载标记为选中的图片
   - 点击"下载全部图片"按钮开始下载
   - 或点击"下载当前图片"只下载当前显示的图片

6. 快捷键：
   - 左/右箭头键：切换上一张/下一张图片
   - Enter键：开始下载
   - Esc键：取消下载
   - F1键：显示帮助

如果遇到问题，可以查看日志或重新启动程序。"""

        text.insert(tk.END, help_text)
        text.config(state=tk.DISABLED)
        
        # 底部按钮
        button_frame = ttk.Frame(help_window, padding="10")
        button_frame.pack(fill=tk.X)
        
        ttk.Button(button_frame, text="关闭", 
                  command=help_window.destroy).pack(side=tk.RIGHT)
        
        # 确保所有布局计算完成
        help_window.update_idletasks()
        
        # 居中显示
        self._center_window(help_window)
        
        # 显示窗口
        help_window.deiconify()

    def clear_url_list(self):
        """清空URL列表"""
        self.url_list = []
        self.url_text.delete(1.0, tk.END)
        self.url_status.config(text="已加载 0 个URL")
    
    def _highlight_current_url(self, index, url):
        """高亮当前处理的URL"""
        # 先清除所有高亮
        self._clear_url_highlight()
        
        try:
            # 找到对应行并高亮
            start_pos = "1.0"
            for i in range(index):
                start_pos = self.url_text.search("\n", start_pos, tk.END) + "+1c"
            
            end_pos = self.url_text.search("\n", start_pos, tk.END)
            if not end_pos:
                end_pos = self.url_text.index(tk.END)
                
            self.url_text.tag_add("current", start_pos, end_pos)
            
            # 确保高亮的URL可见
            self.url_text.see(start_pos)
            
            # 更新URL状态
            self.url_status.config(text=f"处理中: {index+1}/{len(self.url_list)}")
        except Exception:
            pass  # 忽略任何错误
    
    def _clear_url_highlight(self):
        """清除URL高亮"""
        self.url_text.tag_remove("current", "1.0", tk.END)

    def show_image_list(self):
        """显示图片列表"""
        image_list_window = tk.Toplevel(self.root)
        image_list_window.title("图片列表")
        
        # 先隐藏窗口，避免闪烁
        image_list_window.withdraw()
        
        # 设置图标
        try:
            if hasattr(self, 'icon_path') and os.path.exists(self.icon_path):
                image_list_window.iconbitmap(self.icon_path)
        except Exception as e:
            print(f"设置图片列表窗口图标出错: {str(e)}")
        
        image_list_window.geometry("800x600")
        
        # 创建文本区域
        frame = ttk.Frame(image_list_window, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建带滚动条的文本区域
        scrollbar = ttk.Scrollbar(frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        text = tk.Text(frame, wrap=tk.WORD, yscrollcommand=scrollbar.set, font=("Courier New", 10))
        text.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=text.yview)
        
        # 创建标签和标记URL
        if self.preview_images:
            for i, url in enumerate(self.preview_images):
                text.insert(tk.END, f"{i+1}. {url}\n")
            
            # 高亮当前预览的图片
            if 0 <= self.current_preview_index < len(self.preview_images):
                start_index = f"{self.current_preview_index+1}.0"
                end_index = f"{self.current_preview_index+1}.end"
                text.tag_add("current", start_index, end_index)
                text.tag_configure("current", background="#e0e0e0")
                text.see(start_index)  # 滚动到当前图片位置
        else:
            text.insert(tk.END, "没有图片可显示")
        
        # 设置只读
        text.config(state=tk.DISABLED)
        
        # 双击选择图片
        text.bind("<Double-Button-1>", lambda e: self._preview_selected_image(text))
        
        # 底部按钮
        button_frame = ttk.Frame(image_list_window, padding="10")
        button_frame.pack(fill=tk.X)
        
        ttk.Button(button_frame, text="预览选中图片",
                 command=lambda: self._preview_selected_image(text)).pack(side=tk.LEFT)
                 
        ttk.Button(button_frame, text="关闭", 
                  command=image_list_window.destroy).pack(side=tk.RIGHT)
        
        # 确保所有布局计算完成
        image_list_window.update_idletasks()
        
        # 居中显示
        self._center_window(image_list_window)
        
        # 显示窗口
        image_list_window.deiconify()
    
    def _preview_selected_image(self, text_widget):
        """预览图片列表中选中的图片"""
        try:
            text_widget.config(state=tk.NORMAL)
            # 获取选中的行
            selected_text = text_widget.get("insert linestart", "insert lineend")
            text_widget.config(state=tk.DISABLED)
            
            # 解析行号
            match = re.match(r'^(\d+)', selected_text)
            if match:
                index = int(match.group(1)) - 1
                if 0 <= index < len(self.preview_images):
                    self.current_preview_index = index
                    self.load_preview_image()
        except Exception as e:
            messagebox.showerror("错误", f"预览选中图片时出错: {str(e)}")

    def goto_image(self):
        """跳转到指定序号图片"""
        try:
            index = int(self.goto_index.get()) - 1
            if 0 <= index < len(self.preview_images):
                self.current_preview_index = index
                self.load_preview_image()
            else:
                messagebox.showwarning("警告", f"图片序号超出范围(1-{len(self.preview_images)})")
        except ValueError:
            messagebox.showwarning("警告", "请输入有效的图片序号")

    def save_current_image(self):
        """保存当前预览的图片到自定义位置"""
        if not self.preview_images or len(self.preview_images) == 0 or self.current_preview_index < 0 or self.current_preview_index >= len(self.preview_images):
            messagebox.showwarning("警告", "没有可保存的图片")
            return
            
        # 获取文件名前缀
        prefix = self.prefix_var.get().strip()
        if not prefix:
            prefix = "image"  # 如果前缀为空，使用默认值
            
        # 获取当前图片URL
        img_url = self.preview_images[self.current_preview_index]
        
        # 解析默认文件名
        filename = os.path.basename(urlparse(img_url).path)
        if not filename or '.' not in filename:
            # 如果文件名无效或没有扩展名，使用默认扩展名
            filename = f"{prefix}_{self.current_preview_index+1}.jpg"
        else:
            # 从URL提取文件名和扩展名
            base_name, ext = os.path.splitext(filename)
            # 确保扩展名是小写字母
            ext = ext.lower()
            # 在原文件名前添加前缀
            filename = f"{prefix}_{base_name}{ext}"

        # 打开文件保存对话框
        file_path = filedialog.asksaveasfilename(
            initialfile=filename,
            defaultextension=os.path.splitext(filename)[1],
            filetypes=[
                ("JPEG 图片", "*.jpg;*.jpeg"), 
                ("PNG 图片", "*.png"),
                ("GIF 图片", "*.gif"),
                ("WebP 图片", "*.webp"),
                ("BMP 图片", "*.bmp"),
                ("SVG 图片", "*.svg"),
                ("所有文件", "*.*")
            ]
        )
        
        if not file_path:
            return
            
        self.status_label.config(text=f"保存图片中...")
        self.root.update()
        
        try:
            # 下载图片
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                'Referer': img_url
            }
            response = requests.get(img_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # 保存文件
            with open(file_path, 'wb') as f:
                f.write(response.content)
                
            # 更新状态
            self.status_label.config(text=f"图片已保存到: {file_path}")
            
        except Exception as e:
            self._handle_error(f"保存图片失败: {str(e)}")

    def show_about(self):
        """显示关于对话框"""
        about_window = tk.Toplevel(self.root)
        about_window.title("关于")
        
        # 先隐藏窗口，避免闪烁
        about_window.withdraw()
        
        # 设置图标
        try:
            if hasattr(self, 'icon_path') and os.path.exists(self.icon_path):
                about_window.iconbitmap(self.icon_path)
        except Exception as e:
            print(f"设置关于窗口图标出错: {str(e)}")
        
        about_window.geometry("550x500")
        about_window.resizable(False, False)
        about_window.configure(bg=AppTheme.BG_COLOR)
        
        # 设置模态对话框
        about_window.transient(self.root)
        about_window.grab_set()
        
        # 创建内容框架
        content_frame = ttk.Frame(about_window, padding="20")
        content_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_frame = ttk.Frame(content_frame)
        title_frame.pack(fill=tk.X, pady=(0, 20))
        
        # 显示应用图标
        try:
            if hasattr(self, 'icon_path') and os.path.exists(self.icon_path):
                logo_img = Image.open(self.icon_path)
                # 调整图标大小
                logo_img = logo_img.resize((64, 64), Image.LANCZOS)
                logo_photo = ImageTk.PhotoImage(logo_img)
                logo_label = ttk.Label(title_frame, image=logo_photo)
                logo_label.image = logo_photo  # 保持引用，防止被垃圾回收
                logo_label.pack(pady=(0, 10))
        except Exception as e:
            print(f"在关于窗口显示图标出错: {str(e)}")
        
        app_title = ttk.Label(
            title_frame, 
            text="URL图片批量下载器", 
            font=("Helvetica", 18, "bold"),
            foreground=AppTheme.PRIMARY_COLOR
        )
        app_title.pack(pady=(0, 5))
        
        version_label = ttk.Label(
            title_frame, 
            text="版本 1.2.0", 
            font=("Helvetica", 10),
            foreground=AppTheme.LIGHT_TEXT
        )
        version_label.pack()
        
        # 分隔线
        separator = ttk.Separator(content_frame, orient=tk.HORIZONTAL)
        separator.pack(fill=tk.X, pady=10)
        
        # 创建选项卡控件
        notebook = ttk.Notebook(content_frame)
        notebook.pack(fill=tk.BOTH, expand=True)
        
        # 功能介绍选项卡
        features_frame = ttk.Frame(notebook, padding=10)
        notebook.add(features_frame, text="功能介绍")
        
        desc_text = "这是一个用于从网页批量下载图片的工具，支持多种图片提取方式，" \
                    "可以预览图片并选择性下载。\n\n" \
                    "主要功能包括：\n" \
                    "• 从单个网页或多个网页提取图片\n" \
                    "• 支持图片预览和筛选\n" \
                    "• 支持批量下载与选择性下载\n" \
                    "• 多线程并行下载提高效率\n" \
                    "• 可设置图片尺寸过滤条件\n" \
                    "• 支持按分辨率、宽度或高度筛选图片\n" \
                    "• 图片缩放与查看\n" \
                    "• 支持保存当前查看的图片"
        
        desc_label = ttk.Label(
            features_frame, 
            text=desc_text,
            wraplength=500,
            justify=tk.LEFT
        )
        desc_label.pack(fill=tk.X, pady=5, anchor=tk.W)
        
        # 更新日志选项卡
        changelog_frame = ttk.Frame(notebook, padding=10)
        notebook.add(changelog_frame, text="更新日志")
        
        changelog_text = "版本 1.2.0 (2025-04-24)\n" \
                        "• 新增按分辨率、宽度和高度筛选图片功能\n" \
                        "• 优化界面布局，改进用户体验\n" \
                        "• 修复部分图片无法下载的问题\n\n" \
                        "版本 1.1.0 (2024-12-15)\n" \
                        "• 添加图片缩放功能\n" \
                        "• 增加选择性下载功能\n" \
                        "• 改进图片提取算法\n\n" \
                        "版本 1.0.0 (2023-10-01)\n" \
                        "• 初始版本发布"
        
        changelog_label = ttk.Label(
            changelog_frame, 
            text=changelog_text,
            wraplength=500,
            justify=tk.LEFT
        )
        changelog_label.pack(fill=tk.X, pady=5, anchor=tk.W)
        
        # 开发者信息选项卡
        dev_frame = ttk.Frame(notebook, padding=10)
        notebook.add(dev_frame, text="开发者信息")
        
        dev_text = "作者：摆渡人吾师\n\n" \
                  "公众号：摆渡的狂想曲\n\n" \
                  "如果您有任何建议或发现Bug，请联系我们。\n" \
                  "我们将不断改进这个工具，使其更好用、更强大。"
        
        dev_label = ttk.Label(
            dev_frame, 
            text=dev_text,
            wraplength=500,
            justify=tk.LEFT
        )
        dev_label.pack(fill=tk.X, pady=5, anchor=tk.W)
        
        # 添加作者信息和公众号到主框架底部，使其更加醒目
        author_frame = ttk.Frame(content_frame)
        author_frame.pack(fill=tk.X, pady=(15, 0))
        
        author_label = ttk.Label(
            author_frame,
            text="作者：摆渡人吾师  |  公众号：摆渡的狂想曲",
            font=("Microsoft YaHei UI", 10, "bold"),
            foreground=AppTheme.PRIMARY_COLOR
        )
        author_label.pack(anchor=tk.CENTER)
        
        # 底部按钮
        button_frame = ttk.Frame(about_window, padding="10")
        button_frame.pack(fill=tk.X)
        
        open_github_button = ttk.Button(
            button_frame, 
            text="访问项目主页", 
            command=lambda: webbrowser.open("https://github.com/imagedownloader/url-image-downloader"),
            style="Secondary.TButton"
        )
        open_github_button.pack(side=tk.LEFT)
        
        close_button = ttk.Button(
            button_frame, 
            text="关闭", 
            command=about_window.destroy,
            style="Accent.TButton"
        )
        close_button.pack(side=tk.RIGHT)
        
        # 确保所有布局计算完成
        about_window.update_idletasks()
        
        # 居中显示
        self._center_window(about_window)
        
        # 显示窗口
        about_window.deiconify()

    def download_current(self):
        """下载当前显示的图片"""
        if not self.preview_images or self.current_preview_index < 0 or self.current_preview_index >= len(self.preview_images):
            messagebox.showwarning("警告", "没有可下载的图片")
            return
            
        save_path = self.path_var.get().strip()
        if not save_path:
            messagebox.showwarning("警告", "请选择保存路径")
            return
            
        if not os.path.exists(save_path):
            try:
                os.makedirs(save_path)
            except Exception as e:
                messagebox.showerror("错误", f"创建保存目录失败: {str(e)}")
                return
        
        # 获取当前图片URL
        img_url = self.preview_images[self.current_preview_index]
        
        # 显示下载状态
        self.status_label.config(text=f"正在下载当前图片...")
        self.root.update()
        
        # 在新线程中下载当前图片
        threading.Thread(target=self._download_single_image, args=(img_url, save_path), daemon=True).start()
    
    def _download_single_image(self, img_url, save_path):
        """下载单个图片的线程函数"""
        try:
            # 获取文件名前缀
            prefix = self.prefix_var.get().strip()
            if not prefix:
                prefix = "image"  # 如果前缀为空，使用默认值
                
            # 下载图片
            headers = {
                'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                'Referer': img_url
            }
            response = requests.get(img_url, headers=headers, timeout=15)
            response.raise_for_status()
            
            # 解析文件名
            filename = os.path.basename(urlparse(img_url).path)
            if filename and '.' in filename:
                # 从URL提取文件名和扩展名
                base_name, ext = os.path.splitext(filename)
                # 确保扩展名是小写字母
                ext = ext.lower()
                # 在原文件名前添加前缀
                filename = f"{prefix}_{base_name}{ext}"
            else:
                # 从Content-Type确定文件扩展名
                content_type = response.headers.get('Content-Type', '')
                if 'jpeg' in content_type or 'jpg' in content_type:
                    ext = '.jpg'
                elif 'png' in content_type:
                    ext = '.png'
                elif 'gif' in content_type:
                    ext = '.gif'
                elif 'webp' in content_type:
                    ext = '.webp'
                elif 'bmp' in content_type:
                    ext = '.bmp'
                elif 'svg' in content_type:
                    ext = '.svg'
                else:
                    ext = '.jpg'  # 默认扩展名
                
                filename = f"{prefix}_{self.current_preview_index+1}{ext}"
            
            # 确保文件名合法
            filename = re.sub(r'[\\/*?:"<>|]', "_", filename)
            
            # 保存文件
            save_file_path = os.path.join(save_path, filename)
            
            # 检查是否存在同名文件
            if os.path.exists(save_file_path):
                base_name, ext = os.path.splitext(filename)
                counter = 1
                while os.path.exists(os.path.join(save_path, f"{base_name}_{counter}{ext}")):
                    counter += 1
                save_file_path = os.path.join(save_path, f"{base_name}_{counter}{ext}")
            
            with open(save_file_path, 'wb') as f:
                f.write(response.content)
            
            # 更新状态
            self.root.after(0, lambda: self.status_label.config(text=f"图片已保存到: {save_file_path}"))
            
        except Exception as e:
            self.root.after(0, lambda: self._handle_error(f"下载图片失败: {str(e)}"))

    def toggle_selection(self):
        """切换当前图片的选中状态"""
        if not self.preview_images or self.current_preview_index < 0 or self.current_preview_index >= len(self.preview_images):
            return
            
        # 更新状态文本
        selected = self.selected_var.get()
        status = "已选中" if selected else "已取消选中"
        
        # 如果启用了选择性下载，显示更详细的信息
        if self.selective_var.get():
            msg = f"{status}当前图片 ({self.current_preview_index + 1}/{len(self.preview_images)}) - 选择性下载模式已启用"
        else:
            msg = f"{status}当前图片 ({self.current_preview_index + 1}/{len(self.preview_images)})"
            
        self._update_status(msg)

    def batch_analyze(self):
        """分析按钮点击事件处理函数，处理一个或多个URL"""
        # 首先检查是否已经有加载好的URL列表
        if self.url_list:
            # 已有URL列表，直接分析
            self.analyze_all_urls()
            return
            
        # 如果没有已加载的列表，则从文本框获取URL列表
        urls_text = self.batch_text.get(1.0, tk.END).strip()
        if not urls_text:
            messagebox.showwarning("警告", "请先输入网址")
            return
            
        # 按行分割，去除空行
        urls = [line.strip() for line in urls_text.split('\n') if line.strip()]
        
        if not urls:
            messagebox.showwarning("警告", "没有有效的URL")
            return
            
        # 如果只有一个URL，使用单URL分析功能
        if len(urls) == 1:
            self._analyze_single_url(urls[0])
            return
            
        # 多个URL，存储并开始批量分析
        self.url_list = urls
        
        # 显示URLs到文本区域
        self.url_text.delete(1.0, tk.END)
        self.url_text.tag_configure("current", background="#e0e0e0")  # 定义高亮样式
        
        for i, url in enumerate(urls):
            self.url_text.insert(tk.END, f"{i+1}. {url}\n")
            
        # 更新URL状态
        self.url_status.config(text=f"已加载 {len(urls)} 个URL")
        
        # 开始分析
        self.analyze_all_urls()
        
    def _analyze_single_url(self, url):
        """分析单个URL"""
        if not url:
            messagebox.showwarning("警告", "请输入URL")
            return
            
        self.status_label.config(text="分析中...")
        self.root.update()
        
        # 在新线程中处理，避免UI冻结
        threading.Thread(target=self._analyze_url_thread, args=(url,), daemon=True).start()

    def _sync_selective_checkboxes(self):
        """同步两个选择性下载复选框的状态"""
        # 如果右侧的选择性下载变量已经存在，同步它
        if hasattr(self, 'select_download_var'):
            self.select_download_var.set(self.selective_var.get())
            
        # 根据选择性下载状态更新UI提示
        if self.selective_var.get():
            self._update_status("已开启选择性下载模式 - 只会下载选中的图片")
        else:
            self._update_status("已关闭选择性下载模式 - 将下载所有图片")

    def _sync_right_to_left(self):
        """从右侧同步选择性下载状态到左侧"""
        self.selective_var.set(self.select_download_var.get())
        # 调用同步方法更新状态提示
        self._sync_selective_checkboxes()

    def _on_filter_type_changed(self):
        """处理筛选类型下拉框选择变化事件"""
        filter_type = self.filter_type_var.get()
        
        # 根据筛选类型更新下拉框标题
        if filter_type == "分辨率":
            self.resolution_combobox.set("全部")
            if self.resolution_info_collected:
                # 使用已收集的分辨率信息
                resolution_list = ["全部"] + sorted(list(set(self.resolution_map.values())), 
                                                  key=lambda x: int(x.split('x')[0]) * int(x.split('x')[1]), 
                                                  reverse=True)
                self.resolution_combobox['values'] = resolution_list
            else:
                self.resolution_combobox['values'] = ["全部"]
                
        elif filter_type == "宽度":
            self.resolution_combobox.set("全部")
            if self.resolution_info_collected:
                # 使用已收集的宽度信息
                width_list = ["全部"] + sorted(list(set(self.width_map.values())), reverse=True)
                self.resolution_combobox['values'] = width_list
            else:
                self.resolution_combobox['values'] = ["全部"]
                
        elif filter_type == "高度":
            self.resolution_combobox.set("全部")
            if self.resolution_info_collected:
                # 使用已收集的高度信息
                height_list = ["全部"] + sorted(list(set(self.height_map.values())), reverse=True)
                self.resolution_combobox['values'] = height_list
            else:
                self.resolution_combobox['values'] = ["全部"]
    
    def _update_resolution_list(self):
        """收集并更新可用的图片分辨率列表"""
        if not self.preview_images:
            messagebox.showinfo("提示", "请先分析URL获取图片列表")
            return
            
        # 如果已经收集过分辨率信息，直接使用缓存
        if self.resolution_info_collected:
            self._on_filter_type_changed()  # 更新当前选择的筛选类型的下拉框
            return
            
        # 显示加载中提示
        self.status_label.config(text="正在获取图片分辨率信息...")
        self.root.update()
        
        # 在新线程中执行以避免UI冻结
        threading.Thread(target=self._collect_resolutions_thread, daemon=True).start()
        
    def _collect_resolutions_thread(self):
        """在后台线程中收集图片分辨率"""
        resolutions = set()
        widths = set()
        heights = set()
        total = len(self.preview_images)
        
        # 清空映射字典
        self.resolution_map = {}
        self.width_map = {}
        self.height_map = {}
        
        for i, url in enumerate(self.preview_images):
            try:
                # 更新进度
                progress = (i / total) * 100
                self.root.after(0, lambda p=progress, i=i, t=total: 
                               self._update_progress(p, i, t, prefix="获取分辨率"))
                
                # 获取图片并检查尺寸
                headers = {
                    'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
                }
                response = requests.get(url, headers=headers, timeout=10, stream=True)
                
                # 检查是否为图片
                content_type = response.headers.get('Content-Type', '')
                if not content_type.startswith('image/'):
                    continue
                
                # 获取图片尺寸
                img_data = response.content
                image = Image.open(BytesIO(img_data))
                width, height = image.size
                
                # 记录分辨率信息
                resolution_str = f"{width}x{height}"
                resolutions.add(resolution_str)
                widths.add(width)
                heights.add(height)
                
                # 保存到映射字典
                self.resolution_map[url] = resolution_str
                self.width_map[url] = width
                self.height_map[url] = height
                
            except Exception as e:
                # 忽略错误，继续处理下一个图片
                continue
        
        # 更新UI必须在主线程进行
        self.resolution_info_collected = True
        self.root.after(0, lambda: self._update_resolution_combobox(resolutions, widths, heights))
        
    def _update_resolution_combobox(self, resolutions, widths, heights):
        """更新分辨率下拉框的值"""
        filter_type = self.filter_type_var.get()
        
        if filter_type == "分辨率":
            resolution_list = ["全部"] + sorted(list(resolutions), 
                                              key=lambda x: int(x.split('x')[0]) * int(x.split('x')[1]), 
                                              reverse=True)
            self.resolution_combobox['values'] = resolution_list
            self.status_label.config(text=f"找到 {len(resolutions)} 种不同分辨率")
            
        elif filter_type == "宽度":
            width_list = ["全部"] + sorted(list(widths), reverse=True)
            self.resolution_combobox['values'] = width_list
            self.status_label.config(text=f"找到 {len(widths)} 种不同宽度")
            
        elif filter_type == "高度":
            height_list = ["全部"] + sorted(list(heights), reverse=True)
            self.resolution_combobox['values'] = height_list
            self.status_label.config(text=f"找到 {len(heights)} 种不同高度")
        
        self.resolution_combobox.set("全部")

    def _apply_resolution_filter(self):
        """应用分辨率筛选"""
        if not self.preview_images:
            messagebox.showinfo("提示", "请先分析URL获取图片列表")
            return
        
        # 获取筛选类型和值    
        filter_type = self.filter_type_var.get()
        selected_value = self.resolution_var.get()
        
        # 显示加载中提示
        self.status_label.config(text=f"正在应用{filter_type}筛选...")
        self.root.update()
        
        # 如果选择"全部"，则显示所有图片
        if selected_value == "全部":
            self.filter_resolution_var.set(False)
            # 如果已经有原始的图片列表，则直接更新预览
            if hasattr(self, 'original_preview_images'):
                self._update_preview(self.original_preview_images)
            return
        
        # 开启分辨率筛选
        self.filter_resolution_var.set(True)
        
        # 保存原始图片列表，以便稍后恢复
        if not hasattr(self, 'original_preview_images'):
            self.original_preview_images = self.preview_images.copy()
        
        # 如果还没有收集分辨率信息，需要先收集
        if not self.resolution_info_collected:
            messagebox.showinfo("提示", "需要先收集分辨率信息，请点击'刷新列表'")
            self._update_resolution_list()
            return
            
        # 根据筛选类型进行筛选
        filtered_images = []
        
        if filter_type == "分辨率":
            # 按完整分辨率筛选
            filtered_images = [url for url in self.original_preview_images 
                              if url in self.resolution_map 
                              and self.resolution_map[url] == selected_value]
                              
            result_message = f"找到 {len(filtered_images)} 张 {selected_value} 分辨率的图片"
            
        elif filter_type == "宽度":
            # 按宽度筛选
            selected_width = int(selected_value)
            filtered_images = [url for url in self.original_preview_images 
                              if url in self.width_map 
                              and self.width_map[url] == selected_width]
                              
            result_message = f"找到 {len(filtered_images)} 张宽度为 {selected_value} 的图片"
            
        elif filter_type == "高度":
            # 按高度筛选
            selected_height = int(selected_value)
            filtered_images = [url for url in self.original_preview_images 
                              if url in self.height_map 
                              and self.height_map[url] == selected_height]
                              
            result_message = f"找到 {len(filtered_images)} 张高度为 {selected_value} 的图片"
        
        # 更新预览
        if filtered_images:
            self._update_preview(filtered_images)
            self.status_label.config(text=result_message)
        else:
            messagebox.showinfo("提示", f"没有找到符合条件的图片")
            # 恢复原始设置
            self.resolution_combobox.set("全部")
            self.filter_resolution_var.set(False)

    def _on_resolution_selected(self):
        """处理分辨率下拉框选择事件"""
        # 自动应用筛选
        self._apply_resolution_filter()

    def _toggle_resolution_frame(self):
        """根据复选框状态显示或隐藏分辨率筛选框架"""
        if self.filter_resolution_var.get():
            # 如果勾选了复选框，显示分辨率框架
            self.resolution_frame.pack(fill=tk.X, padx=5, pady=5)
        else:
            # 如果取消勾选，隐藏分辨率框架
            self.resolution_frame.pack_forget()
            
            # 如果已经有原始的图片列表并进行了筛选，恢复显示所有图片
            if hasattr(self, 'original_preview_images') and self.preview_images != self.original_preview_images:
                self._update_preview(self.original_preview_images)

    def _on_mouse_wheel(self, event):
        """处理鼠标滚轮事件，调整图片缩放"""
        if not self.original_pil_img:
            return  # 没有图片可缩放
            
        # 确定滚轮方向和缩放步长
        delta = 0
        if event.num == 5 or event.delta < 0:  # 向下滚动，缩小
            delta = -0.1
        elif event.num == 4 or event.delta > 0:  # 向上滚动，放大
            delta = 0.1
            
        # 计算新的缩放比例，限制在合理范围内
        new_scale = max(0.1, min(3.0, self.current_scale + delta))
        
        if new_scale != self.current_scale:
            self.current_scale = new_scale
            self._apply_zoom()
            
    def _apply_zoom(self):
        """应用缩放到当前图片"""
        if not self.original_pil_img:
            return
            
        # 更新缩放指示器
        zoom_percentage = int(self.current_scale * 100)
        self.zoom_label.config(text=f"缩放: {zoom_percentage}%")
        
        # 计算缩放后的尺寸
        new_width = int(self.original_pil_img.width * self.base_scale * self.current_scale)
        new_height = int(self.original_pil_img.height * self.base_scale * self.current_scale)
        
        # 缩放图片
        if new_width > 0 and new_height > 0:
            try:
                resized_img = self.original_pil_img.resize((new_width, new_height), Image.LANCZOS)
                
                # 转换为PhotoImage
                self._photo_image = ImageTk.PhotoImage(resized_img)
                
                # 获取画布大小
                canvas_width = self.preview_canvas.winfo_width()
                canvas_height = self.preview_canvas.winfo_height()
                
                # 计算居中位置
                x_center = canvas_width // 2
                y_center = canvas_height // 2
                
                # 清空画布并添加图像
                self.preview_canvas.delete("all")
                self.preview_canvas.create_image(
                    x_center, y_center,
                    image=self._photo_image,
                    anchor="center"  # 使用中心点作为锚点
                )
                
                # 调整画布的滚动区域以适应图片
                self.preview_canvas.config(scrollregion=self.preview_canvas.bbox("all"))
                
            except Exception as e:
                print(f"缩放图片出错: {str(e)}")

    def _toggle_always_on_top(self):
        """切换窗口置顶状态"""
        self.root.attributes('-topmost', self.always_on_top.get())
        if self.always_on_top.get():
            self._update_status("窗口已置顶")
        else:
            self._update_status("窗口已取消置顶")

if __name__ == "__main__":
    root = tk.Tk()
    app = ImageDownloader(root)
    root.mainloop() 
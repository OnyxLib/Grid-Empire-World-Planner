import tkinter as tk
from tkinter import filedialog, messagebox
from PIL import Image, ImageTk
import numpy as np
import os
import pickle
import sys
from ctypes import windll

# Set a higher recursion limit for deep drawing/export calls
sys.setrecursionlimit(2000)

VERSION_NUM = "2.12"

class TileBuilderApp:
    # Basic Map Sizes
    MAP_WIDTH = 100
    MAP_HEIGHT = 60
    INITIAL_TILE_SIZE = 16
    TILE_ASSET_SIZE = 32
    
    # Layer Constants
    NUM_LAYERS = 2
    LAYER_BACKGROUND = 0
    LAYER_FOREGROUND = 1
    
    # Selector Configuration
    SELECTOR_HEIGHT = 180 
    TILE_DISPLAY_SIZE_IN_SELECTOR = 50
    
    # Folder and Files
    TILE_DIR = "tiles"
    BG_DIR = "backgrounds"
    TITLE = "Grid Empire World Planner"
    
    # Transformation Constants
    ROTATION_DEGREES = [0, 90, 180, 270]
    TRANSFORM_MIRROR = Image.FLIP_LEFT_RIGHT

    # UI Theme
    C_BG_MAIN = "#1e1e1e"        # Deepest dark background
    C_CANVAS_MAP = "#2d2d30"     # Map canvas background (slightly lighter for contrast)
    C_TEXT = "#cccccc"           # Light gray text
    C_ACCENT_BLUE = "#5b9dd9"    # Load Button Color
    C_ACCENT_GREEN = "#4CAF50"   # Save project Button & ms color
    C_ACCENT_RED = "#cc4444"     # Clear Map color
    C_GRID = "#444444"           # Grid lines color
    C_ACCENT_YELLOW = "#ffaa00"  # Selector/Highlight color
    C_ACCENT_PURPLE = "#9c27b0"  # Zoom label color

    def __init__(self, master):
        self.master = master
        master.title(self.TITLE)
        master.configure(bg=self.C_BG_MAIN)
        
        # Initialize canvas variables to None
        self.selector_tile_canvas = None
        self.tile_selector_canvas = None
        self.map_canvas = None

        # --- State Variables ---
        self.tile_images = {}       # Base PIL Image assets
        self.tile_images_tk = {}    # Tkinter PhotoImage assets
        self.tile_name_to_index = {}# Reverse lookup for search and default map population
        
        # --- Render Cache for Memory ---
        self.render_cache = {} 

        # Map data stores tile index (uint16)
        self.map_data = np.zeros(
            (self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint16
        ) 
        # Transformation data stores rotation (0-3 for 0/90/180/270) and mirror (0/1)
        self.map_rotation = np.zeros(
            (self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8
        )
        self.map_mirror = np.zeros(
            (self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8
        )
        self.map_item_ids = np.zeros(
            (self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=int
        ) 

        # Map Interaction State
        self.zoom_level = 1.3
        self.current_tile_size = self.INITIAL_TILE_SIZE * self.zoom_level
        self.current_tile_index = 1
        self.current_bg_index = 1 #0 is for no bg, start at 1
        self.bg_images_list = [] #saves all bg for faster loading time
        self.show_grid = True
        self.current_layer = self.LAYER_FOREGROUND 
        self.current_tool = "Paint"
        self.current_brush = 1
        self.is_dragging = False
        
        # Transformation state for the currently selected tile
        self.current_tile_rotation = 0 
        self.current_tile_mirrored = 0 
        
        # Undo/Redo History
        self.undo_stack = []
        self.redo_stack = []
        self.MAX_HISTORY = 100 
        
        # Load Backgrounds
        self.load_bg_assets(self.BG_DIR)
        
        # --- Setup UI in correct dependency order ---
        self.setup_selector() 
        self.setup_control_panel()
        self.setup_map_canvas()
        
        # --- Initial Tile Load ---
        self.load_tile_assets(self.TILE_DIR)
        
        # --- Mouse Bindings ---
        #paint
        self.map_canvas.bind("<Button-1>", self.on_left_click)
        self.map_canvas.bind("<B1-Motion>", self.on_left_click)
        #erase
        self.map_canvas.bind("<Button-3>", self.on_right_click)
        self.map_canvas.bind("<B3-Motion>", self.on_right_click)
        #pan map
        self.map_canvas.bind("<Button-2>", self.on_pan_start)
        self.map_canvas.bind("<B2-Motion>", self.on_pan_drag)
        self.map_canvas.bind("<ButtonRelease-2>", self.on_pan_end)
        #zoom in and out
        self.map_canvas.bind("<MouseWheel>", self.on_mouse_wheel) 
        self.map_canvas.bind("<Button-4>", self.on_mouse_wheel)  
        self.map_canvas.bind("<Button-5>", self.on_mouse_wheel)  

        # --- Keyboard Bindings ---
        #rotate selected tile
        self.master.bind('<Control-r>', self.on_rotate_key)
        self.master.bind('<Control-R>', self.on_rotate_key)
        #mirror selected tile
        self.master.bind('<Control-m>', self.on_mirror_key)
        self.master.bind('<Control-M>', self.on_mirror_key)
        #change between block and bg layer
        self.master.bind('<Tab>', self.toggle_layer)
        #change between paint or fill
        self.master.bind('<Control-f>', self.toggle_fill_tool)
        self.master.bind('<Control-F>', self.toggle_fill_tool)
        #change brush size
        self.master.bind('<Control-a>', self.cycle_brush_size)
        self.master.bind('<Control-A>', self.cycle_brush_size)
        #save map design to a file
        self.master.bind('<Control-s>', self.save_project)
        self.master.bind('<Control-S>', self.save_project)
        #load previously saved map design
        self.master.bind('<Control-d>', self.load_project)
        self.master.bind('<Control-D>', self.load_project)
        #save map to an image
        self.master.bind('<Control-x>', self.export_map_image)
        self.master.bind('<Control-X>', self.export_map_image)
        #reset map to empty
        self.master.bind('<Control-c>', self.clear_map)
        self.master.bind('<Control-C>', self.clear_map)
        #make a list containing all blocks used in map
        self.master.bind('<Control-v>', self.export_block_list)
        self.master.bind('<Control-V>', self.export_block_list)
        
        #select a tile from the map
        self.master.bind('<q>', self.pick_tile_at_pos)
        self.master.bind('<Q>', self.pick_tile_at_pos)
        #undo
        self.master.bind('<Control-z>', self.undo)
        self.master.bind('<Control-Z>', self.undo)
        #redo
        self.master.bind('<Control-Shift-z>', self.redo) 
        self.master.bind('<Control-Shift-Z>', self.redo)
        #change background
        self.master.bind('<Control-e>', self.cycle_background)
        self.master.bind('<Control-E>', self.cycle_background)
        #toggle grid
        self.master.bind('<Control-g>', self.toggle_grid)
        self.master.bind('<Control-G>', self.toggle_grid)

    def setup_control_panel(self):
        """Creates the main control panel for tools, layers, and status."""
        control_frame = tk.Frame(self.master, bg=self.C_BG_MAIN, padx=10, pady=7)
        control_frame.pack(side=tk.TOP, fill=tk.X, padx=10)
        
        # --- Layer Selection ---
        # Updated: Label now shows 'Tab'
        tk.Label(control_frame, text="Layer:", bg=self.C_BG_MAIN, fg=self.C_TEXT, font=("calibiri",11,'bold')).pack(side=tk.LEFT)
        self.layer_var = tk.IntVar(value=self.current_layer) 
        self.layer_var.trace_add("write", lambda *args: self.set_layer(self.layer_var.get()))

        tk.Radiobutton(control_frame, text="Block", font=("calibiri",11), variable=self.layer_var, value=self.LAYER_FOREGROUND, 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        tk.Radiobutton(control_frame, text="Background", font=("calibiri",11), variable=self.layer_var, value=self.LAYER_BACKGROUND, 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        
        # --- Tool Selection ---
        tk.Label(control_frame, text="Tool:", bg=self.C_BG_MAIN, fg=self.C_TEXT, font=("calibiri",11,'bold')).pack(side=tk.LEFT, padx=(10, 0))
        
        self.tool_var = tk.StringVar(value=self.current_tool)
        self.tool_var.trace_add("write", lambda *args: self.set_tool(self.tool_var.get()))

        tk.Radiobutton(control_frame, text="Paint", font=("calibiri",11), variable=self.tool_var, value="Paint", 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        tk.Radiobutton(control_frame, text="Fill", font=("calibiri",11), variable=self.tool_var, value="Fill", 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        
         # --- Brush Size Selection ---
        tk.Label(control_frame, text="Brush Size:", bg=self.C_BG_MAIN, fg=self.C_TEXT, font=("calibiri",11,'bold')).pack(side=tk.LEFT, padx=(10, 0))
        
        self.brush_var = tk.StringVar(value=self.current_brush)
        self.brush_var.trace_add("write", lambda *args: self.set_brush(self.brush_var.get()))

        tk.Radiobutton(control_frame, text="1x1", font=("calibiri",11), variable=self.brush_var, value=1, 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        tk.Radiobutton(control_frame, text="3x3", font=("calibiri",11), variable=self.brush_var, value=3, 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        tk.Radiobutton(control_frame, text="5x5", font=("calibiri",11), variable=self.brush_var, value=5, 
                       bg=self.C_BG_MAIN, fg=self.C_TEXT, selectcolor=self.C_BG_MAIN).pack(side=tk.LEFT)
        
        # --- File/Action Buttons ---
        button_frame = tk.Frame(control_frame, bg=self.C_BG_MAIN)
        button_frame.pack(side=tk.RIGHT, padx=5)

        tk.Button(button_frame, text="Save Project", font=("calibiri",11,'bold'), command=self.save_project, bg=self.C_ACCENT_GREEN, fg="white", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Load Project", font=("calibiri",11,'bold'), command=self.load_project, bg=self.C_ACCENT_BLUE, fg="white", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Export Image", font=("calibiri",11,'bold'), command=self.export_map_image, bg=self.C_ACCENT_YELLOW, fg="black", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Clear Map", font=("calibiri",11,'bold'), command=self.clear_map, bg=self.C_ACCENT_RED, fg="white", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Export List", font=("calibiri",11,'bold'), command=self.export_block_list, bg=self.C_ACCENT_PURPLE, fg="white", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text=" ? ", font=("calibiri",11,'bold'), command=self.qna_info, bg=self.C_GRID, fg="white", relief=tk.FLAT).pack(side=tk.LEFT, padx=5)

    def setup_map_canvas(self):
        """Creates the main map canvas."""
        
        self.map_canvas = tk.Canvas(
            self.master, 
            bg=self.C_CANVAS_MAP, 
            scrollregion=(0, 0, 
                          self.MAP_WIDTH * self.INITIAL_TILE_SIZE, 
                          self.MAP_HEIGHT * self.INITIAL_TILE_SIZE)
        )
        
        h_scrollbar = tk.Scrollbar(self.master, orient=tk.HORIZONTAL, command=self.map_canvas.xview)
        v_scrollbar = tk.Scrollbar(self.master, orient=tk.VERTICAL, command=self.map_canvas.yview)
        
        h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X, padx=15)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y, padx=(0,15))
        self.map_canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(15,0))
        
        self.map_canvas.config(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
    def setup_selector(self):
        """Creates the tile selector and current tile preview area."""
        selector_frame = tk.Frame(self.master, bg=self.C_BG_MAIN)
        selector_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(15,0))
        
        # --- Current Tile Title ---
        preview_frame = tk.Frame(selector_frame, bg=self.C_BG_MAIN, pady=5)
        preview_frame.pack(side=tk.TOP, fill=tk.X)
        
        self.selected_tile_name_var = tk.StringVar(value="Tile: Empty") 
        
        tk.Label(preview_frame, 
                 textvariable=self.selected_tile_name_var, 
                 bg=self.C_BG_MAIN,
                 font=("Inter", 11,'bold'), 
                 fg=self.C_TEXT).pack(pady=(5,2)) # Uses the StringVar for tile name
        
        # --- Current Tile Image ---
        self.selector_tile_canvas = tk.Canvas(
            preview_frame, 
            width=self.TILE_DISPLAY_SIZE_IN_SELECTOR, 
            height=self.TILE_DISPLAY_SIZE_IN_SELECTOR, 
            bg=self.C_CANVAS_MAP, 
            highlightthickness=2, 
            highlightbackground=self.C_ACCENT_YELLOW
        )
        self.selector_tile_canvas.pack(pady=5)
        self.current_tile_ref = None # To prevent garbage collection
        
        # --- Tile Picker Rot and Mirror Label ---
        self.transform_label = tk.Label(
            preview_frame, text="Rot: 0° | Mirror: Off", bg=self.C_BG_MAIN, fg=self.C_TEXT, font=("Inter", 10)
        )
        self.transform_label.pack()
        self.update_transform_label() 

        # --- Tile Picker Label ---
        tk.Label(selector_frame, text="Tile Picker:", font=("Inter", 11,'bold'), bg=self.C_BG_MAIN, fg=self.C_TEXT).pack(pady=5)

        # --- SEARCH FEATURE ---
        self.search_var = tk.StringVar()
        self.search_var.trace("w", self.on_search_update) 
        
        self.search_entry = tk.Entry(
            selector_frame, 
            textvariable=self.search_var, 
            bg=self.C_CANVAS_MAP, 
            fg=self.C_TEXT,
            font=("Inter", 11), 
            insertbackground=self.C_TEXT,
            relief=tk.FLAT,
            highlightthickness=1,
            highlightbackground=self.C_GRID,
        )
        #removes focus when you click away
        self.search_entry.bind_all("<Button-1>", lambda e: e.widget.focus_set())
        self.search_entry.pack(pady=(0, 5), padx=(5,0), fill=tk.X)
        
        
        # --- Tile Picker Body ---
        self.tile_selector_canvas = tk.Canvas(
            selector_frame, 
            width=self.TILE_DISPLAY_SIZE_IN_SELECTOR * 4 + 20, 
            height=self.SELECTOR_HEIGHT, 
            bg=self.C_CANVAS_MAP,
            scrollregion=(0, 0, 0, 0)
        )
        
        v_scrollbar = tk.Scrollbar(selector_frame, orient=tk.VERTICAL, command=self.tile_selector_canvas.yview)
        v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y,pady=(5,15))
        self.tile_selector_canvas.config(yscrollcommand=v_scrollbar.set)
        
        self.tile_selector_canvas.bind("<MouseWheel>", self.on_selector_mouse_wheel)
        
        self.tile_selector_canvas.bind("<Button-1>", self.on_selector_click)
        self.tile_selector_canvas.pack(padx=5, pady=(5,15), fill=tk.BOTH, expand=True)
                
    # --- Tool and Layer Management ---
    def set_tool(self, tool_name):
        self.current_tool = tool_name
    
    def set_brush(self, brush_size):
        self.current_brush = brush_size
        
    def toggle_fill_tool(self, event=None):
        """Toggles the current tool between Fill and Paint."""
        if self.current_tool == "Fill":
            self.tool_var.set("Paint")
        else:
            self.tool_var.set("Fill")
    
    def toggle_grid(self, event=None):
        if self.show_grid == True:
            self.show_grid = False
        else:
            self.show_grid = True
        self.full_redraw_map()
    
    def cycle_brush_size(self, event=None):
        """cycles brush sizes 1x1 -> 3x3 -> 5x5 -> 1x1."""
        if int(self.current_brush) == 1:
            self.brush_var.set(3)
        elif int(self.current_brush) == 3:
            self.brush_var.set(5)
        else:
            self.brush_var.set(1)
        
    def cycle_background(self,event=None):
        if self.current_bg_index == len(self.bg_images_list) - 1:
            self.current_bg_index = 0
        elif len(self.bg_images_list) != 1:
            self.current_bg_index += 1
        
        self.draw_background()
        self.draw_map()
        if self.show_grid == True: 
            self.draw_grid()

    def set_layer(self, layer_index):
        self.current_layer = layer_index
        if self.map_canvas:
            self.map_canvas.tag_raise(f"layer{self.current_layer}")
            
    def toggle_layer(self, event=None):
        """Toggles the current layer between Foreground (1) and Background (0). Bound to Tab."""
        current_layer = self.layer_var.get()
        new_layer = 1 - current_layer # Flips 0 to 1, or 1 to 0
        
        self.set_layer(new_layer)
        self.layer_var.set(new_layer)
        
    # --- Panning Handlers (Unchanged) ---
    def on_pan_start(self, event):
        self.map_canvas.scan_mark(event.x, event.y)
        self.map_canvas.config(cursor="fleur")

    def on_pan_drag(self, event):
        self.map_canvas.scan_dragto(event.x, event.y, gain=1)
   
    def on_pan_end(self, event):
        self.map_canvas.config(cursor="")
        
    # --- Transformation Handlers (Unchanged) ---
    def update_transform_label(self):
        rotation_deg = self.ROTATION_DEGREES[self.current_tile_rotation]
        mirror_state = "On" if self.current_tile_mirrored == 1 else "Off"
        self.transform_label.config(text=f"Rot: {rotation_deg}° | Mirror: {mirror_state}")
        self.update_selected_tile_preview()

    def on_rotate_key(self, event):
        self.current_tile_rotation = (self.current_tile_rotation + 1) % 4
        self.update_transform_label()

    def on_mirror_key(self, event):
        self.current_tile_mirrored = 1 - self.current_tile_mirrored
        self.update_transform_label()

    # --- Transformation Helper (Unchanged) ---
    def get_transformed_tile_image(self, tile_index, rotation_state, mirror_state, target_size=None):
        """Applies rotation/mirroring. target_size If None, scales to self.current_tile_size."""
        if tile_index == 0 or tile_index not in self.tile_images:
            if target_size:
                return Image.new('RGBA', (target_size, target_size), (0, 0, 0, 0))
            return None

        tile_img = self.tile_images[tile_index]

        if mirror_state == 1:
            tile_img = tile_img.transpose(self.TRANSFORM_MIRROR)

        if rotation_state == 1: 
            tile_img = tile_img.transpose(Image.ROTATE_90)
        elif rotation_state == 2: 
            tile_img = tile_img.transpose(Image.ROTATE_180)
        elif rotation_state == 3: 
            tile_img = tile_img.transpose(Image.ROTATE_270)
        
        size = target_size if target_size else int(self.current_tile_size)
        return tile_img.resize((size, size), Image.NEAREST)

    # --- Asset Loading (Unchanged) ---
    def load_tile_assets(self, tile_dir):
        if not os.path.isdir(tile_dir):
            messagebox.showerror("Error", f"Tile directory '{tile_dir}' not found.")
            return

        self.tile_images = {}
        self.tile_images_tk = {}
        self.tile_name_to_index = {}
        # Clear cache on reload
        self.render_cache.clear()

        file_list = [f for f in os.listdir(tile_dir) if f.endswith(".png")]
        
        for i, filename in enumerate(sorted(file_list)):
            tile_index = i + 1
            filepath = os.path.join(tile_dir, filename)
            try:
                img = Image.open(filepath).convert("RGBA")
                if img.width != self.TILE_ASSET_SIZE or img.height != self.TILE_ASSET_SIZE:
                    img = img.resize((self.TILE_ASSET_SIZE, self.TILE_ASSET_SIZE), Image.NEAREST)
                    
                self.tile_images[tile_index] = img
                
                # Pre-scale for selector (this is small, so we don't cache deeply)
                scaled_img_for_selector = img.resize(
                    (self.TILE_DISPLAY_SIZE_IN_SELECTOR, self.TILE_DISPLAY_SIZE_IN_SELECTOR), Image.NEAREST
                )
                self.tile_images_tk[tile_index] = ImageTk.PhotoImage(scaled_img_for_selector)
                
                base_name = os.path.splitext(filename)[0]
                self.tile_name_to_index[base_name] = tile_index
            except Exception as e:
                print(f"Error loading tile {filename}: {e}")

        self.draw_tile_selector()
        self.update_selected_tile_preview()
        self.load_default_map() 
        self.full_redraw_map()
    
    def load_bg_assets(self, bg_dir):
        if not os.path.isdir(bg_dir):
            messagebox.showerror("Error", f"Background directory '{bg_dir}' not found.")
            return
        
        file_list = [f for f in os.listdir(bg_dir)]
        
        for i in file_list:
            original_image = Image.open(os.path.join(bg_dir, i))
            self.bg_images_list.append(original_image)   
        
    def load_default_map(self):
        bedrock_index = self.tile_name_to_index.get('Bedrock', None)
        if bedrock_index is None:
            return

        num_rows_to_fill = 3
        start_row = self.MAP_HEIGHT - num_rows_to_fill
        if start_row < 0: start_row = 0
            
        self.map_data[self.LAYER_BACKGROUND, start_row:, :] = bedrock_index
        
    # --- History Management (Unchanged) ---
    def record_action(self, layer, row, col, old_idx, old_rot, old_mirror, new_idx, new_rot, new_mirror):
        action = (layer, row, col, old_idx, old_rot, old_mirror, new_idx, new_rot, new_mirror)
        self.redo_stack.clear()
        self.undo_stack.append(action)
        if len(self.undo_stack) > self.MAX_HISTORY:
            self.undo_stack.pop(0)

    def record_mega_action(self, changes):
        self.redo_stack.clear()
        self.undo_stack.append(changes)
        if len(self.undo_stack) > self.MAX_HISTORY:
            self.undo_stack.pop(0)

    def perform_action(self, action, is_undo, redraw_immediately=True):
        layer, r, c, old_idx, old_rot, old_mirror, new_idx, new_rot, new_mirror = action
        
        if is_undo:
            target_idx, target_rot, target_mirror = old_idx, old_rot, old_mirror
        else:
            target_idx, target_rot, target_mirror = new_idx, new_rot, new_mirror

        self.map_data[layer, r, c] = target_idx
        self.map_rotation[layer, r, c] = target_rot
        self.map_mirror[layer, r, c] = target_mirror
        
        if redraw_immediately:
            self.draw_tile_on_map(layer, target_idx, r, c)

    def undo(self,event=None):
        if not self.undo_stack: return
        action = self.undo_stack.pop()
        
        if isinstance(action, list):
            for act in reversed(action): 
                self.perform_action(act, is_undo=True, redraw_immediately=False)
            self.redo_stack.append(action)
            self.full_redraw_map() 
        else:
            self.perform_action(action, is_undo=True)
            self.redo_stack.append(action)

    def redo(self,event=None):
        if not self.redo_stack: return
        action = self.redo_stack.pop()
        
        if isinstance(action, list):
            for act in action:
                self.perform_action(act, is_undo=False, redraw_immediately=False)
            self.undo_stack.append(action)
            self.full_redraw_map() 
        else:
            self.perform_action(action, is_undo=False)
            self.undo_stack.append(action)
        
    # --- Map Painting/Interaction (Unchanged) ---
    def on_left_click(self, event):
        self.is_dragging = True
        if self.current_tool == "Fill":
            self.bucket_fill(event) 
        elif int(self.current_brush) == 3 or int(self.current_brush) == 5:
            self.paint_big_tile(event,int(self.current_brush))
        else:
            self.paint_tile(event)

        self.map_canvas.bind("<ButtonRelease-1>", self.on_release)

    def on_right_click(self, event):
        self.is_dragging = True
        if self.current_tool != "Fill" and int(self.current_brush) != 3 and int(self.current_brush) != 5:
            self.paint_tile(event, force_tool="Eraser")
        else:
            self.paint_big_tile(event,int(self.current_brush), force_tool="Eraser")
        self.map_canvas.bind("<ButtonRelease-3>", self.on_release)

    def on_release(self, event):
        self.is_dragging = False
        self.map_canvas.unbind("<ButtonRelease-1>")
        self.map_canvas.unbind("<ButtonRelease-3>")

# --- Pick Tile Logic (Refactored) ---
    def pick_tile_at_pos(self, event):
        row, col = self.get_map_coords(event)
        
        if 0 <= row < self.MAP_HEIGHT and 0 <= col < self.MAP_WIDTH:
            layer = self.current_layer
            index = self.map_data[layer, row, col]
        
        if index != -1 and index in self.tile_images:
            self.current_tile_index = index # Sync variable used by selector
            self.current_tile_rotation = self.map_rotation[layer, row, col]
            self.current_tile_mirrored = self.map_mirror[layer, row, col]
            self.highlight_selected_tile()
            self.update_transform_label()

    def get_map_coords(self, event):
        canvas_x = self.map_canvas.canvasx(event.x)
        canvas_y = self.map_canvas.canvasy(event.y)
        col = int(canvas_x // self.current_tile_size)
        row = int(canvas_y // self.current_tile_size)
        return row, col

    def paint_tile(self, event, force_tool=None):
        row, col = self.get_map_coords(event)

        if 0 <= row < self.MAP_HEIGHT and 0 <= col < self.MAP_WIDTH:
            layer = self.current_layer
            
            original_index = self.map_data[layer, row, col]
            original_rot = self.map_rotation[layer, row, col]
            original_mirror = self.map_mirror[layer, row, col]
            
            tool = force_tool if force_tool else self.current_tool

            if tool == "Paint":
                new_index = self.current_tile_index
                new_rot = self.current_tile_rotation
                new_mirror = self.current_tile_mirrored
                
                if (new_index != original_index or 
                    new_rot != original_rot or 
                    new_mirror != original_mirror):
                    
                    self.record_action(
                        layer, row, col, 
                        original_index, original_rot, original_mirror,
                        new_index, new_rot, new_mirror
                    )
                    self.map_data[layer, row, col] = new_index
                    self.map_rotation[layer, row, col] = new_rot
                    self.map_mirror[layer, row, col] = new_mirror
                    self.draw_tile_on_map(layer, new_index, row, col)

            elif tool == "Eraser":
                if original_index != 0:
                    self.record_action(
                        layer, row, col, 
                        original_index, original_rot, original_mirror,
                        0, 0, 0
                    )
                    self.map_data[layer, row, col] = 0
                    self.map_rotation[layer, row, col] = 0 
                    self.map_mirror[layer, row, col] = 0   
                    self.draw_tile_on_map(layer, 0, row, col)
                    
    def paint_big_tile(self, event, brush_size, force_tool=None):
        # 1. Get the center point (where the mouse is)
        center_row, center_col = self.get_map_coords(event)
        layer = self.current_layer
        changes = []
        
        # 2. Determine brush radius
        # 1x1 -> radius 1 | 3x3 -> radius 3 | 5x5 -> radius 5
        # Ensure you define self.brush_size in your __init__ (e.g., self.brush_size = 1)
        radius = (brush_size - 1) // 2

        tool = force_tool if force_tool else self.current_tool 

        # Pre-fetch current tile properties to avoid doing it inside the loop repeatedly
        cur_index = self.current_tile_index
        cur_rot = self.current_tile_rotation
        cur_mirror = self.current_tile_mirrored

        # 3. Iterate over the area defined by the radius
        for r_offset in range(-radius, radius + 1):
            for c_offset in range(-radius, radius + 1):
                
                # Calculate the actual target coordinates
                row = center_row + r_offset
                col = center_col + c_offset

                # 4. Perform Bounds Check (Must check every tile in the loop)
                if 0 <= row < self.MAP_HEIGHT and 0 <= col < self.MAP_WIDTH:
                    
                    original_index = self.map_data[layer, row, col]
                    original_rot = self.map_rotation[layer, row, col]
                    original_mirror = self.map_mirror[layer, row, col]

                    if tool == "Paint":
                        # Check if anything actually changes
                        if (cur_index != original_index or 
                            cur_rot != original_rot or 
                            cur_mirror != original_mirror):
                            
                            changes.append((
                                layer, row, col, 
                                original_index, original_rot, original_mirror,
                                cur_index, cur_rot, cur_mirror
                            ))
                            self.map_data[layer, row, col] = cur_index
                            self.map_rotation[layer, row, col] = cur_rot
                            self.map_mirror[layer, row, col] = cur_mirror
                            self.draw_tile_on_map(layer, cur_index, row, col)

                    elif tool == "Eraser":
                        if original_index != 0:
                            changes.append((
                                layer, row, col, 
                                original_index, original_rot, original_mirror,
                                0, 0, 0
                            ))
                            self.map_data[layer, row, col] = 0
                            self.map_rotation[layer, row, col] = 0 
                            self.map_mirror[layer, row, col] = 0   
                            self.draw_tile_on_map(layer, 0, row, col)
        self.record_mega_action(changes)
                    
    # --- Bucket Fill Implementation (Unchanged) ---
    def bucket_fill(self, event):
        start_row, start_col = self.get_map_coords(event)
        layer = self.current_layer
        
        if not (0 <= start_row < self.MAP_HEIGHT and 0 <= start_col < self.MAP_WIDTH):
            return

        target_index = self.map_data[layer, start_row, start_col]
        target_rot = self.map_rotation[layer, start_row, start_col]
        target_mirror = self.map_mirror[layer, start_row, start_col]

        new_index = self.current_tile_index
        new_rot = self.current_tile_rotation
        new_mirror = self.current_tile_mirrored

        if (target_index == new_index and 
            target_rot == new_rot and 
            target_mirror == new_mirror):
            return

        queue = [(start_row, start_col)]
        visited = set([(start_row, start_col)])
        changes = []

        while queue:
            r, c = queue.pop(0)
            
            current_idx = self.map_data[layer, r, c]
            current_rot = self.map_rotation[layer, r, c]
            current_mirror = self.map_mirror[layer, r, c]
            
            if (current_idx == target_index and 
                current_rot == target_rot and 
                current_mirror == target_mirror):

                changes.append((layer, r, c, current_idx, current_rot, current_mirror, new_index, new_rot, new_mirror))

                self.map_data[layer, r, c] = new_index
                self.map_rotation[layer, r, c] = new_rot
                self.map_mirror[layer, r, c] = new_mirror

                for dr, dc in [(0, 1), (0, -1), (1, 0), (-1, 0)]:
                    nr, nc = r + dr, c + dc
                    if (0 <= nr < self.MAP_HEIGHT and 
                        0 <= nc < self.MAP_WIDTH and 
                        (nr, nc) not in visited):
                        
                        visited.add((nr, nc))
                        
                        n_idx = self.map_data[layer, nr, nc]
                        n_rot = self.map_rotation[layer, nr, nc]
                        n_mirror = self.map_mirror[layer, nr, nc]
                        
                        if (n_idx == target_index and 
                            n_rot == target_rot and 
                            n_mirror == target_mirror):
                            queue.append((nr, nc))

        if changes:
            self.record_mega_action(changes)
            self.full_redraw_map() 

    # --- Selector Drawing with Search Feature and Name Display (Unchanged) ---

    def on_search_update(self, *args):
        """Callback when search text changes."""
        self.draw_tile_selector()

    def get_visible_tile_indices(self):
        """Returns a sorted list of tile indices matching the search term."""
        search_term = self.search_var.get().lower().strip()
        
        if not search_term:
            return sorted(self.tile_images.keys())
        
        matched_indices = []
        for name, idx in self.tile_name_to_index.items():
            if search_term in name.lower():
                matched_indices.append(idx)
        
        return sorted(matched_indices)

    def get_tile_name(self, tile_index):
        """Looks up the tile name from its index."""
        if tile_index == 0:
            return "Eraser/Empty"
        
        for name, index in self.tile_name_to_index.items():
            if index == tile_index:
                return name
        return f"Tile #{tile_index}"

    def update_selected_tile_preview(self):
        """Updates both the tile name label and the tile preview image."""
        if not self.selector_tile_canvas: return
        
        # 1. Update Label
        tile_name = self.get_tile_name(self.current_tile_index)
        self.selected_tile_name_var.set(f"Tile: {tile_name}")
        
        # 2. Update Image 
        self.selector_tile_canvas.delete("all")
        
        scaled_img = self.get_transformed_tile_image(
            self.current_tile_index, 
            self.current_tile_rotation, 
            self.current_tile_mirrored, 
            target_size=self.TILE_DISPLAY_SIZE_IN_SELECTOR
        )

        self.current_tile_ref = ImageTk.PhotoImage(scaled_img)
        #the highlighted boundary makes it 52x52. so start at 2,2
        self.selector_tile_canvas.create_image(2, 2, image=self.current_tile_ref, anchor='nw', tags="current_tile")

    def draw_tile_selector(self):
        if not self.tile_selector_canvas: return

        self.tile_selector_canvas.delete("all")
        self.tile_selector_refs = []
        
        tile_indices = self.get_visible_tile_indices()
        
        tiles_per_row = 4
        padding = 5
        
        x_offset = padding
        y_offset = padding
        max_y = 0

        for i, tile_index in enumerate(tile_indices):
            row = i // tiles_per_row
            col = i % tiles_per_row
            
            x = x_offset + col * (self.TILE_DISPLAY_SIZE_IN_SELECTOR + padding)
            y = y_offset + row * (self.TILE_DISPLAY_SIZE_IN_SELECTOR + padding)
            
            img_tk = self.tile_images_tk.get(tile_index)
            if img_tk:
                self.tile_selector_refs.append(img_tk) 

                self.tile_selector_canvas.create_image(
                    x, y, 
                    image=img_tk, 
                    anchor=tk.NW,
                    tags=(f"tile_{tile_index}", "selectable")
                )
                
                self.tile_selector_canvas.create_rectangle(
                    x, y, 
                    x + self.TILE_DISPLAY_SIZE_IN_SELECTOR, 
                    y + self.TILE_DISPLAY_SIZE_IN_SELECTOR,
                    outline=self.C_GRID,
                    tags=f"border_{tile_index}"
                )
                max_y = y + self.TILE_DISPLAY_SIZE_IN_SELECTOR + padding
            
        self.tile_selector_canvas.config(scrollregion=(0, 0, 
            tiles_per_row * (self.TILE_DISPLAY_SIZE_IN_SELECTOR + padding) + padding, 
            max_y
        ))
        self.highlight_selected_tile()

    def highlight_selected_tile(self):
        if not self.tile_selector_canvas: return

        self.tile_selector_canvas.delete("highlight")
        
        visible_indices = self.get_visible_tile_indices()
        
        if self.current_tile_index in visible_indices:
            border_tag = f"border_{self.current_tile_index}"
            coords = self.tile_selector_canvas.coords(border_tag)
            
            if coords:
                self.tile_selector_canvas.create_rectangle(
                    coords[0], coords[1], coords[2], coords[3],
                    outline=self.C_ACCENT_YELLOW,
                    width=3,
                    tags="highlight"
                )
                self.tile_selector_canvas.tag_raise("highlight")

    def on_selector_click(self, event):
        canvas_x = self.tile_selector_canvas.canvasx(event.x)
        canvas_y = self.tile_selector_canvas.canvasy(event.y)
        
        tiles_per_row = 4
        padding = 5
        tile_size = self.TILE_DISPLAY_SIZE_IN_SELECTOR
        
        col_index = int((canvas_x - padding) // (tile_size + padding))
        row_index = int((canvas_y - padding) // (tile_size + padding))
        
        x_start = padding + col_index * (tile_size + padding)
        y_start = padding + row_index * (tile_size + padding)
        
        if (x_start <= canvas_x < x_start + tile_size and
            y_start <= canvas_y < y_start + tile_size):
            
            tile_keys = self.get_visible_tile_indices()
            overall_index = row_index * tiles_per_row + col_index
            
            if overall_index < len(tile_keys):
                new_index = tile_keys[overall_index]
                
                # Check if tile changed
                if new_index != self.current_tile_index or self.current_tile_rotation != 0 or self.current_tile_mirrored != 0:
                    self.current_tile_index = new_index
                    self.current_tile_rotation = 0
                    self.current_tile_mirrored = 0
                    self.update_transform_label() 
                    self.highlight_selected_tile()
    
    def on_selector_mouse_wheel(self, event):
        """Handles mouse wheel scrolling for the tile selector."""
        # Standard Tkinter scroll amount: 1 unit per click/delta step
        if event.delta < 0:
            self.tile_selector_canvas.yview_scroll(1, "units") # Scroll down
        elif event.delta > 0:
            self.tile_selector_canvas.yview_scroll(-1, "units") # Scroll up

    # --- Utility Functions ---
    def clear_map(self,event=None):
        if messagebox.askyesno("Clear Map", "Are you sure you want to clear the entire map?"):
            self.map_data.fill(0)
            self.map_rotation.fill(0)
            self.map_mirror.fill(0)
            self.load_default_map()
            self.full_redraw_map()
            self.undo_stack.clear()
            self.redo_stack.clear()
            messagebox.showinfo("Map Cleared", "The map has been cleared.")
    
    def qna_info(self):
        dialog = tk.Toplevel()
        dialog.title("Info")
        dialog.transient(dialog.master) # Make it a modal dialog

        window_height = 580 # +20 for every line of text
        window_width = 300
        
        x_cordinate = int((dialog.winfo_screenwidth()/2) - (window_width/2))
        y_cordinate = int((dialog.winfo_screenheight()/2) - (window_height/2))

        dialog.geometry("{}x{}+{}+{}".format(window_width, window_height, x_cordinate, y_cordinate))
        
        # Create a frame to hold the labels
        frame = tk.Frame(dialog)
        frame.pack(padx=15, pady=5)

        tk.Label(frame, text="Keybinds:",font=("Arial", 16, "bold"),anchor=tk.CENTER).pack(side="top")
        
        keybind_body = [
            "Right Click - Add Tiles",
            "Left Click - Remove Tiles",
            "Middle Mouse - Pan Map",
            "Tab - Change Layer",
            "Q - Select Tile in Map",
            "CTRL+R - Rotate Tile",
            "CTRL+M - Mirror Tile",
            "CTRL+E - Cycle Background",
            "CTRL+G - Toggle Grid",
            "CTRL+A - Cycle Brush",
            "CTRL+F - Change Tool",
            "CTRL+S - Save Project",
            "CTRL+D - Load Project",
            "CTRL+X - Export Image",
            "CTRL+C - Clear Map",
            "CTRL+V - Export List",
        ]
        for i in keybind_body:
            tk.Label(frame, text=i, font=("Arial", 14)).pack(side="top")

        tk.Label(frame, text="Tool built by: Onyx", font=("Arial", 14)).pack(side="top",pady=(20,0))
        tk.Label(frame, text="Version: " + VERSION_NUM, font=("Arial", 14)).pack(side="top")

        dialog.wait_window(dialog) # Wait until the dialog is closed
            
    def full_redraw_map(self):
        """Clears the canvas and redraws the entire map and grid using cached images."""
        if not self.map_canvas: return

        self.map_canvas.delete("all")
        
        map_pixel_width = self.MAP_WIDTH * self.current_tile_size
        map_pixel_height = self.MAP_HEIGHT * self.current_tile_size
        
        self.map_canvas.config(scrollregion=(0, 0, map_pixel_width, map_pixel_height))

        # Reset item IDs but NOT the render_cache
        self.map_item_ids.fill(0)
        
        #draw_background takes longer than draw_map to load when the map is empty.
        #if the tile map is full, draw_map takes around double the load time compared to draw_background.
        #initial attempt to thread both processes resulted in longer loading times. 
        #FUTURE: optimize draw_map further or do a better threading implementation.
        self.draw_background()
        self.draw_map()
        if self.show_grid == True:
            self.draw_grid()

    def draw_background(self):
        map_pixel_width = self.MAP_WIDTH * self.current_tile_size
        map_pixel_height = self.MAP_HEIGHT * self.current_tile_size
    
        #used Image.NEAREST for the fastest resize loading time with PIL
        #Future: explore ImageTk zoom & subsample OR threading to make it marginally faster
        resized_image = self.bg_images_list[self.current_bg_index].resize((int(map_pixel_width),int(map_pixel_height)), Image.NEAREST)
        self.converted_bg = ImageTk.PhotoImage(resized_image)
        self.map_canvas.create_image(0,0, image=self.converted_bg, anchor='nw')  

    def draw_map(self):
        for layer_idx in range(self.NUM_LAYERS):
            for r in range(self.MAP_HEIGHT):
                for c in range(self.MAP_WIDTH):
                    tile_idx = self.map_data[layer_idx, r, c]
                    self.draw_tile_on_map(layer_idx, tile_idx, r, c)

    def draw_grid(self):
        if not self.map_canvas: return
        map_pixel_width = self.MAP_WIDTH * self.current_tile_size
        map_pixel_height = self.MAP_HEIGHT * self.current_tile_size
        
        for i in range(self.MAP_WIDTH + 1):
            x = int(i * self.current_tile_size)
            self.map_canvas.create_line(x, 0, x, map_pixel_height, fill=self.C_GRID, tags="grid")
            
        for i in range(self.MAP_HEIGHT + 1):
            y = int(i * self.current_tile_size)
            self.map_canvas.create_line(0, y, map_pixel_width, y, fill=self.C_GRID, tags="grid")
        
    def draw_tile_on_map(self, layer_index, tile_index, row, col):
        """Draws a single tile using cached images to prevent memory errors."""
        if not self.map_canvas: return
        if row < 0 or row >= self.MAP_HEIGHT or col < 0 or col >= self.MAP_WIDTH:
            return

        x1 = int(col * self.current_tile_size)
        y1 = int(row * self.current_tile_size)

        item_id = self.map_item_ids[layer_index, row, col]
        if item_id:
            self.map_canvas.delete(item_id)
            self.map_item_ids[layer_index, row, col] = 0

        if tile_index != 0:
            rot = self.map_rotation[layer_index, row, col]
            mirror = self.map_mirror[layer_index, row, col]
            size = int(self.current_tile_size)

            # --- THE MEMORY FIX ---
            cache_key = (tile_index, rot, mirror, size)

            if cache_key in self.render_cache:
                photo_image = self.render_cache[cache_key]
            else:
                # Create the image only if it doesn't exist in cache
                pil_img = self.get_transformed_tile_image(tile_index, rot, mirror)
                if pil_img:
                    photo_image = ImageTk.PhotoImage(pil_img)
                    self.render_cache[cache_key] = photo_image
                else:
                    return

            new_id = self.map_canvas.create_image(
                x1, y1, image=photo_image, anchor=tk.NW, tags=f"layer{layer_index}"
            )
            self.map_item_ids[layer_index, row, col] = new_id

    def save_project(self,event=None):
        file_path = filedialog.asksaveasfilename(
            defaultextension=".map",
            filetypes=[("Map Files", "*.map")],
            title="Save Map Project"
        )
        if file_path:
            try:
                project_data = {
                    'map_data': self.map_data,
                    'map_rotation': self.map_rotation, 
                    'map_mirror': self.map_mirror,     
                    'tile_dir': self.TILE_DIR, 
                    'map_width': self.MAP_WIDTH,
                    'map_height': self.MAP_HEIGHT,
                }
                with open(file_path, 'wb') as f:
                    pickle.dump(project_data, f)
                messagebox.showinfo("Save Project", "Map project saved successfully!")
            except Exception as e:
                messagebox.showerror("Error", f"Error saving project: {e}")

    def load_project(self,event=None):
        file_path = filedialog.askopenfilename(
            defaultextension=".map",
            filetypes=[("Map Files", "*.map")],
            title="Load Map Project"
        )
        if file_path:
            try:
                with open(file_path, 'rb') as f:
                    loaded_data = pickle.load(f)

                self.MAP_WIDTH = loaded_data.get('map_width', self.MAP_WIDTH)
                self.MAP_HEIGHT = loaded_data.get('map_height', self.MAP_HEIGHT)

                self.map_data = loaded_data.get('map_data', self.map_data)
                
                self.map_rotation = loaded_data.get('map_rotation', 
                    np.zeros((self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8)
                )
                self.map_mirror = loaded_data.get('map_mirror', 
                    np.zeros((self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8)
                )
                
                if self.map_data.shape[1] != self.MAP_HEIGHT or self.map_data.shape[2] != self.MAP_WIDTH:
                    new_map_data = np.zeros((self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint16)
                    new_map_rotation = np.zeros((self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8)
                    new_map_mirror = np.zeros((self.NUM_LAYERS, self.MAP_HEIGHT, self.MAP_WIDTH), dtype=np.uint8)

                    h = min(self.MAP_HEIGHT, self.map_data.shape[1])
                    w = min(self.MAP_WIDTH, self.map_data.shape[2])

                    new_map_data[:, :h, :w] = self.map_data[:, :h, :w]
                    new_map_rotation[:, :h, :w] = self.map_rotation[:, :h, :w]
                    new_map_mirror[:, :h, :w] = self.map_mirror[:, :h, :w]
                    
                    self.map_data = new_map_data
                    self.map_rotation = new_map_rotation
                    self.map_mirror = new_map_mirror
                
                # Clear cache before redrawing to be safe
                self.render_cache.clear()
                
                self.load_tile_assets(loaded_data.get('tile_dir', self.TILE_DIR))
                self.full_redraw_map()
                
                self.undo_stack.clear()
                self.redo_stack.clear()
                
                messagebox.showinfo("Load Project", "Map project loaded successfully!")
            except Exception as e:
                messagebox.showerror("Error", f"Error loading project: {e}")

    def export_map_image(self,event=None):
        try:
            pixel_width = self.MAP_WIDTH * self.TILE_ASSET_SIZE
            pixel_height = self.MAP_HEIGHT * self.TILE_ASSET_SIZE
            
            final_image = Image.new('RGBA', (pixel_width, pixel_height), (0, 0, 0, 0))

            for layer_idx in range(self.NUM_LAYERS):
                for r in range(self.MAP_HEIGHT):
                    for c in range(self.MAP_WIDTH):
                        tile_idx = self.map_data[layer_idx, r, c]
                        if tile_idx != 0:
                            rotation_state = self.map_rotation[layer_idx, r, c]
                            mirror_state = self.map_mirror[layer_idx, r, c]
                            
                            tile_img = self.get_transformed_tile_image(
                                tile_idx, rotation_state, mirror_state, target_size=self.TILE_ASSET_SIZE
                            )
                            if tile_img:
                                x = c * self.TILE_ASSET_SIZE
                                y = r * self.TILE_ASSET_SIZE
                                final_image.paste(tile_img, (x, y), tile_img)
    
            try:
                resized_bg = self.bg_images_list[self.current_bg_index].resize((pixel_width, pixel_height), Image.Resampling.LANCZOS)
                exported_image = resized_bg.convert("RGBA")
                exported_image.paste(final_image, (0, 0), final_image)
            except Exception as e:
                print(f"Exporting without background. Reason: {e}")
                exported_image = final_image
            
            file_path = filedialog.asksaveasfilename(
                defaultextension=".png",
                filetypes=[("PNG files", "*.png"), ("All files", "*.*")],
                title="Save Map Image As"
            )

            if file_path:
                exported_image.save(file_path)
                print(f"Map image successfully exported to {file_path}")

        except Exception as e:
            messagebox.showerror("Error", f"Error during image export: {e}")

    # --- NEW FEATURE: Export Block List ---
    def export_block_list(self,event=None):
        """Exports a text file listing the counts of all used blocks."""
        try:
            # Get unique elements and their counts from the numpy array
            # return_counts=True is efficient
            unique, counts = np.unique(self.map_data, return_counts=True)
            counts_dict = dict(zip(unique, counts))
            
            # Remove empty tile (index 0) if present
            if 0 in counts_dict:
                del counts_dict[0]
            
            if not counts_dict:
                messagebox.showinfo("Export List", "Map is empty.")
                return

            # Create reverse lookup for names: Index -> Name
            index_to_name = {v: k for k, v in self.tile_name_to_index.items()}
            
            lines = ["All the blocks used:\n"]
            
            # Sort by count descending for better readability
            sorted_items = sorted(counts_dict.items(), key=lambda item: item[1], reverse=True)
            
            for idx, count in sorted_items:
                name = index_to_name.get(idx, f"Unknown Tile {idx}")
                # Capitalize words (e.g., "dirt_block" -> "Dirt Block")
                display_name = name.replace("_", " ").title()
                lines.append(f"{count} - {display_name}")
            
            output_text = "\n".join(lines)
            
            # Save file dialog
            file_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                filetypes=[("Text Files", "*.txt")],
                title="Export Block List"
            )
            
            if file_path:
                with open(file_path, "w") as f:
                    f.write(output_text)
                messagebox.showinfo("Export List", f"Block list saved to {file_path}")
                
        except Exception as e:
            messagebox.showerror("Error", f"Error exporting list: {e}")

    def zoom(self, factor):
        new_zoom = self.zoom_level * factor
        if 0.5 <= new_zoom <= 4.0:
            self.zoom_level = new_zoom
            self.current_tile_size = self.INITIAL_TILE_SIZE * self.zoom_level
            
            # CLEAR CACHE: Pixel size changed, so old images are invalid
            self.render_cache.clear()
            
            self.full_redraw_map()
        
    def on_mouse_wheel(self, event):
        if event.num == 5 or event.delta < 0:
            self.zoom(1 / 1.1) 
        elif event.num == 4 or event.delta > 0:
            self.zoom(1.1) 

if __name__ == "__main__":
    root = tk.Tk()
    windll.shcore.SetProcessDpiAwareness(1)
    app = TileBuilderApp(root)
    root.geometry("1200x800")
    root.minsize(800, 600)
    root.state("zoomed")
    root.config(bg=TileBuilderApp.C_BG_MAIN)
    root.mainloop()
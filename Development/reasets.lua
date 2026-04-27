-- @description reasets - REAper track-SETS manager
-- @version 1.1
-- @author captaincurrie
-- @license GNU General Public License
-- @date 2026-03-13
-- @about reasets - REAper track-SETS manager

--[[ 
# REASETS - REAPER TRACK SET SELECTOR
A lightweight, per-project track set management system for REAPER.

## CORE CONCEPT:
A "set" is a saved collection of REAPER tracks with a descriptive name.
Sets allow quick recall of track selection states. Each set stores:
- Unique ID (timestamp-based)
- User-defined name
- Array of track unique IDs (stored in track extended state)
- Selected color (derived from first track's color)

Tracks are identified by unique IDs stored in their extended state (P_EXT:REASETS_TRACK_ID).
This ensures sets remain valid even when tracks are reordered, added, or removed.

## ARCHITECTURE:

### STATE MANAGEMENT:
The program uses a centralized STATE table with dirty flagging for performance:
- `sets`: Array of set objects
- `current_project`: GUID for detecting project changes
- `view`: Current view mode ("main" or "settings")
- `editing_set_id`: Set currently being renamed (nil when not editing)
- `dirty`: Flag to trigger redraw only when needed
- `cached_boxes`: Cached set box positions (invalidated on layout changes)
- `scroll_offset`: Main view scroll position
- `settings_scroll_offset`: Settings panel scroll position
- Mouse chord state: `left_click_set_id`, `chord_triggered`
- Text editing state: `editing_text`, `cursor_position`, `selection_start/end`
- Mode state: `ab_mode`, `auto_hide_tcp`, `auto_hide_mcp`

### PERSISTENCE:
- `.reasets/sets`: JSON file storing sets per-project
- `.reasets/undo`: JSON file storing undo/redo history per-project
- Debounced saves (500ms delay) to reduce I/O operations
- Automatic reload on project change detection
- Mode preferences saved per-project

### UNDO/REDO SYSTEM:
Command-based undo with operation types:
- CREATE: Records set_id, name, trackIndices, selectedColor
- DELETE: Records full set state for restoration
- RENAME: Records old_name and new_name
- OVERWRITE: Records old/new trackIndices and selectedColor
- RECOLOR: Records old_color and new_color
History is capped at MAX_UNDO_HISTORY entries per project.

## USER INTERFACE:

### MAIN VIEW LAYOUT:
- Sticky toolbar at top or bottom (configurable, can be hidden)
- Vertically scrollable list of sets (mouse wheel scrolling)
- Sets displayed as colored boxes with centered text
- Box width: Responsive (80% of window width, clamped to MIN/MAX_BOX_WIDTH)
- Box color states:
  * Default: COLOR_BOX (unselected)
  * Selected: Per-set color from first track (or fallback)
  * Partial: COLOR_BOX_PARTIAL (some tracks selected)
  * Border: Brightened version of selected color
- Text color: Auto-adjusts based on box brightness (light/dark)
- Create button: Plus sign (+) below last set or at center if no sets
- Growth direction: Configurable (top-down or bottom-up)

### TOOLBAR:
- Position: Configurable (top, bottom, or hidden)
- Sticky: Always visible, not affected by scrolling
- Sort by color button:
  * Icon: Color palette with paint spots
  * Left-click: Sort sets once by color (hue, saturation, lightness)
  * Right-click: Toggle auto-sort mode (new sets automatically sorted)
  * Visual indicator: Button color changes when auto-sort is active
  * Persistent state: Auto-sort preference saved per project
- A/B mode button:
  * Icon: "A/B" text
  * Left-click: Toggle A/B mode (exclusive solo on click)
  * Visual indicator: Button color and dot when active
  * Persistent state: A/B mode preference saved per project
- TCP hide button:
  * Icon: Vertical tracks (Track Control Panel)
  * Left-click: Toggle auto-hide tracks not in selected set (TCP only)
  * Visual indicator: Button color and dot when active
  * Persistent state: TCP auto-hide preference saved per project
- MCP hide button:
  * Icon: Vertical faders (Mixer Control Panel)
  * Left-click: Toggle auto-hide tracks not in selected set (MCP only)
  * Visual indicator: Button color and dot when active
  * Persistent state: MCP auto-hide preference saved per project

### EDIT MODE:
When editing a set name (right-click on set):
- Text cursor shown as pipe character (|) at cursor_position
- Full text selection support with mouse dragging
- Selection highlight: COLOR_SELECTION_HIGHLIGHT
- Double-click in edit mode: Select all text
- Click outside or Enter: Save and exit
- Escape: Cancel or clear selection

### SETTINGS PANEL:
Right-click outside sets toggles settings view:
- Font size: +/- buttons (range: 8-32)
- Growth direction: "Down" / "Up" toggle buttons
- Toolbar position: "Top" / "Bottom" / "Hide" toggle buttons
- Show All Tracks Set: "ON" / "OFF" toggle button
- Sliders (draggable):
  * Set Width (MIN_BOX_WIDTH to MAX_BOX_WIDTH)
  * Set Height (30 to 100)
  * Scroll Speed (5 to 50)
- Scrollable when content exceeds window height
- Right-click again to return to main view

## OPERATING MODES:

### DEFAULT MODE:
- Left-click set: Toggle selection (select or deselect)
- Selecting a set: Changes track selection to match set
- Deselecting a set: Clears all track selections

### A/B MODE:
- Enabled via toolbar A/B button
- Left-click unselected set: Select tracks AND exclusively solo them (unsolo all others)
- Left-click selected set: Deselect all tracks AND unsolo all tracks
- Purpose: Quick A/B comparison between different track groups
- State persists per-project

### TCP AUTO-HIDE MODE:
- Enabled via toolbar TCP button
- When a set is selected: Automatically hide all tracks NOT in the set (TCP only)
- When set is deselected: Show all tracks again
- Purpose: Clean up Track Control Panel to show only relevant tracks
- State persists per-project
- Can be combined with A/B mode and MCP auto-hide

### MCP AUTO-HIDE MODE:
- Enabled via toolbar MCP button
- When a set is selected: Automatically hide all tracks NOT in the set (MCP only)
- When set is deselected: Show all tracks again
- Purpose: Clean up Mixer Control Panel to show only relevant tracks
- State persists per-project
- Can be combined with A/B mode and TCP auto-hide

## MOUSE CONTROLS:

### MAIN VIEW:
- **Left-click set**: Toggle selection (behavior depends on active modes)
- **Ctrl+Left-click set**: Mute/unmute all tracks in set (toggle based on current state)
- **Left-hold + Right-click set**: OVERWRITE set with current track selection (mouse chord)
- **Left-hold + Middle-click set**: RANDOMIZE set color (mouse chord)
- **Right-click set**: Enter edit mode for renaming
- **Ctrl+Right-click set**: Solo/unsolo all tracks in set (toggle based on current state)
- **Right-click outside**: Toggle settings panel (or exit edit mode if editing)
- **Middle-click set**: Delete set immediately
- **Click create button (+)**: Create new set from current selection
- **Double-click outside**: Create new set (alternative to create button)
- **Mouse wheel**: Scroll main view

### TOOLBAR:
- **Left-click sort button**: Sort sets once by color
- **Right-click sort button**: Toggle auto-sort mode (automatically sorts new sets)
- **Left-click A/B button**: Toggle A/B mode (exclusive solo on click)
- **Left-click TCP button**: Toggle TCP auto-hide mode
- **Left-click MCP button**: Toggle MCP auto-hide mode
- **Hover any button**: Button highlights to indicate interactivity

### EDIT MODE:
- **Left-click**: Position cursor at click location
- **Left-drag**: Select text range
- **Double-click**: Select all text
- **Enter**: Confirm rename
- **Escape**: Cancel rename (or clear selection if text selected)

### SETTINGS VIEW:
- **Click buttons**: Adjust font size, change growth direction, toolbar position
- **Click/drag sliders**: Adjust box dimensions and scroll speed
- **Mouse wheel**: Scroll settings panel
- **Right-click**: Return to main view

## KEYBOARD INPUT (Edit Mode Only):
- **Printable characters (32-126)**: Insert at cursor or replace selection
- **Backspace**: Delete before cursor or delete selection
- **Delete**: Delete after cursor or delete selection
- **Enter/Return**: Confirm rename and exit edit mode
- **Escape**: Cancel rename or clear selection

## SORTING SYSTEM:
- Manual sort: Left-click toolbar sort button to sort once
- Auto-sort: Right-click toolbar sort button to enable/disable
- Sort algorithm: HSL color space (hue → saturation → lightness)
- Persistence: Auto-sort state saved per project
- New sets: Automatically sorted if auto-sort is enabled
- Visual feedback: Sort button changes color when auto-sort is active

## PERFORMANCE OPTIMIZATIONS:
- Dirty flagging: Redraws only when STATE.dirty is true
- Cached box positions: Recalculated only on layout changes
- Window resize detection: Cached gfx.w/gfx.h tracking
- Frame rate limiting: TARGET_FPS (20 FPS) with MIN_FRAME_TIME
- Debounced file saves: SAVE_DELAY (500ms)
- Optimized JSON encoding: Uses table.concat for efficiency
- Input processing: Always runs (even between frames) for responsiveness
- Rendering: Rate-limited independently from input
- Toolbar rendering: Separate from scrollable content
- Hover state tracking: Only redraws when hover changes

## COLOR SYSTEM:
- Sets inherit color from first track in their selection
- Colors stored in hex format: "RRGGBB"
- Auto-brightening for borders: 30% brighter than base color
- Text color adapts: Dark text on light backgrounds, light text on dark
- Luminance calculation: ITU-R BT.709 standard (threshold: 0.6)
- Native color conversion: Uses reaper.ColorFromNative() for track colors

## MOUSE CHORD DETECTION:
The program implements a sophisticated chord system:
1. Left-press on set stores `left_click_set_id`
2. If right-press occurs while left is held: OVERWRITE operation
3. If middle-press occurs while left is held: RANDOMIZE COLOR operation
4. Sets `chord_triggered` flag to prevent normal left-release action
5. Left-release without chord: Normal select/deselect operation
This prevents accidental selections during chord operations.

## TEXT EDITING IMPLEMENTATION:
Cursor and selection state:
- `cursor_position`: Integer position (0 = before first char)
- `selection_start/end`: Range of selected text (nil if no selection)
- `selection_dragging`: Mouse drag in progress
- `editing_text_selected`: All text selected (legacy flag)
Selection rendering: Highlight drawn before text, cursor hidden during selection

## SCROLLING BEHAVIOR:
Both main and settings views support independent scrolling:
- Scroll offset clamped to [0, max_scroll]
- Max scroll calculated from total content height
- Helper text and create button included in scroll calculation
- Settings scroll resets to 0 when panel opens
- Scroll speed configurable via settings slider

## FILE I/O:
- Project directory: Uses .reasets subdirectory in project folder
- File format: Custom JSON encoder/decoder (no external dependencies)
- Safe file operations: Check existence before read, handle errors gracefully
- Version field in saved data for future compatibility
- Automatic directory creation if missing

## CONFIGURATION (CONFIG table):
All magic numbers stored in CONFIG for easy tuning:
- Layout: PADDING, BOX_SPACING, BOX_WIDTH_PERCENT
- Constraints: MIN/MAX_BOX_WIDTH, MIN_BOX_HEIGHT
- Colors: All UI colors in hex format
- Performance: TARGET_FPS, MIN_FRAME_TIME, SAVE_DELAY
- Interaction: DOUBLE_CLICK_TIME, SCROLL_SPEED
- Create button: SIZE, SPACING, THICKNESS
- Toolbar: HEIGHT, BUTTON_SIZE, COLORS, SPACING

## IMPLEMENTATION NOTES:
- Written in Lua for REAPER ReaScript
- Uses built-in gfx library (no external dependencies)
- Single-file architecture (~1500 lines)
- No REAPER undo integration (uses internal undo system)
- Dockable window via gfx.init()
- Project change detection via GUID comparison
- Handles non-existent tracks gracefully (filters invalid indices)
- Track visibility API: B_SHOWINTCP (TCP) and B_SHOWINMIXER (MCP)
- Efficient track operations: Uses bulk REAPER commands where possible
--]]

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

local PROGNAME = "reasets"

-- Extended state key for storing unique track IDs
local EXT_STATE_KEY = "P_EXT:REASETS_TRACK_ID"

-- Mouse button and modifier constants
local MOUSE = {
	LEFT = 1,
	RIGHT = 2,
	CTRL = 4,
	CMD = 8,
	SHIFT = 16,
	MIDDLE = 64,
}

local CONFIG = {
	DEFAULT_SETTINGS_FONT_SIZE = 14,
	DEFAULT_BOX_WIDTH = 200,
	DEFAULT_BOX_HEIGHT = 40,
	DEFAULT_FONT_SIZE = 16,
	DEFAULT_FONT = "Arial",
	DEFAULT_GROWTH_DIR = "down", -- "up" or "down"
	PADDING = 10,
	BOX_SPACING = 10,
	BOX_WIDTH_PERCENT = 0.8, -- Percentage of window width (80%)
	MIN_BOX_WIDTH = 50, -- Minimum box width
	MAX_BOX_WIDTH = 300, -- Maximum box width
	SETTINGS_PANEL_WIDTH = 350,
	SETTINGS_PANEL_HEIGHT = 500,
	SETTINGS_BUTTON_WIDTH = 60,
	SETTINGS_BUTTON_HEIGHT = 30,
	SETTINGS_SLIDER_WIDTH = 200,
	SETTINGS_SLIDER_HEIGHT = 20,
	SETTINGS_MIN_SLIDER_WIDTH = 100,
	SETTINGS_MIN_PANEL_WIDTH = 180, -- Minimum width for settings panel
	SETTINGS_PANEL_PADDING = 20, -- Padding around settings content inside border
	SETTINGS_PANEL_BORDER_COLOR = "5b5b5b", -- Border color for settings panel
	SCROLL_SPEED = 10, -- Default scroll speed
	DOUBLE_CLICK_TIME = 0.3, -- Time window for double-click detection (seconds)
	BORDER_THICKNESS = 2, -- Border thickness in pixels

	-- Drag and drop
	DRAG_LONG_PRESS_TIME = 0.1, -- Time to hold before drag starts (150ms)
	DRAG_THRESHOLD = 5, -- Pixels to move before drag activates
	DRAG_GHOST_OPACITY = 0.5, -- Opacity of dragged set ghost (50%)
	DRAG_AUTO_SCROLL_ZONE = 60, -- Pixels from edge to trigger auto-scroll
	DRAG_AUTO_SCROLL_SPEED = 8, -- Scroll speed multiplier when dragging
	DRAG_INSERTION_LINE_THICKNESS = 4, -- Thickness of insertion indicator
	COLOR_DRAG_INSERTION = "6a9bd4", -- Blue insertion line color

	-- Persistence
	REASETS_DIR = "." .. PROGNAME,
	FILE_SETS_BASENAME = "sets",


	-- Performance
	TARGET_FPS = 20, -- Target frame rate
	MIN_FRAME_TIME = 1 / 20, -- Minimum time between frames (33ms for 30 FPS)

	-- Create Set Button
	CREATE_SET_BUTTON_SIZE = 25,
	CREATE_SET_BUTTON_SPACING = 30, -- Distance from last set or center
	CREATE_SET_BUTTON_THICKNESS = 3, -- Line thickness
	CREATE_SET_BUTTON_COLOR = "838a8a", -- Color of the plus sign

	-- Toolbar
	TOOLBAR_HEIGHT = 30,
	TOOLBAR_BUTTON_SIZE = 24,
	TOOLBAR_BUTTON_SIZE_MIN = 12,
	TOOLBAR_BUTTON_SIZE_MAX = 28,
	TOOLBAR_BUTTON_PADDING = 3,
	TOOLBAR_SPACING = 2, -- Space between buttons within a group
	TOOLBAR_GROUP_SPACING = 12, -- Space between button groups
	TOOLBAR_BG_COLOR = "3b3b3b", -- Background color of toolbar
	TOOLBAR_BUTTON_COLOR = "555555",
	TOOLBAR_BUTTON_HOVER_COLOR = "575757",
	TOOLBAR_BUTTON_ACTIVE_COLOR = "6a9bd4",
	TOOLBAR_ICON_COLOR = "cccccc",

	-- Colors (hex format "RRGGBB")
	COLOR_BG = "3e3e3e",
	COLOR_BOX = "3e3e3e",
	COLOR_BOX_SELECTED = "848484",
	COLOR_BOX_PARTIAL = "3e3e3e",
	COLOR_BOX_BORDER = "5b5b5b",
	COLOR_BOX_BORDER_SELECTED = "787878",
	COLOR_TEXT = "FFFFFF",
	COLOR_TEXT_DARK = "333333",
	COLOR_TEXT_GREY = "cdcdcd",
	COLOR_SELECTION_HIGHLIGHT = "6680B3",
	COLOR_ALL_TRACKS_SET = "646464", -- Color for "All Tracks" set

	-- Special Set ID
	ALL_TRACKS_SET_ID = -1, -- Special ID for "All Tracks" set
}

-- ============================================================================
-- COLOR MAP
-- Color map: if a set name contains any of these keys (case-insensitive
-- substring match), the mapped color is applied at creation and on rename.
-- User-defined color changes (e.g. randomize) are not overridden.
-- ============================================================================

local COLOR_MAP = {
	["Recording"] = "FF0000",
}

-- Returns the mapped color hex string for the given name, or nil if no match.
-- On multiple matches the longest key wins to avoid "Main" swallowing "Main Bus".
local function get_color_for_name(name)
	if not name then
		return nil
	end
	local lower_name = name:lower()
	local best_color = nil
	local best_len   = 0
	for key, color in pairs(COLOR_MAP) do
		local lower_key = key:lower()
		if lower_name:find(lower_key, 1, true) then
			if #lower_key > best_len then
				best_len   = #lower_key
				best_color = color
			end
		end
	end
	return best_color
end

-- ============================================================================
-- UTILITY: ID GENERATION (must be defined before FRAME-LEVEL CACHE)
-- ============================================================================

local function generate_set_id()
	return math.floor(reaper.time_precise() * 1000000)
end

-- ============================================================================
-- FRAME-LEVEL CACHE
-- ============================================================================

-- Cache that is invalidated each time we need fresh track data
local FRAME_CACHE = {
	track_map = nil, -- id -> track mapping
	track_count = nil, -- cached track count
	selected_count = nil, -- cached selected track count
}

local function invalidate_frame_cache()
	FRAME_CACHE.track_map = nil
	FRAME_CACHE.track_count = nil
	FRAME_CACHE.selected_count = nil
end

local function build_track_map()
	local map = {}
	local track_count = reaper.CountTracks(0)
	for i = 0, track_count - 1 do
		local track = reaper.GetTrack(0, i)
		if track then
			local retval, track_id = reaper.GetSetMediaTrackInfo_String(track, EXT_STATE_KEY, "", false)
			if track_id ~= "" then
				if map[track_id] then
					-- Duplicate ID detected (from track duplication in REAPER)
					-- First track keeps the original ID, this one gets a new one
					local new_id = tostring(generate_set_id())
					reaper.GetSetMediaTrackInfo_String(track, EXT_STATE_KEY, new_id, true)
					map[new_id] = track
				else
					map[track_id] = track
				end
			end
		end
	end
	return map
end

local function get_cached_track_by_id(track_id)
	if not track_id then
		return nil
	end

	if not FRAME_CACHE.track_map then
		FRAME_CACHE.track_map = build_track_map()
	end

	return FRAME_CACHE.track_map[track_id]
end

local function get_cached_track_count()
	if not FRAME_CACHE.track_count then
		FRAME_CACHE.track_count = reaper.CountTracks(0)
	end
	return FRAME_CACHE.track_count
end

local function get_cached_selected_count()
	if not FRAME_CACHE.selected_count then
		FRAME_CACHE.selected_count = reaper.CountSelectedTracks2(0, true)
	end
	return FRAME_CACHE.selected_count
end

-- ============================================================================
-- STATE
-- ============================================================================

local STATE = {
	sets = {}, -- Array of {id, name, trackIndices}
	current_project = nil, -- GUID of current project
	selected_set_id = nil, -- Currently selected set
	last_save_time = 0,
	last_change_time = 0, -- Track when last change was made (for debounced saves)
	last_click_time = 0,
	last_create_button_click_time = 0, -- Track last create button click for double-click
	mouse_was_down = false,
	right_click_was_down = false,
	middle_click_was_down = false,
	view = "main", -- "main" or "settings"
	editing_set_id = nil, -- ID of set being renamed
	editing_text = "",
	editing_text_selected = false, -- Whether all editing text is selected
	cursor_position = 0, -- Position of cursor in editing_text (0 = before first char)
	selection_start = nil, -- Start position of text selection (nil if no selection)
	selection_end = nil, -- End position of text selection (nil if no selection)
	selection_dragging = false, -- Whether currently dragging to select text
	create_button_pos = { x = 0, y = 0 }, -- Position of create set button

	settings_font_size = CONFIG.DEFAULT_SETTINGS_FONT_SIZE,

	-- Settings
	box_width = CONFIG.DEFAULT_BOX_WIDTH,
	box_height = CONFIG.DEFAULT_BOX_HEIGHT,
	font_size = CONFIG.DEFAULT_FONT_SIZE,
	growth_direction = CONFIG.DEFAULT_GROWTH_DIR,
	show_all_tracks_set = false, -- Whether to show "All Tracks" set at top
	toolbar_position = "top", -- "top", "bottom", or "hide"
	auto_sort_by_color = false, -- Whether to auto-sort new sets by color
	use_first_track_name = true, -- Whether to use first track name when creating sets

	-- Performance optimization
	dirty = true, -- Flag to track if redraw is needed
	cached_boxes = nil, -- Cached box positions
	cached_gfx_size = { w = 0, h = 0 }, -- Track window size changes
	pending_save = false, -- Flag for debounced saves
	last_mouse_x = -1,
	last_mouse_y = -1,
	last_mouse_cap = 0,
	last_frame_time = 0, -- Track last frame time for rate limiting

	-- Scrolling
	scroll_offset = 0, -- Current scroll position
	last_mouse_wheel = 0, -- Track mouse wheel state
	scroll_speed = CONFIG.SCROLL_SPEED, -- Configurable scroll speed

	-- Settings UI
	settings_dragging_slider = nil, -- Which slider is being dragged
	settings_cached_elements = nil, -- Cached settings UI elements
	settings_scroll_offset = 0, -- Scroll offset for settings panel
	settings_last_mouse_wheel = 0, -- Track mouse wheel in settings

	-- Toolbar state
	toolbar_hover_button = nil, -- Which toolbar button is being hovered
	toolbar_buttons = {}, -- Cached button positions from last render

	-- Dock state
	is_docked = false, -- Whether window is docked

	-- Help view
	help_scroll_offset = 0,
	help_last_mouse_wheel = 0,
	help_max_scroll = 0, -- Updated each draw; used to clamp wheel input immediately

	-- Toolbar
	toolbar_button_size = CONFIG.TOOLBAR_BUTTON_SIZE,

	-- Mode state
	ab_mode = false, -- Whether A/B mode is active (exclusive solo on click)
	auto_hide_tcp = false, -- Whether to auto-hide tracks not in selected set (TCP)
	auto_hide_mcp = false, -- Whether to auto-hide tracks not in selected set (MCP)

	-- Mouse chord state
	left_click_set_id = nil, -- Set ID that was left-clicked (waiting for release or chord)
	chord_triggered = false, -- Whether a mouse chord was triggered

	-- Drag and drop state
	dragging_set_id = nil, -- ID of set being dragged
	drag_start_time = nil, -- Time when mouse first pressed on set
	drag_start_y = nil, -- Initial mouse Y position
	drag_start_index = nil, -- Original index in sets array
	drag_initiated = false, -- Whether drag has actually started (threshold met)
	drag_hover_insert_index = nil, -- Current insertion position (where set will be dropped)
	drag_ghost_y = nil, -- Y position of ghost set following cursor
}

-- ============================================================================
-- UTILITY FUNCTIONS
-- ============================================================================

local function get_project_path()
	-- Get the full path to the .rpp file
	local _, project_file = reaper.EnumProjects(-1, "")
	if project_file == "" then
		return nil
	end

	-- Extract directory path from the full file path
	-- Works on both Windows (\ or /) and Unix (/)
	local dir = project_file:match("^(.+)[/\\][^/\\]+$")
	return dir
end

local function get_current_project_id()
	-- Get the full path to the .rpp file
	local _, project_file = reaper.EnumProjects(-1, "")
	if project_file == "" then
		return nil
	end

	-- Use the full project file path as the unique identifier
	return project_file
end

local function file_exists(path)
	local f = io.open(path, "r")
	if f then
		io.close(f)
		return true
	end
	return false
end

local function read_file(path)
	local f = io.open(path, "r")
	if not f then
		return nil
	end
	local content = f:read("*a")
	io.close(f)
	return content
end

local function write_file(path, content)
	local f = io.open(path, "w")
	if not f then
		return false
	end
	f:write(content)
	io.close(f)
	return true
end

-- Optimized JSON serialization using table.concat
local function json_encode(t)
	if type(t) == "table" then
		local parts = {}
		local is_array = true
		local max_idx = 0
		local count = 0

		-- Check if it's an array
		for k, v in pairs(t) do
			count = count + 1
			if type(k) ~= "number" or k < 1 or k ~= math.floor(k) then
				is_array = false
				break
			end
			if k > max_idx then
				max_idx = k
			end
		end

		-- Also check for sparse arrays (gaps with nil values)
		if is_array and max_idx ~= count then
			is_array = false
		end

		if is_array and max_idx > 0 then
			-- Array encoding
			parts[1] = "["
			for i = 1, max_idx do
				if i > 1 then
					parts[#parts + 1] = ","
				end
				parts[#parts + 1] = json_encode(t[i])
			end
			parts[#parts + 1] = "]"
		elseif is_array and count == 0 then
			-- Empty array
			return "[]"
		else
			-- Object encoding
			parts[1] = "{"
			local first = true
			for k, v in pairs(t) do
				if not first then
					parts[#parts + 1] = ","
				end
				parts[#parts + 1] = '"'
				parts[#parts + 1] = tostring(k)
				parts[#parts + 1] = '":'
				parts[#parts + 1] = json_encode(v)
				first = false
			end
			parts[#parts + 1] = "}"
		end
		return table.concat(parts)
	elseif type(t) == "string" then
		return '"' .. t:gsub('"', '\\"') .. '"'
	elseif type(t) == "number" then
		return tostring(t)
	elseif type(t) == "boolean" then
		return t and "true" or "false"
	else
		return "null"
	end
end

-- Simple JSON decoding
local function json_decode(str)
	local pos = 1

	-- Declare all functions first to allow mutual recursion
	local parse_value, parse_object, parse_array, parse_string, parse_number, parse_boolean, parse_null

	local function skip_whitespace()
		while pos <= #str and str:sub(pos, pos):match("%s") do
			pos = pos + 1
		end
	end

	function parse_value()
		skip_whitespace()
		local ch = str:sub(pos, pos)

		if ch == "{" then
			return parse_object()
		elseif ch == "[" then
			return parse_array()
		elseif ch == '"' then
			return parse_string()
		elseif ch == "t" or ch == "f" then
			return parse_boolean()
		elseif ch == "n" then
			return parse_null()
		else
			return parse_number()
		end
	end

	function parse_object()
		pos = pos + 1 -- skip {
		local obj = {}
		skip_whitespace()

		if str:sub(pos, pos) == "}" then
			pos = pos + 1
			return obj
		end

		while true do
			skip_whitespace()
			local key = parse_string()
			skip_whitespace()
			pos = pos + 1 -- skip :
			local value = parse_value()
			obj[key] = value
			skip_whitespace()

			if str:sub(pos, pos) == "}" then
				pos = pos + 1
				break
			end
			pos = pos + 1 -- skip ,
		end

		return obj
	end

	function parse_array()
		pos = pos + 1 -- skip [
		local arr = {}
		skip_whitespace()

		if str:sub(pos, pos) == "]" then
			pos = pos + 1
			return arr
		end

		while true do
			table.insert(arr, parse_value())
			skip_whitespace()

			if str:sub(pos, pos) == "]" then
				pos = pos + 1
				break
			end
			pos = pos + 1 -- skip ,
			skip_whitespace()
		end

		return arr
	end

	function parse_string()
		pos = pos + 1 -- skip opening "
		local result = ""

		while pos <= #str do
			local ch = str:sub(pos, pos)
			if ch == '"' then
				pos = pos + 1
				break
			elseif ch == "\\" then
				pos = pos + 1
				local escaped = str:sub(pos, pos)
				if escaped == "n" then
					result = result .. "\n"
				elseif escaped == "t" then
					result = result .. "\t"
				elseif escaped == '"' then
					result = result .. '"'
				else
					result = result .. escaped
				end
			else
				result = result .. ch
			end
			pos = pos + 1
		end

		return result
	end

	function parse_number()
		local start = pos
		if str:sub(pos, pos) == "-" then
			pos = pos + 1
		end
		while pos <= #str and str:sub(pos, pos):match("[0-9.]") do
			pos = pos + 1
		end
		return tonumber(str:sub(start, pos - 1))
	end

	function parse_boolean()
		if str:sub(pos, pos + 3) == "true" then
			pos = pos + 4
			return true
		else
			pos = pos + 5
			return false
		end
	end

	function parse_null()
		pos = pos + 4
		return nil
	end

	return parse_value()
end

-- ============================================================================
-- SET MANAGEMENT
-- ============================================================================

-- Forward declaration: defined in FILE PERSISTENCE section below
local request_save

-- Get or create a unique ID for a track using extended state
local function get_track_unique_id(track)
	if not track then
		return nil
	end

	local retval, track_id = reaper.GetSetMediaTrackInfo_String(track, EXT_STATE_KEY, "", false)

	-- If track has no ID, generate one
	if track_id == "" then
		track_id = tostring(generate_set_id())
		reaper.GetSetMediaTrackInfo_String(track, EXT_STATE_KEY, track_id, true)
		return track_id
	end

	-- Check for duplicate IDs using the frame cache map if available
	-- (happens when tracks are duplicated in REAPER, which copies extended state)
	if FRAME_CACHE.track_map then
		local existing_track = FRAME_CACHE.track_map[track_id]
		if existing_track and existing_track ~= track then
			track_id = tostring(generate_set_id())
			reaper.GetSetMediaTrackInfo_String(track, EXT_STATE_KEY, track_id, true)
			FRAME_CACHE.track_map[track_id] = track
		end
	end

	return track_id
end

-- Find a track by its unique ID (uses frame cache for performance)
local function find_track_by_id(track_id)
	return get_cached_track_by_id(track_id)
end

-- ============================================================================
-- ALL TRACKS SET MODULE
-- ============================================================================

local AllTracksSet = {}

function AllTracksSet.get_all_track_ids()
	local all_track_ids = {}
	local track_count = get_cached_track_count()
	for i = 0, track_count - 1 do
		local track = reaper.GetTrack(0, i)
		if track then
			local track_id = get_track_unique_id(track)
			if track_id then
				table.insert(all_track_ids, track_id)
			end
		end
	end
	return all_track_ids
end

function AllTracksSet.is_fully_selected()
	local track_count = get_cached_track_count()
	local selected_count = get_cached_selected_count()
	return track_count > 0 and selected_count == track_count
end

function AllTracksSet.is_partially_selected()
	local selected_count = get_cached_selected_count()
	return selected_count > 0 and not AllTracksSet.is_fully_selected()
end

function AllTracksSet.handle_click()
	local is_all_selected = AllTracksSet.is_fully_selected()
	local all_track_ids = AllTracksSet.get_all_track_ids()

	reaper.PreventUIRefresh(1)

	if is_all_selected then
		-- Deselect all tracks
		set_selected_tracks({})

		-- If in A/B mode, unsolo all tracks
		if STATE.ab_mode then
			reaper.SoloAllTracks(0)
		end

		-- If auto-hide is enabled, show all tracks
		if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
			show_all_tracks(STATE.auto_hide_tcp, STATE.auto_hide_mcp)
		end
	else
		-- Select all tracks
		set_selected_tracks(all_track_ids)

		-- If in A/B mode, solo all tracks
		if STATE.ab_mode then
			for _, track_id in ipairs(all_track_ids) do
				local track = find_track_by_id(track_id)
				if track then
					reaper.SetMediaTrackInfo_Value(track, "I_SOLO", 1)
				end
			end
		end

		-- If auto-hide is enabled, show all tracks (they're all in the "set")
		if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
			show_all_tracks(STATE.auto_hide_tcp, STATE.auto_hide_mcp)
		end
	end

	reaper.PreventUIRefresh(-1)
	reaper.UpdateArrange()

	STATE.dirty = true
end

function AllTracksSet.draw(box, scroll_offset)
	local is_all_selected = AllTracksSet.is_fully_selected()
	local is_partial = AllTracksSet.is_partially_selected()

	local base_color = CONFIG.COLOR_ALL_TRACKS_SET
	local box_color
	if is_all_selected then
		box_color = base_color
	elseif is_partial then
		box_color = CONFIG.COLOR_BOX_PARTIAL
	else
		box_color = CONFIG.COLOR_BOX
	end

	local border_color = brighten_color(base_color)
	local visible_y = box.y - scroll_offset

	draw_rect_filled(box.x, visible_y, box.w, box.h, box_color)
	draw_rect_border(box.x, visible_y, box.w, box.h, border_color)

	-- Determine text color
	local text_color = CONFIG.COLOR_TEXT
	if is_all_selected and is_color_light(base_color) then
		text_color = CONFIG.COLOR_TEXT_DARK
	end

	-- Draw "All Tracks" text, truncated if necessary
	local text = truncate_text_with_ellipsis("All Tracks", box.w - CONFIG.PADDING * 2)
	local text_width = gfx.measurestr(text)
	local text_x = box.x + (box.w - text_width) / 2
	draw_text(text_x, visible_y + (box.h - gfx.texth) / 2, text, text_color)
end

-- ============================================================================
-- COLOR UTILITIES
-- ============================================================================

local function get_track_color(track)
	if not track then
		return CONFIG.COLOR_BOX_SELECTED -- fallback
	end

	local color = reaper.GetTrackColor(track)
	if color == 0 then
		return CONFIG.COLOR_BOX_SELECTED -- track has no color
	end

	-- Convert native color to RGB using Reaper's built-in function
	local r, g, b = reaper.ColorFromNative(color)

	return string.format("%02X%02X%02X", r, g, b)
end

local function brighten_color(hex_color, factor)
	factor = factor or 1.3 -- default 30% brighter

	local r = tonumber(hex_color:sub(1, 2), 16)
	local g = tonumber(hex_color:sub(3, 4), 16)
	local b = tonumber(hex_color:sub(5, 6), 16)

	-- Brighten by factor, clamping to 255
	r = math.min(255, math.floor(r * factor))
	g = math.min(255, math.floor(g * factor))
	b = math.min(255, math.floor(b * factor))

	return string.format("%02X%02X%02X", r, g, b)
end

local function generate_random_color()
	-- Generate a random RGB color in hex format
	local r = math.random(0, 255)
	local g = math.random(0, 255)
	local b = math.random(0, 255)
	return string.format("%02X%02X%02X", r, g, b)
end

local function is_color_light(hex_color)
	-- Calculate relative luminance to determine if color is light
	local r = tonumber(hex_color:sub(1, 2), 16) / 255
	local g = tonumber(hex_color:sub(3, 4), 16) / 255
	local b = tonumber(hex_color:sub(5, 6), 16) / 255

	-- Relative luminance formula (ITU-R BT.709)
	local luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b

	-- Consider color "light" if luminance is above 0.6
	return luminance > 0.6
end

local function get_selected_tracks()
	local track_ids = {}
	local track_count = reaper.CountTracks(0)

	for i = 0, track_count - 1 do
		local track = reaper.GetTrack(0, i)
		if track and reaper.IsTrackSelected(track) then
			local track_id = get_track_unique_id(track)
			if track_id then
				table.insert(track_ids, track_id)
			end
		end
	end

	return track_ids
end

local function set_selected_tracks(track_ids)
	reaper.PreventUIRefresh(1)

	-- Unselect all tracks using action (faster than manual iteration)
	reaper.Main_OnCommand(40297, 0) -- Track: Unselect all tracks

	-- Select specified tracks
	for _, track_id in ipairs(track_ids) do
		local track = find_track_by_id(track_id)
		if track then
			reaper.SetTrackSelected(track, true)
		end
	end

	reaper.PreventUIRefresh(-1)
	reaper.UpdateArrange()

	-- Invalidate cache since selection changed
	invalidate_frame_cache()
end

-- Unified track property toggle function
-- property_name: "B_MUTE" or "I_SOLO"
local function toggle_track_property(track_ids, property_name)
	if #track_ids == 0 then
		return
	end

	-- Check if all tracks have this property enabled
	local all_enabled = true
	for _, track_id in ipairs(track_ids) do
		local track = find_track_by_id(track_id)
		if track then
			local value = reaper.GetMediaTrackInfo_Value(track, property_name)
			if value == 0 then
				all_enabled = false
				break
			end
		end
	end

	-- Toggle: if all enabled, disable all; otherwise enable all
	reaper.PreventUIRefresh(1)
	local new_state = all_enabled and 0 or 1
	for _, track_id in ipairs(track_ids) do
		local track = find_track_by_id(track_id)
		if track then
			reaper.SetMediaTrackInfo_Value(track, property_name, new_state)
		end
	end
	reaper.PreventUIRefresh(-1)
	reaper.UpdateArrange()
end

-- Convenience wrapper: toggle mute
local function toggle_set_mute(track_ids)
	toggle_track_property(track_ids, "B_MUTE")
end

-- Convenience wrapper: toggle solo
local function toggle_set_solo(track_ids)
	toggle_track_property(track_ids, "I_SOLO")
end

-- Unified track visibility function
-- If track_ids_to_show is nil, shows all tracks
-- If track_ids_to_show is a table, shows only those tracks
local function set_tracks_visibility(track_ids_to_show, show_tcp, show_mcp)
	if not show_tcp and not show_mcp then
		return
	end

	local track_count = reaper.CountTracks(0)
	if track_count == 0 then
		return
	end

	-- Create lookup table if showing specific tracks
	local tracks_lookup = nil
	if track_ids_to_show then
		tracks_lookup = {}
		for _, track_id in ipairs(track_ids_to_show) do
			tracks_lookup[track_id] = true
		end
	end

	reaper.PreventUIRefresh(1)

	-- Set visibility for all tracks
	for i = 0, track_count - 1 do
		local track = reaper.GetTrack(0, i)
		if track then
			local should_show = 1 -- Default to visible (show all)

			-- If we have a specific set of tracks to show, check if this track is in it
			if tracks_lookup then
				local track_id = get_track_unique_id(track)
				should_show = tracks_lookup[track_id] and 1 or 0
			end

			if show_tcp then
				reaper.SetMediaTrackInfo_Value(track, "B_SHOWINTCP", should_show)
			end
			if show_mcp then
				reaper.SetMediaTrackInfo_Value(track, "B_SHOWINMIXER", should_show)
			end
		end
	end

	reaper.PreventUIRefresh(-1)
	reaper.TrackList_AdjustWindows(false)
	reaper.UpdateArrange()
end

-- Convenience wrapper: show only tracks in set
local function show_only_tracks_in_set(track_ids, show_tcp, show_mcp)
	set_tracks_visibility(track_ids, show_tcp, show_mcp)
end

-- Convenience wrapper: show all tracks
local function show_all_tracks(show_tcp, show_mcp)
	set_tracks_visibility(nil, show_tcp, show_mcp)
end

local function is_set_selected(track_ids)
	if #track_ids == 0 then
		return false
	end

	-- Count only tracks that still exist in the project
	local valid_count = 0
	local ids_set = {}
	for _, track_id in ipairs(track_ids) do
		local track = find_track_by_id(track_id)
		if track then
			ids_set[track_id] = true
			valid_count = valid_count + 1
		end
	end

	if valid_count == 0 then
		return false
	end

	local selected_count = reaper.CountSelectedTracks2(0, true)
	if selected_count ~= valid_count then
		return false
	end

	-- Check all selected tracks are in this set
	local track_count = reaper.CountTracks(0)
	for i = 0, track_count - 1 do
		local track = reaper.GetTrack(0, i)
		if track and reaper.IsTrackSelected(track) then
			local track_id = get_track_unique_id(track)
			if not ids_set[track_id] then
				return false
			end
		end
	end

	return true
end

local function is_set_partially_selected(track_ids)
	if #track_ids == 0 then
		return false
	end

	local valid_count = 0
	local matches = 0
	for _, track_id in ipairs(track_ids) do
		local track = find_track_by_id(track_id)
		if track then
			valid_count = valid_count + 1
			if reaper.IsTrackSelected(track) then
				matches = matches + 1
			end
		end
	end

	if valid_count == 0 then
		return false
	end

	return matches > 0 and matches < valid_count
end

-- Helper function to convert RGB to HSL for better color sorting
local function rgb_to_hsl(r, g, b)
	r, g, b = r / 255, g / 255, b / 255
	local max = math.max(r, g, b)
	local min = math.min(r, g, b)
	local h, s, l = 0, 0, (max + min) / 2

	if max ~= min then
		local d = max - min
		s = l > 0.5 and d / (2 - max - min) or d / (max + min)

		if max == r then
			h = (g - b) / d + (g < b and 6 or 0)
		elseif max == g then
			h = (b - r) / d + 2
		else
			h = (r - g) / d + 4
		end

		h = h / 6
	end

	return h, s, l
end

local function sort_sets_by_color()
	-- Sort sets by their selectedColor (hex string)
	-- This creates a visually pleasing gradient effect
	table.sort(STATE.sets, function(a, b)
		local color_a = a.selectedColor or CONFIG.COLOR_BOX_SELECTED
		local color_b = b.selectedColor or CONFIG.COLOR_BOX_SELECTED

		-- Convert hex to RGB for better sorting
		local r_a = tonumber(color_a:sub(1, 2), 16)
		local g_a = tonumber(color_a:sub(3, 4), 16)
		local b_a = tonumber(color_a:sub(5, 6), 16)

		local r_b = tonumber(color_b:sub(1, 2), 16)
		local g_b = tonumber(color_b:sub(3, 4), 16)
		local b_b = tonumber(color_b:sub(5, 6), 16)

		-- Sort by hue, then saturation, then lightness
		local h_a, s_a, l_a = rgb_to_hsl(r_a, g_a, b_a)
		local h_b, s_b, l_b = rgb_to_hsl(r_b, g_b, b_b)

		if math.abs(h_a - h_b) > 0.01 then
			return h_a < h_b
		elseif math.abs(s_a - s_b) > 0.01 then
			return s_a < s_b
		else
			return l_a < l_b
		end
	end)

	STATE.dirty = true
	STATE.cached_boxes = nil
end

local function create_set(name, track_ids)
	local id = generate_set_id()

	-- Determine selected color from first track
	local selected_color = CONFIG.COLOR_BOX_SELECTED
	if track_ids and #track_ids > 0 then
		local first_track = find_track_by_id(track_ids[1])
		if first_track then
			selected_color = get_track_color(first_track)
		end
	end

	-- COLOR_MAP overrides track-derived color when the name matches
	local mapped_color = get_color_for_name(name)
	if mapped_color then
		selected_color = mapped_color
	end

	local set = {
		id = id,
		name = name or "Set " .. (#STATE.sets + 1),
		trackIndices = track_ids or {}, -- Keep old name for backwards compatibility
		selectedColor = selected_color,
	}
	table.insert(STATE.sets, set)

	-- Auto-sort if enabled
	if STATE.auto_sort_by_color then
		sort_sets_by_color()
	end

	STATE.dirty = true
	STATE.cached_boxes = nil
	return id
end

local function delete_set(set_id)
	for i, set in ipairs(STATE.sets) do
		if set.id == set_id then
			table.remove(STATE.sets, i)
			request_save()
			STATE.dirty = true
			STATE.cached_boxes = nil
			return true
		end
	end
	return false
end

local function rename_set(set_id, new_name)
	for _, set in ipairs(STATE.sets) do
		if set.id == set_id then
			set.name = new_name
			-- Apply COLOR_MAP: name change may warrant a new color
			local mapped_color = get_color_for_name(new_name)
			if mapped_color then
				set.selectedColor = mapped_color
			end
			STATE.dirty = true
			return true
		end
	end
	return false
end

local function overwrite_set(set_id, track_ids)
	for _, set in ipairs(STATE.sets) do
		if set.id == set_id then
			set.trackIndices = track_ids or {}

			-- Update selected color from first track
			if #set.trackIndices > 0 then
				local first_track = find_track_by_id(set.trackIndices[1])
				if first_track then
					set.selectedColor = get_track_color(first_track)
				else
					set.selectedColor = CONFIG.COLOR_BOX_SELECTED
				end
			else
				set.selectedColor = CONFIG.COLOR_BOX_SELECTED
			end

			STATE.dirty = true
			return true
		end
	end
	return false
end

local function find_set(set_id)
	for _, set in ipairs(STATE.sets) do
		if set.id == set_id then
			return set
		end
	end
	return nil
end

local function get_track_name(track)
	if not track then
		return nil
	end

	local _, name = reaper.GetSetMediaTrackInfo_String(track, "P_NAME", "", false)
	if name == "" then
		-- If track has no custom name, return "Track N" where N is the track number (1-based)
		local track_index = reaper.GetMediaTrackInfo_Value(track, "IP_TRACKNUMBER") - 1
		return "Track " .. (track_index + 1)
	end
	return name
end

-- ============================================================================
-- FILE PERSISTENCE
-- ============================================================================

local function dir_exists(path)
	return reaper.file_exists(path .. "/.")
end

local function ensure_reasets_directory()
	local proj_path = get_project_path()
	if not proj_path then
		return false
	end

	local reasets_dir = proj_path .. "/" .. CONFIG.REASETS_DIR

	if dir_exists(reasets_dir) then
		return true
	elseif reaper.RecursiveCreateDirectory(reasets_dir, 0) == 1 then
		return true
	else
		return false
	end
end

local function get_sets_file_path()
	local proj_path = get_project_path()
	if not proj_path then
		return nil
	end
	return proj_path .. "/" .. CONFIG.REASETS_DIR .. "/" .. CONFIG.FILE_SETS_BASENAME
end

local function save_sets()
	if not ensure_reasets_directory() then
		return false
	end

	local path = get_sets_file_path()
	if not path then
		return false
	end

	local data = {
		sets = STATE.sets,
		version = 1,
		settings = {
			box_width = STATE.box_width,
			box_height = STATE.box_height,
			font_size = STATE.font_size,
			growth_direction = STATE.growth_direction,
			show_all_tracks_set = STATE.show_all_tracks_set,
			toolbar_position = STATE.toolbar_position,
			auto_sort_by_color = STATE.auto_sort_by_color,
			scroll_speed = STATE.scroll_speed,
			toolbar_button_size = STATE.toolbar_button_size,
			ab_mode = STATE.ab_mode,
			auto_hide_tcp = STATE.auto_hide_tcp,
			auto_hide_mcp = STATE.auto_hide_mcp,
			use_first_track_name = STATE.use_first_track_name,
			is_docked = STATE.is_docked,
			settings_font_size = STATE.settings_font_size,
		},
	}

	local json = json_encode(data)
	local result = write_file(path, json)
	STATE.last_save_time = reaper.time_precise()
	return result
end

local function load_sets()
	local path = get_sets_file_path()
	if not path or not file_exists(path) then
		STATE.sets = {}
		return
	end

	local content = read_file(path)
	if not content then
		STATE.sets = {}
		return
	end

	local data = json_decode(content)
	if data and data.sets then
		STATE.sets = data.sets

		-- Load settings if available
		if data.settings then
			STATE.box_width = data.settings.box_width or STATE.box_width
			STATE.box_height = data.settings.box_height or STATE.box_height
			STATE.font_size = data.settings.font_size or STATE.font_size
			STATE.growth_direction = data.settings.growth_direction or STATE.growth_direction
			STATE.show_all_tracks_set = data.settings.show_all_tracks_set or false
			STATE.toolbar_position = data.settings.toolbar_position or "top"
			STATE.auto_sort_by_color = data.settings.auto_sort_by_color or false
			STATE.scroll_speed = data.settings.scroll_speed or STATE.scroll_speed
			if data.settings.toolbar_button_size then
				STATE.toolbar_button_size = data.settings.toolbar_button_size
			end
			STATE.ab_mode = data.settings.ab_mode or false
			STATE.auto_hide_tcp = data.settings.auto_hide_tcp or false
			STATE.auto_hide_mcp = data.settings.auto_hide_mcp or false
			-- Default to true if not present (for backwards compatibility)
			if data.settings.use_first_track_name ~= nil then
				STATE.use_first_track_name = data.settings.use_first_track_name
			end
			if data.settings.is_docked ~= nil then
				STATE.is_docked = data.settings.is_docked
			end
			if data.settings.settings_font_size ~= nil then
				STATE.settings_font_size = data.settings.settings_font_size
			end
		end
	else
		STATE.sets = {}
	end
end

-- Debounced save function
local SAVE_DELAY = 0.5 -- Save 500ms after last change

request_save = function()
	STATE.pending_save = true
	STATE.last_change_time = reaper.time_precise()
end

local function process_pending_saves()
	if not STATE.pending_save then
		return
	end

	local current_time = reaper.time_precise()
	if current_time - STATE.last_change_time >= SAVE_DELAY then
		save_sets()
		STATE.pending_save = false
	end
end

local function check_project_changed()
	local current_proj = get_current_project_id()

	if current_proj ~= STATE.current_project then
		STATE.current_project = current_proj
		STATE.selected_set_id = nil
		STATE.view = "main"
		STATE.editing_set_id = nil
		STATE.scroll_offset = 0
		STATE.settings_scroll_offset = 0
		load_sets()
		STATE.cached_boxes = nil
		STATE.dirty = true
		return true
	end

	return false
end

-- ============================================================================
-- GUI RENDERING
-- ============================================================================

local function set_color(color)
	-- Parse hex color string "RRGGBB" to RGB values (0-1 range)
	local r = tonumber(color:sub(1, 2), 16) / 255
	local g = tonumber(color:sub(3, 4), 16) / 255
	local b = tonumber(color:sub(5, 6), 16) / 255
	gfx.set(r, g, b, 1.0)
end

local function draw_rect_filled(x, y, w, h, color)
	set_color(color)
	gfx.rect(x, y, w, h, 1)
end

local function draw_rect_border(x, y, w, h, color, thickness)
	thickness = thickness or CONFIG.BORDER_THICKNESS
	set_color(color)
	for i = 0, thickness - 1 do
		gfx.rect(x + i, y + i, w - i * 2, h - i * 2, 0)
	end
end

local function draw_text(x, y, text, color)
	set_color(color)
	gfx.x = x
	gfx.y = y
	gfx.drawstr(text)
end

local function truncate_text_with_ellipsis(text, max_width)
	local text_width = gfx.measurestr(text)
	if text_width <= max_width then
		return text
	end

	local ellipsis = "..."
	local ellipsis_width = gfx.measurestr(ellipsis)
	local available_width = max_width - ellipsis_width

	if available_width <= 0 then
		return ellipsis
	end

	local truncated = ""
	for i = 1, #text do
		local substr = text:sub(1, i)
		if gfx.measurestr(substr) > available_width then
			break
		end
		truncated = substr
	end

	return truncated .. ellipsis
end

local function draw_plus_button(cx, cy, size, thickness, color)
	-- Draw plus sign
	set_color(color)
	local plus_size = size * 0.5
	-- Horizontal line
	gfx.rect(cx - plus_size, cy - thickness / 2, plus_size * 2, thickness, 1)
	-- Vertical line
	gfx.rect(cx - thickness / 2, cy - plus_size, thickness, plus_size * 2, 1)
end

local function get_toolbar_height()
	if STATE.toolbar_position == "hide" then
		return 0
	end
	return CONFIG.TOOLBAR_HEIGHT
end

local function get_content_area_top()
	if STATE.toolbar_position == "top" then
		return get_toolbar_height()
	end
	return 0
end

local function get_content_area_bottom()
	if STATE.toolbar_position == "bottom" then
		return gfx.h - get_toolbar_height()
	end
	return gfx.h
end

local function calculate_set_box_positions()
	-- Check if we can use cached positions
	if STATE.cached_boxes and STATE.cached_gfx_size.w == gfx.w and STATE.cached_gfx_size.h == gfx.h then
		return STATE.cached_boxes
	end

	local boxes = {}
	local gfx_w, gfx_h = gfx.w, gfx.h

	-- Calculate box width: use STATE.box_width as maximum, scale down proportionally with window
	local box_width = math.floor(gfx_w * CONFIG.BOX_WIDTH_PERCENT)
	box_width = math.min(STATE.box_width, box_width)
	box_width = math.max(CONFIG.MIN_BOX_WIDTH, box_width)

	local center_x = (gfx_w - box_width) / 2
	local spacing_offset = STATE.box_height + CONFIG.BOX_SPACING

	-- Account for toolbar
	local content_top = get_content_area_top()
	local content_bottom = get_content_area_bottom()

	local start_y
	local box_index = 1

	if STATE.growth_direction == "down" then
		-- Growth downward: start at top (accounting for toolbar)
		start_y = content_top + CONFIG.PADDING

		-- Add "All Tracks" set if enabled
		if STATE.show_all_tracks_set then
			boxes[box_index] = {
				set_id = CONFIG.ALL_TRACKS_SET_ID,
				x = center_x,
				y = start_y,
				w = box_width,
				h = STATE.box_height,
			}
			box_index = box_index + 1
			start_y = start_y + spacing_offset
		end

		-- Add regular sets
		for i, set in ipairs(STATE.sets) do
			boxes[box_index] = {
				set_id = set.id,
				x = center_x,
				y = start_y + (i - 1) * spacing_offset,
				w = box_width,
				h = STATE.box_height,
			}
			box_index = box_index + 1
		end
	else
		-- Growth upward: start at bottom (accounting for toolbar)
		start_y = content_bottom - STATE.box_height - CONFIG.PADDING

		-- Add regular sets (from bottom up)
		for i, set in ipairs(STATE.sets) do
			boxes[box_index] = {
				set_id = set.id,
				x = center_x,
				y = start_y - (i - 1) * spacing_offset,
				w = box_width,
				h = STATE.box_height,
			}
			box_index = box_index + 1
		end

		-- Add "All Tracks" set at top if enabled
		if STATE.show_all_tracks_set then
			local all_tracks_y = start_y - #STATE.sets * spacing_offset
			boxes[box_index] = {
				set_id = CONFIG.ALL_TRACKS_SET_ID,
				x = center_x,
				y = all_tracks_y,
				w = box_width,
				h = STATE.box_height,
			}
		end
	end

	-- Cache the results
	STATE.cached_boxes = boxes
	STATE.cached_gfx_size = { w = gfx_w, h = gfx_h }

	return boxes
end

local function calculate_max_scroll()
	local boxes = calculate_set_box_positions()
	if #boxes == 0 then
		return 0
	end

	-- Calculate total content height including create button
	local last_box = boxes[#boxes]

	-- Account for: last box + spacing + create button + padding
	local content_height = last_box.y
		+ last_box.h
		+ CONFIG.CREATE_SET_BUTTON_SPACING
		+ CONFIG.CREATE_SET_BUTTON_SIZE
		+ 20
		+ CONFIG.PADDING
	local content_area_height = get_content_area_bottom() - get_content_area_top()
	local max_scroll = math.max(0, content_height - content_area_height)
	return max_scroll
end

local function draw_sort_icon(x, y, size, is_active)
	-- Draw a color palette icon
	-- Always use icon color for visibility (even when active)
	set_color(CONFIG.TOOLBAR_ICON_COLOR)

	-- Draw palette base (rounded rectangle outline)
	local palette_w = size * 0.85
	local palette_h = size * 0.7
	local palette_x = x + (size - palette_w) / 2
	local palette_y = y + (size - palette_h) / 2

	-- Draw palette outline
	gfx.rect(palette_x, palette_y, palette_w, palette_h, 0)

	-- Draw thumb hole (small circle on the right side)
	local thumb_radius = size * 0.08
	local thumb_x = palette_x + palette_w - thumb_radius * 2
	local thumb_y = palette_y + palette_h / 2
	gfx.circle(thumb_x, thumb_y, thumb_radius, 0, 1)

	-- Draw color spots (small filled circles)
	local spot_radius = size * 0.12
	local spot_spacing = size * 0.25

	-- Row 1: Red, Yellow, Blue
	local row1_y = palette_y + palette_h * 0.3
	local start_x = palette_x + size * 0.15

	-- Red spot
	set_color("FF6B6B")
	gfx.circle(start_x, row1_y, spot_radius, 1, 1)

	-- Yellow spot
	set_color("FFD93D")
	gfx.circle(start_x + spot_spacing, row1_y, spot_radius, 1, 1)

	-- Blue spot
	set_color("6BCF7F")
	gfx.circle(start_x + spot_spacing * 2, row1_y, spot_radius, 1, 1)

	-- Row 2: Purple, Orange
	local row2_y = palette_y + palette_h * 0.7

	-- Purple spot
	set_color("A78BFA")
	gfx.circle(start_x + spot_spacing * 0.5, row2_y, spot_radius, 1, 1)

	-- Orange spot
	set_color("FB923C")
	gfx.circle(start_x + spot_spacing * 1.5, row2_y, spot_radius, 1, 1)
end

local function draw_help_icon(x, y, size, is_active)
	set_color(CONFIG.TOOLBAR_ICON_COLOR)
	local font_size = math.floor(size * 0.55)
	gfx.setfont(2, CONFIG.DEFAULT_FONT, font_size, "b")
	local text = "?"
	local text_w, text_h = gfx.measurestr(text)
	gfx.x = x + (size - text_w) / 2
	gfx.y = y + (size - text_h) / 2
	gfx.drawstr(text)
	gfx.setfont(1)
end

local function draw_dock_icon(x, y, size, is_active)
	set_color(CONFIG.TOOLBAR_ICON_COLOR)

	local w  = math.floor(size * 0.78)
	local h  = math.floor(size * 0.68)
	local bx = x + math.floor((size - w) / 2)
	local by = y + math.floor((size - h) / 2)

	-- Outer window border
	gfx.rect(bx, by, w, h, 0)

	-- Docked-panel strip on the right edge
	local strip_w = math.max(2, math.floor(w * 0.32))
	gfx.rect(bx + w - strip_w, by, strip_w, h, 1)

	-- Small gap line to visually separate strip from body
	set_color(is_active and CONFIG.TOOLBAR_BUTTON_ACTIVE_COLOR or CONFIG.TOOLBAR_BG_COLOR)
	gfx.rect(bx + w - strip_w - 1, by + 1, 1, h - 2, 1)
end

local function draw_ab_icon(x, y, size, is_active)
	-- Draw A/B text icon
	set_color(CONFIG.TOOLBAR_ICON_COLOR)

	-- Set smaller font for A/B text (use font slot 2 to avoid interfering with main font)
	local font_size = math.floor(size * 0.5)
	gfx.setfont(2, CONFIG.DEFAULT_FONT, font_size, "b") -- Bold for better visibility

	-- Draw A/B text centered
	local text = "A/B"
	local text_w, text_h = gfx.measurestr(text)
	local text_x = x + (size - text_w) / 2
	local text_y = y + (size - text_h) / 2
	gfx.x = text_x
	gfx.y = text_y
	gfx.drawstr(text)

	-- Restore active font to slot 1 (main font)
	gfx.setfont(1)
end

local function draw_tcp_icon(x, y, size, is_active)
	-- Draw TCP text icon
	set_color(CONFIG.TOOLBAR_ICON_COLOR)

	-- Set smaller font for TCP text (use font slot 2 to avoid interfering with main font)
	local font_size = math.floor(size * 0.45)
	gfx.setfont(2, CONFIG.DEFAULT_FONT, font_size, "b") -- Bold for better visibility

	-- Draw TCP text centered
	local text = "TCP"
	local text_w, text_h = gfx.measurestr(text)
	local text_x = x + (size - text_w) / 2
	local text_y = y + (size - text_h) / 2
	gfx.x = text_x
	gfx.y = text_y
	gfx.drawstr(text)

	-- Restore active font to slot 1 (main font)
	gfx.setfont(1)
end

local function draw_mcp_icon(x, y, size, is_active)
	-- Draw MCP text icon
	set_color(CONFIG.TOOLBAR_ICON_COLOR)

	-- Set smaller font for MCP text (use font slot 2 to avoid interfering with main font)
	local font_size = math.floor(size * 0.45)
	gfx.setfont(2, CONFIG.DEFAULT_FONT, font_size, "b") -- Bold for better visibility

	-- Draw MCP text centered
	local text = "MCP"
	local text_w, text_h = gfx.measurestr(text)
	local text_x = x + (size - text_w) / 2
	local text_y = y + (size - text_h) / 2
	gfx.x = text_x
	gfx.y = text_y
	gfx.drawstr(text)

	-- Restore active font to slot 1 (main font)
	gfx.setfont(1)
end

-- Toolbar button definitions organized by functional groups
local TOOLBAR_BUTTON_GROUPS = {
	-- Group 1: Set organization
	{
		{
			id = "sort_by_color",
			draw_icon = draw_sort_icon,
			get_active_state = function()
				return STATE.auto_sort_by_color
			end,
		},
	},
	-- Group 2: Selection/playback workflow
	{
		{
			id = "ab_mode",
			draw_icon = draw_ab_icon,
			get_active_state = function()
				return STATE.ab_mode
			end,
		},
	},
	-- Group 3: Visibility controls
	{
		{
			id = "tcp_hide",
			draw_icon = draw_tcp_icon,
			get_active_state = function()
				return STATE.auto_hide_tcp
			end,
		},
		{
			id = "mcp_hide",
			draw_icon = draw_mcp_icon,
			get_active_state = function()
				return STATE.auto_hide_mcp
			end,
		},
	},
	-- Group 4: Window management
	{
		{
			id = "dock_toggle",
			draw_icon = draw_dock_icon,
			get_active_state = function()
				return STATE.is_docked
			end,
		},
	},
	-- Group 5: Help
	{
		{
			id = "help_view",
			draw_icon = draw_help_icon,
			get_active_state = function()
				return STATE.view == "help"
			end,
		},
	},
}

local function draw_toolbar()
	if STATE.toolbar_position == "hide" then
		return {}
	end

	local toolbar_y = STATE.toolbar_position == "top" and 0 or (gfx.h - CONFIG.TOOLBAR_HEIGHT)

	-- Draw toolbar background
	draw_rect_filled(0, toolbar_y, gfx.w, CONFIG.TOOLBAR_HEIGHT, CONFIG.TOOLBAR_BG_COLOR)

	local buttons = {}
	local bsize = STATE.toolbar_button_size
	local button_y = toolbar_y + (CONFIG.TOOLBAR_HEIGHT - bsize) / 2
	local button_x = CONFIG.TOOLBAR_BUTTON_PADDING
	local icon_padding = math.max(2, math.floor(bsize * 0.15))

	-- Draw button groups
	for group_idx, group in ipairs(TOOLBAR_BUTTON_GROUPS) do
		for btn_idx, btn_def in ipairs(group) do
			-- Create button data
			local button = {
				x = button_x,
				y = button_y,
				w = bsize,
				h = bsize,
				action = btn_def.id,
			}

			-- Determine button color based on hover and active state
			local button_color = CONFIG.TOOLBAR_BUTTON_COLOR
			if STATE.toolbar_hover_button == btn_def.id then
				button_color = CONFIG.TOOLBAR_BUTTON_HOVER_COLOR
			end
			if btn_def.get_active_state() then
				button_color = CONFIG.TOOLBAR_BUTTON_ACTIVE_COLOR
			end

			-- Draw button background
			draw_rect_filled(button.x, button.y, button.w, button.h, button_color)

			-- Draw button icon
			btn_def.draw_icon(
				button.x + icon_padding,
				button.y + icon_padding,
				bsize - icon_padding * 2,
				btn_def.get_active_state()
			)

			table.insert(buttons, button)

			-- Advance x position for next button in group
			button_x = button_x + bsize + CONFIG.TOOLBAR_SPACING
		end

		-- Add group spacing (except after last group)
		if group_idx < #TOOLBAR_BUTTON_GROUPS then
			button_x = button_x - CONFIG.TOOLBAR_SPACING + CONFIG.TOOLBAR_GROUP_SPACING
		end
	end

	return buttons
end

-- Calculate insertion index based on mouse Y position
local function calculate_insertion_index(mouse_y)
	if not STATE.dragging_set_id then
		return nil
	end

	local boxes = calculate_set_box_positions()
	local dragged_box = nil

	-- Find the box being dragged
	for _, box in ipairs(boxes) do
		if box.set_id == STATE.dragging_set_id then
			dragged_box = box
			break
		end
	end

	if not dragged_box then
		return nil
	end

	-- Calculate mouse Y in scrolled space
	local scroll_mouse_y = mouse_y + STATE.scroll_offset

	-- Count regular sets (excluding All Tracks and dragged set)
	local regular_set_count = 0
	for _, box in ipairs(boxes) do
		if box.set_id ~= CONFIG.ALL_TRACKS_SET_ID and box.set_id ~= STATE.dragging_set_id then
			regular_set_count = regular_set_count + 1
		end
	end

	-- Determine insertion position
	local insert_index = 1

	for i, box in ipairs(boxes) do
		-- Skip the All Tracks set
		if box.set_id == CONFIG.ALL_TRACKS_SET_ID then
			goto continue_calc
		end

		-- Skip the dragged set itself
		if box.set_id == STATE.dragging_set_id then
			goto continue_calc
		end

		local box_midpoint = box.y + box.h / 2

		if scroll_mouse_y < box_midpoint then
			break
		end

		insert_index = insert_index + 1

		::continue_calc::
	end

	-- Clamp to valid range (after removing dragged set, max position is #STATE.sets)
	insert_index = math.max(1, math.min(insert_index, #STATE.sets))

	return insert_index
end

local function draw_main_view()
	-- Draw background
	draw_rect_filled(0, 0, gfx.w, gfx.h, CONFIG.COLOR_BG)

	-- Draw toolbar (returns button positions)
	local toolbar_buttons = draw_toolbar()

	local boxes = calculate_set_box_positions()

	-- Calculate clipping area for scrollable content
	local content_top = get_content_area_top()
	local content_bottom = get_content_area_bottom()

	-- Calculate insertion index if dragging
	local insert_visual_y = nil
	if STATE.drag_initiated and STATE.dragging_set_id then
		local insert_index = STATE.drag_hover_insert_index or 1

		-- Find the Y position for insertion line
		local regular_boxes = {}
		for _, box in ipairs(boxes) do
			if box.set_id ~= CONFIG.ALL_TRACKS_SET_ID and box.set_id ~= STATE.dragging_set_id then
				table.insert(regular_boxes, box)
			end
		end

		if #regular_boxes > 0 then
			if insert_index <= 1 then
				-- Insert at top (before first set)
				insert_visual_y = regular_boxes[1].y - CONFIG.BOX_SPACING / 2
			elseif insert_index > #regular_boxes then
				-- Insert at bottom (after last set)
				local last_box = regular_boxes[#regular_boxes]
				insert_visual_y = last_box.y + last_box.h + CONFIG.BOX_SPACING / 2
			else
				-- Insert between sets
				local prev_box = regular_boxes[insert_index - 1]
				local next_box = regular_boxes[insert_index]
				insert_visual_y = (prev_box.y + prev_box.h + next_box.y) / 2
			end
		end
	end

	for i, box in ipairs(boxes) do
		-- Apply scroll offset
		local visible_y = box.y - STATE.scroll_offset

		-- Skip rendering if box is not visible within content area
		if visible_y + box.h < content_top or visible_y > content_bottom then
			goto continue
		end

		-- Skip rendering the dragged set (we'll draw it as ghost later)
		if STATE.drag_initiated and box.set_id == STATE.dragging_set_id then
			goto continue
		end

		-- Handle special "All Tracks" set using module
		if box.set_id == CONFIG.ALL_TRACKS_SET_ID then
			AllTracksSet.draw(box, STATE.scroll_offset)
			goto continue
		end

		-- Handle regular sets
		local set = find_set(box.set_id)
		if not set then
			goto continue
		end

		-- Determine selection state
		local is_selected = is_set_selected(set.trackIndices)
		local is_partial = is_set_partially_selected(set.trackIndices)

		-- Use per-set selected color (with fallback for old sets)
		local base_selected_color = set.selectedColor or CONFIG.COLOR_BOX_SELECTED
		local box_color
		if is_selected then
			box_color = base_selected_color
		elseif is_partial then
			box_color = CONFIG.COLOR_BOX_PARTIAL
		else
			box_color = CONFIG.COLOR_BOX
		end

		local border_color = brighten_color(base_selected_color)

		-- Draw box (using visible_y instead of box.y)
		draw_rect_filled(box.x, visible_y, box.w, box.h, box_color)
		draw_rect_border(box.x, visible_y, box.w, box.h, border_color)

		-- Determine text color based on box color brightness
		local text_color = CONFIG.COLOR_TEXT
		if is_selected and is_color_light(base_selected_color) then
			text_color = CONFIG.COLOR_TEXT_DARK
		end

		-- Draw text
		if STATE.editing_set_id == set.id then
			-- Draw edit mode with cursor and optional selection highlight
			local text_y = visible_y + (box.h - gfx.texth) / 2
			local text_width = gfx.measurestr(STATE.editing_text)
			local text_x = box.x + (box.w - text_width) / 2

			-- Draw selection highlight if there is a selection
			if STATE.selection_start and STATE.selection_end then
				local sel_start = math.min(STATE.selection_start, STATE.selection_end)
				local sel_end = math.max(STATE.selection_start, STATE.selection_end)

				if sel_start < sel_end then
					local text_before_sel = STATE.editing_text:sub(1, sel_start)
					local text_selected = STATE.editing_text:sub(sel_start + 1, sel_end)

					local before_width = gfx.measurestr(text_before_sel)
					local selected_width = gfx.measurestr(text_selected)

					draw_rect_filled(
						text_x + before_width,
						text_y - 2,
						selected_width,
						gfx.texth + 4,
						CONFIG.COLOR_SELECTION_HIGHLIGHT
					)
				end
			elseif STATE.editing_text_selected then
				-- Draw selection highlight behind all text (for backward compatibility)
				local text_width = gfx.measurestr(STATE.editing_text)
				draw_rect_filled(
					text_x - 2,
					text_y - 2,
					text_width + 4,
					gfx.texth + 4,
					CONFIG.COLOR_SELECTION_HIGHLIGHT
				)
			end

			-- Draw text with cursor at cursor_position (only show cursor if no selection)
			if STATE.selection_start and STATE.selection_end and STATE.selection_start ~= STATE.selection_end then
				-- Don't show cursor when there's a selection
				draw_text(text_x, text_y, STATE.editing_text, text_color)
			else
				-- Show cursor
				local text_before = STATE.editing_text:sub(1, STATE.cursor_position)
				local text_after = STATE.editing_text:sub(STATE.cursor_position + 1)
				local text = text_before .. "|" .. text_after
				draw_text(text_x, text_y, text, text_color)
			end
		else
			-- Draw set name centered, truncated if necessary
			local padding = CONFIG.PADDING * 2
			local display_name = truncate_text_with_ellipsis(set.name, box.w - padding)
			local text_width = gfx.measurestr(display_name)
			local text_x = box.x + (box.w - text_width) / 2
			draw_text(text_x, visible_y + (box.h - gfx.texth) / 2, display_name, text_color)
		end

		::continue::
	end

	-- Draw ghost set if dragging (before insertion line so line is visible)
	if STATE.drag_initiated and STATE.dragging_set_id and STATE.drag_ghost_y then
		local dragged_set = find_set(STATE.dragging_set_id)
		if dragged_set then
			local ghost_y = STATE.drag_ghost_y - STATE.scroll_offset

			-- Only draw if visible
			if ghost_y >= content_top - STATE.box_height and ghost_y <= content_bottom then
				local boxes_for_width = calculate_set_box_positions()
				local box_width = #boxes_for_width > 0 and boxes_for_width[1].w or 200
				local box_x = #boxes_for_width > 0 and boxes_for_width[1].x or (gfx.w - box_width) / 2

				local base_selected_color = dragged_set.selectedColor or CONFIG.COLOR_BOX_SELECTED
				local is_selected = is_set_selected(dragged_set.trackIndices)
				local box_color = is_selected and base_selected_color or CONFIG.COLOR_BOX

				-- Draw ghost with reduced opacity (simulate by drawing over background)
				-- First draw at full opacity
				draw_rect_filled(box_x, ghost_y, box_width, STATE.box_height, box_color)

				-- Draw semi-transparent background on top to create opacity effect
				local r = tonumber(CONFIG.COLOR_BG:sub(1, 2), 16) / 255
				local g = tonumber(CONFIG.COLOR_BG:sub(3, 4), 16) / 255
				local b = tonumber(CONFIG.COLOR_BG:sub(5, 6), 16) / 255
				gfx.set(r, g, b, 1 - CONFIG.DRAG_GHOST_OPACITY)
				gfx.rect(box_x, ghost_y, box_width, STATE.box_height, 1)

				-- Draw border using set's brightened color
				local border_color = brighten_color(base_selected_color)
				draw_rect_border(box_x, ghost_y, box_width, STATE.box_height, border_color)
				-- Draw text
				local text_color = CONFIG.COLOR_TEXT
				if is_selected and is_color_light(base_selected_color) then
					text_color = CONFIG.COLOR_TEXT_DARK
				end
				local text_width = gfx.measurestr(dragged_set.name)
				local text_x = box_x + (box_width - text_width) / 2
				draw_text(text_x, ghost_y + (STATE.box_height - gfx.texth) / 2, dragged_set.name, text_color)
			end
		end
	end

	-- Draw insertion line if dragging (drawn after ghost so it's on top)
	if STATE.drag_initiated and insert_visual_y then
		local line_y = insert_visual_y - STATE.scroll_offset
		if line_y >= content_top and line_y <= content_bottom then
			local boxes_for_width = calculate_set_box_positions()
			local box_width = #boxes_for_width > 0 and boxes_for_width[1].w or 200
			local box_x = #boxes_for_width > 0 and boxes_for_width[1].x or (gfx.w - box_width) / 2

			-- Draw thick insertion line
			set_color(CONFIG.COLOR_DRAG_INSERTION)
			gfx.rect(
				box_x,
				line_y - CONFIG.DRAG_INSERTION_LINE_THICKNESS / 2,
				box_width,
				CONFIG.DRAG_INSERTION_LINE_THICKNESS,
				1
			)
		end
	end

	-- Draw create set button (circle with plus sign)
	local button_y
	local content_center = (content_top + content_bottom) / 2
	if #boxes == 0 then
		-- No sets: center the button in content area
		button_y = content_center
	else
		-- With sets: place below the last set
		local last_box = boxes[#boxes]
		button_y = last_box.y + last_box.h + CONFIG.CREATE_SET_BUTTON_SPACING - STATE.scroll_offset
	end

	local button_x = gfx.w / 2
	STATE.create_button_pos = { x = button_x, y = button_y }

	-- Draw button only if visible within content area
	if
		button_y >= content_top - CONFIG.CREATE_SET_BUTTON_SIZE
		and button_y <= content_bottom + CONFIG.CREATE_SET_BUTTON_SIZE
	then
		draw_plus_button(
			button_x,
			button_y,
			CONFIG.CREATE_SET_BUTTON_SIZE,
			CONFIG.CREATE_SET_BUTTON_THICKNESS,
			CONFIG.CREATE_SET_BUTTON_COLOR
		)
	end

	-- Return toolbar buttons for click detection
	return toolbar_buttons
end

local function draw_button(x, y, w, h, text, is_active)
	local color = is_active and CONFIG.COLOR_BOX_SELECTED or CONFIG.COLOR_BOX
	local border_color = is_active and CONFIG.COLOR_BOX_BORDER_SELECTED or CONFIG.COLOR_BOX_BORDER

	draw_rect_filled(x, y, w, h, color)
	draw_rect_border(x, y, w, h, border_color)

	local text_width = gfx.measurestr(text)
	local text_x = x + (w - text_width) / 2
	local text_y = y + (h - gfx.texth) / 2
	draw_text(text_x, text_y, text, CONFIG.COLOR_TEXT)

	return { x = x, y = y, w = w, h = h }
end

local function draw_slider(x, y, w, h, value, min_val, max_val)
	-- Draw slider background
	draw_rect_filled(x, y, w, h, CONFIG.COLOR_BOX)
	draw_rect_border(x, y, w, h, CONFIG.COLOR_BOX_BORDER)

	-- Draw slider fill
	local fill_width = ((value - min_val) / (max_val - min_val)) * w
	draw_rect_filled(x, y, fill_width, h, CONFIG.COLOR_BOX_SELECTED)

	-- Draw value text to the right of the slider
	local value_text = string.format("%d", value)
	draw_text(x + w + 8, y + (h - gfx.texth) / 2, value_text, CONFIG.COLOR_TEXT)

	return { x = x, y = y, w = w, h = h, min = min_val, max = max_val }
end

local function calculate_settings_elements()
	-- Single-column layout: every label sits directly above its control.
	-- All controls are full-width (minus side padding).
	local padding    = 12
	local gap        = 6   -- gap between label and its control
	local section    = 18  -- vertical gap between sections
	local btn_h      = CONFIG.SETTINGS_BUTTON_HEIGHT
	local slider_h   = CONFIG.SETTINGS_SLIDER_HEIGHT
	local ctrl_w     = gfx.w - padding * 2          -- full control width
	local half_w     = (ctrl_w - 6) / 2             -- for paired +/- or 2-option buttons
	local third_w    = (ctrl_w - 12) / 3            -- for 3-option toolbar buttons
	-- Leave 32px on the right for the value readout next to sliders
	local slider_w   = ctrl_w - 32

	local elements   = {}
	elements.padding = padding

	local y          = 15
	local label_h    = gfx.texth + gap  -- label height + gap before control

	-- ── Set Font Size ────────────────────────────────────────────────────────
	elements.font_size_label_y = y
	y = y + label_h
	elements.font_dec_btn = { x = padding,              y = y, w = half_w, h = btn_h }
	elements.font_inc_btn = { x = padding + half_w + 6, y = y, w = half_w, h = btn_h }
	y = y + btn_h + section

	-- ── Settings Font Size ───────────────────────────────────────────────────
	elements.settings_font_size_label_y = y
	y = y + label_h
	elements.settings_font_dec_btn = { x = padding,              y = y, w = half_w, h = btn_h }
	elements.settings_font_inc_btn = { x = padding + half_w + 6, y = y, w = half_w, h = btn_h }
	y = y + btn_h + section

	-- ── Growth Direction ─────────────────────────────────────────────────────
	elements.growth_label_y = y
	y = y + label_h
	elements.growth_down_btn = { x = padding,              y = y, w = half_w, h = btn_h }
	elements.growth_up_btn   = { x = padding + half_w + 6, y = y, w = half_w, h = btn_h }
	y = y + btn_h + section

	-- ── Set Width slider ─────────────────────────────────────────────────────
	elements.width_slider_label_y = y
	y = y + label_h
	elements.width_slider = {
		x = padding, y = y, w = slider_w, h = slider_h,
		min = CONFIG.MIN_BOX_WIDTH, max = CONFIG.MAX_BOX_WIDTH,
	}
	y = y + slider_h + section

	-- ── Set Height slider ────────────────────────────────────────────────────
	elements.height_slider_label_y = y
	y = y + label_h
	elements.height_slider = {
		x = padding, y = y, w = slider_w, h = slider_h,
		min = 30, max = 100,
	}
	y = y + slider_h + section

	--  Scroll Speed slider 
	elements.scroll_slider_label_y = y
	y = y + label_h
	elements.scroll_slider = {
		x = padding, y = y, w = slider_w, h = slider_h,
		min = 1, max = 20,
	}
	y = y + slider_h + section

	-- ── Show All Tracks Set ──────────────────────────────────────────────────
	elements.all_tracks_label_y = y
	y = y + label_h
	elements.all_tracks_toggle_btn = { x = padding, y = y, w = ctrl_w, h = btn_h }
	y = y + btn_h + section

	-- ── Use First Track Name ─────────────────────────────────────────────────
	elements.use_track_name_label_y = y
	y = y + label_h
	elements.use_track_name_toggle_btn = { x = padding, y = y, w = ctrl_w, h = btn_h }
	y = y + btn_h + section

	--  Toolbar Button Size slider 
	elements.toolbar_btn_size_label_y = y
	y = y + label_h
	elements.toolbar_btn_size_slider = {
		x = padding, y = y, w = slider_w, h = slider_h,
		min = CONFIG.TOOLBAR_BUTTON_SIZE_MIN, max = CONFIG.TOOLBAR_BUTTON_SIZE_MAX,
	}
	y = y + slider_h + section

	--  Toolbar Position 
	elements.toolbar_label_y = y
	y = y + label_h
	elements.toolbar_top_btn    = { x = padding,                      y = y, w = third_w, h = btn_h }
	elements.toolbar_bottom_btn = { x = padding + third_w + 6,        y = y, w = third_w, h = btn_h }
	elements.toolbar_hide_btn   = { x = padding + (third_w + 6) * 2,  y = y, w = third_w, h = btn_h }
	y = y + btn_h + section

	-- ── Max scroll ───────────────────────────────────────────────────────────
	-- Visible area is reduced by border_top (10) + border_bottom margin (50)
	-- + is_within_bounds padding (5 top + 5 bottom) = 70px total.
	elements.content_height = y
	elements.max_scroll = math.max(0, elements.content_height - (gfx.h - 70))

	return elements
end

-- ============================================================================
-- HELP VIEW
-- ============================================================================

local HELP_CONTENT = {
	{
		heading = "WHAT IS REASETS?",
		body = "Reasets lets you save named groups of tracks called sets and recall their selection instantly. Instead of manually hunting for tracks, one click selects exactly the group you need.",
	},
	{
		heading = "CREATING A SET",
		body = "Select one or more tracks in REAPER, then click the [+] button at the bottom of the set list. A set is created and named after the first selected track. You can also double-click any empty area of the set list to create a set.",
	},
	{
		heading = "SELECTING A SET",
		body = "Left-click a set to select it. REAPER will immediately select its tracks. Left-click the same set again to deselect it, which clears the track selection.",
	},
	{
		heading = "RENAMING A SET",
		body = "Right-click a set to enter rename mode. A text cursor appears. Type your new name, then press Enter to confirm or Escape to cancel. Double-click inside the name to select all text.",
	},
	{
		heading = "DELETING A SET",
		body = "Middle-click (scroll wheel click) a set to delete it immediately. The set is removed but your tracks are unaffected.",
	},
	{
		heading = "OVERWRITING A SET",
		body = "To update a set with a new track selection: select the tracks you want in REAPER, then hold Left mouse button on the set and press Middle mouse button. The set is updated in place.",
	},
	{
		heading = "CHANGING A SET'S COLOR",
		body = "Hold Left mouse button on a set, then Right-click it to assign a random color. To copy a color from one set to another, hold Left on the source set and Right-click the target set.",
	},
	{
		heading = "MUTE & SOLO",
		body = "Ctrl+Left-click a set to toggle mute on all its tracks. Ctrl+Right-click to toggle solo. Both toggle based on the current state — if all tracks are muted they will be unmuted, otherwise all will be muted.",
	},
	{
		heading = "REORDERING SETS",
		body = "Click and hold a set until it lifts, then drag it up or down to a new position. A blue insertion line shows where it will be dropped. Release to confirm. Manual reordering disables auto color-sort.",
	},
	{
		heading = "A/B MODE (toolbar)",
		body = "Click the A/B toolbar button to enable A/B mode. In this mode, selecting a set exclusively solos its tracks, making it easy to compare two groups by clicking between them. Selecting the active set deselects and un-solos everything.",
	},
	{
		heading = "TCP HIDE / MCP HIDE (toolbar)",
		body = "The TCP and MCP buttons auto-hide tracks not in the selected set. TCP affects the Track Control Panel on the left; MCP affects the Mixer. When you deselect the set, all tracks become visible again. Both can be active simultaneously.",
	},
	{
		heading = "SORT BY COLOR (toolbar)",
		body = "Left-click the palette button to toggle auto-sort mode — new sets are automatically placed in color order. Right-click to perform a one-time sort of the existing sets without enabling auto-sort.",
	},
	{
		heading = "SETTINGS",
		body = "Right-click anywhere outside the set list to open Settings. From there you can adjust the font size, set width and height, scroll speed, growth direction (sets grow down or up), toolbar position, and whether to show an All Tracks shortcut at the top of the list.",
	},
	{
		heading = "SCROLLING",
		body = "Use the mouse wheel to scroll the set list when there are more sets than fit on screen. The Settings and Help panels scroll the same way.",
	},
}

local function wrap_text(text, max_width)
	local lines = {}
	local words = {}
	for word in text:gmatch("%S+") do
		table.insert(words, word)
	end
	local current_line = ""
	for _, word in ipairs(words) do
		local test = current_line == "" and word or (current_line .. " " .. word)
		if gfx.measurestr(test) <= max_width then
			current_line = test
		else
			if current_line ~= "" then
				table.insert(lines, current_line)
			end
			current_line = word
		end
	end
	if current_line ~= "" then
		table.insert(lines, current_line)
	end
	return lines
end

local function draw_help_view()
	draw_rect_filled(0, 0, gfx.w, gfx.h, CONFIG.COLOR_BG)

	local border_left   = 6
	local border_top    = 10
	local border_width  = gfx.w - border_left * 2
	local border_bottom = gfx.h - 50
	local border_height = border_bottom - border_top

	draw_rect_filled(border_left, border_top, border_width, border_height, CONFIG.COLOR_BG)
	draw_rect_border(border_left, border_top, border_width, border_height,
		CONFIG.SETTINGS_PANEL_BORDER_COLOR, CONFIG.BORDER_THICKNESS)

	local padding    = 14
	local max_w      = gfx.w - padding * 2
	local scroll     = STATE.help_scroll_offset
	local line_h     = gfx.texth
	local section_gap = 14
	local heading_gap = 4  -- gap between heading and body
	local y          = 12  -- starting y in content space

	-- Measure heading font (slightly larger) using same slot trick
	local heading_font_size = math.min(STATE.font_size + 2, 32)

	local function vis(elem_y, h)
		local sy = elem_y - scroll
		return sy + h > border_top + 4 and sy < border_bottom - 4
	end

	for _, section in ipairs(HELP_CONTENT) do
		-- Draw heading
		gfx.setfont(2, CONFIG.DEFAULT_FONT, heading_font_size, "b")
		local h_line_h = gfx.texth

		if vis(y, h_line_h) then
			set_color(CONFIG.TOOLBAR_BUTTON_ACTIVE_COLOR)
			gfx.x = padding
			gfx.y = y - scroll
			gfx.drawstr(section.heading)
		end
		y = y + h_line_h + heading_gap

		-- Draw body (word-wrapped)
		gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.font_size)
		local body_lines = wrap_text(section.body, max_w)
		for _, line in ipairs(body_lines) do
			if vis(y, line_h) then
				draw_text(padding, y - scroll, line, CONFIG.COLOR_TEXT)
			end
			y = y + line_h
		end

		y = y + section_gap
	end

	-- Restore main font
	gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.font_size)

	-- Clamp scroll now that we know content height
	local content_height = y
	local visible_height = border_bottom - border_top - 10
	local max_scroll = math.max(0, content_height - visible_height)
	STATE.help_max_scroll = max_scroll
	if STATE.help_scroll_offset > max_scroll then
		STATE.help_scroll_offset = max_scroll
	end

	-- Footer
	local help_text = "Right-click to close"
	local help_w = gfx.measurestr(help_text)
	draw_text((gfx.w - help_w) / 2, gfx.h - 35, help_text, CONFIG.COLOR_TEXT_GREY)
end

local function draw_settings_view()
	-- Draw background
	draw_rect_filled(0, 0, gfx.w, gfx.h, CONFIG.COLOR_BG)

	-- Only recalculate settings elements when window size changes
	if not STATE.settings_cached_elements
		or STATE.settings_cached_gfx_w ~= gfx.w
		or STATE.settings_cached_gfx_h ~= gfx.h
	then
		STATE.settings_cached_elements = calculate_settings_elements()
		STATE.settings_cached_gfx_w = gfx.w
		STATE.settings_cached_gfx_h = gfx.h
	end
	local el     = STATE.settings_cached_elements
	local scroll = STATE.settings_scroll_offset

	-- Panel border
	local border_left   = 6
	local border_top    = 10
	local border_width  = gfx.w - border_left * 2
	local border_bottom = gfx.h - 50
	local border_height = border_bottom - border_top

	draw_rect_filled(border_left, border_top, border_width, border_height, CONFIG.COLOR_BG)
	draw_rect_border(border_left, border_top, border_width, border_height,
		CONFIG.SETTINGS_PANEL_BORDER_COLOR, CONFIG.BORDER_THICKNESS)

	-- Returns true if the element at scrolled-y with height h is visible
	local function vis(elem_y, h)
		local sy = elem_y - scroll
		return sy + h > border_top + 5 and sy < border_bottom - 5
	end

	-- Draws a centered label, truncated with ellipsis if wider than available area
	local max_label_w = gfx.w - el.padding * 2
	local function draw_label(raw_y, text)
		if not vis(raw_y, gfx.texth) then return end
		local truncated = truncate_text_with_ellipsis(text, max_label_w)
		local tw = gfx.measurestr(truncated)
		draw_text((gfx.w - tw) / 2, raw_y - scroll, truncated, CONFIG.COLOR_TEXT_GREY)
	end

	-- ── Set Font Size ────────────────────────────────────────────────────────
	draw_label(el.font_size_label_y, "Set Font Size: " .. STATE.font_size)
	if vis(el.font_dec_btn.y, el.font_dec_btn.h) then
		draw_button(el.font_dec_btn.x, el.font_dec_btn.y - scroll,
			el.font_dec_btn.w, el.font_dec_btn.h, "-", false)
		draw_button(el.font_inc_btn.x, el.font_inc_btn.y - scroll,
			el.font_inc_btn.w, el.font_inc_btn.h, "+", false)
	end

	-- ── Settings Font Size ───────────────────────────────────────────────────
	draw_label(el.settings_font_size_label_y, "Settings Font Size: " .. STATE.settings_font_size)
	if vis(el.settings_font_dec_btn.y, el.settings_font_dec_btn.h) then
		draw_button(el.settings_font_dec_btn.x, el.settings_font_dec_btn.y - scroll,
			el.settings_font_dec_btn.w, el.settings_font_dec_btn.h, "-", false)
		draw_button(el.settings_font_inc_btn.x, el.settings_font_inc_btn.y - scroll,
			el.settings_font_inc_btn.w, el.settings_font_inc_btn.h, "+", false)
	end

	-- ── Growth Direction ─────────────────────────────────────────────────────
	draw_label(el.growth_label_y, "Growth Direction")
	if vis(el.growth_down_btn.y, el.growth_down_btn.h) then
		draw_button(el.growth_down_btn.x, el.growth_down_btn.y - scroll,
			el.growth_down_btn.w, el.growth_down_btn.h, "Down",
			STATE.growth_direction == "down")
		draw_button(el.growth_up_btn.x, el.growth_up_btn.y - scroll,
			el.growth_up_btn.w, el.growth_up_btn.h, "Up",
			STATE.growth_direction == "up")
	end

	-- ── Set Width slider ─────────────────────────────────────────────────────
	draw_label(el.width_slider_label_y, "Set Width")
	if vis(el.width_slider.y, el.width_slider.h) then
		draw_slider(el.width_slider.x, el.width_slider.y - scroll,
			el.width_slider.w, el.width_slider.h,
			STATE.box_width, el.width_slider.min, el.width_slider.max)
	end

	-- ── Set Height slider ────────────────────────────────────────────────────
	draw_label(el.height_slider_label_y, "Set Height")
	if vis(el.height_slider.y, el.height_slider.h) then
		draw_slider(el.height_slider.x, el.height_slider.y - scroll,
			el.height_slider.w, el.height_slider.h,
			STATE.box_height, el.height_slider.min, el.height_slider.max)
	end

	-- ── Scroll Speed slider ──────────────────────────────────────────────────
	draw_label(el.scroll_slider_label_y, "Scroll Speed")
	if vis(el.scroll_slider.y, el.scroll_slider.h) then
		draw_slider(el.scroll_slider.x, el.scroll_slider.y - scroll,
			el.scroll_slider.w, el.scroll_slider.h,
			STATE.scroll_speed, el.scroll_slider.min, el.scroll_slider.max)
	end

	-- ── Show All Tracks Set ──────────────────────────────────────────────────
	draw_label(el.all_tracks_label_y, "Show All Tracks Set")
	if vis(el.all_tracks_toggle_btn.y, el.all_tracks_toggle_btn.h) then
		draw_button(el.all_tracks_toggle_btn.x, el.all_tracks_toggle_btn.y - scroll,
			el.all_tracks_toggle_btn.w, el.all_tracks_toggle_btn.h,
			STATE.show_all_tracks_set and "ON" or "OFF",
			STATE.show_all_tracks_set)
	end

	-- ── Use First Track Name ─────────────────────────────────────────────────
	draw_label(el.use_track_name_label_y, "Use First Track Name")
	if vis(el.use_track_name_toggle_btn.y, el.use_track_name_toggle_btn.h) then
		draw_button(el.use_track_name_toggle_btn.x, el.use_track_name_toggle_btn.y - scroll,
			el.use_track_name_toggle_btn.w, el.use_track_name_toggle_btn.h,
			STATE.use_first_track_name and "ON" or "OFF",
			STATE.use_first_track_name)
	end

	--  Toolbar Button Size slider 
	draw_label(el.toolbar_btn_size_label_y, "Toolbar Button Size")
	if vis(el.toolbar_btn_size_slider.y, el.toolbar_btn_size_slider.h) then
		draw_slider(el.toolbar_btn_size_slider.x, el.toolbar_btn_size_slider.y - scroll,
			el.toolbar_btn_size_slider.w, el.toolbar_btn_size_slider.h,
			STATE.toolbar_button_size,
			el.toolbar_btn_size_slider.min, el.toolbar_btn_size_slider.max)
	end

	--  Toolbar Position 
	draw_label(el.toolbar_label_y, "Toolbar Position")
	if vis(el.toolbar_top_btn.y, el.toolbar_top_btn.h) then
		draw_button(el.toolbar_top_btn.x, el.toolbar_top_btn.y - scroll,
			el.toolbar_top_btn.w, el.toolbar_top_btn.h, "Top",
			STATE.toolbar_position == "top")
		draw_button(el.toolbar_bottom_btn.x, el.toolbar_bottom_btn.y - scroll,
			el.toolbar_bottom_btn.w, el.toolbar_bottom_btn.h, "Bottom",
			STATE.toolbar_position == "bottom")
		draw_button(el.toolbar_hide_btn.x, el.toolbar_hide_btn.y - scroll,
			el.toolbar_hide_btn.w, el.toolbar_hide_btn.h, "Hide",
			STATE.toolbar_position == "hide")
	end

	-- ── Footer (non-scrolling) ───────────────────────────────────────────────
	local help_text = "Right-click to close"
	local help_w = gfx.measurestr(help_text)
	draw_text((gfx.w - help_w) / 2, gfx.h - 35, help_text, CONFIG.COLOR_TEXT_GREY)
end


local function render()
	-- Only render if state has changed or window was resized
	if not STATE.dirty and STATE.cached_gfx_size.w == gfx.w and STATE.cached_gfx_size.h == gfx.h then
		return
	end

	gfx.dest = -1 -- Draw to main window

	if STATE.view == "settings" then
		gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.settings_font_size)
		draw_settings_view()
	elseif STATE.view == "help" then
		gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.font_size)
		draw_help_view()
	else
		gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.font_size)
		STATE.toolbar_buttons = draw_main_view()
	end

	gfx.update()
	STATE.dirty = false
end

-- ============================================================================
-- MOUSE INPUT HELPERS
-- ============================================================================

-- Update mouse button state (called at end of mouse handlers)
local function update_mouse_state(is_left_down, is_right_down, is_middle_down)
	STATE.mouse_was_down = is_left_down
	STATE.right_click_was_down = is_right_down
	STATE.middle_click_was_down = is_middle_down
end

-- Check if mouse is over a toolbar button
local function get_hovered_toolbar_button(mouse_x, mouse_y)
	if not STATE.toolbar_buttons then
		return nil
	end

	for _, btn in ipairs(STATE.toolbar_buttons) do
		if mouse_x >= btn.x and mouse_x <= btn.x + btn.w and mouse_y >= btn.y and mouse_y <= btn.y + btn.h then
			return btn
		end
	end
	return nil
end

-- Find which set box the mouse is over
local function get_clicked_box(mouse_x, mouse_y, scroll_offset)
	local boxes = calculate_set_box_positions()

	for _, box in ipairs(boxes) do
		local visible_y = box.y - scroll_offset
		if mouse_x >= box.x and mouse_x <= box.x + box.w and mouse_y >= visible_y and mouse_y <= visible_y + box.h then
			return box
		end
	end
	return nil
end

-- Check if mouse is over create button
local function is_over_create_button(mouse_x, mouse_y)
	local dx = mouse_x - STATE.create_button_pos.x
	local dy = mouse_y - STATE.create_button_pos.y
	local distance = math.sqrt(dx * dx + dy * dy)
	return distance <= CONFIG.CREATE_SET_BUTTON_SIZE
end

-- Helper function to calculate cursor position from mouse x coordinate
local function calculate_cursor_position_from_mouse(text, text_x, mouse_x)
	local relative_x = mouse_x - text_x
	gfx.setfont(1, CONFIG.DEFAULT_FONT, STATE.font_size)

	-- Handle click before text
	if relative_x <= 0 then
		return 0
	end

	-- Find which character position was clicked
	local cursor_pos = #text
	for i = 1, #text do
		local substr = text:sub(1, i)
		local char_width = gfx.measurestr(substr)
		if relative_x < char_width then
			-- Check if click is closer to left or right side of character
			local prev_width = i > 1 and gfx.measurestr(text:sub(1, i - 1)) or 0
			local mid_point = prev_width + (char_width - prev_width) / 2
			cursor_pos = relative_x < mid_point and (i - 1) or i
			break
		end
	end

	return cursor_pos
end

-- ============================================================================
-- MOUSE INPUT HANDLERS
-- ============================================================================

local function handle_mouse_wheel_scroll(view)
	local mouse_wheel = gfx.mouse_wheel

	if view == "settings" then
		if mouse_wheel ~= STATE.settings_last_mouse_wheel then
			local wheel_delta = mouse_wheel - STATE.settings_last_mouse_wheel
			STATE.settings_scroll_offset = STATE.settings_scroll_offset - (wheel_delta * STATE.scroll_speed)

			if STATE.settings_cached_elements then
				STATE.settings_scroll_offset =
					math.max(0, math.min(STATE.settings_scroll_offset, STATE.settings_cached_elements.max_scroll))
			end

			STATE.settings_last_mouse_wheel = mouse_wheel
			STATE.dirty = true
		end
	elseif view == "help" then
		if mouse_wheel ~= STATE.help_last_mouse_wheel then
			local wheel_delta = mouse_wheel - STATE.help_last_mouse_wheel
			STATE.help_scroll_offset = math.max(
				0,
				math.min(
					STATE.help_max_scroll,
					STATE.help_scroll_offset - (wheel_delta * STATE.scroll_speed)
				)
			)
			STATE.help_last_mouse_wheel = mouse_wheel
			STATE.dirty = true
		end
	else
		if mouse_wheel ~= STATE.last_mouse_wheel then
			local wheel_delta = mouse_wheel - STATE.last_mouse_wheel
			STATE.scroll_offset = STATE.scroll_offset - (wheel_delta * STATE.scroll_speed)

			local max_scroll = calculate_max_scroll()
			STATE.scroll_offset = math.max(0, math.min(STATE.scroll_offset, max_scroll))

			STATE.last_mouse_wheel = mouse_wheel
			STATE.dirty = true
		end
	end
end

local function handle_ctrl_click_modifiers(clicked_box, is_left_press, is_right_press)
	if not clicked_box or STATE.editing_set_id then
		return false
	end

	-- Handle "All Tracks" set
	if clicked_box.set_id == CONFIG.ALL_TRACKS_SET_ID then
		if is_left_press then
			toggle_set_mute(AllTracksSet.get_all_track_ids())
			STATE.dirty = true
			return true
		elseif is_right_press then
			toggle_set_solo(AllTracksSet.get_all_track_ids())
			STATE.dirty = true
			return true
		end
	else
		-- Handle regular set
		local set = find_set(clicked_box.set_id)
		if set then
			if is_left_press then
				toggle_set_mute(set.trackIndices)
				STATE.dirty = true
				return true
			elseif is_right_press then
				toggle_set_solo(set.trackIndices)
				STATE.dirty = true
				return true
			end
		end
	end

	return false
end

local function handle_toolbar_button_click(button_id, is_left_click)
	if button_id == "sort_by_color" then
		if is_left_click then
			STATE.auto_sort_by_color = not STATE.auto_sort_by_color
			if STATE.auto_sort_by_color then
				sort_sets_by_color()
			end
		else
			sort_sets_by_color()
		end
		request_save()
		STATE.dirty = true
		return true
	elseif button_id == "ab_mode" then
		if is_left_click then
			STATE.ab_mode = not STATE.ab_mode
			request_save()
			STATE.dirty = true
			return true
		end
	elseif button_id == "tcp_hide" then
		if is_left_click then
			STATE.auto_hide_tcp = not STATE.auto_hide_tcp

			if STATE.selected_set_id then
				local set = find_set(STATE.selected_set_id)
				if set and is_set_selected(set.trackIndices) then
					if STATE.auto_hide_tcp then
						show_only_tracks_in_set(set.trackIndices, true, false)
					else
						show_all_tracks(true, false)
					end
				end
			end

			request_save()
			STATE.dirty = true
			return true
		end
	elseif button_id == "mcp_hide" then
		if is_left_click then
			STATE.auto_hide_mcp = not STATE.auto_hide_mcp

			if STATE.selected_set_id then
				local set = find_set(STATE.selected_set_id)
				if set and is_set_selected(set.trackIndices) then
					if STATE.auto_hide_mcp then
						show_only_tracks_in_set(set.trackIndices, false, true)
					else
						show_all_tracks(false, true)
					end
				end
			end

			request_save()
			STATE.dirty = true
			return true
		end
	elseif button_id == "dock_toggle" then
		if is_left_click then
			STATE.is_docked = not STATE.is_docked
			gfx.dock(STATE.is_docked and 1 or 0)
			request_save()
			STATE.dirty = true
			return true
		end
	elseif button_id == "help_view" then
		if is_left_click then
			if STATE.view == "help" then
				STATE.view = "main"
				STATE.last_mouse_wheel = gfx.mouse_wheel
			else
				STATE.view = "help"
				STATE.help_scroll_offset = 0
				STATE.help_last_mouse_wheel = gfx.mouse_wheel
			end
			STATE.dirty = true
			return true
		end
	end

	return false
end

local function handle_toolbar_interaction(mouse_x, mouse_y, is_left_press, is_right_press)
	if STATE.view ~= "main" or not STATE.toolbar_buttons then
		return false
	end

	local btn = get_hovered_toolbar_button(mouse_x, mouse_y)
	if not btn then
		return false
	end

	if is_left_press then
		return handle_toolbar_button_click(btn.action, true)
	elseif is_right_press then
		return handle_toolbar_button_click(btn.action, false)
	end

	return false
end

local function handle_mouse_chord(clicked_box, is_left_down, is_right_press, is_middle_press)
	if not STATE.left_click_set_id or STATE.editing_set_id then
		return false
	end

	-- Detect mouse chord: left held + middle pressed = OVERWRITE
	if is_left_down and is_middle_press then
		local set = find_set(STATE.left_click_set_id)
		if set then
			local new_tracks = get_selected_tracks()
			overwrite_set(STATE.left_click_set_id, new_tracks)
			request_save()
			STATE.chord_triggered = true
			STATE.dirty = true
			return true
		end
	end

	-- Detect mouse chord: left held + right pressed
	if is_left_down and is_right_press then
		-- Check if right-click is on a different set (copy color) or same set (randomize)
		if clicked_box and clicked_box.set_id ~= STATE.left_click_set_id and clicked_box.set_id ~= CONFIG.ALL_TRACKS_SET_ID then
			-- Different set: COPY COLOR from left-clicked set to right-clicked set
			local source_set = find_set(STATE.left_click_set_id)
			local target_set = find_set(clicked_box.set_id)
			if source_set and target_set then
				target_set.selectedColor = source_set.selectedColor
				request_save()
				STATE.chord_triggered = true
				STATE.dirty = true
				return true
			end
		else
			-- Same set or no clicked box: RANDOMIZE COLOR
			local set = find_set(STATE.left_click_set_id)
			if set then
				set.selectedColor = generate_random_color()
				request_save()
				STATE.chord_triggered = true
				STATE.dirty = true
				return true
			end
		end
	end

	return false
end

local function handle_right_click(clicked_box, is_left_down)
	if is_left_down then
		return false -- Chord takes priority
	end

	-- Right-click in help view: return to main
	if STATE.view == "help" then
		STATE.view = "main"
		STATE.last_mouse_wheel = gfx.mouse_wheel
		STATE.dirty = true
		return true
	end

	if clicked_box and clicked_box.set_id ~= CONFIG.ALL_TRACKS_SET_ID then
		-- Right-click on set: enter edit mode
		local set = find_set(clicked_box.set_id)
		if set then
			STATE.editing_set_id = clicked_box.set_id
			STATE.editing_text = set.name
			STATE.cursor_position = #set.name
			STATE.editing_text_selected = true
			STATE.selection_start = 0
			STATE.selection_end = #set.name
			STATE.selection_dragging = false
			STATE.view = "main"
			STATE.dirty = true
		end
	else
		-- Right-click outside: exit edit mode or toggle settings
		if STATE.editing_set_id then
			STATE.editing_set_id = nil
			STATE.editing_text = ""
			STATE.cursor_position = 0
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.selection_dragging = false
			STATE.dirty = true
		else
			if STATE.view == "main" then
				STATE.view = "settings"
				STATE.settings_scroll_offset = 0
				STATE.settings_cached_elements = nil
				STATE.settings_last_mouse_wheel = gfx.mouse_wheel
			else
				STATE.view = "main"
				STATE.last_mouse_wheel = gfx.mouse_wheel
			end
			STATE.dirty = true
		end
	end

	return true
end

local function handle_middle_click(clicked_box)
	if not clicked_box or clicked_box.set_id == CONFIG.ALL_TRACKS_SET_ID then
		return false
	end

	local set = find_set(clicked_box.set_id)
	if set then
		delete_set(set.id)
		STATE.selected_set_id = nil
		STATE.editing_set_id = nil
		STATE.left_click_set_id = nil
		STATE.chord_triggered = false
		return true
	end

	return false
end

local function handle_create_button_click()
	local tracks = get_selected_tracks()
	local selected_color = CONFIG.COLOR_BOX_SELECTED
	if #tracks > 0 then
		local first_track = find_track_by_id(tracks[1])
		if first_track then
			selected_color = get_track_color(first_track)
		end
	end

	local set_name
	if STATE.use_first_track_name and #tracks > 0 then
		local first_track = find_track_by_id(tracks[1])
		set_name = get_track_name(first_track) or "Set " .. (#STATE.sets + 1)
	else
		set_name = "Set " .. (#STATE.sets + 1)
	end

	create_set(set_name, tracks)
	STATE.last_create_button_click_time = reaper.time_precise()
	STATE.dirty = true
end

local function handle_edit_mode_click(clicked_box, mouse_x)
	if not clicked_box or STATE.editing_set_id ~= clicked_box.set_id then
		return false
	end

	local text_width = gfx.measurestr(STATE.editing_text)
	local text_x = clicked_box.x + (clicked_box.w - text_width) / 2
	local cursor_pos = calculate_cursor_position_from_mouse(STATE.editing_text, text_x, mouse_x)

	local current_time = reaper.time_precise()
	local time_diff = current_time - STATE.last_click_time

	if time_diff < CONFIG.DOUBLE_CLICK_TIME then
		-- Double-click: select all text
		STATE.editing_text_selected = true
		STATE.selection_start = 0
		STATE.selection_end = #STATE.editing_text
		STATE.cursor_position = #STATE.editing_text
		STATE.dirty = true
	else
		-- Single click: start new selection
		STATE.editing_text_selected = false
		STATE.selection_start = cursor_pos
		STATE.selection_end = cursor_pos
		STATE.selection_dragging = true
		STATE.cursor_position = cursor_pos
		STATE.dirty = true
	end

	STATE.last_click_time = current_time
	return true
end

local function handle_set_left_click_press(clicked_box, mouse_y)
	if clicked_box.set_id == CONFIG.ALL_TRACKS_SET_ID then
		AllTracksSet.handle_click()
		return true
	end

	-- Start tracking for potential drag
	STATE.left_click_set_id = clicked_box.set_id
	STATE.chord_triggered = false
	STATE.drag_start_time = reaper.time_precise()
	STATE.drag_start_y = mouse_y

	-- Find the index of clicked set
	for i, set in ipairs(STATE.sets) do
		if set.id == clicked_box.set_id then
			STATE.drag_start_index = i
			break
		end
	end

	return true
end

local function handle_set_left_click_release()
	if not STATE.left_click_set_id or STATE.chord_triggered or STATE.editing_set_id then
		return false
	end

	if STATE.left_click_set_id == CONFIG.ALL_TRACKS_SET_ID then
		return false -- Already handled on press
	end

	local set = find_set(STATE.left_click_set_id)
	if not set then
		return false
	end

	local is_selected = is_set_selected(set.trackIndices)

	if STATE.ab_mode then
		-- A/B mode: toggle between selecting/soloing or deselecting/unsoloing
		reaper.PreventUIRefresh(1)

		if is_selected then
			reaper.Main_OnCommand(40297, 0) -- Unselect all tracks
			reaper.SoloAllTracks(0)

			-- Apply auto-hide: show all tracks when deselecting
			if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
				show_all_tracks(STATE.auto_hide_tcp, STATE.auto_hide_mcp)
			end
		else
			reaper.Main_OnCommand(40297, 0)
			for _, track_id in ipairs(set.trackIndices) do
				local track = find_track_by_id(track_id)
				if track then
					reaper.SetTrackSelected(track, true)
				end
			end

			reaper.SoloAllTracks(0)

			for _, track_id in ipairs(set.trackIndices) do
				local track = find_track_by_id(track_id)
				if track then
					reaper.SetMediaTrackInfo_Value(track, "I_SOLO", 1)
				end
			end

			-- Apply auto-hide: show only tracks in set
			if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
				show_only_tracks_in_set(set.trackIndices, STATE.auto_hide_tcp, STATE.auto_hide_mcp)
			end
		end

		reaper.PreventUIRefresh(-1)
		reaper.UpdateArrange()
	else
		-- Default mode: toggle selection
		if is_selected then
			set_selected_tracks({})

			if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
				show_all_tracks(STATE.auto_hide_tcp, STATE.auto_hide_mcp)
			end
		else
			set_selected_tracks(set.trackIndices)

			if STATE.auto_hide_tcp or STATE.auto_hide_mcp then
				show_only_tracks_in_set(set.trackIndices, STATE.auto_hide_tcp, STATE.auto_hide_mcp)
			end
		end
	end

	STATE.selected_set_id = is_selected and nil or STATE.left_click_set_id
	STATE.dirty = true

	return true
end

local function handle_left_click_outside(clicked_box, clicked_create_button)
	if clicked_box or clicked_create_button then
		return false
	end

	if STATE.editing_set_id then
		-- Save changes and exit edit mode
		if STATE.editing_text ~= "" then
			local set = find_set(STATE.editing_set_id)
			if set then
				rename_set(STATE.editing_set_id, STATE.editing_text)
				request_save()
			end
		end
		STATE.editing_set_id = nil
		STATE.editing_text = ""
		STATE.editing_text_selected = false
		STATE.cursor_position = 0
		STATE.selection_start = nil
		STATE.selection_end = nil
		STATE.selection_dragging = false
		STATE.dirty = true
		return true
	else
		-- Check for double-click to create new set
		local current_time = reaper.time_precise()
		local time_diff = current_time - STATE.last_click_time
		local time_since_create_button = current_time - STATE.last_create_button_click_time

		if time_diff < CONFIG.DOUBLE_CLICK_TIME and time_since_create_button > 0.1 then
			handle_create_button_click()
		else
			STATE.last_click_time = current_time
		end
		return true
	end
end

local function handle_drag_and_drop(is_dragging, is_left_down, mouse_y)
	-- Check if we should initiate drag
	if not STATE.drag_initiated and STATE.left_click_set_id and is_left_down and STATE.drag_start_time then
		local time_held = reaper.time_precise() - STATE.drag_start_time
		local distance_moved = math.abs(mouse_y - STATE.drag_start_y)

		-- Initiate drag if long-press time met and moved beyond threshold
		if time_held >= CONFIG.DRAG_LONG_PRESS_TIME and distance_moved >= CONFIG.DRAG_THRESHOLD then
			STATE.drag_initiated = true
			STATE.dragging_set_id = STATE.left_click_set_id
			STATE.drag_ghost_y = STATE.drag_start_y
			STATE.chord_triggered = true -- Prevent normal click action
			STATE.dirty = true
		end
	end

	-- Handle active drag
	if STATE.drag_initiated and STATE.dragging_set_id then
		if is_left_down then
			-- Update ghost position
			STATE.drag_ghost_y = mouse_y

			-- Calculate insertion index
			STATE.drag_hover_insert_index = calculate_insertion_index(mouse_y)

			-- Handle auto-scroll
			local content_top = get_content_area_top()
			local content_bottom = get_content_area_bottom()

			if mouse_y < content_top + CONFIG.DRAG_AUTO_SCROLL_ZONE then
				-- Scroll up
				local distance_from_edge = content_top + CONFIG.DRAG_AUTO_SCROLL_ZONE - mouse_y
				local scroll_amount = (distance_from_edge / CONFIG.DRAG_AUTO_SCROLL_ZONE)
					* CONFIG.DRAG_AUTO_SCROLL_SPEED
				STATE.scroll_offset = math.max(0, STATE.scroll_offset - scroll_amount)
			elseif mouse_y > content_bottom - CONFIG.DRAG_AUTO_SCROLL_ZONE then
				-- Scroll down
				local distance_from_edge = mouse_y - (content_bottom - CONFIG.DRAG_AUTO_SCROLL_ZONE)
				local scroll_amount = (distance_from_edge / CONFIG.DRAG_AUTO_SCROLL_ZONE)
					* CONFIG.DRAG_AUTO_SCROLL_SPEED
				local max_scroll = calculate_max_scroll()
				STATE.scroll_offset = math.min(max_scroll, STATE.scroll_offset + scroll_amount)
			end

			STATE.dirty = true
			return true
		else
			-- Mouse released - complete the drag
			local insert_index = STATE.drag_hover_insert_index
			local dragged_index = STATE.drag_start_index

			if insert_index and dragged_index then
				-- Only perform reorder if position actually changed
				if insert_index ~= dragged_index then
					-- Perform the reorder
					local dragged_set = table.remove(STATE.sets, dragged_index)
					table.insert(STATE.sets, insert_index, dragged_set)

					-- Disable auto-sort since user manually reordered
					if STATE.auto_sort_by_color then
						STATE.auto_sort_by_color = false
					end

					request_save()
					STATE.cached_boxes = nil
				end
			end

			-- Reset drag state
			STATE.drag_initiated = false
			STATE.dragging_set_id = nil
			STATE.drag_start_time = nil
			STATE.drag_start_y = nil
			STATE.drag_start_index = nil
			STATE.drag_hover_insert_index = nil
			STATE.drag_ghost_y = nil
			STATE.dirty = true

			return true
		end
	end

	return false
end

local function handle_text_selection_drag(is_dragging, mouse_x)
	if not STATE.editing_set_id or not STATE.selection_dragging or not is_dragging then
		return false
	end

	local boxes = calculate_set_box_positions()
	local editing_box = nil

	for _, box in ipairs(boxes) do
		if box.set_id == STATE.editing_set_id then
			editing_box = box
			break
		end
	end

	if editing_box then
		local text_width = gfx.measurestr(STATE.editing_text)
		local text_x = editing_box.x + (editing_box.w - text_width) / 2
		local cursor_pos = calculate_cursor_position_from_mouse(STATE.editing_text, text_x, mouse_x)

		STATE.selection_end = cursor_pos
		STATE.cursor_position = cursor_pos

		if STATE.selection_start ~= 0 or STATE.selection_end ~= #STATE.editing_text then
			STATE.editing_text_selected = false
		end

		STATE.dirty = true
		return true
	end

	return false
end

local function handle_settings_interaction(mouse_x, mouse_y, is_left_down, is_left_press)
	if not STATE.settings_cached_elements then
		return false
	end

	local el = STATE.settings_cached_elements
	local scroll = STATE.settings_scroll_offset

	local function is_over(elem)
		local adjusted_y = elem.y - scroll
		return mouse_x >= elem.x
			and mouse_x <= elem.x + elem.w
			and mouse_y >= adjusted_y
			and mouse_y <= adjusted_y + elem.h
	end

	-- Handle slider dragging
	if STATE.settings_dragging_slider then
		if is_left_down then
			local slider = el[STATE.settings_dragging_slider]
			if slider then
				local relative_x = mouse_x - slider.x
				local percent = math.max(0, math.min(1, relative_x / slider.w))
				local value = math.floor(slider.min + percent * (slider.max - slider.min))

				if STATE.settings_dragging_slider == "width_slider" then
					STATE.box_width = value
					STATE.cached_boxes = nil
				elseif STATE.settings_dragging_slider == "height_slider" then
					STATE.box_height = value
					STATE.cached_boxes = nil
				elseif STATE.settings_dragging_slider == "scroll_slider" then
					STATE.scroll_speed = value
				elseif STATE.settings_dragging_slider == "toolbar_btn_size_slider" then
					STATE.toolbar_button_size = value
				end

				STATE.dirty = true
				request_save()
			end
		else
			STATE.settings_dragging_slider = nil
		end
		return true
	end

	-- Handle button/slider clicks
	if is_left_press then
		if is_over(el.font_dec_btn) then
			STATE.font_size = math.max(8, STATE.font_size - 1)
			STATE.settings_cached_elements = nil
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.font_inc_btn) then
			STATE.font_size = math.min(32, STATE.font_size + 1)
			STATE.settings_cached_elements = nil
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.settings_font_dec_btn) then
			STATE.settings_font_size = math.max(8, STATE.settings_font_size - 1)
			STATE.settings_cached_elements = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.settings_font_inc_btn) then
			STATE.settings_font_size = math.min(32, STATE.settings_font_size + 1)
			STATE.settings_cached_elements = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.growth_down_btn) then
			STATE.growth_direction = "down"
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.growth_up_btn) then
			STATE.growth_direction = "up"
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.width_slider) then
			STATE.settings_dragging_slider = "width_slider"
			local relative_x = mouse_x - el.width_slider.x
			local percent = math.max(0, math.min(1, relative_x / el.width_slider.w))
			STATE.box_width = math.floor(el.width_slider.min + percent * (el.width_slider.max - el.width_slider.min))
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.height_slider) then
			STATE.settings_dragging_slider = "height_slider"
			local relative_x = mouse_x - el.height_slider.x
			local percent = math.max(0, math.min(1, relative_x / el.height_slider.w))
			STATE.box_height =
				math.floor(el.height_slider.min + percent * (el.height_slider.max - el.height_slider.min))
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.scroll_slider) then
			STATE.settings_dragging_slider = "scroll_slider"
			local relative_x = mouse_x - el.scroll_slider.x
			local percent = math.max(0, math.min(1, relative_x / el.scroll_slider.w))
			STATE.scroll_speed =
				math.floor(el.scroll_slider.min + percent * (el.scroll_slider.max - el.scroll_slider.min))
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.toolbar_btn_size_slider) then
			STATE.settings_dragging_slider = "toolbar_btn_size_slider"
			local relative_x = mouse_x - el.toolbar_btn_size_slider.x
			local percent = math.max(0, math.min(1, relative_x / el.toolbar_btn_size_slider.w))
			STATE.toolbar_button_size = math.floor(
				el.toolbar_btn_size_slider.min
				+ percent * (el.toolbar_btn_size_slider.max - el.toolbar_btn_size_slider.min)
			)
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.all_tracks_toggle_btn) then
			STATE.show_all_tracks_set = not STATE.show_all_tracks_set
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.use_track_name_toggle_btn) then
			STATE.use_first_track_name = not STATE.use_first_track_name
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.toolbar_top_btn) then
			STATE.toolbar_position = "top"
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.toolbar_bottom_btn) then
			STATE.toolbar_position = "bottom"
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		elseif is_over(el.toolbar_hide_btn) then
			STATE.toolbar_position = "hide"
			STATE.cached_boxes = nil
			STATE.dirty = true
			request_save()
			return true
		end
	end

	return false
end

local function handle_mouse_input()
	local mouse_x = gfx.mouse_x
	local mouse_y = gfx.mouse_y
	local mouse_cap = gfx.mouse_cap

	-- Handle mouse wheel scrolling
	handle_mouse_wheel_scroll(STATE.view)

	-- Skip if mouse hasn't changed
	if mouse_x == STATE.last_mouse_x and mouse_y == STATE.last_mouse_y and mouse_cap == STATE.last_mouse_cap then
		return
	end

	STATE.last_mouse_x = mouse_x
	STATE.last_mouse_y = mouse_y
	STATE.last_mouse_cap = mouse_cap

	-- Detect mouse button states using named constants
	local is_left_down = (mouse_cap & MOUSE.LEFT == MOUSE.LEFT)
	local is_right_down = (mouse_cap & MOUSE.RIGHT == MOUSE.RIGHT)
	local is_middle_down = (mouse_cap & MOUSE.MIDDLE == MOUSE.MIDDLE)
	local is_ctrl_held = (mouse_cap & MOUSE.CTRL == MOUSE.CTRL) or (mouse_cap & MOUSE.CMD == MOUSE.CMD)

	-- Detect button transitions
	local is_left_press = is_left_down and not STATE.mouse_was_down
	local is_right_press = is_right_down and not STATE.right_click_was_down
	local is_middle_press = is_middle_down and not STATE.middle_click_was_down
	local is_left_release = not is_left_down and STATE.mouse_was_down
	local is_dragging = is_left_down and STATE.mouse_was_down

	-- Update toolbar hover state
	local prev_hover = STATE.toolbar_hover_button
	STATE.toolbar_hover_button = nil
	if STATE.view == "main" then
		local btn = get_hovered_toolbar_button(mouse_x, mouse_y)
		if btn then
			STATE.toolbar_hover_button = btn.action
		end
	end
	if prev_hover ~= STATE.toolbar_hover_button then
		STATE.dirty = true
	end

	-- Determine clicked elements
	local clicked_create_button = (is_left_press or is_left_down) and is_over_create_button(mouse_x, mouse_y)
	local clicked_box = nil
	if is_left_press or is_right_press or is_middle_press or is_left_down then
		clicked_box = get_clicked_box(mouse_x, mouse_y, STATE.scroll_offset)
	end

	-- Handle Ctrl+Click modifiers (mute/solo)
	if is_ctrl_held and (is_left_press or is_right_press) then
		if handle_ctrl_click_modifiers(clicked_box, is_left_press, is_right_press) then
			update_mouse_state(is_left_down, is_right_down, is_middle_down)
			return
		end
	end

	-- Handle toolbar button clicks
	if is_left_press or is_right_press then
		if handle_toolbar_interaction(mouse_x, mouse_y, is_left_press, is_right_press) then
			update_mouse_state(is_left_down, is_right_down, is_middle_down)
			return
		end
	end

	-- Handle mouse chords
	if (is_right_press or is_middle_press) and is_left_down then
		if handle_mouse_chord(clicked_box, is_left_down, is_right_press, is_middle_press) then
			update_mouse_state(is_left_down, is_right_down, is_middle_down)
			return
		end
	end

	-- Handle right click (only if not part of a chord)
	if is_right_press and not is_left_down then
		if handle_right_click(clicked_box, is_left_down) then
			update_mouse_state(is_left_down, true, is_middle_down)
			return
		end
	end
	STATE.right_click_was_down = is_right_down

	-- Handle settings view
	if STATE.view == "settings" then
		handle_settings_interaction(mouse_x, mouse_y, is_left_down, is_left_press)
		update_mouse_state(is_left_down, is_right_down, is_middle_down)
		return
	end

	-- Absorb all input in help view (right-click already handled above)
	if STATE.view == "help" then
		update_mouse_state(is_left_down, is_right_down, is_middle_down)
		return
	end

	-- Handle middle click (delete set)
	if is_middle_press then
		if handle_middle_click(clicked_box) then
			update_mouse_state(is_left_down, is_right_down, true)
			return
		end
	end
	STATE.middle_click_was_down = is_middle_down

	-- Handle create button click
	if is_left_press and clicked_create_button then
		handle_create_button_click()
		update_mouse_state(is_left_down, is_right_down, is_middle_down)
		return
	end

	-- Handle drag and drop (must come before other left-click handlers)
	if (is_left_down or is_left_release) and not STATE.editing_set_id then
		if handle_drag_and_drop(is_dragging, is_left_down, mouse_y) then
			-- If drag is active or just completed, skip other handlers
			if is_left_release then
				STATE.left_click_set_id = nil
				STATE.chord_triggered = false
			end
			update_mouse_state(is_left_down, is_right_down, is_middle_down)
			return
		end
	end

	-- Handle left click press on set
	if is_left_press and clicked_box then
		if STATE.editing_set_id == clicked_box.set_id then
			handle_edit_mode_click(clicked_box, mouse_x)
		else
			handle_set_left_click_press(clicked_box, mouse_y)
		end
		update_mouse_state(is_left_down, is_right_down, is_middle_down)
		return
	end

	-- Handle left click release
	if is_left_release then
		handle_set_left_click_release()
		STATE.left_click_set_id = nil
		STATE.chord_triggered = false

		-- Reset drag state if not already reset
		if not STATE.drag_initiated then
			STATE.drag_start_time = nil
			STATE.drag_start_y = nil
			STATE.drag_start_index = nil
		end
	end

	-- Handle left click outside
	if is_left_press and not clicked_box and not clicked_create_button then
		handle_left_click_outside(clicked_box, clicked_create_button)
		update_mouse_state(is_left_down, is_right_down, is_middle_down)
		return
	end

	-- Handle text selection dragging
	handle_text_selection_drag(is_dragging, mouse_x)

	-- Stop dragging when mouse is released
	if STATE.selection_dragging and not is_left_down then
		STATE.selection_dragging = false
		if STATE.selection_start == STATE.selection_end then
			STATE.selection_start = nil
			STATE.selection_end = nil
		end
	end

	update_mouse_state(is_left_down, is_right_down, is_middle_down)
end

-- ============================================================================
-- KEYBOARD INPUT
-- ============================================================================

local function handle_editing_input(char)
	-- Don't process if no char or special system chars
	if char == 0 or char < 0 then
		return
	end

	-- Enter/Return key - confirm edit (checking multiple possible codes)
	-- 13 = Enter/Return, 6579564 = numpad Enter
	if char == 13 or char == 6579564 or char == 10 then
		if STATE.editing_text ~= "" then
			local set = find_set(STATE.editing_set_id)
			if set then
				rename_set(STATE.editing_set_id, STATE.editing_text)
				request_save()
			end
		end
		STATE.editing_set_id = nil
		STATE.editing_text = ""
		STATE.cursor_position = 0
		STATE.selection_start = nil
		STATE.selection_end = nil
		STATE.selection_dragging = false
		STATE.dirty = true
		return
	end

	-- Escape key (27) - cancel edit or deselect
	if char == 27 then
		if STATE.editing_text_selected or (STATE.selection_start and STATE.selection_end) then
			STATE.editing_text_selected = false
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.dirty = true
		else
			STATE.editing_set_id = nil
			STATE.editing_text = ""
			STATE.editing_text_selected = false
			STATE.cursor_position = 0
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.selection_dragging = false
			STATE.dirty = true
		end
		return
	end

	-- Backspace (8) or Delete (127) - delete character or selected text
	if char == 8 then
		-- Backspace: delete character before cursor or delete selection
		if STATE.selection_start and STATE.selection_end and STATE.selection_start ~= STATE.selection_end then
			-- Delete selected text
			local sel_start = math.min(STATE.selection_start, STATE.selection_end)
			local sel_end = math.max(STATE.selection_start, STATE.selection_end)
			local before = STATE.editing_text:sub(1, sel_start)
			local after = STATE.editing_text:sub(sel_end + 1)
			STATE.editing_text = before .. after
			STATE.cursor_position = sel_start
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.editing_text_selected = false
			STATE.dirty = true
		elseif STATE.editing_text_selected then
			-- Delete all selected text
			STATE.editing_text = ""
			STATE.editing_text_selected = false
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.cursor_position = 0
			STATE.dirty = true
		elseif STATE.cursor_position > 0 then
			-- Delete character before cursor
			local before = STATE.editing_text:sub(1, STATE.cursor_position - 1)
			local after = STATE.editing_text:sub(STATE.cursor_position + 1)
			STATE.editing_text = before .. after
			STATE.cursor_position = STATE.cursor_position - 1
			STATE.dirty = true
		end
		return
	end

	if char == 127 then
		-- Delete: delete character after cursor or delete selection
		if STATE.selection_start and STATE.selection_end and STATE.selection_start ~= STATE.selection_end then
			-- Delete selected text
			local sel_start = math.min(STATE.selection_start, STATE.selection_end)
			local sel_end = math.max(STATE.selection_start, STATE.selection_end)
			local before = STATE.editing_text:sub(1, sel_start)
			local after = STATE.editing_text:sub(sel_end + 1)
			STATE.editing_text = before .. after
			STATE.cursor_position = sel_start
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.editing_text_selected = false
			STATE.dirty = true
		elseif STATE.editing_text_selected then
			-- Delete all selected text
			STATE.editing_text = ""
			STATE.editing_text_selected = false
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.cursor_position = 0
			STATE.dirty = true
		elseif STATE.cursor_position < #STATE.editing_text then
			-- Delete character after cursor
			local before = STATE.editing_text:sub(1, STATE.cursor_position)
			local after = STATE.editing_text:sub(STATE.cursor_position + 2)
			STATE.editing_text = before .. after
			STATE.dirty = true
		end
		return
	end

	-- Regular character input (printable ASCII range)
	if char >= 32 and char <= 126 then
		if STATE.selection_start and STATE.selection_end and STATE.selection_start ~= STATE.selection_end then
			-- Replace selected text with new character
			local sel_start = math.min(STATE.selection_start, STATE.selection_end)
			local sel_end = math.max(STATE.selection_start, STATE.selection_end)
			local before = STATE.editing_text:sub(1, sel_start)
			local after = STATE.editing_text:sub(sel_end + 1)
			STATE.editing_text = before .. string.char(char) .. after
			STATE.cursor_position = sel_start + 1
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.editing_text_selected = false
		elseif STATE.editing_text_selected then
			-- Replace all selected text with new character
			STATE.editing_text = string.char(char)
			STATE.editing_text_selected = false
			STATE.selection_start = nil
			STATE.selection_end = nil
			STATE.cursor_position = 1
		else
			-- Insert at cursor position
			local before = STATE.editing_text:sub(1, STATE.cursor_position)
			local after = STATE.editing_text:sub(STATE.cursor_position + 1)
			STATE.editing_text = before .. string.char(char) .. after
			STATE.cursor_position = STATE.cursor_position + 1
		end
		STATE.dirty = true
		return
	end
end

local function handle_keybinds(char)
	-- Space: Play/Pause (char code 32)
	if char == 32 then
		reaper.Main_OnCommand(40044, 0) -- Transport: Play/Stop
		return
	end
end

local function handle_keyboard_input(char)
	-- Escape key cancels drag
	if char == 27 and STATE.drag_initiated then
		STATE.drag_initiated = false
		STATE.dragging_set_id = nil
		STATE.drag_start_time = nil
		STATE.drag_start_y = nil
		STATE.drag_start_index = nil
		STATE.drag_hover_insert_index = nil
		STATE.drag_ghost_y = nil
		STATE.left_click_set_id = nil
		STATE.chord_triggered = false
		STATE.dirty = true
		return
	end

	if STATE.editing_set_id == nil then
		handle_keybinds(char)
	else
		handle_editing_input(char)
	end
end

-- ============================================================================
-- MAIN LOOP
-- ============================================================================

local function main()
	-- Initialize window if needed
	if gfx.w == 0 or gfx.h == 0 then
		gfx.init(PROGNAME, 400, 600)
		-- Apply saved dock state immediately after window creation
		gfx.dock(STATE.is_docked and 1 or 0)
		STATE.dirty = true
		STATE.last_frame_time = reaper.time_precise()
		-- Sync mouse wheel to current value to avoid initial scroll jump
		STATE.last_mouse_wheel = gfx.mouse_wheel
		STATE.settings_last_mouse_wheel = gfx.mouse_wheel
		STATE.help_last_mouse_wheel = gfx.mouse_wheel
	end

	-- Sync is_docked with actual gfx dock state (user may have docked/undocked
	-- via REAPER's own docker UI, e.g. dragging the window)
	local actual_docked = (gfx.dock(-1) & 1) == 1
	if actual_docked ~= STATE.is_docked then
		STATE.is_docked = actual_docked
		request_save()
		STATE.dirty = true
	end

	-- Get character once per frame (gfx.getchar consumes the buffer!)
	local char = gfx.getchar()

	-- Check if window was closed first (always check this)
	if char == -1 then
		-- Save before exiting if there are pending changes
		if STATE.pending_save then
			save_sets()
		end
		return -- Exit the defer loop
	end

	-- ALWAYS process input regardless of frame timing
	-- Invalidate frame cache at start of each frame for fresh track data
	invalidate_frame_cache()

	check_project_changed()
	handle_mouse_input()
	handle_keyboard_input(char)
	process_pending_saves()

	-- Frame rate limiting for rendering only
	local current_time = reaper.time_precise()
	local time_since_last_frame = current_time - STATE.last_frame_time

	-- Only render if enough time has elapsed
	if time_since_last_frame >= CONFIG.MIN_FRAME_TIME then
		STATE.last_frame_time = current_time

		-- Check for window resize
		if gfx.w ~= STATE.cached_gfx_size.w or gfx.h ~= STATE.cached_gfx_size.h then
			STATE.dirty = true
			STATE.cached_boxes = nil
			STATE.settings_cached_elements = nil
		end

		render()
	end

	reaper.defer(main)
end

-- ============================================================================
-- INITIALIZATION
-- ============================================================================

STATE.current_project = get_current_project_id()
load_sets()

main()

--[[
Copyright (C) 2026 captaincurrie

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
--]]

-- @description reamacros - REAper MACROS
-- @version 1.1
-- @author captaincurrie
-- @license GNU General Public License
-- @date 2026-03-13
-- @about reamacros - REAper MACROS

--[[ PROGRAM SPEC

# Description

This program emulates the Ableton Live macro controller. Reaper does not
provide a centralized location to organize macro controllers; this script
intends to rectify that.

## What is a Macro?

A **macro** is a named, parameterized value (ranging from 0-100%) that can
be linked to **parameters** in a project. A parameter is any FX parameter
accessible via Reaper's FX system. Each macro can be linked to multiple
individual parameters. Each macro controls its linked parameters via a
draggable arc **knob**  the knob is the visual control, the macro is the
whole thing (name, value, links).

# Architecture: JSFX Signal Path

  All parameter control runs at audio block rate (~1-5ms), not at the Lua
  defer rate (~30-60ms). The Lua script is purely a GUI/configuration layer.

  ## Signal Flow
    1. **Reamacros.jsfx** (controller, one instance on master or chosen track):
       - Holds 64 sliders, each carrying a macro value (0..1)
       - Automation envelopes can be drawn on these sliders in the arrange view
       - Every @block, writes all slider values into gmem[]

    2. **Reamacros_link.jsfx** (one instance per linked parameter, on target track):
       - Reads its assigned macro value from gmem[] every @block
       - Applies quadratic Bezier curve + scale + offset math
       - Writes the result to slider8

    3. **Reaper parameter modulation** (native, sample-accurate):
       - slider8 of each link JSFX is wired to the target FX parameter
         via Reaper's built-in parameter modulation system
       - This final leg is resolved by the audio engine natively

  ## Consequence
    The entire path (envelope -> gmem -> curve math -> parameter modulation)
    runs at block rate. The Lua defer loop only polls slider values for GUI
    display (knob positions reflecting automation). No TrackFX_SetParam calls
    are made on target parameters from Lua.

  ## FX Container Architecture
    Per-track link JSFX instances are placed inside an FX Container named
    "Reamacros Links". The container keeps the FX chain clean (one collapsed
    item per track regardless of link count). Each link JSFX's slider8 output
    is mapped to a container parameter, and the target FX's parameter link
    (plink) references the container parameter, not the internal JSFX directly.
    Signal path: link JSFX slider8 → container param mapping → plink → target.

  ## Caveats
    - Track processing order: if the controller track renders after a target
      track in a given buffer, link JSFX on that target read 1-buffer-stale
      gmem (~1-5ms, not 30-60ms).
    - Manual knob drags from the GUI write to the controller JSFX slider via
      TrackFX_SetParam, which propagates via gmem next block.
    - One link JSFX per linked parameter inside the container; up to 256
      container parameter mappings per track (Reaper limit).

# Layout (fixed, top to bottom)

  1. Toolbar (icon-style 2828 buttons + right-aligned status text)
  2. Separator
  3. Macro bank (wrapping knob grid)
  4. Separator
  5. Add-link button (last-touched FX parameter, centered)
  6. Separator
  7. Filter bar + action buttons
  8. Parameter table (linked parameters)
  9. Separator
  10. Curve editor (for selected parameter link)

# Section Details

## Toolbar
  - Buttons (2828, icon-style):
      - [+] Add Macro (green): appends a new macro, selects it
      - [0] Reset All: sets all macro values to 0
      - [JSFX] Move JSFX: moves automation JSFX to the first selected
        track (with confirmation dialog); tooltip shows current host track
      - [X] Clear All Links (red): removes all parameter links from all
        macros (with confirmation dialog)
  - Right-aligned status text on same row: shows the last status message
    for 3 seconds, then idle text "reamacros v<VERSION>"

## Macro Bank
  - Macros arranged in a wrapping grid; cell width = KNOB_SIZE + KNOB_SPACING
  - Wrap: cols = floor((avail_w + KNOB_SPACING) / cell_w)
  - Initial window width = DEFAULT_MACROS * cell_w - KNOB_SPACING + 20
  - Each macro cell (top to bottom):
      - Draggable arc knob (vertical drag adjusts value; click selects)
      - Percentage value in accent color
      - Macro name; double-click to edit inline
      - Link count ("N lnk") in grey
  - Selected macro has an accent-colored border
  - Double-click arc: reset value to 0
  - Middle-click arc: remove macro (minimum 1 must remain)
  - Right-click arc context menu:
      - Show Envelope: creates/shows Reaper automation envelope
      - Reset to 0 / Set to 100%
      - Copy Value / Paste Value (internal clipboard, shows %)
      - Remove Macro (red, disabled if only 1 macro)

## Add-Link Button
  - Centered button showing the last-touched FX parameter as:
    "TrackName > FXName > ParamName"
  - Green when linkable; grey with tooltip when already linked to any macro
  - Click to link to the currently selected macro
  - Installs a Reamacros_link.jsfx on the target track and wires
    parameter modulation automatically
  - When no parameter touched yet: centered grey hint text

## Filter Bar
  - Regex search input (300px) with placeholder hint
  - [X] clear filter button
  - View toggle (when filter empty): "Sel" (selected macro only) / "All"
  - When filter non-empty: greyed label "Regex active  showing all knobs";
    matches case-insensitively against track, FX, and param names
  - "Clear Table" (red): removes all links from the selected macro
  - "Clear Orphans" (amber): removes links to tracks/FX that no longer exist
  - "Learn" toggle: when ON (green), every newly-touched FX parameter is
    automatically linked to the selected macro; duplicates rejected silently

## Parameter Table
  - Columns: Macro | Track | FX | Name | Curve | M | X
  - Macro: macro name in accent color; entire row is a selectable (sets
    selected_link for curve editor)
  - Track: track name with colored background from Reaper track color;
    "[!]" prefix in warning red if track is missing
  - FX: FX name; "[!]" prefix in warning red if FX can't be resolved
  - Name: parameter name
  - Curve: inline sparkline (78px) with Bzier curve + macro position tick;
    supports drag-and-drop (DragDropPayload "REAMACROS_CURVE") to copy
    curve shapes between links
  - M: mute toggle  when muted (red), the link is frozen at its current
    value; muted rows are dimmed
  - X: remove link (red button); also removes the link JSFX and clears
    parameter modulation on the target
  - Column headers (Macro, Track, FX, Name) are clickable to sort
    ascending/descending; active sort column shown with / and accent color

## Curve Editor
  - Shown below the parameter table when a link row is selected
  - Full-width canvas with quadratic Bzier curve visualization
  - Three draggable handles:
      - P0 (blue, x=0): controls y0 (output when macro = 0)
      - P1 (orange, floating): control point (cx, cy) for curve shape
      - P2 (blue, x=1): controls y1 (output when macro = 1)
  - Dragging P0 or P2 preserves the curve offset (cy adjusts to maintain
    relative shape)
  - Double-click P1: reset to linear (preserving y0/y1)
  - White vertical line + dot shows current macro value on the curve
  - Right-side button column:
      - "Linear": reset shape to linear, keep y0/y1
      - "Full Range": reset to linear 01
      - "Invert": swap y0y1 and mirror cy
      - Two DragDouble inputs for precise y0 and y1 editing
  - Grid lines (44) drawn for visual reference
  - When no link selected: shows grey hint text (only if links exist)

## Confirmation Dialog
  - Modal popup for destructive actions (move JSFX, clear all links)
  - Message text with Confirm (green) and Cancel (red) buttons

# Automation via Reaper Envelopes
  - On init the script writes Effects/Reamacros.jsfx (controller, 64 sliders)
    and Effects/Reamacros_link.jsfx (per-link curve processor)
  - Controller JSFX installed on Master Track by default if not found elsewhere
  - On init, all tracks are searched (master first) for the controller JSFX;
    relocating it persists across sessions
  - The defer loop polls controller JSFX slider values only for GUI display
    (updating knob positions to reflect automation playback)
  - Macro value changes from GUI knob drags write back to the controller JSFX
    slider, which propagates via gmem at block rate
  - All actual parameter control flows through the JSFX gmem + parameter
    modulation path at audio block rate
  - To automate: show the controller JSFX slider's envelope in arrange view

# Persistence
  - Saves to: <project_dir>/.<scriptname> (hidden dotfile, plain-text k=v)
  - Falls back to Reaper ExtState if project has no disk path
  - Loads project file first, then falls back to ExtState
  - Auto-saves on window close

# Macro Data Model
  Each macro:
    name      string
    value     float 0.01.0
    links[]   each link:
      track_guid   string (Reaper track GUID)
      fx_guid      string (Reaper FX GUID for re-resolution)
      fx           int (0-based FX index, auto-updated on resolve)
      param        int (0-based param index)
      curve        table {y0, y1, cx, cy} (quadratic Bzier)
      label        string ("Track > FX > Param")
      track_name   string
      fx_name      string
      param_name   string
      track_color  int (native Reaper color)
      muted        bool
      link_fx_idx      int (item position inside the container, 0-based)
      container_fx_idx int (top-level FX index of the container on the track)
      container_param  int (container parameter index mapping slider8 for plink)
      link_fx_guid     string (GUID of the link JSFX instance for resolution)

# Constants
  KNOB_SIZE       = 72
  KNOB_SPACING    = 8   (matches ImGui_StyleVar_ItemSpacing x)
  KNOB_DRAG_SPEED = 0.004
  DEFAULT_MACROS  = 8
  MAX_MACROS      = 64

# Requires
  - ReaImGui extension (mandatory)
--]]

local r = reaper
local math_floor = math.floor
local math_max = math.max
local math_min = math.min
local math_abs = math.abs
local math_sqrt = math.sqrt
local math_cos = math.cos
local math_sin = math.sin

--
-- Dependency check
--
if not r.ImGui_CreateContext then
	r.MB("ReaImGui is required.\nInstall via ReaPack -> ReaTeam Extensions.", "reamacros", 0)
	return
end

--
-- Constants
--
local SCRIPT_NAME = "reamacros"
local SCRIPT_VERSION = 1
local DEFAULT_MACROS = 8
local MAX_MACROS = 64
local AUTOMATION_FX_NAME = "Reamacros_master"
local EXT_SECTION = SCRIPT_NAME .. "_v" .. SCRIPT_VERSION
local EXT_KEY = "state"
local VERSION = "1.0"
local KNOB_SIZE = 72
local KNOB_SPACING = 8 -- matches ImGui_StyleVar_ItemSpacing x value
local KNOB_DRAG_SPEED = 0.004
local SEP_THICKNESS = 2.0 -- section separator line thickness (px)
local SEP_MARGIN = 8 -- spacing above and below each section separator (px)
local SEP_COLOR = 0x505050FF

-- Precomputed arc geometry for knob drawing (avoids trig every frame)
local ARC_START_RAD = math.pi * 0.75
local ARC_SWEEP_RAD = math.pi * 1.5
local ARC_SEG = 48
local ARC_UNIT = {} -- [0..ARC_SEG] = { c=cos, s=sin }
do
	for s = 0, ARC_SEG do
		local a = ARC_START_RAD + (s / ARC_SEG) * ARC_SWEEP_RAD
		ARC_UNIT[s] = { c = math.cos(a), s = math.sin(a) }
	end
end

--
-- State
--
local ctx
local macros = {}
local automation_fx_idx = -1
local automation_track = nil
local macro_clipboard = nil -- float 0..1, for copy/paste macro value
local guid_cache = {} -- frame-level cache: guid -> track|false; cleared each loop
local ui = {
	selected = 1,
	status_msg = "",
	status_time = 0,
	filter_text = "",
	show_all = false,
	editing_name = nil, -- knob index currently being name-edited, or nil
	editing_name_focus = false, -- true on the frame we enter edit mode (auto-focus)
	selected_link = nil, -- {mi=, li=} of the selected parameter row
	confirm = nil, -- { msg=, action= } pending confirmation
	sort_col = nil, -- nil = no sort; 0=Macro 1=Track 2=FX 3=Name
	sort_asc = true, -- true = ascending, false = descending
	learn_mode = false,
	learn_last_touched = nil, -- { trnum, fxnum, pnum } of last auto-added param
}
local last_tick_time = 0
-- Layout state set by draw_curve_editor each frame, read by draw_modulation_controls
local curve_editor_ox = 0
local curve_editor_cw = 0
--
-- Macro factory
--
local function new_macro(i)
	return {
		name = "Macro " .. i,
		value = 0.0,
		links = {},
		-- link = { track_guid, fx, param, curve, scale, offset, out_min, out_max, label }
	}
end

local function init_macros(count)
	local m = {}
	for i = 1, count do
		m[i] = new_macro(i)
	end
	return m
end

-- Forward declarations (defined later)
local apply_macro
local resolve_fx_index
local eval_curve
local default_curve
local get_track_by_guid
local set_status

--
-- Automation JSFX helpers
--
local function get_jsfx_path()
	return r.GetResourcePath() .. "/Effects/" .. AUTOMATION_FX_NAME .. ".jsfx"
end

-- gmem base offset. Chosen to be well clear of common JSFX namespaces.
-- Must match the value hardcoded in Reamacros_link.jsfx.
local GMEM_BASE = 4096
local GMEM_SLOTS_PER_MACRO = 1 -- just the processed value for now
local CONTAINER_NAME = "Reamacros Links"
local LINK_FX_NAME = "Reamacros_slave"

local function get_link_jsfx_path()
	return r.GetResourcePath() .. "/Effects/" .. LINK_FX_NAME .. ".jsfx"
end

--
-- FX Container helpers
--

-- Find the Reamacros Links container on a track; return top-level FX index or -1
local function find_container_on_track(tr)
	local n = r.TrackFX_GetCount(tr)
	for i = 0, n - 1 do
		local _, name = r.TrackFX_GetFXName(tr, i, "")
		if name:find(CONTAINER_NAME, 1, true) then
			return i
		end
	end
	return -1
end

-- Find or create the Reamacros Links container on a track
local function find_or_create_container(tr)
	local idx = find_container_on_track(tr)
	if idx >= 0 then return idx end
	idx = r.TrackFX_AddByName(tr, "Container", false, -1)
	if idx >= 0 then
		r.TrackFX_SetNamedConfigParm(tr, idx, "renamed_name", CONTAINER_NAME)
	end
	return idx
end

-- Get number of items inside a container
local function get_container_count(tr, container_fx)
	local rv, cnt_str = r.TrackFX_GetNamedConfigParm(tr, container_fx, "container_count")
	return rv and (tonumber(cnt_str) or 0) or 0
end

-- Get the full encoded FX address for item at position item_idx inside container
local function get_container_item_address(tr, container_fx, item_idx)
	local rv, addr_str = r.TrackFX_GetNamedConfigParm(tr, container_fx, "container_item." .. item_idx)
	if rv then return tonumber(addr_str) end
	return nil
end

-- Resolve a link's JSFX to its full encoded FX address (container-aware)
local function get_link_fx_address(tr, lk)
	if not tr or lk.link_fx_idx == nil then return nil end
	if lk.container_fx_idx ~= nil then
		return get_container_item_address(tr, lk.container_fx_idx, lk.link_fx_idx)
	end
	-- Legacy fallback: direct top-level FX index (pre-container migration)
	return lk.link_fx_idx
end

local function ensure_jsfx_file()
	-- Controller JSFX: reads its own sliders (which carry automation envelopes)
	-- and writes the raw macro values into gmem every block.
	-- Curve math lives in the link JSFX so parameters can differ per link.
	local path = get_jsfx_path()
	local f = io.open(path, "r")
	if not f then
		f = io.open(path, "w")
		if not f then return end
		f:write("desc:" .. AUTOMATION_FX_NAME .. "\n")
		f:write("// Auto-generated by reamacros.lua -- do not edit\n")
		for i = 1, MAX_MACROS do
			f:write(("slider%d:0<0,1,0.001>Macro %d\n"):format(i, i))
		end
		f:write("\n@init\n")
		f:write(("  reamacros_gmem_base = %d;\n"):format(GMEM_BASE))
		f:write("\n@slider\n")
		-- Write on slider change for immediate response to manual knob moves
		for i = 1, MAX_MACROS do
			f:write(("  gmem[reamacros_gmem_base + %d] = slider%d;\n"):format(i - 1, i))
		end
		f:write("\n@block\n")
		-- Also write every block so automation envelopes are picked up
		-- at block rate (sample-accurate within the block).
		for i = 1, MAX_MACROS do
			f:write(("  gmem[reamacros_gmem_base + %d] = slider%d;\n"):format(i - 1, i))
		end
		f:close()
	else
		f:close()
	end

	-- Link JSFX: one instance per linked parameter on the target track.
	-- Reads a gmem slot, applies quadratic Bezier + scale/offset, writes
	-- slider8. The user (or Lua) links slider8 to the target FX parameter
	-- via Reaper's parameter modulation, which is resolved at audio-engine
	-- level -- this is the sample-accurate leg of the signal path.
	-- Always (re)write link JSFX so upgrades pick up new slider definitions.
	-- Existing instances already placed in projects keep running the in-memory
	-- code until Reaper reloads the JSFX (reopen project / rescan FX).
	local lpath = get_link_jsfx_path()
	local lf = io.open(lpath, "w")
	if lf then
		lf:write("desc:" .. LINK_FX_NAME .. "\n")
		lf:write("// Auto-generated by reamacros.lua -- do not edit\n")
		lf:write("// Insert on target track. Link slider8 to the target FX parameter.\n")
		lf:write("slider1:0<0,63,1>Macro Slot\n")
		lf:write("slider2:0<0,1,0.0001>Curve y0 (out at macro=x0)\n")
		lf:write("slider3:1<0,1,0.0001>Curve y1 (out at macro=x1)\n")
		lf:write("slider4:0.5<0.02,0.98,0.0001>Curve cx (relative to [x0,x1])\n")
		lf:write("slider5:0.5<0,1,0.0001>Curve cy\n")
		lf:write("slider6:1<-8,8,0.0001>Scale\n")
		lf:write("slider7:0<-1,1,0.0001>Offset\n")
		lf:write("slider8:0<0,1,0.0001>Output  [link this to target parameter]\n")
		lf:write("slider9:0<0,1,0.0001>Curve x0 (input threshold low)\n")
		lf:write("slider10:1<0,1,0.0001>Curve x1 (input threshold high)\n")
		lf:write("\n@init\n")
		lf:write(("  reamacros_gmem_base = %d;\n"):format(GMEM_BASE))
		lf:write("\n@block\n")
		lf:write("  macro_val = max(0, min(1, gmem[reamacros_gmem_base + slider1]));\n")
		lf:write("  _y0 = slider2; _y1 = slider3; _cx = slider4; _cy = slider5;\n")
		lf:write("  _x0 = slider9; _x1 = slider10;\n")
		lf:write("  // Piecewise: flat y0 below x0, flat y1 above x1, bezier in between.\n")
		lf:write("  (macro_val <= _x0) ? (\n")
		lf:write("    curved = _y0;\n")
		lf:write("  ) : (macro_val >= _x1) ? (\n")
		lf:write("    curved = _y1;\n")
		lf:write("  ) : (\n")
		lf:write("    _range = _x1 - _x0;\n")
		lf:write("    (_range < 0.000001) ? (\n")
		lf:write("      curved = _y0;\n")
		lf:write("    ) : (\n")
		lf:write("      _mx = (macro_val - _x0) / _range;\n")
		lf:write("      _a = 1 - 2*_cx; _b = 2*_cx;\n")
		lf:write("      _disc = _b*_b + 4*_a*_mx;\n")
		lf:write("      _disc = max(0, _disc);\n")
		lf:write("      t = (abs(_a) < 0.000001)\n")
		lf:write("          ? (abs(_b) < 0.000001 ? _mx : _mx/_b)\n")
		lf:write("          : (-_b + sqrt(_disc)) / (2*_a);\n")
		lf:write("      t = max(0, min(1, t));\n")
		lf:write("      _mt = 1 - t;\n")
		lf:write("      curved = _mt*_mt*_y0 + 2*_mt*t*_cy + t*t*_y1;\n")
		lf:write("    );\n")
		lf:write("  );\n")
		lf:write("  out_val = max(0, min(1, curved * slider6 + slider7));\n")
		lf:write("  slider8 = out_val;\n")
		lf:write("  sliderchange(slider8);\n")
		lf:close()
	end
end


local function find_automation_fx_on_track(tr)
	local n = r.TrackFX_GetCount(tr)
	for i = 0, n - 1 do
		local _, name = r.TrackFX_GetFXName(tr, i, "")
		if name:find(AUTOMATION_FX_NAME, 1, true) then
			return i
		end
	end
	return -1
end

local function find_or_install_automation_fx()
	-- Search master first, then all tracks
	local master = r.GetMasterTrack(0)
	if master then
		local idx = find_automation_fx_on_track(master)
		if idx >= 0 then
			automation_track = master
			return idx
		end
	end
	for i = 0, r.CountTracks(0) - 1 do
		local tr = r.GetTrack(0, i)
		local idx = find_automation_fx_on_track(tr)
		if idx >= 0 then
			automation_track = tr
			return idx
		end
	end
	-- Not found anywhere; install on master
	if not master then
		return -1
	end
	automation_track = master
	return r.TrackFX_AddByName(master, AUTOMATION_FX_NAME, false, -1)
end

local function write_macro_to_fx(i, val)
	if automation_fx_idx < 0 or not automation_track then
		return
	end
	r.TrackFX_SetParam(automation_track, automation_fx_idx, i - 1, val)
end

local function sync_all_to_fx()
	for i, mac in ipairs(macros) do
		write_macro_to_fx(i, mac.value)
	end
end

-- Push curve and modulation parameters into a link JSFX instance.
-- fx_addr must be the full encoded FX address (container-aware).
-- Called whenever a link's curve/scale/offset changes.
local function sync_link_jsfx_params(tr, fx_addr, macro_slot, crv, scale, offset)
	if not tr or not fx_addr then return end
	r.TrackFX_SetParam(tr, fx_addr, 0, macro_slot)      -- slider1: macro slot (0-based)
	r.TrackFX_SetParam(tr, fx_addr, 1, crv.y0)          -- slider2: y0
	r.TrackFX_SetParam(tr, fx_addr, 2, crv.y1)          -- slider3: y1
	r.TrackFX_SetParam(tr, fx_addr, 3, crv.cx)          -- slider4: cx
	r.TrackFX_SetParam(tr, fx_addr, 4, crv.cy)          -- slider5: cy
	r.TrackFX_SetParam(tr, fx_addr, 5, scale or 1.0)    -- slider6: scale
	r.TrackFX_SetParam(tr, fx_addr, 6, offset or 0.0)   -- slider7: offset
	-- slider8 (index 7) is the output; do not write it, Reaper owns it
	r.TrackFX_SetParam(tr, fx_addr, 8, crv.x0 or 0.0)   -- slider9: x0 (input threshold low)
	r.TrackFX_SetParam(tr, fx_addr, 9, crv.x1 or 1.0)   -- slider10: x1 (input threshold high)
end

-- Install a link JSFX inside the "Reamacros Links" container on the target
-- track, map its output (slider8) to a container parameter, and wire
-- parameter modulation from the container parameter  target FX parameter.
-- Returns the item index inside the container, or -1 on failure.
local function install_link_jsfx(tr, lk, macro_idx)
	if not tr then return -1 end

	-- Find or create the per-track container
	local container_fx = find_or_create_container(tr)
	if container_fx < 0 then
		set_status("Container create failed")
		return -1
	end

	-- Reaper container addressing (see reaper.h / ReaScript docs):
	--   encoded_addr = 0x2000000 + (1 + container_idx)
	--                            + (1 + pos_in_container) * (1 + top_level_fx_count)
	-- top_level_fx_count is the FX count at the enclosing level (includes the
	-- container itself). To INSERT at that address via TrackFX_AddByName,
	-- pass instantiate = -1 - encoded_addr (== -(encoded_addr + 1)).
	local tc = r.TrackFX_GetCount(tr)
	local cnt = get_container_count(tr, container_fx)
	local pos = cnt -- insert at end of container
	local insert_addr = 0x2000000 + (1 + container_fx) + (1 + pos) * (1 + tc)

	-- TrackFX_AddByName sentinel: -1000 - encoded_addr for positional insert
	local new_fx = r.TrackFX_AddByName(tr, LINK_FX_NAME, false, -1000 - insert_addr)
	if new_fx < 0 then
		set_status(("Link insert failed (addr=0x%X, tc=%d, cnt=%d)"):format(insert_addr, tc, cnt))
		return -1
	end

	-- Determine the item position of the newly added FX (should be at end)
	local new_cnt = get_container_count(tr, container_fx)
	local item_idx = new_cnt - 1
	if item_idx < 0 then
		set_status("Link insert: container_count did not increase")
		return -1
	end

	lk.container_fx_idx = container_fx
	lk.link_fx_idx = item_idx

	-- Get the encoded address and store the GUID for future resolution
	local fx_addr = get_container_item_address(tr, container_fx, item_idx)
	if not fx_addr then return -1 end
	lk.link_fx_guid = r.TrackFX_GetFXGUID(tr, fx_addr) or ""

	-- Set link JSFX parameters (curve, scale, offset, macro slot)
	local crv = lk.curve or default_curve(0.0, 1.0)
	sync_link_jsfx_params(tr, fx_addr, macro_idx - 1, crv, lk.scale, lk.offset)

	-- Respect pre-existing mute state (e.g., loaded from project)
	if lk.muted then
		local mac = macros[macro_idx]
		if mac then
			local frozen = eval_curve(crv, mac.value) * (lk.scale or 1.0) + (lk.offset or 0.0)
			r.TrackFX_SetParam(tr, fx_addr, 5, 0.0)
			r.TrackFX_SetParam(tr, fx_addr, 6, math_max(-1, math_min(1, frozen)))
		end
	end

	-- Map link JSFX slider8 (param 7) to a container parameter
	local rv, cp_str = r.TrackFX_GetNamedConfigParm(
		tr, container_fx,
		"container_map.add." .. item_idx .. ".7"
	)
	if rv then
		lk.container_param = tonumber(cp_str)
	end

	-- Wire parameter modulation: target FX param → container parameter
	-- The container parameter mirrors slider8 of the link JSFX inside it.
	local target_fx = resolve_fx_index(tr, lk)
	if target_fx >= 0 and lk.container_param ~= nil then
		local parm_prefix = ("param.%d.plink."):format(lk.param)
		r.TrackFX_SetNamedConfigParm(tr, target_fx, parm_prefix .. "active",  "1")
		r.TrackFX_SetNamedConfigParm(tr, target_fx, parm_prefix .. "effect",  tostring(container_fx))
		r.TrackFX_SetNamedConfigParm(tr, target_fx, parm_prefix .. "param",   tostring(lk.container_param))
		r.TrackFX_SetNamedConfigParm(tr, target_fx, parm_prefix .. "scale",   "1")
		r.TrackFX_SetNamedConfigParm(tr, target_fx, parm_prefix .. "offset",  "0")
	end

	return item_idx
end

-- Remove the link JSFX installed for a given link, clean up the container
-- parameter mapping, and clear parameter modulation wiring on the target.
local function remove_link_jsfx(tr, lk)
	if not tr then return end

	-- Clear parameter modulation on target FX first
	local target_fx = resolve_fx_index(tr, lk)
	if target_fx >= 0 then
		r.TrackFX_SetNamedConfigParm(tr, target_fx, ("param.%d.plink.active"):format(lk.param), "0")
	end

	local container_fx = lk.container_fx_idx
	if container_fx ~= nil and lk.link_fx_idx ~= nil then
		-- Delete container parameter mapping
		if lk.container_param ~= nil then
			r.TrackFX_GetNamedConfigParm(tr, container_fx, "container_map.delete." .. lk.container_param)
		end

		-- Delete the link JSFX from inside the container
		local fx_addr = get_container_item_address(tr, container_fx, lk.link_fx_idx)
		if fx_addr then
			r.TrackFX_Delete(tr, fx_addr)
		end

		-- If container is now empty, delete the container itself
		local cnt = get_container_count(tr, container_fx)
		if cnt == 0 then
			r.TrackFX_Delete(tr, container_fx)
			-- Invalidate container_fx_idx on all other links pointing to this track
			-- (container is gone; they'll be re-resolved if needed)
			local tguid = lk.track_guid
			for _, mac in ipairs(macros) do
				for _, other in ipairs(mac.links) do
					if other ~= lk and other.track_guid == tguid and other.container_fx_idx == container_fx then
						other.container_fx_idx = nil
						other.link_fx_idx = nil
					end
				end
			end
		else
			-- Items after the deleted one shifted; re-resolve all links on this track
			local tguid = lk.track_guid
			local deleted_idx = lk.link_fx_idx
			for _, mac in ipairs(macros) do
				for _, other in ipairs(mac.links) do
					if other ~= lk and other.track_guid == tguid
					   and other.container_fx_idx == container_fx
					   and other.link_fx_idx and other.link_fx_idx > deleted_idx then
						other.link_fx_idx = other.link_fx_idx - 1
					end
				end
			end
		end
	elseif lk.link_fx_idx ~= nil then
		-- Legacy: direct top-level FX (pre-container migration)
		r.TrackFX_Delete(tr, lk.link_fx_idx)
	end

	lk.link_fx_idx = nil
	lk.container_fx_idx = nil
	lk.container_param = nil
	lk.link_fx_guid = nil
end

-- After load, re-resolve link JSFX positions for each link by scanning
-- inside the per-track "Reamacros Links" container. Falls back to scanning
-- top-level FX for legacy (pre-container) links.
local function resolve_all_link_jsfx()
	for mi, mac in ipairs(macros) do
		for _, lk in ipairs(mac.links) do
			local tr = get_track_by_guid(lk.track_guid)
			if not tr then goto next_link end

			-- Try to find the container on this track
			local container_fx = find_container_on_track(tr)
			if container_fx >= 0 then
				lk.container_fx_idx = container_fx
				local cnt = get_container_count(tr, container_fx)
				local found = false

				-- First pass: match by GUID (most reliable)
				if lk.link_fx_guid and lk.link_fx_guid ~= "" then
					for ci = 0, cnt - 1 do
						local addr = get_container_item_address(tr, container_fx, ci)
						if addr then
							local guid = r.TrackFX_GetFXGUID(tr, addr)
							if guid and guid == lk.link_fx_guid then
								lk.link_fx_idx = ci
								found = true
								break
							end
						end
					end
				end

				-- Second pass: match by macro slot + param values
				if not found then
					for ci = 0, cnt - 1 do
						local addr = get_container_item_address(tr, container_fx, ci)
						if addr then
							local _, name = r.TrackFX_GetFXName(tr, addr, "")
							if name:find(LINK_FX_NAME, 1, true) then
								local slot = r.TrackFX_GetParam(tr, addr, 0)
								if math_floor(slot + 0.5) == (mi - 1) then
									lk.link_fx_idx = ci
									lk.link_fx_guid = r.TrackFX_GetFXGUID(tr, addr) or ""
									found = true
									break
								end
							end
						end
					end
				end

				-- Resolve container_param by scanning container mappings
				if found and lk.container_param == nil and lk.link_fx_idx ~= nil then
					-- Walk existing mappings to find one pointing to our item's param 7
					-- (container_map.get.N returns "fx_idx\tparam_idx")
					local pi = 0
					while pi < 256 do
						local rv, info = r.TrackFX_GetNamedConfigParm(
							tr, container_fx, "container_map.get." .. pi)
						if not rv then break end
						-- info is "internal_fx_idx\tparam_idx" (tab-separated)
						local mfx, mpar = info:match("^(%d+)\t(%d+)$")
						if mfx and tonumber(mfx) == lk.link_fx_idx and tonumber(mpar) == 7 then
							lk.container_param = pi
							break
						end
						pi = pi + 1
					end
				end
			else
				-- No container; scan top-level FX for legacy link JSFX
				if not lk.link_fx_idx then
					local n = r.TrackFX_GetCount(tr)
					for i = 0, n - 1 do
						local _, name = r.TrackFX_GetFXName(tr, i, "")
						if name:find(LINK_FX_NAME, 1, true) then
							local slot = r.TrackFX_GetParam(tr, i, 0)
							if math_floor(slot + 0.5) == (mi - 1) then
								lk.link_fx_idx = i
								lk.container_fx_idx = nil
								break
							end
						end
					end
				end
			end

			::next_link::
		end
	end
end

local function poll_automation_fx()
	if automation_fx_idx < 0 or not automation_track then
		return
	end
	-- Guard against track having been deleted
	if not r.ValidatePtr(automation_track, "MediaTrack*") then
		automation_track = nil
		automation_fx_idx = -1
		return
	end

	-- Read slider values for GUI display only.
	-- Actual parameter control flows through the JSFX gmem + parameter
	-- modulation path at audio block rate.
	for i, mac in ipairs(macros) do
		local val = r.TrackFX_GetParam(automation_track, automation_fx_idx, i - 1)
		if math_abs(val - mac.value) > 0.001 then
			mac.value = val
		end
	end
end

--
-- Persistence
--
local function serialize()
	local t = {}
	local function w(s)
		t[#t + 1] = s
	end
	w("version=" .. VERSION)
	w("count=" .. #macros)
	for i, m in ipairs(macros) do
		w(("m%d.name=%s"):format(i, m.name))
		w(("m%d.val=%.6f"):format(i, m.value))
		w(("m%d.lc=%d"):format(i, #m.links))
		for j, lk in ipairs(m.links) do
			local crv = lk.curve or default_curve(lk.min or 0.0, lk.max or 1.0)
			w(("m%d.l%d.guid=%s"):format(i, j, lk.track_guid))
			w(("m%d.l%d.fxguid=%s"):format(i, j, lk.fx_guid or ""))
			w(("m%d.l%d.fx=%d"):format(i, j, lk.fx))
			w(("m%d.l%d.p=%d"):format(i, j, lk.param))
			w(("m%d.l%d.crv.y0=%.6f"):format(i, j, crv.y0))
			w(("m%d.l%d.crv.y1=%.6f"):format(i, j, crv.y1))
			w(("m%d.l%d.crv.cx=%.6f"):format(i, j, crv.cx))
			w(("m%d.l%d.crv.cy=%.6f"):format(i, j, crv.cy))
			w(("m%d.l%d.crv.x0=%.6f"):format(i, j, crv.x0 or 0.0))
			w(("m%d.l%d.crv.x1=%.6f"):format(i, j, crv.x1 or 1.0))
			w(("m%d.l%d.lbl=%s"):format(i, j, lk.label or ""))
			w(("m%d.l%d.trn=%s"):format(i, j, lk.track_name or ""))
			w(("m%d.l%d.fxn=%s"):format(i, j, lk.fx_name or ""))
			w(("m%d.l%d.pnm=%s"):format(i, j, lk.param_name or ""))
			w(("m%d.l%d.tcol=%d"):format(i, j, lk.track_color or 0))
			w(("m%d.l%d.muted=%d"):format(i, j, lk.muted and 1 or 0))
			w(("m%d.l%d.scale=%.6f"):format(i, j, lk.scale or 1.0))
			w(("m%d.l%d.offset=%.6f"):format(i, j, lk.offset or 0.0))
			w(("m%d.l%d.vymin=%.6f"):format(i, j, lk.view_ymin or 0.0))
			w(("m%d.l%d.vymax=%.6f"):format(i, j, lk.view_ymax or 1.0))
			w(("m%d.l%d.vxmin=%.6f"):format(i, j, lk.view_xmin or 0.0))
			w(("m%d.l%d.vxmax=%.6f"):format(i, j, lk.view_xmax or 1.0))
			w(("m%d.l%d.gy=%.6f"):format(i, j, lk.guide_y or 0.5))
			w(("m%d.l%d.gv=%d"):format(i, j, lk.guide_visible and 1 or 0))
			w(("m%d.l%d.lfxguid=%s"):format(i, j, lk.link_fx_guid or ""))
			if lk.container_param ~= nil then
				w(("m%d.l%d.cparam=%d"):format(i, j, lk.container_param))
			end
		end
	end
	return table.concat(t, "\n")
end

local function deserialize(str)
	if not str or str == "" then
		return nil
	end
	local d = {}
	for line in str:gmatch("[^\n]+") do
		local k, v = line:match("^(.-)=(.*)$")
		if k then
			d[k] = v
		end
	end
	local count = tonumber(d["count"])
	if not count then
		return nil
	end
	local m = {}
	for i = 1, count do
		local mac = {
			name = d[("m%d.name"):format(i)] or ("Macro " .. i),
			value = tonumber(d[("m%d.val"):format(i)]) or 0.0,
			links = {},
		}
		local lc = tonumber(d[("m%d.lc"):format(i)]) or 0
		for j = 1, lc do
			local lbl = d[("m%d.l%d.lbl"):format(i, j)] or ""
			local trn = d[("m%d.l%d.trn"):format(i, j)]
			local fxn = d[("m%d.l%d.fxn"):format(i, j)]
			local pnm = d[("m%d.l%d.pnm"):format(i, j)]
			-- backward compat: split old label "Track > FX > Param" if new fields absent
			if not trn or trn == "" then
				local parts = {}
				for seg in lbl:gmatch("[^>]+") do
					parts[#parts + 1] = seg:match("^%s*(.-)%s*$")
				end
				trn = parts[1] or ""
				fxn = parts[2] or ""
				pnm = parts[3] or lbl
			end
			-- Backward compat: old files have min/max, new files have crv.*
			local old_min = tonumber(d[("m%d.l%d.mn"):format(i, j)])
			local old_max = tonumber(d[("m%d.l%d.mx"):format(i, j)])
			local crv_y0 = tonumber(d[("m%d.l%d.crv.y0"):format(i, j)])
			local crv_y1 = tonumber(d[("m%d.l%d.crv.y1"):format(i, j)])
			local crv_cx = tonumber(d[("m%d.l%d.crv.cx"):format(i, j)])
			local crv_cy = tonumber(d[("m%d.l%d.crv.cy"):format(i, j)])
			local crv_x0 = tonumber(d[("m%d.l%d.crv.x0"):format(i, j)])
			local crv_x1 = tonumber(d[("m%d.l%d.crv.x1"):format(i, j)])
			local curve
			if crv_y0 then
				-- New format
				curve = {
					y0 = crv_y0, y1 = crv_y1 or 1.0,
					cx = crv_cx or 0.5, cy = crv_cy or 0.5,
					x0 = crv_x0 or 0.0, x1 = crv_x1 or 1.0,
				}
			else
				-- Legacy: reconstruct linear curve from min/max
				local y0 = old_min or 0.0
				local y1 = old_max or 1.0
				curve = { y0 = y0, y1 = y1, cx = 0.5, cy = (y0 + y1) * 0.5, x0 = 0.0, x1 = 1.0 }
			end
			local cparam_str = d[("m%d.l%d.cparam"):format(i, j)]
			mac.links[j] = {
				track_guid = d[("m%d.l%d.guid"):format(i, j)] or "",
				fx_guid = d[("m%d.l%d.fxguid"):format(i, j)] or "",
				fx = tonumber(d[("m%d.l%d.fx"):format(i, j)]) or 0,
				param = tonumber(d[("m%d.l%d.p"):format(i, j)]) or 0,
				curve = curve,
				scale = tonumber(d[("m%d.l%d.scale"):format(i, j)]) or 1.0,
				offset = tonumber(d[("m%d.l%d.offset"):format(i, j)]) or 0.0,
				view_ymin = tonumber(d[("m%d.l%d.vymin"):format(i, j)]) or 0.0,
				view_ymax = tonumber(d[("m%d.l%d.vymax"):format(i, j)]) or 1.0,
				view_xmin = tonumber(d[("m%d.l%d.vxmin"):format(i, j)]) or 0.0,
				view_xmax = tonumber(d[("m%d.l%d.vxmax"):format(i, j)]) or 1.0,
				guide_y = tonumber(d[("m%d.l%d.gy"):format(i, j)]) or 0.5,
				guide_visible = (d[("m%d.l%d.gv"):format(i, j)] == "1"),
				label = lbl,
				track_name = trn,
				fx_name = fxn,
				param_name = pnm,
				track_color = tonumber(d[("m%d.l%d.tcol"):format(i, j)]) or 0,
				muted = (d[("m%d.l%d.muted"):format(i, j)] == "1"),
				link_fx_guid = d[("m%d.l%d.lfxguid"):format(i, j)] or "",
				container_param = cparam_str and tonumber(cparam_str) or nil,
				-- link_fx_idx and container_fx_idx are resolved at runtime
			}
		end
		m[i] = mac
	end
	return m
end

--
-- Persistence: project file with ExtState fallback
--
local function get_project_path()
	local _, project_file = r.EnumProjects(-1, "")
	if project_file == "" then
		return nil
	end
	return project_file:match("^(.+)[/\\][^/\\]+$")
end

local function get_project_file_path()
	local proj_path = get_project_path()
	if not proj_path then
		return nil
	end
	return proj_path .. "/." .. SCRIPT_NAME
end

local function save_state()
	local data = serialize()
	local fpath = get_project_file_path()
	if fpath then
		local f = io.open(fpath, "w")
		if f then
			f:write(data)
			f:close()
			return
		end
	end
	-- fallback
	r.SetExtState(EXT_SECTION, EXT_KEY, data, true)
end

local function load_state()
	local fpath = get_project_file_path()
	if fpath then
		local f = io.open(fpath, "r")
		if f then
			local data = f:read("*a")
			f:close()
			local result = deserialize(data)
			if result then
				return result
			end
		end
	end
	-- fallback
	local saved = r.GetExtState(EXT_SECTION, EXT_KEY)
	return deserialize(saved)
end

--
-- REAPER helpers
--
get_track_by_guid = function(guid)
	local cached = guid_cache[guid]
	if cached ~= nil then
		return cached or nil -- false means "looked up but not found"
	end
	for i = 0, r.CountTracks(0) - 1 do
		local tr = r.GetTrack(0, i)
		local _, g = r.GetSetMediaTrackInfo_String(tr, "GUID", "", false)
		if g == guid then
			guid_cache[guid] = tr
			return tr
		end
	end
	local master = r.GetMasterTrack(0)
	local _, g = r.GetSetMediaTrackInfo_String(master, "GUID", "", false)
	if g == guid then
		guid_cache[guid] = master
		return master
	end
	guid_cache[guid] = false
	return nil
end

local function ensure_link_curves()
	for _, mac in ipairs(macros) do
		for _, lk in ipairs(mac.links) do
			if not lk.curve then
				lk.curve = default_curve(lk.min or 0.0, lk.max or 1.0)
			end
		end
	end
end

local function backfill_fx_guids()
	for _, mac in ipairs(macros) do
		for _, lk in ipairs(mac.links) do
			if not lk.fx_guid or lk.fx_guid == "" then
				local tr = get_track_by_guid(lk.track_guid)
				if tr and lk.fx >= 0 and lk.fx < r.TrackFX_GetCount(tr) then
					lk.fx_guid = r.TrackFX_GetFXGUID(tr, lk.fx) or ""
				end
			end
		end
	end
end

resolve_fx_index = function(tr, lk)
	if not lk.fx_guid or lk.fx_guid == "" then
		-- Legacy link without GUID; trust stored index
		return lk.fx
	end
	-- Fast path: check stored index first
	if lk.fx >= 0 and lk.fx < r.TrackFX_GetCount(tr) then
		local guid = r.TrackFX_GetFXGUID(tr, lk.fx)
		if guid and guid == lk.fx_guid then
			return lk.fx
		end
	end
	-- Scan all FX for matching GUID (FX may have moved index)
	local n = r.TrackFX_GetCount(tr)
	for i = 0, n - 1 do
		local guid = r.TrackFX_GetFXGUID(tr, i)
		if guid and guid == lk.fx_guid then
			lk.fx = i -- update stored index
			return i
		end
	end
	return -1 -- orphaned
end

apply_macro = function(macro, macro_idx)
	for _, lk in ipairs(macro.links) do
		local tr = get_track_by_guid(lk.track_guid)
		if lk.link_fx_idx == nil or not tr then
			goto continue
		end

		local fx_addr = get_link_fx_address(tr, lk)
		if not fx_addr then
			goto continue
		end

		-- Sync curve/scale/offset parameters to the link JSFX.
		-- The actual macro value propagates via gmem at audio block rate.
		if not lk.muted then
			sync_link_jsfx_params(
				tr, fx_addr,
				(macro_idx or 1) - 1,
				lk.curve or default_curve(0, 1),
				lk.scale, lk.offset
			)
		else
			-- Muted: freeze the output at the current value by setting
			-- scale=0 and offset=current mapped value on the link JSFX
			local frozen = eval_curve(lk.curve, macro.value) * (lk.scale or 1.0) + (lk.offset or 0.0)
			r.TrackFX_SetParam(tr, fx_addr, 5, 0.0)   -- scale=0
			r.TrackFX_SetParam(tr, fx_addr, 6, frozen) -- offset=frozen val
		end

		::continue::
	end
end

set_status = function(msg)
	ui.status_msg = msg
	ui.status_time = r.time_precise() + 3.0
end

local function select_first_link()
	local mac = macros[ui.selected]
	if mac and #mac.links > 0 then
		ui.selected_link = { mi = ui.selected, li = 1 }
	else
		ui.selected_link = nil
	end
end

--
-- Knob drawing
--
-- Returns: changed (bool), new_value (0..1)
-- Uses mouse delta drag (vertical) + double-click reset
local knob_drag_start = {} -- id -> { start_val, start_y }

local function draw_knob(id, value, size)
	local dl = r.ImGui_GetWindowDrawList(ctx)
	local sx, sy = r.ImGui_GetCursorScreenPos(ctx)
	local cx = sx + size * 0.5
	local cy = sy + size * 0.5
	local R = size * 0.5 - 4

	-- Background
	r.ImGui_DrawList_AddCircleFilled(dl, cx, cy, R, 0x2A2A2AFF, 40)
	r.ImGui_DrawList_AddCircle(dl, cx, cy, R, 0x666666FF, 40, 1.5)

	-- Arc (270 sweep, starting bottom-left) — uses precomputed unit vectors
	local filled = math_floor(value * ARC_SEG + 0.5)
	local arc_r = R - 3

	for s = 0, ARC_SEG - 1 do
		local u1 = ARC_UNIT[s]
		local u2 = ARC_UNIT[s + 1]
		local col = (s < filled) and 0xFFAA0099 or 0x444444FF
		r.ImGui_DrawList_AddLine(
			dl,
			cx + arc_r * u1.c,
			cy + arc_r * u1.s,
			cx + arc_r * u2.c,
			cy + arc_r * u2.s,
			col,
			3.5
		)
	end

	-- Pointer line (value-dependent angle, cannot precompute)
	local pa = ARC_START_RAD + value * ARC_SWEEP_RAD
	local px = cx + (R - 8) * math_cos(pa)
	local py = cy + (R - 8) * math_sin(pa)
	r.ImGui_DrawList_AddLine(dl, cx, cy, px, py, 0xFFFFFFFF, 2.0)
	r.ImGui_DrawList_AddCircleFilled(dl, cx, cy, 4, 0xFFFFFFFF, 8)

	-- Invisible hit area
	r.ImGui_SetCursorScreenPos(ctx, sx, sy)
	r.ImGui_InvisibleButton(ctx, "##k" .. id, size, size)

	local changed = false
	local new_val = value
	local mid_clicked = r.ImGui_IsItemClicked(ctx, 2)
	local right_clicked = r.ImGui_IsItemClicked(ctx, 1)

	if r.ImGui_IsItemActive(ctx) then
		if not knob_drag_start[id] then
			local _, my = r.ImGui_GetMousePos(ctx)
			knob_drag_start[id] = { val = value, y = my }
		end
		local _, my = r.ImGui_GetMousePos(ctx)
		local dy = knob_drag_start[id].y - my
		new_val = math_max(0, math_min(1, knob_drag_start[id].val + dy * KNOB_DRAG_SPEED))
		if new_val ~= value then
			changed = true
		end
	else
		knob_drag_start[id] = nil
	end

	-- Double-click to reset
	if r.ImGui_IsItemHovered(ctx) and r.ImGui_IsMouseDoubleClicked(ctx, 0) then
		new_val = 0.0
		changed = (new_val ~= value)
	end

	-- Tooltip
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, ("%.3f"):format(new_val))
		r.ImGui_EndTooltip(ctx)
	end

	-- Advance cursor past knob
	r.ImGui_SetCursorScreenPos(ctx, sx, sy + size)

	return changed, new_val, mid_clicked, right_clicked
end

--
-- GUI
--
local COL_HEADER = 0x1A1A2EFF
local COL_PANEL = 0x16213EFF
local COL_ACCENT = 0x3A8FFFFF
local COL_SEL_BG = 0x3A8FFF33
local COL_BTN = 0x0F3460FF
local COL_BTN_HOV = 0x1A5276FF
local COL_BTN_ACT = 0x2980B9FF
local COL_WARN = 0xFF6B6BFF

local function push_btn_style()
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), COL_BTN)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), COL_BTN_HOV)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), COL_BTN_ACT)
end
local function pop_btn_style()
	r.ImGui_PopStyleColor(ctx, 3)
end

local function section_separator()
	r.ImGui_Dummy(ctx, 0, SEP_MARGIN)
	local dl = r.ImGui_GetWindowDrawList(ctx)
	local sx, sy = r.ImGui_GetCursorScreenPos(ctx)
	local avail_w = r.ImGui_GetContentRegionAvail(ctx)
	r.ImGui_DrawList_AddLine(dl, sx, sy, sx + avail_w, sy, SEP_COLOR, SEP_THICKNESS)
	r.ImGui_Dummy(ctx, 0, SEP_MARGIN + SEP_THICKNESS)
end

local function center_text(text, width)
	local tw = r.ImGui_CalcTextSize(ctx, text)
	local ox = (width - tw) * 0.5
	if ox > 0 then
		r.ImGui_SetCursorPosX(ctx, r.ImGui_GetCursorPosX(ctx) + ox)
	end
	r.ImGui_Text(ctx, text)
end

-- Set the VIS (visible) flag in an envelope state chunk.
-- The Reaper chunk format uses "VIS <0|1> ..." not "VISIBLE".
local function set_env_chunk_visible(chunk, visible)
	local v = visible and "1" or "0"
	if chunk:find("\nVIS %d") then
		chunk = chunk:gsub("(\nVIS )%d", "%1" .. v)
	end
	return chunk
end

local function show_macro_envelope(macro_idx)
	if automation_fx_idx < 0 or not automation_track then
		set_status("No automation JSFX found")
		return
	end
	local env = r.GetFXEnvelope(automation_track, automation_fx_idx, macro_idx - 1, true)
	if not env then
		set_status("Could not create envelope")
		return
	end
	local ok, chunk = r.GetEnvelopeStateChunk(env, "", false)
	if not ok then
		set_status("Could not read envelope state")
		return
	end
	chunk = set_env_chunk_visible(chunk, true)
	r.SetEnvelopeStateChunk(env, chunk, false)
	r.TrackList_AdjustWindows(false)
	r.UpdateArrange()
	local _, trname = r.GetTrackName(automation_track)
	set_status("Envelope shown for Macro " .. macro_idx .. " on: " .. trname)
end

local function show_macro_envelope_exclusive(macro_idx)
	if automation_fx_idx < 0 or not automation_track then
		set_status("No automation JSFX found")
		return
	end
	-- Hide all other macro envelopes that already exist (don't create them)
	for i = 1, MAX_MACROS do
		if i ~= macro_idx then
			local env = r.GetFXEnvelope(automation_track, automation_fx_idx, i - 1, false)
			if env then
				local ok, chunk = r.GetEnvelopeStateChunk(env, "", false)
				if ok then
					local updated = set_env_chunk_visible(chunk, false)
					if updated ~= chunk then
						r.SetEnvelopeStateChunk(env, updated, false)
					end
				end
			end
		end
	end
	-- Show (and create if needed) the target envelope
	local env = r.GetFXEnvelope(automation_track, automation_fx_idx, macro_idx - 1, true)
	if not env then
		set_status("Could not create envelope")
		return
	end
	local ok, chunk = r.GetEnvelopeStateChunk(env, "", false)
	if not ok then
		set_status("Could not read envelope state")
		return
	end
	chunk = set_env_chunk_visible(chunk, true)
	r.SetEnvelopeStateChunk(env, chunk, false)
	r.TrackList_AdjustWindows(false)
	r.UpdateArrange()
	local _, trname = r.GetTrackName(automation_track)
	set_status("Exclusive envelope: Macro " .. macro_idx .. " on: " .. trname)
end

local function move_automation_fx_to_track(target_tr)
	if not target_tr then
		return
	end
	if automation_track and r.ValidatePtr(automation_track, "MediaTrack*") and automation_track == target_tr then
		set_status("JSFX already on this track")
		return
	end
	-- Remove from old track
	if automation_track and r.ValidatePtr(automation_track, "MediaTrack*") and automation_fx_idx >= 0 then
		r.TrackFX_Delete(automation_track, automation_fx_idx)
	end
	-- Add to new track
	automation_track = target_tr
	automation_fx_idx = r.TrackFX_AddByName(target_tr, AUTOMATION_FX_NAME, false, -1)
	-- Restore slider values
	sync_all_to_fx()
	local _, trname = r.GetTrackName(target_tr)
	set_status("JSFX installed on: " .. trname)
end

--  Knob bank panel
local function draw_knob_bank()
	local avail_w = r.ImGui_GetContentRegionAvail(ctx)
	local cell_w = KNOB_SIZE + KNOB_SPACING
	local cols = math_max(1, math_floor((avail_w + KNOB_SPACING) / cell_w))
	local dl = r.ImGui_GetWindowDrawList(ctx)

	local mid_remove = nil

	for i, mac in ipairs(macros) do
		local col_idx = (i - 1) % cols
		if col_idx ~= 0 then
			r.ImGui_SameLine(ctx)
		end

		local is_sel = (i == ui.selected)

		r.ImGui_BeginGroup(ctx)

		local changed, new_val, mid_clicked, right_clicked = draw_knob(i, mac.value, KNOB_SIZE)
		if changed then
			mac.value = new_val
			apply_macro(mac, i)
			write_macro_to_fx(i, new_val)
		end
		if r.ImGui_IsItemClicked(ctx, 0) and ui.selected ~= i then
			ui.selected = i
			select_first_link()
		end
		if mid_clicked and #macros > 1 then
			mid_remove = i
		end
		if right_clicked then
			ui.selected = i
			select_first_link()
			r.ImGui_OpenPopup(ctx, "##knobctx" .. i)
		end

		-- Knob context menu
		if r.ImGui_BeginPopup(ctx, "##knobctx" .. i) then
			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), COL_ACCENT)
			r.ImGui_Text(ctx, mac.name)
			r.ImGui_PopStyleColor(ctx)
			r.ImGui_Separator(ctx)

			if r.ImGui_MenuItem(ctx, "Show Envelope") then
				show_macro_envelope(i)
			end
			if r.ImGui_IsItemHovered(ctx) then
				r.ImGui_BeginTooltip(ctx)
				r.ImGui_Text(ctx, "Create/show the automation envelope\nfor this macro in the arrange view")
				r.ImGui_EndTooltip(ctx)
			end

			if r.ImGui_MenuItem(ctx, "Show Envelope Exclusive") then
				show_macro_envelope_exclusive(i)
			end
			if r.ImGui_IsItemHovered(ctx) then
				r.ImGui_BeginTooltip(ctx)
				r.ImGui_Text(ctx, "Show only this macro's envelope;\nhides all other visible macro envelopes")
				r.ImGui_EndTooltip(ctx)
			end

			r.ImGui_Separator(ctx)

			if r.ImGui_MenuItem(ctx, "Reset to 0") then
				mac.value = 0.0
				apply_macro(mac, i)
				write_macro_to_fx(i, 0.0)
				set_status(mac.name .. " reset to 0")
			end

			if r.ImGui_MenuItem(ctx, "Set to 100%") then
				mac.value = 1.0
				apply_macro(mac, i)
				write_macro_to_fx(i, 1.0)
				set_status(mac.name .. " set to 100%")
			end

			r.ImGui_Separator(ctx)

			if r.ImGui_MenuItem(ctx, "Copy Value") then
				macro_clipboard = mac.value
				set_status("Copied: " .. math_floor(mac.value * 100 + 0.5) .. "%")
			end

			local paste_lbl = macro_clipboard ~= nil
					and ("Paste Value  (" .. math_floor(macro_clipboard * 100 + 0.5) .. "%)")
				or "Paste Value"
			if r.ImGui_MenuItem(ctx, paste_lbl, nil, false, macro_clipboard ~= nil) then
				mac.value = macro_clipboard
				apply_macro(mac, i)
				write_macro_to_fx(i, macro_clipboard)
				set_status("Pasted: " .. math_floor(macro_clipboard * 100 + 0.5) .. "% to " .. mac.name)
			end

			r.ImGui_Separator(ctx)

			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), COL_WARN)
			local can_remove = #macros > 1
			if r.ImGui_MenuItem(ctx, "Remove Macro", nil, false, can_remove) then
				mid_remove = i -- cleanup handled in mid_remove block below
			end
			r.ImGui_PopStyleColor(ctx)

			r.ImGui_EndPopup(ctx)
		end

		-- Percentage value
		local pct_str = math_floor(mac.value * 100 + 0.5) .. "%"
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), COL_ACCENT)
		center_text(pct_str, KNOB_SIZE)
		r.ImGui_PopStyleColor(ctx)

		-- Knob name (double-click to edit inline)
		if ui.editing_name == i then
			r.ImGui_SetNextItemWidth(ctx, KNOB_SIZE)
			if ui.editing_name_focus then
				r.ImGui_SetKeyboardFocusHere(ctx, 0)
				ui.editing_name_focus = false
			end
			local rv, nname = r.ImGui_InputText(ctx, "##kname" .. i, mac.name, r.ImGui_InputTextFlags_AutoSelectAll())
			if rv then
				mac.name = nname
			end
			if r.ImGui_IsItemDeactivated(ctx) then
				ui.editing_name = nil
			end
		else
			local nx, ny = r.ImGui_GetCursorScreenPos(ctx)
			center_text(mac.name, KNOB_SIZE)
			local _, ny2 = r.ImGui_GetCursorScreenPos(ctx)
			if r.ImGui_IsMouseDoubleClicked(ctx, 0) then
				local mx, my = r.ImGui_GetMousePos(ctx)
				if mx >= nx and mx <= nx + KNOB_SIZE and my >= ny and my < ny2 then
					ui.editing_name = i
					ui.editing_name_focus = true
				end
			end
		end

		-- Link count
		local lk_str = #mac.links .. " lnk"
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
		center_text(lk_str, KNOB_SIZE)
		r.ImGui_PopStyleColor(ctx)

		r.ImGui_EndGroup(ctx)

		-- Draw selection border around the group
		if is_sel then
			local rx1, ry1 = r.ImGui_GetItemRectMin(ctx)
			local rx2, ry2 = r.ImGui_GetItemRectMax(ctx)
			r.ImGui_DrawList_AddRect(dl, rx1 - 3, ry1 - 3, rx2 + 3, ry2 + 3, COL_ACCENT, 4, nil, 2.0)
		end
	end

	if mid_remove and #macros > 1 then
		local removed_mac = macros[mid_remove]
		-- Clean up link JSFX for all links in the removed macro
		for _, lk in ipairs(removed_mac.links) do
			local tr = get_track_by_guid(lk.track_guid)
			if tr then remove_link_jsfx(tr, lk) end
		end
		table.remove(macros, mid_remove)
		-- Resync shifted macros' link JSFX to their new slot numbers
		-- (macros that followed the removed one now live at a lower index,
		-- so their links' slider1 needs to point at the new gmem slot)
		for i = mid_remove, #macros do
			apply_macro(macros[i], i)
		end
		-- Re-write controller slider values at shifted positions and clear
		-- the now-unused trailing slot so a stale value doesn't leak into
		-- a subsequently-added macro via poll_automation_fx.
		sync_all_to_fx()
		write_macro_to_fx(#macros + 1, 0.0)
		ui.selected = math.min(ui.selected, #macros)
		select_first_link()
		set_status("Macro removed")
		save_state()
	end
end

--
-- Curve helpers
--

-- Evaluate the quadratic Bezier at x, returning y.
-- P0=(0,y0), P1=(cx,cy), P2=(1,y1)
eval_curve = function(crv, x)
	local y0, y1, cxv, cy = crv.y0, crv.y1, crv.cx, crv.cy
	local x0, x1 = crv.x0 or 0.0, crv.x1 or 1.0
	x = math_max(0, math_min(1, x))
	-- Piecewise: flat y0 below x0, flat y1 above x1, bezier in between
	if x <= x0 then return y0 end
	if x >= x1 then return y1 end
	local range = x1 - x0
	if range < 1e-6 then return y0 end
	local xn = (x - x0) / range
	local t
	local a = 1 - 2 * cxv
	local b = 2 * cxv
	if math_abs(a) < 1e-6 then
		t = math_abs(b) < 1e-6 and xn or (xn / b)
	else
		local disc = b * b + 4 * a * xn
		if disc < 0 then
			disc = 0
		end
		t = (-b + math_sqrt(disc)) / (2 * a)
	end
	t = math_max(0, math_min(1, t))
	local mt = 1 - t
	return mt * mt * y0 + 2 * mt * t * cy + t * t * y1
end

default_curve = function(y0, y1)
	y0 = y0 or 0.0
	y1 = y1 or 1.0
	return { y0 = y0, y1 = y1, cx = 0.5, cy = (y0 + y1) * 0.5, x0 = 0.0, x1 = 1.0 }
end

local HANDLE_R = 5.0

-- Dragging state for curve handles { handle = "p0"|"p1"|"p2" }
local curve_drag = nil

-- Full curve editor section; call after the parameter table.
local function draw_curve_editor()
	section_separator()

	-- Validate selected link still exists
	local mi = ui.selected_link and ui.selected_link.mi
	local li = ui.selected_link and ui.selected_link.li
	local mac = mi and macros[mi]
	local lk = mac and li and mac.links[li]

	if not lk then
		-- Only show the hint if there are actually links to select
		local total_links = 0
		for _, m in ipairs(macros) do
			total_links = total_links + #m.links
		end
		if total_links > 0 then
			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x555555FF)
			r.ImGui_Text(ctx, "  Curve Editor    select a parameter row above")
			r.ImGui_PopStyleColor(ctx)
		end
		return
	end

	local crv = lk.curve
	-- Per-link viewport (visual zoom into the 0..1 X/Y ranges)
	local vymin = lk.view_ymin or 0.0
	local vymax = lk.view_ymax or 1.0
	local vyrange = math_max(0.0001, vymax - vymin)
	local vxmin = lk.view_xmin or 0.0
	local vxmax = lk.view_xmax or 1.0
	local vxrange = math_max(0.0001, vxmax - vxmin)

	-- Canvas dimensions  use available width, fixed height.
	-- Layout: [left sidebar: viewport labels] [canvas] [right sidebar: buttons]
	local avail_w = r.ImGui_GetContentRegionAvail(ctx)
	local LBL_COL_W = 54
	local LBL_GAP = 6
	local BTN_COL_W = 110
	local CW = avail_w - LBL_COL_W - LBL_GAP - BTN_COL_W - 12
	local CH = 180
	local PAD = 12
	local SEGS = 64

	local dl = r.ImGui_GetWindowDrawList(ctx)
	local ox_outer, oy = r.ImGui_GetCursorScreenPos(ctx)
	local ox = ox_outer + LBL_COL_W + LBL_GAP  -- canvas origin X
	curve_editor_ox = ox
	curve_editor_cw = CW

	-- Helpers: curve-space <-> screen (respects per-link X/Y viewport)
	local function lcs(x, y)
		local vx = (x - vxmin) / vxrange
		local vy = (y - vymin) / vyrange
		return ox + PAD + vx * (CW - 2 * PAD), oy + PAD + (1 - vy) * (CH - 2 * PAD)
	end
	local function lsc(px, py)
		local vx = (px - ox - PAD) / (CW - 2 * PAD)
		local vy = 1 - (py - oy - PAD) / (CH - 2 * PAD)
		return vxmin + vx * vxrange, vymin + vy * vyrange
	end
	-- Canvas background
	r.ImGui_DrawList_AddRectFilled(dl, ox, oy, ox + CW, oy + CH, 0x0E1220FF)
	r.ImGui_DrawList_AddRect(dl, ox, oy, ox + CW, oy + CH, 0x505050FF)

	-- Grid lines (4x4)
	for gi = 1, 3 do
		local gf = gi / 4
		local gxp = ox + PAD + gf * (CW - 2 * PAD)
		local gyp = oy + PAD + gf * (CH - 2 * PAD)
		r.ImGui_DrawList_AddLine(dl, gxp, oy + 1, gxp, oy + CH - 1, 0x22283AFF)
		r.ImGui_DrawList_AddLine(dl, ox + 1, gyp, ox + CW - 1, gyp, 0x22283AFF)
	end

	-- Optional horizontal guide line (e.g. bipolar rest line at 0.5)
	if lk.guide_visible then
		local gy = lk.guide_y or 0.5
		if gy >= vymin and gy <= vymax then
			local _, gsy = lcs(0, gy)
			r.ImGui_DrawList_AddLine(dl, ox + 1, gsy, ox + CW - 1, gsy, 0xFFAA0099, 1.5)
		end
	end

	-- Bezier curve (iterate only over the visible X viewport)
	for s = 0, SEGS - 1 do
		local x1 = vxmin + (s / SEGS) * vxrange
		local x2 = vxmin + ((s + 1) / SEGS) * vxrange
		local px1, py1 = lcs(x1, eval_curve(crv, x1))
		local px2, py2 = lcs(x2, eval_curve(crv, x2))
		py1 = math_max(oy, math_min(oy + CH, py1))
		py2 = math_max(oy, math_min(oy + CH, py2))
		r.ImGui_DrawList_AddLine(dl, px1, py1, px2, py2, 0x3A8FFFFF, 2.0)
	end

	-- Handle positions (P0 at x0, P2 at x1; P1's cx is relative to [x0,x1])
	local crv_x0 = crv.x0 or 0.0
	local crv_x1 = crv.x1 or 1.0
	local p1_abs_x = crv_x0 + crv.cx * (crv_x1 - crv_x0)
	local hp0x, hp0y = lcs(crv_x0, crv.y0)
	local hp1x, hp1y = lcs(p1_abs_x, crv.cy)
	local hp2x, hp2y = lcs(crv_x1, crv.y1)
	-- Clamp handle display positions to the canvas so they stay reachable
	-- even when their values fall outside the current X/Y viewport.
	local canv_xmin = ox + 2
	local canv_xmax = ox + CW - 2
	local canv_ymin = oy + 2
	local canv_ymax = oy + CH - 2
	hp0x = math_max(canv_xmin, math_min(canv_xmax, hp0x))
	hp0y = math_max(canv_ymin, math_min(canv_ymax, hp0y))
	hp1x = math_max(canv_xmin, math_min(canv_xmax, hp1x))
	hp1y = math_max(canv_ymin, math_min(canv_ymax, hp1y))
	hp2x = math_max(canv_xmin, math_min(canv_xmax, hp2x))
	hp2y = math_max(canv_ymin, math_min(canv_ymax, hp2y))

	-- Tangent guide lines
	r.ImGui_DrawList_AddLine(dl, hp0x, hp0y, hp1x, hp1y, 0x55555588, 1.0)
	r.ImGui_DrawList_AddLine(dl, hp1x, hp1y, hp2x, hp2y, 0x55555588, 1.0)

	-- Current macro position indicator
	local macro_val = mac.value
	local cur_sx, _ = lcs(macro_val, 0)
	local cur_sx2, cur_sy2 = lcs(macro_val, eval_curve(crv, macro_val))
	cur_sx = math_max(canv_xmin, math_min(canv_xmax, cur_sx))
	cur_sx2 = math_max(canv_xmin, math_min(canv_xmax, cur_sx2))
	cur_sy2 = math_max(canv_ymin, math_min(canv_ymax, cur_sy2))
	r.ImGui_DrawList_AddLine(dl, cur_sx, oy, cur_sx, oy + CH, 0xFFAA0099, 1.5)
	r.ImGui_DrawList_AddCircleFilled(dl, cur_sx2, cur_sy2, 5, 0xFFFFFFBB, 10)

	-- Y-axis viewport range controls in the LEFT SIDEBAR as DragDouble widgets,
	-- matching the style of the right-side coordinate inputs.
	local lbl_h = r.ImGui_GetFrameHeight(ctx)
	local lbl_w = LBL_COL_W - 2

	-- Top: vymax
	r.ImGui_SetCursorScreenPos(ctx, ox_outer, oy + PAD - lbl_h * 0.5)
	r.ImGui_SetNextItemWidth(ctx, lbl_w)
	local vymax_changed, new_vymax = r.ImGui_DragDouble(ctx, "##vymax_lbl", vymax, 0.003, 0.0, 1.0, "%.2f")
	if vymax_changed then
		lk.view_ymax = math_max((lk.view_ymin or 0.0) + 0.05, math_min(1.0, new_vymax))
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then save_state() end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Y-axis max viewport.\nDrag or Ctrl+Click to edit.\nScroll over canvas to zoom Y.")
		r.ImGui_EndTooltip(ctx)
	end

	-- Bottom: vymin
	r.ImGui_SetCursorScreenPos(ctx, ox_outer, oy + CH - PAD - lbl_h * 0.5)
	r.ImGui_SetNextItemWidth(ctx, lbl_w)
	local vymin_changed, new_vymin = r.ImGui_DragDouble(ctx, "##vymin_lbl", vymin, 0.003, 0.0, 1.0, "%.2f")
	if vymin_changed then
		lk.view_ymin = math_max(0.0, math_min((lk.view_ymax or 1.0) - 0.05, new_vymin))
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then save_state() end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Y-axis min viewport.\nDrag or Ctrl+Click to edit.")
		r.ImGui_EndTooltip(ctx)
	end

	-- X-axis viewport range controls below the canvas as DragDouble widgets.
	local xlbl_w = 54
	local xmin_lbl_x = ox
	local xmin_lbl_y = oy + CH + 4
	local xmax_lbl_x = ox + CW - xlbl_w
	local xmax_lbl_y = oy + CH + 4

	r.ImGui_SetCursorScreenPos(ctx, xmin_lbl_x, xmin_lbl_y)
	r.ImGui_SetNextItemWidth(ctx, xlbl_w)
	local vxmin_changed, new_vxmin = r.ImGui_DragDouble(ctx, "##vxmin_lbl", vxmin, 0.003, 0.0, 1.0, "%.2f")
	if vxmin_changed then
		lk.view_xmin = math_max(0.0, math_min((lk.view_xmax or 1.0) - 0.05, new_vxmin))
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then save_state() end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "X-axis min viewport.\nDrag or Ctrl+Click to edit.")
		r.ImGui_EndTooltip(ctx)
	end

	r.ImGui_SetCursorScreenPos(ctx, xmax_lbl_x, xmax_lbl_y)
	r.ImGui_SetNextItemWidth(ctx, xlbl_w)
	local vxmax_changed, new_vxmax = r.ImGui_DragDouble(ctx, "##vxmax_lbl", vxmax, 0.003, 0.0, 1.0, "%.2f")
	if vxmax_changed then
		lk.view_xmax = math_max((lk.view_xmin or 0.0) + 0.05, math_min(1.0, new_vxmax))
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then save_state() end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "X-axis max viewport.\nDrag or Ctrl+Click to edit.")
		r.ImGui_EndTooltip(ctx)
	end

	-- Invisible interaction area (must come before handle drawing so handles win clicks)
	r.ImGui_SetCursorScreenPos(ctx, ox, oy)
	r.ImGui_InvisibleButton(ctx, "##cedcanvas", CW, CH)
	local canvas_hovered = r.ImGui_IsItemHovered(ctx)
	local mx, my = r.ImGui_GetMousePos(ctx)

	local handles = {
		p0 = { x = hp0x, y = hp0y },
		p1 = { x = hp1x, y = hp1y },
		p2 = { x = hp2x, y = hp2y },
	}

	-- Begin drag on click nearest handle; double-click p1 resets to linear
	if canvas_hovered then
		local best_d, best_h = 999, nil
		for hname, hpos in pairs(handles) do
			local d = math_sqrt((mx - hpos.x) ^ 2 + (my - hpos.y) ^ 2)
			if d < best_d then
				best_d = d
				best_h = hname
			end
		end
		if r.ImGui_IsMouseDoubleClicked(ctx, 0) and best_d < HANDLE_R * 3 and best_h == "p1" then
			-- Reset curve shape to linear, keep x-range and y-range
			crv.cx = 0.5
			crv.cy = (crv.y0 + crv.y1) * 0.5
			apply_macro(mac, mi)
			save_state()
			curve_drag = nil
		elseif r.ImGui_IsMouseClicked(ctx, 0) and best_d < HANDLE_R * 3 then
			curve_drag = { handle = best_h, mi = mi, li = li }
		end
	end

	-- Mouse wheel over canvas: zoom Y viewport around cursor
	if canvas_hovered then
		local wy = r.ImGui_GetMouseWheel(ctx)
		if wy ~= 0 then
			local _, vy_at_mouse = lsc(0, my)
			local factor = (wy > 0) and 0.9 or (1 / 0.9)
			local new_range = math_max(0.05, math_min(1.0, vyrange * factor))
			local t = (vy_at_mouse - vymin) / vyrange
			local new_vymin = vy_at_mouse - t * new_range
			local new_vymax = new_vymin + new_range
			if new_vymin < 0 then new_vymin, new_vymax = 0, new_range end
			if new_vymax > 1 then new_vymin, new_vymax = 1 - new_range, 1 end
			lk.view_ymin = new_vymin
			lk.view_ymax = new_vymax
			save_state()
		end
	end

	-- Update drag (values restricted to the current X/Y viewport)
	if r.ImGui_IsMouseDown(ctx, 0) and curve_drag and curve_drag.mi == mi and curve_drag.li == li then
		local nx, ny = lsc(mx, my)
		nx = math_max(vxmin, math_min(vxmax, nx))
		ny = math_max(vymin, math_min(vymax, ny))
		local cur_x0 = crv.x0 or 0.0
		local cur_x1 = crv.x1 or 1.0
		if curve_drag.handle == "p0" then
			local offset = crv.cy - ((1 - crv.cx) * crv.y0 + crv.cx * crv.y1)
			crv.y0 = ny
			crv.x0 = math_max(vxmin, math_min(cur_x1 - 0.02, nx))
			crv.cy = math_max(vymin, math_min(vymax, offset + (1 - crv.cx) * crv.y0 + crv.cx * crv.y1))
		elseif curve_drag.handle == "p2" then
			local offset = crv.cy - ((1 - crv.cx) * crv.y0 + crv.cx * crv.y1)
			crv.y1 = ny
			crv.x1 = math_max(cur_x0 + 0.02, math_min(vxmax, nx))
			crv.cy = math_max(vymin, math_min(vymax, offset + (1 - crv.cx) * crv.y0 + crv.cx * crv.y1))
		elseif curve_drag.handle == "p1" then
			local range = cur_x1 - cur_x0
			if range > 1e-6 then
				crv.cx = math_max(0.02, math_min(0.98, (nx - cur_x0) / range))
			end
			crv.cy = ny
		end
		apply_macro(mac, mi)
	end

	if r.ImGui_IsMouseReleased(ctx, 0) then
		if curve_drag then
			save_state()
		end
		curve_drag = nil
	end

	-- Draw handles on top of everything
	for hname, hpos in pairs(handles) do
		local col = (hname == "p1") and 0xFFAA00FF or 0x3A8FFFFF
		r.ImGui_DrawList_AddCircleFilled(dl, hpos.x, hpos.y, HANDLE_R, col, 14)
		r.ImGui_DrawList_AddCircle(dl, hpos.x, hpos.y, HANDLE_R, 0xFFFFFFBB, 14, 1.5)
	end

	-- Right-side button column
	r.ImGui_SetCursorScreenPos(ctx, ox + CW + 8, oy)
	r.ImGui_BeginGroup(ctx)

	push_btn_style()
	if r.ImGui_Button(ctx, "Reset Graph##rst01", BTN_COL_W) then
		lk.curve = default_curve(0.0, 1.0)
		lk.view_ymin = 0.0
		lk.view_ymax = 1.0
		lk.view_xmin = 0.0
		lk.view_xmax = 1.0
		apply_macro(mac, mi)
		save_state()
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Reset curve and axes to default linear 0\xe2\x86\x921")
		r.ImGui_EndTooltip(ctx)
	end

	if r.ImGui_Button(ctx, "Invert##invcrv", BTN_COL_W) then
		crv.y0, crv.y1 = crv.y1, crv.y0
		crv.cy = 1.0 - crv.cy
		apply_macro(mac, mi)
		save_state()
	end
	pop_btn_style()

	-- Guide line: toggle + value on the same line
	local guide_btn_w = math_floor((BTN_COL_W - 4) * 0.5)
	local guide_drag_w = BTN_COL_W - guide_btn_w - 4
	if lk.guide_visible then
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x8B5A00FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xAA7000FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xCC8500FF)
	else
		push_btn_style()
	end
	if r.ImGui_Button(ctx, "Guide##gdtog", guide_btn_w) then
		lk.guide_visible = not lk.guide_visible
		save_state()
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Toggle horizontal reference line\n(useful as bipolar rest marker)")
		r.ImGui_EndTooltip(ctx)
	end
	if lk.guide_visible then
		r.ImGui_PopStyleColor(ctx, 3)
	else
		pop_btn_style()
	end
	r.ImGui_SameLine(ctx, 0, 4)
	r.ImGui_SetNextItemWidth(ctx, guide_drag_w)
	local gy_changed, new_gy = r.ImGui_DragDouble(ctx, "##gdy", lk.guide_y or 0.5, 0.005, 0.0, 1.0, "%.3f")
	if gy_changed then
		lk.guide_y = new_gy
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
		save_state()
	end

	r.ImGui_Spacing(ctx)
	local half_w = (BTN_COL_W - 4) * 0.5

	-- P0 row: x0, y0
	r.ImGui_SetNextItemWidth(ctx, half_w)
	local x0_upper = math_min(vxmax, (crv.x1 or 1.0) - 0.02)
	local p0x_changed, new_x0 = r.ImGui_DragDouble(ctx, "##p0x", crv.x0 or 0.0, 0.005, vxmin, x0_upper, "%.3f")
	if p0x_changed then
		crv.x0 = math_max(vxmin, math_min(x0_upper, new_x0))
		apply_macro(mac, mi)
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
		save_state()
	end
	r.ImGui_SameLine(ctx, 0, 4)
	r.ImGui_SetNextItemWidth(ctx, half_w)
	local p0_changed, new_y0 = r.ImGui_DragDouble(ctx, "##p0y", crv.y0, 0.005, vymin, vymax, "%.3f")
	if p0_changed then
		local offset = crv.cy - ((1 - crv.cx) * crv.y0 + crv.cx * crv.y1)
		crv.y0 = math_max(vymin, math_min(vymax, new_y0))
		crv.cy = math_max(vymin, math_min(vymax, offset + (1 - crv.cx) * crv.y0 + crv.cx * crv.y1))
		apply_macro(mac, mi)
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
		save_state()
	end

	-- P2 row: x1, y1
	r.ImGui_SetNextItemWidth(ctx, half_w)
	local x1_lower = math_max(vxmin, (crv.x0 or 0.0) + 0.02)
	local p2x_changed, new_x1 = r.ImGui_DragDouble(ctx, "##p2x", crv.x1 or 1.0, 0.005, x1_lower, vxmax, "%.3f")
	if p2x_changed then
		crv.x1 = math_max(x1_lower, math_min(vxmax, new_x1))
		apply_macro(mac, mi)
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
		save_state()
	end
	r.ImGui_SameLine(ctx, 0, 4)
	r.ImGui_SetNextItemWidth(ctx, half_w)
	local p2_changed, new_y1 = r.ImGui_DragDouble(ctx, "##p2y", crv.y1, 0.005, vymin, vymax, "%.3f")
	if p2_changed then
		local offset = crv.cy - ((1 - crv.cx) * crv.y0 + crv.cx * crv.y1)
		crv.y1 = math_max(vymin, math_min(vymax, new_y1))
		crv.cy = math_max(vymin, math_min(vymax, offset + (1 - crv.cx) * crv.y0 + crv.cx * crv.y1))
		apply_macro(mac, mi)
	end
	if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
		save_state()
	end

	r.ImGui_EndGroup(ctx)

	-- Output bar: explicitly aligned with canvas left edge, below x-axis labels + 6px margin
	local eff_val = eval_curve(lk.curve, mac.value) * (lk.scale or 1.0) + (lk.offset or 0.0)
	local bar_w = CW
	local bar_h = 8
	r.ImGui_SetCursorScreenPos(ctx, ox, oy + CH + 4 + lbl_h + 12)
	local bbx, bby = r.ImGui_GetCursorScreenPos(ctx)
	r.ImGui_DrawList_AddRectFilled(dl, bbx, bby, bbx + bar_w, bby + bar_h, 0x1A1A2EFF, 3)
	local ev = math_max(0, math_min(1, eff_val))
	r.ImGui_DrawList_AddRectFilled(dl, bbx, bby, bbx + ev * bar_w, bby + bar_h, 0x3A8FFFAA, 3)
	r.ImGui_DrawList_AddRect(dl, bbx, bby, bbx + bar_w, bby + bar_h, 0x444444FF, 3)

	r.ImGui_SetCursorScreenPos(ctx, ox, bby + bar_h + 4)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
	local bar_hint = ("Final Output: %.3f   (after modulation controls)"):format(eff_val)
	r.ImGui_Text(ctx, bar_hint)
	r.ImGui_PopStyleColor(ctx)
end

--
-- Parameter list view (below link section)
--
--
-- Add-link button: shows last-touched FX parameter, click to link
--
local function draw_add_link_button()
	local ok_lt, trnum_lt, fxnum_lt, pnum_lt = r.GetLastTouchedFX()
	if not ok_lt then
		local avail_w = r.ImGui_GetContentRegionAvail(ctx)
		local msg = "Touch an FX parameter to add a link"
		local tw = r.ImGui_CalcTextSize(ctx, msg)
		r.ImGui_SetCursorPosX(ctx, r.ImGui_GetCursorPosX(ctx) + (avail_w - tw) * 0.5)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
		r.ImGui_Text(ctx, msg)
		r.ImGui_PopStyleColor(ctx)
		return
	end

	local tr_lt = trnum_lt == 0 and r.GetMasterTrack(0) or r.GetTrack(0, trnum_lt - 1)
	if not tr_lt then
		return
	end

	local _, guid_lt = r.GetSetMediaTrackInfo_String(tr_lt, "GUID", "", false)
	local fx_guid_lt = r.TrackFX_GetFXGUID(tr_lt, fxnum_lt) or ""
	local _, fname_lt = r.TrackFX_GetFXName(tr_lt, fxnum_lt, "")
	local _, pname_lt = r.TrackFX_GetParamName(tr_lt, fxnum_lt, pnum_lt, "")
	local _, trname_lt = r.GetTrackName(tr_lt)
	local preview_lbl = trname_lt .. " > " .. fname_lt .. " > " .. pname_lt

	-- Check if already linked to any macro
	local already_linked, already_linked_to = false, nil
	for _, m in ipairs(macros) do
		for _, lk in ipairs(m.links) do
			if lk.track_guid == guid_lt and lk.fx_guid == fx_guid_lt and lk.param == pnum_lt then
				already_linked, already_linked_to = true, m.name
				break
			end
		end
		if already_linked then
			break
		end
	end

	-- Center the button
	local avail_w = r.ImGui_GetContentRegionAvail(ctx)
	local tw = r.ImGui_CalcTextSize(ctx, preview_lbl)
	local offset = (avail_w - tw - 16) * 0.5
	if offset > 0 then
		r.ImGui_SetCursorPosX(ctx, r.ImGui_GetCursorPosX(ctx) + offset)
	end

	if already_linked then
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x3A3A3AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x4A4A4AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x3A3A3AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x888888FF)
	else
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x1A6B1AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x248F24FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x2EAD2EFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0xFFFFFFFF)
	end

		if r.ImGui_Button(ctx, preview_lbl .. "##addlnk") then
			local sel_mac = macros[ui.selected]
			if already_linked then
				set_status("Already linked to " .. (already_linked_to or "?") .. ": " .. pname_lt)
			elseif sel_mac then
				local new_lk = {
					track_guid = guid_lt,
					fx_guid = fx_guid_lt,
					fx = fxnum_lt,
					param = pnum_lt,
					curve = default_curve(0.0, 1.0),
					track_name = trname_lt,
					fx_name = fname_lt,
					param_name = pname_lt,
					label = preview_lbl,
					track_color = r.GetTrackColor(tr_lt),
					-- container fields set by install_link_jsfx
				}
				sel_mac.links[#sel_mac.links + 1] = new_lk
				-- Install the link JSFX inside the per-track container
				local link_idx = install_link_jsfx(tr_lt, new_lk, ui.selected)
				if link_idx >= 0 then
					set_status("Linked: " .. pname_lt .. " on " .. trname_lt)
				else
					set_status("Link JSFX install failed: " .. pname_lt .. " on " .. trname_lt)
				end
				save_state()
			end
		end

	r.ImGui_PopStyleColor(ctx, 4)
end

--
-- Filter bar: search, view toggle, clear/orphan/learn buttons
--
local function draw_filter_bar()
	r.ImGui_SetNextItemWidth(ctx, 300)
	local rv, new_filter =
		r.ImGui_InputTextWithHint(ctx, "##filter", "Filter linked parameters (regex)...", ui.filter_text)
	if rv then
		ui.filter_text = new_filter
	end

	r.ImGui_SameLine(ctx)
	push_btn_style()
	if r.ImGui_Button(ctx, "X##clrfilter") then
		ui.filter_text = ""
	end
	pop_btn_style()

	r.ImGui_SameLine(ctx)

	if ui.filter_text == "" then
		push_btn_style()
		if ui.show_all then
			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x285A28FF)
		end
		if r.ImGui_Button(ctx, ui.show_all and "All##tog" or "Sel##tog") then
			ui.show_all = not ui.show_all
		end
		if ui.show_all then
			r.ImGui_PopStyleColor(ctx)
		end
		pop_btn_style()
	else
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
		r.ImGui_Text(ctx, "  Regex active  showing all knobs")
		r.ImGui_PopStyleColor(ctx)
	end

	r.ImGui_SameLine(ctx)

	push_btn_style()
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x8B0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xAA0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xCC0000FF)
	local mac = macros[ui.selected]
	if r.ImGui_Button(ctx, "Clear Table##clsel") and mac then
		for _, lk in ipairs(mac.links) do
			local tr = get_track_by_guid(lk.track_guid)
			if tr then remove_link_jsfx(tr, lk) end
		end
		mac.links = {}
		set_status("Links cleared for " .. mac.name)
		save_state()
	end
	r.ImGui_PopStyleColor(ctx, 3)

	r.ImGui_SameLine(ctx)

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x8B4500FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xAA5500FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xCC6600FF)
	if r.ImGui_Button(ctx, "Clear Orphans##clorphans") then
		local removed = 0
		for _, m in ipairs(macros) do
			local j = 1
			while j <= #m.links do
				local lk = m.links[j]
				local tr = get_track_by_guid(lk.track_guid)
				if not tr or resolve_fx_index(tr, lk) < 0 then
					if tr then remove_link_jsfx(tr, lk) end
					table.remove(m.links, j)
					removed = removed + 1
				else
					j = j + 1
				end
			end
		end
		if removed > 0 then
			set_status("Removed " .. removed .. " orphaned link" .. (removed > 1 and "s" or ""))
			save_state()
		else
			set_status("No orphaned links found")
		end
	end
	r.ImGui_PopStyleColor(ctx, 3)

	r.ImGui_SameLine(ctx)

	-- Learn mode toggle
	if ui.learn_mode then
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x1A6B1AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x248F24FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x2EAD2EFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0xFFFFFFFF)
	else
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x3A3A3AFF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x5A4A00FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x7A6200FF)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x999999FF)
	end
	if r.ImGui_Button(ctx, "Learn##learnmode") then
		ui.learn_mode = not ui.learn_mode
		ui.learn_last_touched = nil
		set_status(ui.learn_mode and "Learn mode ON  touch FX parameters to link them" or "Learn mode OFF")
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(
			ctx,
			ui.learn_mode
					and "Learn Mode ON: every new FX parameter touch is auto-linked\nto the selected macro. Click to stop."
				or "Learn Mode OFF: click to auto-link touched FX parameters\nto the selected macro."
		)
		r.ImGui_EndTooltip(ctx)
	end
	r.ImGui_PopStyleColor(ctx, 4)
	pop_btn_style()
end

--
-- Parameter table: displays and manages linked parameter rows
--
-- Sort key extractors for the parameter table (hoisted to avoid per-frame allocation)
local sort_key_fns = {
	[0] = function(row)
		return (row.mac.name or ""):lower()
	end,
	[1] = function(row)
		return (row.lk.track_name or ""):lower()
	end,
	[2] = function(row)
		return (row.lk.fx_name or ""):lower()
	end,
	[3] = function(row)
		return (row.lk.param_name or ""):lower()
	end,
}

local function draw_param_table()
	-- Build list of (macro_idx, link_idx) to display
	local rows = {}
	local using_regex = ui.filter_text ~= ""
	local pat = using_regex and ui.filter_text or nil

	for mi, mac in ipairs(macros) do
		local show = using_regex or ui.show_all or (mi == ui.selected)
		if show then
			for li, lk in ipairs(mac.links) do
				local include = true
				if using_regex and pat then
					local haystack = (lk.track_name or "") .. " " .. (lk.fx_name or "") .. " " .. (lk.param_name or "")
					include = haystack:lower():find(pat:lower()) ~= nil
				end
				if include then
					rows[#rows + 1] = { mi = mi, li = li, mac = mac, lk = lk }
				end
			end
		end
	end

	if #rows == 0 then
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
		r.ImGui_Text(ctx, using_regex and "  No parameters match." or "  No linked parameters.")
		r.ImGui_PopStyleColor(ctx)
		return
	end

	-- Sort rows
	if ui.sort_col ~= nil then
		local fn = sort_key_fns[ui.sort_col]
		if fn then
			local asc = ui.sort_asc
			table.sort(rows, function(a, b)
				local ka, kb = fn(a), fn(b)
				if asc then
					return ka < kb
				else
					return ka > kb
				end
			end)
		end
	end

	local tbl_flags = r.ImGui_TableFlags_BordersInnerV()
		| r.ImGui_TableFlags_SizingStretchProp()
		| r.ImGui_TableFlags_BordersOuter()

	local dl = r.ImGui_GetWindowDrawList(ctx)
	local to_remove = nil

	if r.ImGui_BeginTable(ctx, "paramlst", 7, tbl_flags) then
		r.ImGui_TableSetupColumn(ctx, "Macro", r.ImGui_TableColumnFlags_WidthFixed(), 72)
		r.ImGui_TableSetupColumn(ctx, "Track", r.ImGui_TableColumnFlags_WidthStretch(), 1.0)
		r.ImGui_TableSetupColumn(ctx, "FX", r.ImGui_TableColumnFlags_WidthStretch(), 1.2)
		r.ImGui_TableSetupColumn(ctx, "Name", r.ImGui_TableColumnFlags_WidthStretch(), 1.0)
		r.ImGui_TableSetupColumn(ctx, "Curve", r.ImGui_TableColumnFlags_WidthFixed(), 80)
		r.ImGui_TableSetupColumn(ctx, "##mt", r.ImGui_TableColumnFlags_WidthFixed(), 24)
		r.ImGui_TableSetupColumn(ctx, "##rm", r.ImGui_TableColumnFlags_WidthFixed(), 24)

		-- Sortable header row
		r.ImGui_TableNextRow(ctx, r.ImGui_TableRowFlags_Headers())
		local sort_hdrs = { "Macro", "Track", "FX", "Name" }
		for ci, lbl in ipairs(sort_hdrs) do
			r.ImGui_TableSetColumnIndex(ctx, ci - 1)
			local is_active = ui.sort_col == (ci - 1)
			local display = is_active and (lbl .. (ui.sort_asc and " \xe2\x96\xb2" or " \xe2\x96\xbc")) or lbl
			if is_active then
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), COL_ACCENT)
			end
			r.ImGui_TableHeader(ctx, display .. "##hdr" .. ci)
			if is_active then
				r.ImGui_PopStyleColor(ctx)
			end
			if r.ImGui_IsItemClicked(ctx, 0) then
				if ui.sort_col == (ci - 1) then
					ui.sort_asc = not ui.sort_asc
				else
					ui.sort_col = ci - 1
					ui.sort_asc = true
				end
			end
		end
		r.ImGui_TableSetColumnIndex(ctx, 4)
		r.ImGui_TableHeader(ctx, "Curve")
		r.ImGui_TableSetColumnIndex(ctx, 5)
		r.ImGui_TableHeader(ctx, "##mt")
		r.ImGui_TableSetColumnIndex(ctx, 6)
		r.ImGui_TableHeader(ctx, "##rm")

		for _, row in ipairs(rows) do
			local mi, li, mac, lk = row.mi, row.li, row.mac, row.lk
			r.ImGui_PushID(ctx, mi * 1000 + li)
			r.ImGui_TableNextRow(ctx)

			r.ImGui_TableSetColumnIndex(ctx, 0)
			local _, cell_pad_y = r.ImGui_GetStyleVar(ctx, r.ImGui_StyleVar_CellPadding())
			local _, row_y_content = r.ImGui_GetCursorScreenPos(ctx)
			local row_y = row_y_content - cell_pad_y
			local row_h = r.ImGui_GetTextLineHeight(ctx) + 2 * cell_pad_y
			local is_row_sel = ui.selected_link and ui.selected_link.mi == mi and ui.selected_link.li == li
			local tr = get_track_by_guid(lk.track_guid)
			local is_muted = lk.muted == true
			local dim_col = is_muted and 0x44444488 or nil

			-- Col 0: Macro name (selectable row)
			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), is_muted and 0x3A8FFF66 or COL_ACCENT)
			if
				r.ImGui_Selectable(
					ctx,
					mac.name .. "##sel" .. mi .. "_" .. li,
					is_row_sel,
					r.ImGui_SelectableFlags_SpanAllColumns() | r.ImGui_SelectableFlags_AllowOverlap()
				)
			then
				ui.selected_link = { mi = mi, li = li }
			end
			r.ImGui_PopStyleColor(ctx)

			-- Col 1: Track name
			r.ImGui_TableSetColumnIndex(ctx, 1)
			local native = tr and r.GetTrackColor(tr) or 0
			if native ~= 0 then
				local cr, cg, cb = r.ColorFromNative(native)
				local alpha = is_muted and 0x25 or 0x60
				local bg = (((cr & 0xFF) << 24) | ((cg & 0xFF) << 16) | ((cb & 0xFF) << 8) | alpha) & 0xFFFFFFFF
				local cx1, _ = r.ImGui_GetCursorScreenPos(ctx)
				local cw = r.ImGui_GetContentRegionAvail(ctx)
				r.ImGui_DrawList_AddRectFilled(dl, cx1, row_y, cx1 + cw, row_y + row_h, bg)
			end
			if not tr then
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), is_muted and 0xFF6B6B55 or COL_WARN)
				r.ImGui_Text(ctx, "[!] " .. (lk.track_name ~= "" and lk.track_name or "?"))
				r.ImGui_PopStyleColor(ctx)
			else
				if dim_col then
					r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), dim_col)
				end
				r.ImGui_Text(ctx, lk.track_name ~= "" and lk.track_name or "?")
				if dim_col then
					r.ImGui_PopStyleColor(ctx)
				end
			end

			-- Col 2: FX name
			r.ImGui_TableSetColumnIndex(ctx, 2)
			local fx_resolved = tr and resolve_fx_index(tr, lk) >= 0
			if not fx_resolved then
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), is_muted and 0xFF6B6B55 or COL_WARN)
				r.ImGui_Text(ctx, "[!] " .. (lk.fx_name ~= "" and lk.fx_name or "?"))
				r.ImGui_PopStyleColor(ctx)
			else
				if dim_col then
					r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), dim_col)
				end
				r.ImGui_Text(ctx, lk.fx_name ~= "" and lk.fx_name or "?")
				if dim_col then
					r.ImGui_PopStyleColor(ctx)
				end
			end

			-- Col 3: Param name
			r.ImGui_TableSetColumnIndex(ctx, 3)
			if dim_col then
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), dim_col)
			end
			r.ImGui_Text(ctx, lk.param_name ~= "" and lk.param_name or "?")
			if dim_col then
				r.ImGui_PopStyleColor(ctx)
			end

			-- Col 4: Sparkline (drag source + drop target)
			r.ImGui_TableSetColumnIndex(ctx, 4)
			do
				local crv = lk.curve
				local bx, by = r.ImGui_GetCursorScreenPos(ctx)
				local bw = 78
				local bh = r.ImGui_GetTextLineHeight(ctx)
				local pw, ph = bw - 2, bh - 2

				r.ImGui_InvisibleButton(ctx, "##crvdnd" .. mi .. "_" .. li, bw, bh)

				if r.ImGui_BeginDragDropSource(ctx, r.ImGui_DragDropFlags_None()) then
					-- Payload fields (pipe-separated):
					--   y0|y1|cx|cy|x0|x1|vymin|vymax|vxmin|vxmax|guide_y|guide_visible
					local payload = string.format(
						"%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%.6f|%d",
						crv.y0, crv.y1, crv.cx, crv.cy, crv.x0 or 0.0, crv.x1 or 1.0,
						lk.view_ymin or 0.0, lk.view_ymax or 1.0,
						lk.view_xmin or 0.0, lk.view_xmax or 1.0,
						lk.guide_y or 0.5, lk.guide_visible and 1 or 0)
					r.ImGui_SetDragDropPayload(ctx, "REAMACROS_CURVE", payload)
					r.ImGui_Text(ctx, "Curve  " .. mac.name .. "  " .. (lk.param_name or "?"))
					r.ImGui_EndDragDropSource(ctx)
				end

				if r.ImGui_BeginDragDropTarget(ctx) then
					local ok, payload = r.ImGui_AcceptDragDropPayload(ctx, "REAMACROS_CURVE")
					if ok and payload then
						local parts = {}
						for seg in payload:gmatch("[^|]+") do
							parts[#parts + 1] = seg
						end
						if #parts >= 6 then
							lk.curve = {
								y0 = tonumber(parts[1]),
								y1 = tonumber(parts[2]),
								cx = tonumber(parts[3]),
								cy = tonumber(parts[4]),
								x0 = tonumber(parts[5]) or 0.0,
								x1 = tonumber(parts[6]) or 1.0,
							}
							-- Extended fields (present in newer payloads): viewport + guide
							if #parts >= 12 then
								lk.view_ymin = tonumber(parts[7]) or 0.0
								lk.view_ymax = tonumber(parts[8]) or 1.0
								lk.view_xmin = tonumber(parts[9]) or 0.0
								lk.view_xmax = tonumber(parts[10]) or 1.0
								lk.guide_y = tonumber(parts[11]) or 0.5
								lk.guide_visible = (parts[12] == "1")
							end
							apply_macro(mac, mi)
							set_status("Curve pasted onto " .. (lk.param_name or "?"))
							save_state()
						end
					end
					r.ImGui_EndDragDropTarget(ctx)
				end

				local is_dnd_hovered = r.ImGui_IsItemHovered(ctx)
				local bdr_col = is_dnd_hovered and 0xFFAA00FF or (is_row_sel and 0x3A8FFFFF or 0x333333FF)
				r.ImGui_DrawList_AddRectFilled(dl, bx, by, bx + bw, by + bh, 0x111E2EFF, 2)
				r.ImGui_DrawList_AddRect(dl, bx, by, bx + bw, by + bh, bdr_col, 2, nil, 1.0)

				local segs = 20
				local lk_scale = lk.scale or 1.0
				local lk_offset = lk.offset or 0.0
				local lk_out_min = lk.out_min or 0.0
				local lk_out_max = lk.out_max or 1.0
				for s = 0, segs - 1 do
					local x1 = s / segs
					local x2 = (s + 1) / segs
					local function eff(x)
						local v = eval_curve(crv, x) * lk_scale + lk_offset
						return math_max(lk_out_min, math_min(lk_out_max, v))
					end
					local y1s = eff(x1)
					local y2s = eff(x2)
					local sx1 = bx + 1 + x1 * pw
					local sy1 = by + 1 + (1 - math_max(0, math_min(1, y1s))) * ph
					local sx2 = bx + 1 + x2 * pw
					local sy2 = by + 1 + (1 - math_max(0, math_min(1, y2s))) * ph
					r.ImGui_DrawList_AddLine(dl, sx1, sy1, sx2, sy2, 0x3A8FFFFF, 1.0)
				end

				local tx = bx + 1 + mac.value * pw
				r.ImGui_DrawList_AddLine(dl, tx, by + 1, tx, by + bh - 1, 0xFFFFFF66, 1.0)

				if is_dnd_hovered then
					r.ImGui_DrawList_AddText(dl, bx + bw - 10, by, 0xFFAA00FF, "")
				end
			end

			-- Col 5: Mute toggle
			r.ImGui_TableSetColumnIndex(ctx, 5)
			local btn_h = r.ImGui_GetFrameHeight(ctx)
			r.ImGui_SetCursorPosY(ctx, r.ImGui_GetCursorPosY(ctx) + (row_h - btn_h) * 0.5 - cell_pad_y)
			push_btn_style()
			if is_muted then
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0xB93F54FF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xD44A63FF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xE05570FF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0xFFFFFFFF)
			else
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x2A2A2AFF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x3A3A3AFF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x4A4A4AFF)
				r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0x666666FF)
			end
			if r.ImGui_Button(ctx, "M##mt") then
				lk.muted = not lk.muted
				apply_macro(macros[mi], mi)
				save_state()
			end
			if r.ImGui_IsItemHovered(ctx) then
				r.ImGui_BeginTooltip(ctx)
				r.ImGui_Text(
					ctx,
					is_muted and "Unmute: re-enable macro control" or "Mute: freeze parameter at current value"
				)
				r.ImGui_EndTooltip(ctx)
			end
			r.ImGui_PopStyleColor(ctx, 4)
			pop_btn_style()

			-- Col 6: Remove
			r.ImGui_TableSetColumnIndex(ctx, 6)
			r.ImGui_SetCursorPosY(ctx, r.ImGui_GetCursorPosY(ctx) + (row_h - btn_h) * 0.5 - cell_pad_y)
			push_btn_style()
			r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x5A0000FF)
			if r.ImGui_Button(ctx, "X##xl") then
				to_remove = { mi = mi, li = li }
			end
			r.ImGui_PopStyleColor(ctx)
			pop_btn_style()

			r.ImGui_PopID(ctx)
		end

		r.ImGui_EndTable(ctx)
	end

	if to_remove then
		local tr_rem = get_track_by_guid(macros[to_remove.mi].links[to_remove.li].track_guid)
		remove_link_jsfx(tr_rem, macros[to_remove.mi].links[to_remove.li])
		table.remove(macros[to_remove.mi].links, to_remove.li)
		if ui.selected_link and ui.selected_link.mi == to_remove.mi and ui.selected_link.li == to_remove.li then
			ui.selected_link = nil
		end
		set_status("Link removed")
		save_state()
	end
end

--
-- Modulation controls: scale, offset, lag  shown below curve editor for selected link
--
local function draw_modulation_controls()
	local mi = ui.selected_link and ui.selected_link.mi
	local li = ui.selected_link and ui.selected_link.li
	local mac = mi and macros[mi]
	local lk = mac and li and mac.links[li]
	if not lk then
		return
	end

	r.ImGui_Spacing(ctx)

	-- Compute ctrl_w so Scale + gap + Offset fills exactly the canvas width
	local scale_tw = r.ImGui_CalcTextSize(ctx, "Scale")
	local offset_tw = r.ImGui_CalcTextSize(ctx, "Offset")
	local gap = 16
	local ctrl_w = math_max(80, math_floor((curve_editor_cw - scale_tw - offset_tw - 4 - gap) * 0.5))

	local function labeled_drag(label, key, default, speed, lo, hi, fmt, tooltip, wheel_step)
		r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0xAAAAAAAAFF)
		r.ImGui_Text(ctx, label)
		r.ImGui_PopStyleColor(ctx)
		r.ImGui_SameLine(ctx, 0, 2)
		r.ImGui_SetNextItemWidth(ctx, ctrl_w)
		local cur = lk[key] or default
		local changed, nv = r.ImGui_DragDouble(ctx, "##mod_" .. key, cur, speed, lo, hi, fmt)
		if changed then
			lk[key] = nv
			apply_macro(mac, mi)
		end
		if r.ImGui_IsItemDeactivatedAfterEdit(ctx) then
			save_state()
		end
		if r.ImGui_IsItemHovered(ctx) then
			r.ImGui_BeginTooltip(ctx)
			r.ImGui_Text(ctx, tooltip)
			r.ImGui_EndTooltip(ctx)
			local wy = r.ImGui_GetMouseWheel(ctx)
			if wy ~= 0 then
				local nv2 = math_max(lo, math_min(hi, (lk[key] or default) + wy * wheel_step))
				lk[key] = nv2
				apply_macro(mac, mi)
				save_state()
			end
		end
		if r.ImGui_IsItemClicked(ctx, 1) then -- right-click to reset
			lk[key] = default
			apply_macro(mac, mi)
			save_state()
		end
		if r.ImGui_IsItemClicked(ctx, 2) and key == "offset" then -- middle-click to zero output
			local curve_out = eval_curve(lk.curve, mac.value)
			local new_offset = -(curve_out * (lk.scale or 1.0))
			new_offset = math_max(lo, math_min(hi, new_offset))
			lk[key] = new_offset
			apply_macro(mac, mi)
			save_state()
		end
	end

	local _, ctrl_sy = r.ImGui_GetCursorScreenPos(ctx)
	r.ImGui_SetCursorScreenPos(ctx, curve_editor_ox, ctrl_sy)
	labeled_drag(
		"Scale",
		"scale",
		1.0,
		0.005,
		-8.0,
		8.0,
		"%.3f",
		"Multiplies the curve output.\nRight-click to reset to 1.0.",
		0.05
	)
	r.ImGui_SameLine(ctx, 0, gap)
	labeled_drag(
		"Offset",
		"offset",
		0.0,
		0.005,
		-1.0,
		1.0,
		"%.3f",
		"Adds a fixed amount to the scaled output.\nMiddle-click to zero the current output.\nRight-click to reset to 0.0.",
		0.01
	)

	r.ImGui_Spacing(ctx)
end

--
-- Parameter list view: orchestrates add-link, filter bar, and table
--
local function draw_param_list()
	r.ImGui_Spacing(ctx)
	draw_add_link_button()
	section_separator()
	draw_filter_bar()
	r.ImGui_Spacing(ctx)
	draw_param_table()
end

--  Toolbar
local function draw_toolbar()
	push_btn_style()

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x1A6B1AFF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x248F24FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x2EAD2EFF)
	if r.ImGui_Button(ctx, "✚##addmacro", 28, 28) then
		macros[#macros + 1] = new_macro(#macros + 1)
		-- Clear the controller slider at the new position; it may hold a
		-- stale value from a previously-removed macro, which poll_automation_fx
		-- would otherwise copy back into the fresh macro's value.
		write_macro_to_fx(#macros, 0.0)
		ui.selected = #macros
		select_first_link()
		set_status("Macro added")
		save_state()
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Add a new macro")
		r.ImGui_EndTooltip(ctx)
	end
	r.ImGui_PopStyleColor(ctx, 3)

	r.ImGui_SameLine(ctx)

	if r.ImGui_Button(ctx, "0##zeromacro", 28, 28) then
		for i, m in ipairs(macros) do
			m.value = 0.0
			apply_macro(m, i)
			write_macro_to_fx(i, 0.0)
		end
		set_status("All macros reset to 0")
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Reset all macro knobs to zero")
		r.ImGui_EndTooltip(ctx)
	end

	pop_btn_style()

	r.ImGui_SameLine(ctx)

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x8B0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xAA0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xCC0000FF)
	r.ImGui_SameLine(ctx)

	push_btn_style()
	local jsfx_installed = automation_fx_idx >= 0
		and automation_track ~= nil
		and r.ValidatePtr(automation_track, "MediaTrack*")
	if r.ImGui_Button(ctx, "⬇##jsfx", 28, 28) then
		local target = nil
		local sel_count = r.CountSelectedTracks(0)
		if sel_count > 0 then
			target = r.GetSelectedTrack(0, 0)
		else
			local master = r.GetMasterTrack(0)
			if master and r.IsTrackSelected(master) then
				target = master
			end
		end
		if target then
			local _, trname = r.GetTrackName(target)
			ui.confirm = {
				msg = 'Move JSFX to "' .. trname .. '"?',
				action = function()
					move_automation_fx_to_track(target)
				end,
			}
			r.ImGui_OpenPopup(ctx, "##confirm")
		else
			set_status("No track selected")
		end
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		local trname = "?"
		if automation_track and r.ValidatePtr(automation_track, "MediaTrack*") then
			local _, n = r.GetTrackName(automation_track)
			trname = n
		end
		r.ImGui_Text(ctx, "Move JSFX to selected track\nCurrently on: " .. trname)
		r.ImGui_EndTooltip(ctx)
	end
	pop_btn_style()

	r.ImGui_SameLine(ctx)

	if r.ImGui_Button(ctx, "X##clralltables", 28, 28) then
		ui.confirm = {
			msg = "Clear all parameter links from all macros?",
			action = function()
				for _, m in ipairs(macros) do
					for _, lk in ipairs(m.links) do
						local tr = get_track_by_guid(lk.track_guid)
						if tr then
							-- Clear plink on target
							local target_fx = resolve_fx_index(tr, lk)
							if target_fx >= 0 then
								r.TrackFX_SetNamedConfigParm(
									tr, target_fx,
									("param.%d.plink.active"):format(lk.param), "0")
							end
						end
					end
					m.links = {}
				end
				-- Remove all Reamacros Links containers from all tracks
				for ti = 0, r.CountTracks(0) - 1 do
					local tr = r.GetTrack(0, ti)
					local cidx = find_container_on_track(tr)
					if cidx >= 0 then r.TrackFX_Delete(tr, cidx) end
				end
				local master = r.GetMasterTrack(0)
				if master then
					local cidx = find_container_on_track(master)
					if cidx >= 0 then r.TrackFX_Delete(master, cidx) end
				end
				ui.selected_link = nil
				set_status("All links cleared")
			end,
		}
		r.ImGui_OpenPopup(ctx, "##confirm")
	end
	if r.ImGui_IsItemHovered(ctx) then
		r.ImGui_BeginTooltip(ctx)
		r.ImGui_Text(ctx, "Clear all parameter links from all macros")
		r.ImGui_EndTooltip(ctx)
	end
	r.ImGui_PopStyleColor(ctx, 3)

	-- Status text (right-aligned on the same row)
	local status_text
	local status_col
	if ui.status_msg ~= "" and r.time_precise() < ui.status_time then
		status_text = ui.status_msg
		status_col = COL_ACCENT
	else
		status_text = SCRIPT_NAME .. " v" .. VERSION
		status_col = 0x666666FF
	end
	r.ImGui_SameLine(ctx)
	local tw = r.ImGui_CalcTextSize(ctx, status_text)
	local avail_w = r.ImGui_GetContentRegionAvail(ctx)
	if avail_w > tw then
		r.ImGui_SetCursorPosX(ctx, r.ImGui_GetCursorPosX(ctx) + avail_w - tw)
	end
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), status_col)
	r.ImGui_Text(ctx, status_text)
	r.ImGui_PopStyleColor(ctx)

	section_separator()
end

--
-- Confirmation popup
--
local function draw_confirm_popup()
	if
		not r.ImGui_BeginPopupModal(
			ctx,
			"##confirm",
			nil,
			r.ImGui_WindowFlags_AlwaysAutoResize() | r.ImGui_WindowFlags_NoTitleBar()
		)
	then
		return
	end

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Text(), 0xFFFFFFFF)
	r.ImGui_Text(ctx, ui.confirm and ui.confirm.msg or "")
	r.ImGui_PopStyleColor(ctx)

	r.ImGui_Spacing(ctx)

	push_btn_style()
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x1A6B1AFF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0x248F24FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0x2EAD2EFF)
	if r.ImGui_Button(ctx, "Confirm", 80, 0) then
		if ui.confirm and ui.confirm.action then
			ui.confirm.action()
		end
		ui.confirm = nil
		r.ImGui_CloseCurrentPopup(ctx)
	end
	r.ImGui_PopStyleColor(ctx, 3)

	r.ImGui_SameLine(ctx)

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_Button(), 0x5A0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonHovered(), 0xAA0000FF)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_ButtonActive(), 0xCC0000FF)
	if r.ImGui_Button(ctx, "Cancel", 80, 0) then
		ui.confirm = nil
		r.ImGui_CloseCurrentPopup(ctx)
	end
	r.ImGui_PopStyleColor(ctx, 3)
	pop_btn_style()

	r.ImGui_EndPopup(ctx)
end

--
-- Main draw
--
local function draw()
	-- Width: N knobs * (size + spacing) - trailing spacing + window padding (10 each side)
	local init_w = DEFAULT_MACROS * (KNOB_SIZE + KNOB_SPACING) - KNOB_SPACING + 20
	r.ImGui_SetNextWindowSize(ctx, init_w, 620, r.ImGui_Cond_FirstUseEver())

	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_WindowBg(), COL_HEADER)
	r.ImGui_PushStyleColor(ctx, r.ImGui_Col_TitleBgActive(), 0x0F3460FF)
	r.ImGui_PushStyleVar(ctx, r.ImGui_StyleVar_WindowPadding(), 10, 10)
	r.ImGui_PushStyleVar(ctx, r.ImGui_StyleVar_ItemSpacing(), 8, 6)

	local visible, open = r.ImGui_Begin(
		ctx,
		SCRIPT_NAME,
		true,
		r.ImGui_WindowFlags_NoScrollbar() | r.ImGui_WindowFlags_NoCollapse() | r.ImGui_WindowFlags_NoTitleBar()
	)

	r.ImGui_PopStyleColor(ctx, 2)
	r.ImGui_PopStyleVar(ctx, 2)

	if visible then
		draw_toolbar()
		draw_knob_bank()
		section_separator()
		draw_param_list()
		draw_curve_editor()
		draw_modulation_controls()
		draw_confirm_popup()
	end
	r.ImGui_End(ctx)

	return open
end

--
-- Learn mode polling
--
local function poll_learn_mode()
	if not ui.learn_mode then
		return
	end

	local ok, trnum, fxnum, pnum = r.GetLastTouchedFX()
	if not ok then
		return
	end

	-- Check if this is a new parameter touch
	local prev = ui.learn_last_touched
	if prev and prev.trnum == trnum and prev.fxnum == fxnum and prev.pnum == pnum then
		return
	end

	-- Resolve the track
	local tr
	if trnum == 0 then
		tr = r.GetMasterTrack(0)
	else
		tr = r.GetTrack(0, trnum - 1)
	end
	if not tr then
		return
	end

	local _, guid = r.GetSetMediaTrackInfo_String(tr, "GUID", "", false)
	local fx_guid = r.TrackFX_GetFXGUID(tr, fxnum) or ""
	local _, fname = r.TrackFX_GetFXName(tr, fxnum, "")
	local _, pname = r.TrackFX_GetParamName(tr, fxnum, pnum, "")
	local _, trname = r.GetTrackName(tr)
	local preview_lbl = trname .. " > " .. fname .. " > " .. pname

	-- Reject if already linked to any macro
	for _, m in ipairs(macros) do
		for _, lk in ipairs(m.links) do
			if lk.track_guid == guid and lk.fx_guid == fx_guid and lk.param == pnum then
				-- Already linked; update sentinel so we don't spam the status bar
				ui.learn_last_touched = { trnum = trnum, fxnum = fxnum, pnum = pnum }
				set_status("Already linked: " .. pname)
				return
			end
		end
	end

	local sel_mac = macros[ui.selected]
	if not sel_mac then
		return
	end

	local new_lk = {
		track_guid = guid,
		fx_guid = fx_guid,
		fx = fxnum,
		param = pnum,
		curve = default_curve(0.0, 1.0),
		track_name = trname,
		fx_name = fname,
		param_name = pname,
		label = preview_lbl,
		track_color = r.GetTrackColor(tr),
		-- container fields set by install_link_jsfx
	}
	sel_mac.links[#sel_mac.links + 1] = new_lk
	-- Install the link JSFX inside the per-track container
	install_link_jsfx(tr, new_lk, ui.selected)

	ui.learn_last_touched = { trnum = trnum, fxnum = fxnum, pnum = pnum }
	set_status("[Learn] Linked: " .. pname .. " on " .. trname)
	save_state()
end

--
-- Defer loop
--
local function loop()
	if not ctx then
		return
	end

	-- Invalidate per-frame caches
	guid_cache = {}

	-- Poll automation JSFX slider values for GUI display
	poll_automation_fx()

	-- Auto-add last-touched parameters when learn mode is active
	poll_learn_mode()

	-- Draw
	local open = draw()

	if open then
		r.defer(loop)
	else
		save_state()
		ctx = nil
	end
end

--
-- Entry point
--
local function init()
	ctx = r.ImGui_CreateContext(SCRIPT_NAME)

	local loaded = load_state()
	macros = loaded or init_macros(DEFAULT_MACROS)
	backfill_fx_guids()
	ensure_link_curves()
	select_first_link()

	ensure_jsfx_file()
	automation_fx_idx = find_or_install_automation_fx()
	sync_all_to_fx()
	resolve_all_link_jsfx()

	-- Migration: install link JSFX for links that have none yet,
	-- and migrate legacy top-level link JSFX into containers.
	for mi, mac in ipairs(macros) do
		for _, lk in ipairs(mac.links) do
			local tr = get_track_by_guid(lk.track_guid)
			if not tr then goto next_migration end

			if lk.link_fx_idx == nil and lk.container_fx_idx == nil then
				-- No link JSFX at all; install fresh (inside container)
				install_link_jsfx(tr, lk, mi)
			elseif lk.container_fx_idx == nil and lk.link_fx_idx ~= nil then
				-- Legacy: link JSFX is at the top level, migrate into container
				-- Remove the old top-level instance
				local old_fx = lk.link_fx_idx
				-- Clear plink on target before moving
				local target_fx = resolve_fx_index(tr, lk)
				if target_fx >= 0 then
					r.TrackFX_SetNamedConfigParm(
						tr, target_fx,
						("param.%d.plink.active"):format(lk.param), "0")
				end
				r.TrackFX_Delete(tr, old_fx)
				lk.link_fx_idx = nil
				-- Install fresh inside container
				install_link_jsfx(tr, lk, mi)
			elseif lk.link_fx_idx == nil then
				-- Container was resolved but the link JSFX inside could not
				-- be located (externally deleted, GUID mismatch, etc.).
				-- Reinstall; install_link_jsfx will reuse the existing container.
				lk.container_fx_idx = nil
				lk.container_param = nil
				install_link_jsfx(tr, lk, mi)
			end

			::next_migration::
		end
	end

	r.defer(loop)
end

init()

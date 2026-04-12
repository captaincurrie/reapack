-- @description reatask - reaper task manager
-- @version 1.6
-- @author captaincurrie
-- @license GPL v3
-- @date 2025 12 28
-- @about reatask - reaper task manager

--[[ PROGRAM SPEC
The intention of this program is to create a task manager for the DAW Reaper.

- Create a GUI that organizes all important information and operations
in as simple a manner as possible.
- The GUI must be able to do the following:
	- create a list of tasks
	- create sub-tasks of potentially infinite depth
	- tasks with subtasks can be collapsed so only the parent is shown
	- undo/redo each and every operation
	- be dockable within reaper
- The task list can be optionally defined to be per-project, per-project-version, per-selected-track per-selected-item
- The task list will be context-dependent based on current user action
	- when a task is selected, if a task list for that track exist, display it
	- when a item is selected, if a task list for that item exists, display it
	- if nothing else, display the project task list
- There is an input bar at the bottom of the task list
	- this bar will take all keyboard input for the window so that you dont need to
worry about clicking the input bar before you type into it. As long as reatask is the focused window, just start typing and press enter to create a task

INTERFACE:
- middle clicking a task will delete it
- right clicking anywhere on the task list will open a settings menu
- right clicking on the input bar will perform an undo
- shift+right click will perform a redo
- double clicking a task will collapse/expand its children (if they exist)
- pressing enter will take the current text in the input bar and create a sibling task
- pressing Tab will take the current text in the input bar and create a child task
- Pressing Shift+Tab will take the current text in the input bar and create a parent task
--]]



local r = reaper

-- Global variables
local todo_items = {} -- Store items by ID for quick lookup
local root_items = {} -- Store root item IDs in order
local current_project_path = ""
local gui_open = false
local selected_id = nil
local input_text = ""
local scroll_offset = 0
local next_id = 1

-- Performance optimization variables
local needs_save = false
local save_timer = 0
local save_delay = 2.0 -- Save 2 seconds after last modification
local last_project_check_time = 0
local project_check_interval = 0.5 -- Check every 0.5 seconds
local needs_redraw = true
local last_mouse_x, last_mouse_y = -1, -1
local last_mouse_cap = 0
local last_input_text = ""

-- Frame rate limiting
local target_fps = 30 -- Target frames per second
local frame_time = 1.0 / target_fps -- Time per frame in seconds
local last_frame_time = 0
local force_next_frame = false -- Flag to bypass frame limiter for immediate updates

-- Icon font settings
local icon_font_name = "DejaVu Sans" -- Widely available on Linux; Segoe UI Symbol on Windows
-- Font settings (global variables)
local font_name = "Arial"
local font_size = 16
local base_font_size = 16 -- Base size for scaling calculations
local font_size_increment = 1

-- Text positioning settings (base values at base_font_size)
local base_task_text_y_offset = -1
local base_input_text_y_offset = -1
local base_menu_text_y_offset = -2
local base_checkbox_y_offset = 6
local base_collapse_icon_y_offset = 5

-- Scaled dimensions (will be calculated)
local task_text_y_offset = base_task_text_y_offset
local input_text_y_offset = base_input_text_y_offset
local menu_text_y_offset = base_menu_text_y_offset
local checkbox_y_offset = base_checkbox_y_offset
local collapse_icon_y_offset = base_collapse_icon_y_offset

-- Display settings
local show_completed = true
local sort_mode = "custom" -- "custom" or "alphabetical"
local wrap_task_text = false -- Whether to wrap long task text
local toolbar_position = "top" -- "top" or "bottom"

-- Color settings
local bg_color = "3e3e3e" -- Hex color format for main background
local text_color = "FFFFFF" -- Hex color format for main text
local input_bar_bg_color = "3e3e3e" -- Hex color format for input bar
local input_bar_border_color = "606060" -- Hex color format for input bar border
local input_bar_border_thickness = 2 -- Thickness of input bar border in pixels
local toolbar_bg_color = "3b3b3b" -- Hex color format for toolbar background

-- View state
local current_view = "tasks" -- "tasks" or "settings"
local settings_scroll_offset = 0

-- Settings view interaction
local font_slider_dragging = false
local font_slider_value = 0 -- 0-1 range
local input_height_slider_dragging = false
local input_height_slider_value = 0 -- 0-1 range
local toolbar_height_slider_dragging = false
local toolbar_height_slider_value = 0 -- 0-1 range

-- Undo system
local undo_stack = {}
local redo_stack = {}
local max_undo_levels = 20

-- Click/Drag detection variables
local mouse_down_time = 0
local mouse_down_pos = { x = 0, y = 0 }
local mouse_down_item = nil
local click_threshold_time = 0.25 -- 250ms to start drag
local move_threshold = 5 -- pixels to differentiate drag from click
local last_click_time = 0
local last_click_item = nil
local double_click_threshold = 0.25 -- 250ms for double click

-- Tooltip variables
local tooltip_delay = 0.3 -- seconds before tooltip appears
local tooltip_hover_start = 0
local tooltip_current_btn = nil -- unique string key for currently hovered btn
local tooltip_text = ""
local tooltip_visible = false
local tooltip_mouse_x = 0
local tooltip_mouse_y = 0

-- Drag and drop variables
local dragging = false
local drag_item_id = nil
local drag_start_y = 0
local drag_offset_y = 0
local drop_zone_threshold = 0.2 -- Fraction of item height for top/bottom zones
local drop_target = nil
local drop_position = "after" -- "before", "after", "child"

-- Performance optimization
local display_list_cache = nil
local cache_dirty = true
local last_window_w = 0
local last_window_h = 0
local last_blink_state = nil

-- GUI dimensions (base values at base_font_size)
local window_w = 300
local window_h = 400
local base_item_height = 24
local base_input_height = 24
local base_toolbar_height = 24
local base_checkbox_size = 12
local base_indent = 20
local base_menu_width = 160
local base_menu_item_height = 20

-- Scaled dimensions (will be calculated)
local item_height = base_item_height
local input_height = base_input_height
local toolbar_height = base_toolbar_height
local checkbox_size = base_checkbox_size
local indent_size = base_indent
local menu_width = base_menu_width
local menu_item_height = base_menu_item_height

-- Data file variables
local window_name = "reatask"
local todolist_dirname = ".reatask"
local todolist_tasklist_filename = "tasks"
local todolist_settinglist_filename = "settings"
local unsaved_todolist_name = "unsaved"

-- Window settings
local default_dock_state = 0 -- 0 = undocked (floating), 1 = docked

function get_project_identifier()
	-- EnumProjects(-1) returns the active project's file path directly
	local _, proj_file = r.EnumProjects(-1)
	
	if not proj_file or proj_file == "" then
		-- Use Reaper's resource path for unsaved projects
		local resource_path = r.GetResourcePath()
		return resource_path .. "/" .. unsaved_todolist_name
	else
		-- Extract directory from the full project file path
		-- Handle both Unix (/) and Windows (\\) path separators
		local proj_dir = proj_file:match("^(.*[/\\])")
		if not proj_dir then
			return nil
		end
		return proj_dir
	end
end

function get_reatask_dir()
	local proj_id = get_project_identifier()
	if not proj_id then
		return nil
	end
	-- Strip trailing separator to avoid double separators
	proj_id = proj_id:gsub("[/\\]$", "")
	return proj_id .. "/" .. todolist_dirname
end

function ensure_reatask_dir_exists()
	local reatask_dir = get_reatask_dir()
	if not reatask_dir then
		return false
	end

	if not r.file_exists(reatask_dir .. "/") then
		r.RecursiveCreateDirectory(reatask_dir, 0)

		-- Verify directory was created
		if not r.file_exists(reatask_dir .. "/") then
			return false
		end
	end
	
	return true
end

function mark_cache_dirty()
	cache_dirty = true
	needs_redraw = true
	force_next_frame = true -- Force immediate update on cache changes
end

function mark_needs_save()
	needs_save = true
	save_timer = r.time_precise()
end

function request_immediate_update()
	needs_redraw = true
	force_next_frame = true
end

function check_deferred_save()
	if needs_save and (r.time_precise() - save_timer) >= save_delay then
		save_todo_data()
		save_settings()
		needs_save = false
	end
end

function should_reload_project()
	local current_time = r.time_precise()
	if current_time - last_project_check_time < project_check_interval then
		return false
	end
	last_project_check_time = current_time

	local proj_id = get_project_identifier()
	return proj_id ~= current_project_path
end

function hex_to_rgb(hex)
	-- Remove # if present
	hex = hex:gsub("#", "")
	
	-- Handle 3-digit hex codes (e.g., #RGB -> #RRGGBB)
	if #hex == 3 then
		hex = hex:sub(1,1):rep(2) .. hex:sub(2,2):rep(2) .. hex:sub(3,3):rep(2)
	end
	
	-- Parse hex values
	if #hex == 6 then
		local r = tonumber(hex:sub(1, 2), 16) / 255
		local g = tonumber(hex:sub(3, 4), 16) / 255
		local b = tonumber(hex:sub(5, 6), 16) / 255
		return r, g, b
	end
	
	-- Default to gray if parsing fails
	return 0.4, 0.4, 0.4
end

function calculate_scale_factor()
	return font_size / base_font_size
end

function update_scaled_dimensions()
	local scale = calculate_scale_factor()

	-- Scale UI element sizes
	item_height = math.floor(base_item_height * scale + 0.5)
	input_height = math.floor(base_input_height * scale + 0.5)
	toolbar_height = math.floor(base_toolbar_height * scale + 0.5)
	checkbox_size = math.floor(base_checkbox_size * scale + 0.5)
	indent_size = math.floor(base_indent * scale + 0.5)
	menu_width = math.floor(base_menu_width * scale + 0.5)
	menu_item_height = math.floor(base_menu_item_height * scale + 0.5)

	-- Scale offsets
	task_text_y_offset = math.floor(base_task_text_y_offset * scale + 0.5)
	input_text_y_offset = math.floor(base_input_text_y_offset * scale + 0.5)
	menu_text_y_offset = math.floor(base_menu_text_y_offset * scale + 0.5)
	checkbox_y_offset = math.floor(base_checkbox_y_offset * scale + 0.5)
	collapse_icon_y_offset = math.floor(base_collapse_icon_y_offset * scale + 0.5)
end

function set_font()
	gfx.setfont(1, font_name, font_size)
	update_scaled_dimensions()
end

-- Undo system functions
function deep_copy_table(original)
	if type(original) ~= "table" then
		return original
	end
	local copy = {}
	for key, value in pairs(original) do
		copy[key] = deep_copy_table(value)
	end
	return copy
end

function save_state_for_undo(action_description)
	local state = {
		todo_items = deep_copy_table(todo_items),
		root_items = deep_copy_table(root_items),
		selected_id = selected_id,
		next_id = next_id,
		action = action_description,
		timestamp = r.time_precise(),
	}

	table.insert(undo_stack, state)

	-- Limit undo stack size
	if #undo_stack > max_undo_levels then
		table.remove(undo_stack, 1)
	end

	-- Any new action clears the redo stack
	redo_stack = {}
end

function undo_last_action()
	if #undo_stack == 0 then
		return false
	end

	-- Save current state onto redo stack before restoring
	local current = {
		todo_items = deep_copy_table(todo_items),
		root_items = deep_copy_table(root_items),
		selected_id = selected_id,
		next_id = next_id,
		action = undo_stack[#undo_stack].action,
		timestamp = r.time_precise(),
	}
	table.insert(redo_stack, current)

	local last_state = table.remove(undo_stack)

	-- Preserve current selection if the task still exists in restored state
	local preserved_selection = nil
	if selected_id and last_state.todo_items[selected_id] then
		preserved_selection = selected_id
	end

	todo_items = last_state.todo_items
	root_items = last_state.root_items
	next_id = last_state.next_id
	selected_id = preserved_selection or last_state.selected_id

	mark_cache_dirty()
	mark_needs_save()

	return true, last_state.action
end

function redo_last_action()
	if #redo_stack == 0 then
		return false
	end

	-- Save current state onto undo stack before redoing
	local current = {
		todo_items = deep_copy_table(todo_items),
		root_items = deep_copy_table(root_items),
		selected_id = selected_id,
		next_id = next_id,
		action = redo_stack[#redo_stack].action,
		timestamp = r.time_precise(),
	}
	table.insert(undo_stack, current)

	local redo_state = table.remove(redo_stack)

	todo_items = redo_state.todo_items
	root_items = redo_state.root_items
	next_id = redo_state.next_id
	selected_id = redo_state.selected_id

	mark_cache_dirty()
	mark_needs_save()

	return true, redo_state.action
end

function load_settings()
	if not ensure_reatask_dir_exists() then
		return
	end
	
	local reatask_dir = get_reatask_dir()
	local settings_file = reatask_dir .. "/" .. todolist_settinglist_filename

	if r.file_exists(settings_file) then
		local file = io.open(settings_file, "r")
		if file then
			local content = file:read("*all")
			file:close()

			for line in content:gmatch("[^\r\n]+") do
				local key, value = line:match("^([^:]+):(.+)")
				if key and value then
					if key == "font_name" then
						font_name = value
					elseif key == "font_size" then
						font_size = tonumber(value) or 14
					elseif key == "show_completed" then
						show_completed = value == "true"
					elseif key == "sort_mode" then
						sort_mode = value
					elseif key == "target_fps" then
						target_fps = tonumber(value) or 30
						frame_time = target_fps > 0 and (1.0 / target_fps) or 0
					elseif key == "bg_color" then
						bg_color = value
					elseif key == "text_color" then
						text_color = value
					elseif key == "input_bar_bg_color" then
						input_bar_bg_color = value
					elseif key == "input_bar_border_color" then
						input_bar_border_color = value
					elseif key == "input_bar_border_thickness" then
						input_bar_border_thickness = tonumber(value) or 2
    				elseif key == "wrap_task_text" then
    					wrap_task_text = value == "true"
    				elseif key == "toolbar_position" then
    					toolbar_position = value
    				elseif key == "base_input_height" then
						base_input_height = tonumber(value) or 24
					elseif key == "base_toolbar_height" then
						base_toolbar_height = tonumber(value) or 24
					end
				end
			end
		end
	end

	set_font()
	mark_cache_dirty()
end

function save_settings()
	if not ensure_reatask_dir_exists() then
		return false
	end
	return save_settings_to_dir(get_reatask_dir())
end

-- Internal version that marks for deferred save
function save_settings_deferred()
	mark_needs_save()
end

function save_todo_data_to_dir(reatask_dir)
	local data_file = reatask_dir .. "/" .. todolist_tasklist_filename
	local file = io.open(data_file, "w")
	if file then
		for _, item in pairs(todo_items) do
			file:write(
				string.format(
					"%d:%s:%s:%d:%s:%s\n",
					item.id,
					item.parent_id and tostring(item.parent_id) or "",
					tostring(item.done),
					item.order,
					tostring(item.collapsed),
					item.text
				)
			)
		end
		file:close()
		return true
	end
	return false
end

function save_settings_to_dir(reatask_dir)
	local settings_file = reatask_dir .. "/" .. todolist_settinglist_filename
	local file = io.open(settings_file, "w")
	if file then
		file:write(string.format("font_name:%s\n", font_name))
		file:write(string.format("font_size:%d\n", font_size))
		file:write(string.format("show_completed:%s\n", tostring(show_completed)))
		file:write(string.format("sort_mode:%s\n", sort_mode))
		file:write(string.format("target_fps:%d\n", target_fps))
		file:write(string.format("bg_color:%s\n", bg_color))
		file:write(string.format("text_color:%s\n", text_color))
		file:write(string.format("input_bar_bg_color:%s\n", input_bar_bg_color))
		file:write(string.format("input_bar_border_color:%s\n", input_bar_border_color))
		file:write(string.format("input_bar_border_thickness:%d\n", input_bar_border_thickness))
		file:write(string.format("wrap_task_text:%s\n", tostring(wrap_task_text)))
		file:write(string.format("toolbar_position:%s\n", toolbar_position))
		file:write(string.format("base_input_height:%d\n", base_input_height))
		file:write(string.format("base_toolbar_height:%d\n", base_toolbar_height))
		file:close()
		return true
	end
	return false
end

function load_todo_data()
	local proj_id = get_project_identifier()
	if proj_id ~= current_project_path then
		-- Save current project data to the OLD directory before switching
		if current_project_path ~= "" then
			local old_base = current_project_path:gsub("[/\\]$", "")
			local old_reatask_dir = old_base .. "/" .. todolist_dirname
			save_todo_data_to_dir(old_reatask_dir)
			save_settings_to_dir(old_reatask_dir)
		end
		
		-- Only update current_project_path after saving old data
		current_project_path = proj_id
		
		if not ensure_reatask_dir_exists() then
			return
		end
		
		local reatask_dir = get_reatask_dir()
		local data_file = reatask_dir .. "/" .. todolist_tasklist_filename
		
		todo_items = {}
		root_items = {}
		next_id = 1
		undo_stack = {} -- Clear undo/redo stacks for new project
		redo_stack = {}
		needs_save = false -- Old data already saved above
		selected_id = nil
		scroll_offset = 0
		input_text = ""
		mark_cache_dirty()

		if r.file_exists(data_file) then
			local file = io.open(data_file, "r")
			if file then
				local content = file:read("*all")
				file:close()

				-- First pass: create all items
				for line in content:gmatch("[^\r\n]+") do
					local id, parent_id, done, order, collapsed, text =
						line:match("^(%d+):([^:]*):(%w+):(%d+):([^:]*):(.+)")
					if id and done and order and text then
						local item = {
							id = tonumber(id),
							parent_id = (parent_id == "" or parent_id == "0") and nil or tonumber(parent_id),
							text = text or "",
							done = done == "true",
							children = {},
							order = tonumber(order),
							collapsed = (collapsed and collapsed == "true") or false,
						}
						todo_items[item.id] = item
						next_id = math.max(next_id, item.id + 1)
					end
				end

				-- Second pass: build parent-child relationships and root list
				local root_list = {}
				for _, item in pairs(todo_items) do
					if item.parent_id then
						if todo_items[item.parent_id] then
							table.insert(todo_items[item.parent_id].children, item.id)
						end
					else
						table.insert(root_list, { id = item.id, order = item.order })
					end
				end

				-- Sort root items by order
				table.sort(root_list, function(a, b)
					return a.order < b.order
				end)
				root_items = {}
				for _, item in ipairs(root_list) do
					table.insert(root_items, item.id)
				end

				-- Sort children lists by order
				for _, item in pairs(todo_items) do
					table.sort(item.children, function(a, b)
						return todo_items[a].order < todo_items[b].order
					end)
				end
			end
		end

		load_settings()
	end
end

function save_todo_data()
	if not ensure_reatask_dir_exists() then
		return false
	end
	return save_todo_data_to_dir(get_reatask_dir())
end
function sort_children_alphabetically(children_list)
	table.sort(children_list, function(a, b)
		return string.lower(todo_items[a].text) < string.lower(todo_items[b].text)
	end)
end

function sort_children_by_order(children_list)
	table.sort(children_list, function(a, b)
		return todo_items[a].order < todo_items[b].order
	end)
end

function wrap_text(text, max_width)
	local lines = {}
	local words = {}
	
	-- Split text into words
	for word in text:gmatch("%S+") do
		table.insert(words, word)
	end
	
	if #words == 0 then
		return {text}
	end
	
	local current_line = ""
	for _, word in ipairs(words) do
		local test_line = current_line == "" and word or (current_line .. " " .. word)
		local w = gfx.measurestr(test_line)
		
		if w > max_width and max_width > 0 then
			if current_line ~= "" then
				table.insert(lines, current_line)
				current_line = word
			else
				-- Single word is too long, just add it
				table.insert(lines, word)
				current_line = ""
			end
		else
			current_line = test_line
		end
	end
	
	if current_line ~= "" then
		table.insert(lines, current_line)
	end
	
	if #lines == 0 then
		table.insert(lines, text)
	end
	
	return lines
end

function get_item_display_height(item, level)
	if not wrap_task_text then
		return item_height
	end
	
	-- Calculate available width for text
	local x_offset = 10 + (level * indent_size)
	local has_children = #item.children > 0
	local text_x_offset_with_icon = math.floor(checkbox_size * 2.33 + 0.5)
	local text_x_offset_no_icon = math.floor(checkbox_size * 1.67 + 0.5)
	local text_x_offset = has_children and text_x_offset_with_icon or text_x_offset_no_icon
	local available_width = gfx.w - x_offset - text_x_offset - 10
	
	if available_width <= 0 then
		return item_height
	end
	
	local lines = wrap_text(item.text, available_width)
	local line_height = font_size + 2
	local text_height = #lines * line_height
	
	-- Return the maximum of base item height and wrapped text height
	return math.max(item_height, text_height + 8)
end

function get_display_list()
	if not cache_dirty and display_list_cache then
		return display_list_cache
	end

	display_list_cache = {}

	local function add_item_recursive(item_id, level)
		local item = todo_items[item_id]
		if item then
			-- Skip completed tasks if they're hidden
			if not show_completed and item.done then
				return
			end

			local display_height = get_item_display_height(item, level)
			
			table.insert(display_list_cache, {
				id = item_id,
				item = item,
				level = level,
				height = display_height,
			})

			-- Add children only if not collapsed
			if not item.collapsed then
				local children_copy = {}
				for _, child_id in ipairs(item.children) do
					table.insert(children_copy, child_id)
				end

				if sort_mode == "alphabetical" then
					sort_children_alphabetically(children_copy)
				else
					sort_children_by_order(children_copy)
				end

				for _, child_id in ipairs(children_copy) do
					add_item_recursive(child_id, level + 1)
				end
			end
		end
	end

	-- Sort root items
	local root_copy = {}
	for _, root_id in ipairs(root_items) do
		table.insert(root_copy, root_id)
	end

	if sort_mode == "alphabetical" then
		table.sort(root_copy, function(a, b)
			return string.lower(todo_items[a].text) < string.lower(todo_items[b].text)
		end)
	end

	-- Add all root items and their children
	for _, root_id in ipairs(root_copy) do
		add_item_recursive(root_id, 0)
	end

	cache_dirty = false
	return display_list_cache
end

function get_scroll_limits(display_list)
	local available_height = gfx.h - input_height - toolbar_height - 20 -- Account for margins, toolbar and input bar
	
	-- Calculate total content height based on actual item heights
	local total_content_height = 0
	for _, display_item in ipairs(display_list) do
		total_content_height = total_content_height + display_item.height
	end
	
	local max_scroll = math.max(0, total_content_height - available_height)
	return max_scroll
end

function get_settings_scroll_limits()
	-- Calculate total height of settings content
	local margin = 20
	local y_offset = margin
	
	-- Title
	gfx.setfont(1, font_name, font_size * 1.5)
	local title_w, title_h = gfx.measurestr("Settings")
	y_offset = y_offset + title_h + margin
	set_font()
	
	local label_height = font_size + 5
	local button_height = math.max(30, font_size * 1.5)
	local slider_height = math.max(20, font_size * 1.2)
	local section_spacing = margin
	
	-- Font Size Section
	y_offset = y_offset + label_height + slider_height + section_spacing
	
	-- Input Bar Height Section
	y_offset = y_offset + label_height + slider_height + section_spacing

	-- Toolbar Height Section
	y_offset = y_offset + label_height + slider_height + section_spacing

	-- FPS Section
	y_offset = y_offset + label_height + button_height + section_spacing
	
	-- Sort Section
	y_offset = y_offset + label_height + button_height + section_spacing
	
	-- Toolbar position section
	y_offset = y_offset + label_height + button_height + section_spacing
	
	-- Undo Section (if available)
	if #undo_stack > 0 then
		y_offset = y_offset + label_height + button_height + section_spacing
	end
	
	-- Quit button
	y_offset = y_offset + button_height + margin
	
	local total_content_height = y_offset
	local max_scroll = math.max(0, total_content_height - gfx.h)
	return max_scroll
end

function indent_task(task_id)
	local item = todo_items[task_id]
	if not item then return end

	-- Find the previous sibling
	local siblings = item.parent_id and todo_items[item.parent_id].children or root_items
	local prev_sibling_id = nil

	for i, sibling_id in ipairs(siblings) do
		if sibling_id == task_id then
			if i > 1 then
				prev_sibling_id = siblings[i - 1]
			end
			break
		end
	end

	if not prev_sibling_id then return end -- No previous sibling, can't indent

	save_state_for_undo("Indent task")

	-- Remove from current location
	for i, sibling_id in ipairs(siblings) do
		if sibling_id == task_id then
			table.remove(siblings, i)
			break
		end
	end

	-- Add as last child of previous sibling
	item.parent_id = prev_sibling_id
	local prev_sibling = todo_items[prev_sibling_id]
	prev_sibling.collapsed = false -- Expand to show new child
	table.insert(prev_sibling.children, task_id)

	reorder_items()
end

function unindent_task(task_id)
	local item = todo_items[task_id]
	if not item or not item.parent_id then return end -- Already at root level

	save_state_for_undo("Unindent task")

	local parent = todo_items[item.parent_id]
	local grandparent_id = parent.parent_id

	-- Remove from parent's children
	for i, child_id in ipairs(parent.children) do
		if child_id == task_id then
			table.remove(parent.children, i)
			break
		end
	end

	-- Find parent's position in grandparent's list and insert after it
	local grandparent_list = grandparent_id and todo_items[grandparent_id].children or root_items
	local insert_pos = #grandparent_list + 1

	for i, sibling_id in ipairs(grandparent_list) do
		if sibling_id == item.parent_id then
			insert_pos = i + 1
			break
		end
	end

	item.parent_id = grandparent_id
	table.insert(grandparent_list, insert_pos, task_id)

	reorder_items()
end

function has_any_uncollapsed()
	for _, item in pairs(todo_items) do
		if #item.children > 0 and not item.collapsed then
			return true
		end
	end
	return false
end

function collapse_all_tasks()
	save_state_for_undo("Collapse all")
	for _, item in pairs(todo_items) do
		if #item.children > 0 then
			item.collapsed = true
		end
	end
	mark_cache_dirty()
	mark_needs_save()
end

function uncollapse_all_tasks()
	save_state_for_undo("Uncollapse all")
	for _, item in pairs(todo_items) do
		item.collapsed = false
	end
	mark_cache_dirty()
	mark_needs_save()
end

function clear_all_tasks()
	save_state_for_undo("Clear all tasks")
	todo_items = {}
	root_items = {}
	next_id = 1
	selected_id = nil
	scroll_offset = 0
	mark_cache_dirty()
	mark_needs_save()
end

function toggle_collapse(item_id)
	if todo_items[item_id] and #todo_items[item_id].children > 0 then
		save_state_for_undo("Toggle collapse")
		todo_items[item_id].collapsed = not todo_items[item_id].collapsed
		mark_cache_dirty()
		mark_needs_save()
	end
end

function get_next_order()
	local max_order = 0
	for _, item in pairs(todo_items) do
		max_order = math.max(max_order, item.order)
	end
	return max_order + 1
end

function reorder_items()
	-- Reassign order values based on current structure
	local order_counter = 1

	local function assign_order_recursive(item_id)
		local item = todo_items[item_id]
		if item then
			item.order = order_counter
			order_counter = order_counter + 1

			for _, child_id in ipairs(item.children) do
				assign_order_recursive(child_id)
			end
		end
	end

	for _, root_id in ipairs(root_items) do
		assign_order_recursive(root_id)
	end
	mark_cache_dirty()
	mark_needs_save()
end

function is_descendant_or_self(potential_child_id, potential_ancestor_id)
	-- Check if potential_child_id is the same as potential_ancestor_id
	if potential_child_id == potential_ancestor_id then
		return true
	end

	-- Check if potential_child_id is a descendant of potential_ancestor_id
	local function check_descendants(ancestor_id)
		local ancestor = todo_items[ancestor_id]
		if not ancestor then
			return false
		end

		for _, child_id in ipairs(ancestor.children) do
			if child_id == potential_child_id then
				return true
			end
			if check_descendants(child_id) then
				return true
			end
		end
		return false
	end

	return check_descendants(potential_ancestor_id)
end

function is_ancestor_completed(item_id)
	local item = todo_items[item_id]
	if not item then
		return false
	end

	if item.parent_id then
		local parent = todo_items[item.parent_id]
		if parent and parent.done then
			return true
		end
		return is_ancestor_completed(item.parent_id)
	end

	return false
end

function move_item(item_id, target_id, position)
	local item = todo_items[item_id]
	local target = todo_items[target_id]

	if not item or not target or item_id == target_id then
		return
	end

	-- Prevent circular parenting: check if target would become a child/descendant of item
	if position == "child" then
		if is_descendant_or_self(target_id, item_id) then
			return -- Abort the move - would create circular reference
		end
	elseif position == "before" or position == "after" then
		-- For sibling moves, check if the target's parent would become a descendant of item
		if target.parent_id and is_descendant_or_self(target.parent_id, item_id) then
			return -- Abort the move - would create circular reference
		end
	end

	save_state_for_undo("Move task")

	-- Remove item from current location
	if item.parent_id then
		local parent_children = todo_items[item.parent_id].children
		for i, child_id in ipairs(parent_children) do
			if child_id == item_id then
				table.remove(parent_children, i)
				break
			end
		end
	else
		for i, root_id in ipairs(root_items) do
			if root_id == item_id then
				table.remove(root_items, i)
				break
			end
		end
	end

	-- Add item to new location
	if position == "child" then
		-- Make it a child of target
		item.parent_id = target_id
		table.insert(target.children, item_id)
	elseif position == "before" or position == "after" then
		-- Make it a sibling of target
		item.parent_id = target.parent_id

		if target.parent_id then
			-- Insert in parent's children list
			local parent_children = todo_items[target.parent_id].children
			local insert_pos = 1

			for i, child_id in ipairs(parent_children) do
				if child_id == target_id then
					insert_pos = position == "before" and i or i + 1
					break
				end
			end

			table.insert(parent_children, insert_pos, item_id)
		else
			-- Insert in root items list
			local insert_pos = 1

			for i, root_id in ipairs(root_items) do
				if root_id == target_id then
					insert_pos = position == "before" and i or i + 1
					break
				end
			end

			table.insert(root_items, insert_pos, item_id)
		end
	end

	reorder_items()
end

function get_drop_target(mouse_y, display_list)
	local task_area_top = toolbar_position == "top" and toolbar_height or 0
	local item_y = task_area_top + 10 - scroll_offset

	for i, display_item in ipairs(display_list) do
		local item_top = item_y
		local current_height = display_item.height
		local item_bottom = item_y + current_height

		if mouse_y >= item_top and mouse_y <= item_bottom then
			local relative_y = mouse_y - item_top
			local threshold = current_height * drop_zone_threshold

			if relative_y < threshold then
				return { id = display_item.id, position = "before", level = display_item.level }
			elseif relative_y > current_height - threshold then
				return { id = display_item.id, position = "after", level = display_item.level }
			else
				return { id = display_item.id, position = "child", level = display_item.level + 1 }
			end
		end

		item_y = item_y + current_height
	end

	return nil
end

function get_item_at_position(mouse_x, mouse_y, display_list)
	local task_area_top = toolbar_position == "top" and toolbar_height or 0
	local item_y = task_area_top + 10 - scroll_offset

	for i, display_item in ipairs(display_list) do
		local item_top = item_y
		local current_height = display_item.height
		local item_bottom = item_y + current_height

		if mouse_y >= item_top and mouse_y <= item_bottom then
			local x_offset = 10 + (display_item.level * indent_size)

			local click_info = {
				item_id = display_item.id,
				display_item = display_item,
				checkbox_clicked = mouse_x >= x_offset and mouse_x <= x_offset + checkbox_size,
				collapse_icon_clicked = false,
			}

			-- Check if collapse icon was clicked (for items with children)
			if #todo_items[display_item.id].children > 0 then
				local collapse_icon_x_offset = math.floor(checkbox_size * 1.25 + 0.5)
				local icon_x = x_offset + collapse_icon_x_offset
				local icon_width = math.floor(checkbox_size * 0.83 + 0.5) -- ~10px at base size
				click_info.collapse_icon_clicked = mouse_x >= icon_x and mouse_x <= icon_x + icon_width
			end

			return click_info
		end

		item_y = item_y + current_height
	end

	return nil
end

function is_docked()
	return gfx.dock(-1) ~= 0
end

function toggle_dock()
	if is_docked() then
		gfx.dock(0) -- Undock (make it a floating window)
	else
		gfx.dock(1) -- Dock to the first available dock
	end
end

function draw_button(x, y, w, h, text, is_active, mouse_over)
	-- Draw button background
	if is_active then
		gfx.set(0.2, 0.5, 0.2, 1) -- Green for active
	elseif mouse_over then
		gfx.set(0.5, 0.5, 0.6, 1) -- Lighter for hover
	else
		gfx.set(0.3, 0.3, 0.4, 1) -- Default
	end
	gfx.rect(x, y, w, h)
	
	-- Draw button border
	gfx.set(0.6, 0.6, 0.6, 1)
	gfx.rect(x, y, w, 1)
	gfx.rect(x, y, 1, h)
	gfx.rect(x + w - 1, y, 1, h)
	gfx.rect(x, y + h - 1, w, 1)
	
	-- Draw text centered with clipping
	local text_r, text_g, text_b = hex_to_rgb(text_color)
	gfx.set(text_r, text_g, text_b, 1)
	local text_w, text_h = gfx.measurestr(text)
	local padding = 4
	local available_width = w - padding * 2
	
	-- Truncate text if it's too wide
	local display_text = text
	if text_w > available_width then
		local left, right = 1, #text
		while left < right do
			local mid = math.floor((left + right + 1) / 2)
			local test_text = text:sub(1, mid) .. "..."
			local test_w = gfx.measurestr(test_text)
			if test_w <= available_width then
				left = mid
			else
				right = mid - 1
			end
		end
		display_text = text:sub(1, left) .. "..."
		text_w = gfx.measurestr(display_text)
	end
	
	gfx.x = x + (w - text_w) / 2
	gfx.y = y + (h - text_h) / 2
	gfx.drawstr(display_text)
end

-- Map icon type names to Unicode characters
local icon_chars = {
	trash      = "\xe2\x9c\x95",    -- ✕  U+2715
	collapse   = "\xe2\x96\xb2",    -- ▲  U+25B2
	expand     = "\xe2\x96\xbc",    -- ▼  U+25BC
	eye_open   = "\xe2\x97\x89",    -- ◉  U+25C9
	eye_closed = "\xe2\x97\x8e",    -- ◎  U+25CE
	dock       = "\xe2\x8a\x9f",    -- ⊟  U+229F
	undock     = "\xe2\x8a\x9e",    -- ⊞  U+229E
	undo       = "\xe2\x86\xa9",    -- ↩  U+21A9
	redo       = "\xe2\x86\xaa",    -- ↪  U+21AA
	wrap_on    = "\xe2\x86\xbb",    --   U+21BB
	wrap_off   = "\xe2\x86\xbb",    --   U+21BB
}

function draw_icon_button(x, y, w, h, icon_type, is_active, mouse_over, disabled)
	-- Background
	if disabled then
		gfx.set(0.22, 0.22, 0.28, 1)
	elseif is_active then
		gfx.set(0.2, 0.5, 0.2, 1)
	elseif mouse_over then
		gfx.set(0.5, 0.5, 0.6, 1)
	else
		gfx.set(0.3, 0.3, 0.4, 1)
	end
	gfx.rect(x, y, w, h)

	-- Border
	if disabled then
		gfx.set(0.35, 0.35, 0.4, 1)
	else
		gfx.set(0.6, 0.6, 0.6, 1)
	end
	gfx.rect(x, y, w, 1)
	gfx.rect(x, y, 1, h)
	gfx.rect(x + w - 1, y, 1, h)
	gfx.rect(x, y + h - 1, w, 1)

	-- Icon colour (dimmed when disabled)
	local ir, ig, ib = hex_to_rgb(text_color)
	if disabled then
		gfx.set(ir * 0.35, ig * 0.35, ib * 0.35, 1)
	else
		gfx.set(ir, ig, ib, 1)
	end

	-- Choose a font size that fits snugly inside the button
	local icon_size = math.floor(math.min(w, h) * 0.62 + 0.5)
	icon_size = math.max(8, icon_size)
	gfx.setfont(2, icon_font_name, icon_size)

	local ch = icon_chars[icon_type] or "?"
	local cw, ch_h = gfx.measurestr(ch)
	-- Some geometric symbols (circles, triangles) report a line-height that
	-- includes descender space they don't use, making naive centering place
	-- them too low. Apply an upward shift only to those icons.
	local needs_shift = (icon_type == "collapse" or icon_type == "expand"
		or icon_type == "eye_open" or icon_type == "eye_closed")
	local descent_comp = needs_shift and math.floor(ch_h * 0.12 + 0.5) or 0
	gfx.x = math.floor(x + (w - cw) / 2 + 0.5)
	gfx.y = math.floor(y + (h - ch_h) / 2 - descent_comp + 0.5)
	gfx.drawstr(ch)

	-- Restore main font
	gfx.setfont(1, font_name, font_size)
end

function draw_settings_view()
	local bg_r, bg_g, bg_b = hex_to_rgb(bg_color)
	gfx.set(bg_r, bg_g, bg_b, 1)
	gfx.rect(0, 0, gfx.w, gfx.h)
	
	local text_r, text_g, text_b = hex_to_rgb(text_color)
	local margin = 20
	local y_offset = margin - settings_scroll_offset
	local content_width = gfx.w - margin * 2
	
	-- Title
	gfx.set(text_r, text_g, text_b, 1)
	gfx.setfont(1, font_name, font_size * 1.5)
	local title = "Settings"
	local title_w, title_h = gfx.measurestr(title)
	gfx.x = (gfx.w - title_w) / 2
	gfx.y = y_offset
	gfx.drawstr(title)
	y_offset = y_offset + title_h + margin
	
	-- Reset font
	set_font()
	
	local label_height = font_size + 5
	local button_height = math.max(30, font_size * 1.5)
	local slider_height = math.max(20, font_size * 1.2)
	local section_spacing = margin
	
	-- Font Size Section
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Font Size: " .. font_size)
	y_offset = y_offset + label_height
	
	-- Font size slider
	local slider_x = margin
	local slider_y = y_offset
	local slider_w = content_width
	local slider_h = slider_height
	
	-- Slider background
	gfx.set(0.2, 0.2, 0.2, 1)
	gfx.rect(slider_x, slider_y, slider_w, slider_h)
	
	-- Slider border
	gfx.set(0.6, 0.6, 0.6, 1)
	gfx.rect(slider_x, slider_y, slider_w, 1)
	gfx.rect(slider_x, slider_y, 1, slider_h)
	gfx.rect(slider_x + slider_w - 1, slider_y, 1, slider_h)
	gfx.rect(slider_x, slider_y + slider_h - 1, slider_w, 1)
	
	-- Slider value (8-48 range)
	local font_min = 8
	local font_max = 48
	font_slider_value = (font_size - font_min) / (font_max - font_min)
	local handle_x = slider_x + (slider_w - 10) * font_slider_value
	
	-- Slider fill
	gfx.set(0.4, 0.4, 0.6, 1)
	gfx.rect(slider_x + 2, slider_y + 2, handle_x - slider_x, slider_h - 4)
	
	-- Slider handle
	gfx.set(0.7, 0.7, 0.8, 1)
	gfx.rect(handle_x, slider_y, 10, slider_h)
	
	y_offset = y_offset + slider_h + section_spacing

	-- Input Bar Height Section
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Input Bar Height: " .. base_input_height)
	y_offset = y_offset + label_height

	local ih_slider_x = margin
	local ih_slider_y = y_offset
	local ih_slider_w = content_width
	local ih_slider_h = slider_height

	gfx.set(0.2, 0.2, 0.2, 1)
	gfx.rect(ih_slider_x, ih_slider_y, ih_slider_w, ih_slider_h)
	gfx.set(0.6, 0.6, 0.6, 1)
	gfx.rect(ih_slider_x, ih_slider_y, ih_slider_w, 1)
	gfx.rect(ih_slider_x, ih_slider_y, 1, ih_slider_h)
	gfx.rect(ih_slider_x + ih_slider_w - 1, ih_slider_y, 1, ih_slider_h)
	gfx.rect(ih_slider_x, ih_slider_y + ih_slider_h - 1, ih_slider_w, 1)

	local ih_min, ih_max = 12, 64
	input_height_slider_value = (base_input_height - ih_min) / (ih_max - ih_min)
	local ih_handle_x = ih_slider_x + (ih_slider_w - 10) * input_height_slider_value
	gfx.set(0.4, 0.4, 0.6, 1)
	gfx.rect(ih_slider_x + 2, ih_slider_y + 2, ih_handle_x - ih_slider_x, ih_slider_h - 4)
	gfx.set(0.7, 0.7, 0.8, 1)
	gfx.rect(ih_handle_x, ih_slider_y, 10, ih_slider_h)

	y_offset = y_offset + ih_slider_h + section_spacing

	-- Toolbar Height Section
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Toolbar Height: " .. base_toolbar_height)
	y_offset = y_offset + label_height

	local th_slider_x = margin
	local th_slider_y = y_offset
	local th_slider_w = content_width
	local th_slider_h = slider_height

	gfx.set(0.2, 0.2, 0.2, 1)
	gfx.rect(th_slider_x, th_slider_y, th_slider_w, th_slider_h)
	gfx.set(0.6, 0.6, 0.6, 1)
	gfx.rect(th_slider_x, th_slider_y, th_slider_w, 1)
	gfx.rect(th_slider_x, th_slider_y, 1, th_slider_h)
	gfx.rect(th_slider_x + th_slider_w - 1, th_slider_y, 1, th_slider_h)
	gfx.rect(th_slider_x, th_slider_y + th_slider_h - 1, th_slider_w, 1)

	local tth_min, tth_max = 12, 64
	toolbar_height_slider_value = (base_toolbar_height - tth_min) / (tth_max - tth_min)
	local th_handle_x = th_slider_x + (th_slider_w - 10) * toolbar_height_slider_value
	gfx.set(0.4, 0.4, 0.6, 1)
	gfx.rect(th_slider_x + 2, th_slider_y + 2, th_handle_x - th_slider_x, th_slider_h - 4)
	gfx.set(0.7, 0.7, 0.8, 1)
	gfx.rect(th_handle_x, th_slider_y, 10, th_slider_h)

	y_offset = y_offset + th_slider_h + section_spacing

	-- FPS Section
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Frame Rate Limit:")
	y_offset = y_offset + label_height
	
	-- FPS buttons in a row
	local button_spacing = 10
	local num_fps_buttons = 4
	local button_w = (content_width - button_spacing * (num_fps_buttons - 1)) / num_fps_buttons
	local fps_values = {15, 30, 60, 0}
	local fps_labels = {"15", "30", "60", "∞"}
	
	for i = 1, num_fps_buttons do
		local btn_x = margin + (i - 1) * (button_w + button_spacing)
		local is_active = (target_fps == fps_values[i])
		local mouse_over = gfx.mouse_x >= btn_x and gfx.mouse_x <= btn_x + button_w
			and gfx.mouse_y >= y_offset and gfx.mouse_y <= y_offset + button_height
		
		draw_button(btn_x, y_offset, button_w, button_height, fps_labels[i], is_active, mouse_over)
	end
	
	y_offset = y_offset + button_height + section_spacing
	
	-- Sort Section
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Sort Order:")
	y_offset = y_offset + label_height
	
	-- Sort buttons
	local sort_button_w = (content_width - button_spacing) / 2
	local sort_modes = {"custom", "alphabetical"}
	local sort_labels = {"User", "Alphabetical"}
	
	for i = 1, 2 do
		local btn_x = margin + (i - 1) * (sort_button_w + button_spacing)
		local is_active = (sort_mode == sort_modes[i])
		local mouse_over = gfx.mouse_x >= btn_x and gfx.mouse_x <= btn_x + sort_button_w
			and gfx.mouse_y >= y_offset and gfx.mouse_y <= y_offset + button_height
		
		draw_button(btn_x, y_offset, sort_button_w, button_height, sort_labels[i], is_active, mouse_over)
	end
	
	y_offset = y_offset + button_height + section_spacing
	
	-- Toolbar position
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = margin
	gfx.y = y_offset
	gfx.drawstr("Toolbar Position:")
	y_offset = y_offset + label_height

	local tb_btn_spacing = 10
	local tb_pos_w = (content_width - tb_btn_spacing) / 2
	local tb_pos_labels = {"Top", "Bottom"}
	local tb_pos_values = {"top", "bottom"}
	for i = 1, 2 do
		local btn_x = margin + (i - 1) * (tb_pos_w + tb_btn_spacing)
		local is_active = (toolbar_position == tb_pos_values[i])
		local mouse_over = gfx.mouse_x >= btn_x and gfx.mouse_x <= btn_x + tb_pos_w
			and gfx.mouse_y >= y_offset and gfx.mouse_y <= y_offset + button_height
		draw_button(btn_x, y_offset, tb_pos_w, button_height, tb_pos_labels[i], is_active, mouse_over)
	end
	y_offset = y_offset + button_height + section_spacing
	
	-- Undo info
	if #undo_stack > 0 then
		gfx.set(text_r, text_g, text_b, 1)
		gfx.x = margin
		gfx.y = y_offset
		gfx.drawstr("Last Action: " .. undo_stack[#undo_stack].action)
		y_offset = y_offset + label_height
		
		-- Undo button
		mouse_over = gfx.mouse_x >= margin and gfx.mouse_x <= margin + content_width
			and gfx.mouse_y >= y_offset and gfx.mouse_y <= y_offset + button_height
		draw_button(margin, y_offset, content_width, button_height, "Undo", false, mouse_over)
		y_offset = y_offset + button_height + section_spacing
	end
	
	-- Quit button (full width)
	mouse_over = gfx.mouse_x >= margin and gfx.mouse_x <= margin + content_width
		and gfx.mouse_y >= y_offset and gfx.mouse_y <= y_offset + button_height
	draw_button(margin, y_offset, content_width, button_height, "Quit", false, mouse_over)
end

function handle_settings_mouse()
	local mouse_cap = gfx.mouse_cap
	local mouse_x = gfx.mouse_x
	local mouse_y = gfx.mouse_y
	
	-- Handle mouse wheel scrolling
	if gfx.mouse_wheel ~= 0 then
		local max_scroll = get_settings_scroll_limits()
		local scroll_amount = gfx.mouse_wheel > 0 and -30 or 30
		settings_scroll_offset = math.max(0, math.min(settings_scroll_offset + scroll_amount, max_scroll))
		gfx.mouse_wheel = 0
		request_immediate_update()
	end
	
	-- Handle right click to go back to tasks view (check BEFORE any button processing)
	if mouse_cap & 2 == 2 and last_mouse_cap & 2 == 0 then -- Right click
		current_view = "tasks"
		settings_scroll_offset = 0 -- Reset scroll when leaving settings
		request_immediate_update()
		return
	end
	
	local margin = 20
	local content_width = gfx.w - margin * 2
	local y_offset = margin - settings_scroll_offset
	
	-- Skip title
	gfx.setfont(1, font_name, font_size * 1.5)
	local title_w, title_h = gfx.measurestr("Settings")
	y_offset = y_offset + title_h + margin
	set_font()
	
	local label_height = font_size + 5
	local button_height = math.max(30, font_size * 1.5)
	local slider_height = math.max(20, font_size * 1.2)
	local section_spacing = margin
	
	-- Skip font size label
	y_offset = y_offset + label_height

	-- Font slider interaction
	local slider_x = margin
	local slider_y = y_offset
	local slider_w = content_width
	local slider_h = slider_height
	
	if mouse_cap & 1 == 1 then -- Left mouse down
		if mouse_x >= slider_x and mouse_x <= slider_x + slider_w
			and mouse_y >= slider_y and mouse_y <= slider_y + slider_h then
			font_slider_dragging = true
		end
		
		if font_slider_dragging then
			local new_value = (mouse_x - slider_x) / slider_w
			new_value = math.max(0, math.min(1, new_value))
			local font_min = 8
			local font_max = 48
			local new_font_size = math.floor(font_min + new_value * (font_max - font_min) + 0.5)
			if new_font_size ~= font_size then
				font_size = new_font_size
				set_font()
				mark_cache_dirty()
				save_settings_deferred()
				request_immediate_update()
			end
		end
	else
		font_slider_dragging = false
	end
	
	y_offset = y_offset + slider_h + section_spacing

	-- Input bar height slider interaction
	local ih_slider_x = margin
	local ih_slider_y = y_offset
	local ih_slider_w = content_width
	local ih_slider_h = slider_height

	y_offset = y_offset + label_height -- skip label

	if mouse_cap & 1 == 1 then
		if mouse_x >= ih_slider_x and mouse_x <= ih_slider_x + ih_slider_w
			and mouse_y >= ih_slider_y + label_height and mouse_y <= ih_slider_y + label_height + ih_slider_h then
			input_height_slider_dragging = true
		end

		if input_height_slider_dragging then
			local new_value = (mouse_x - ih_slider_x) / ih_slider_w
			new_value = math.max(0, math.min(1, new_value))
			local ih_min, ih_max = 12, 64
			local new_h = math.floor(ih_min + new_value * (ih_max - ih_min) + 0.5)
			if new_h ~= base_input_height then
				base_input_height = new_h
				update_scaled_dimensions()
				mark_cache_dirty()
				save_settings_deferred()
				request_immediate_update()
			end
		end
	else
		input_height_slider_dragging = false
	end

	y_offset = y_offset + ih_slider_h + section_spacing

	-- Toolbar height slider interaction
	local tth_slider_x = margin
	local tth_slider_y = y_offset
	local tth_slider_w = content_width
	local tth_slider_h = slider_height

	y_offset = y_offset + label_height -- skip label

	if mouse_cap & 1 == 1 then
		if mouse_x >= tth_slider_x and mouse_x <= tth_slider_x + tth_slider_w
			and mouse_y >= tth_slider_y + label_height and mouse_y <= tth_slider_y + label_height + tth_slider_h then
			toolbar_height_slider_dragging = true
		end

		if toolbar_height_slider_dragging then
			local new_value = (mouse_x - tth_slider_x) / tth_slider_w
			new_value = math.max(0, math.min(1, new_value))
			local tth_min, tth_max = 12, 64
			local new_h = math.floor(tth_min + new_value * (tth_max - tth_min) + 0.5)
			if new_h ~= base_toolbar_height then
				base_toolbar_height = new_h
				update_scaled_dimensions()
				mark_cache_dirty()
				save_settings_deferred()
				request_immediate_update()
			end
		end
	else
		toolbar_height_slider_dragging = false
	end

	y_offset = y_offset + tth_slider_h + section_spacing

	-- Skip FPS label
	y_offset = y_offset + label_height
	
	-- FPS button clicks
	if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then -- Click (not held)
		local button_spacing = 10
		local num_fps_buttons = 4
		local button_w = (content_width - button_spacing * (num_fps_buttons - 1)) / num_fps_buttons
		local fps_values = {15, 30, 60, 0}
		
		for i = 1, num_fps_buttons do
			local btn_x = margin + (i - 1) * (button_w + button_spacing)
			if mouse_x >= btn_x and mouse_x <= btn_x + button_w
				and mouse_y >= y_offset and mouse_y <= y_offset + button_height then
				target_fps = fps_values[i]
				frame_time = target_fps > 0 and (1.0 / target_fps) or 0
				save_settings_deferred()
				request_immediate_update()
			end
		end
	end
	
	y_offset = y_offset + button_height + section_spacing
	
	-- Skip sort label
	y_offset = y_offset + label_height
	
	-- Sort button clicks
	if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then
		local sort_button_w = (content_width - 10) / 2
		local sort_modes = {"custom", "alphabetical"}
		
		for i = 1, 2 do
			local btn_x = margin + (i - 1) * (sort_button_w + 10)
			if mouse_x >= btn_x and mouse_x <= btn_x + sort_button_w
				and mouse_y >= y_offset and mouse_y <= y_offset + button_height then
				save_state_for_undo("Sort " .. sort_modes[i])
				sort_mode = sort_modes[i]
				mark_cache_dirty()
				save_settings_deferred()
				request_immediate_update()
			end
		end
	end
	
	y_offset = y_offset + button_height + section_spacing
	
	-- Toolbar position buttons
	y_offset = y_offset + label_height -- skip "Toolbar Position:" label
	local tb_pos_w = (content_width - 10) / 2
	local tb_pos_values = {"top", "bottom"}
	if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then
		for i = 1, 2 do
			local btn_x = margin + (i - 1) * (tb_pos_w + 10)
			if mouse_x >= btn_x and mouse_x <= btn_x + tb_pos_w
				and mouse_y >= y_offset and mouse_y <= y_offset + button_height then
				toolbar_position = tb_pos_values[i]
				mark_cache_dirty()
				save_settings_deferred()
				request_immediate_update()
			end
		end
	end
	y_offset = y_offset + button_height + section_spacing
	
	-- Undo button (if available)
	if #undo_stack > 0 then
		y_offset = y_offset + label_height
		if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then
			if mouse_x >= margin and mouse_x <= margin + content_width
				and mouse_y >= y_offset and mouse_y <= y_offset + button_height then
				undo_last_action()
				request_immediate_update()
			end
		end
		y_offset = y_offset + button_height + section_spacing
	end
	
	-- Quit button (full width)
	if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then
		if mouse_x >= margin and mouse_x <= margin + content_width
			and mouse_y >= y_offset and mouse_y <= y_offset + button_height then
			save_todo_data()
			save_settings()
			gfx.quit()
		end
	end
end

function add_task(text, as_subtask, outdent)
	if text and text ~= "" then
		save_state_for_undo("Add task")

		local new_item = {
			id = next_id,
			parent_id = nil,
			text = text,
			done = false,
			children = {},
			order = get_next_order(),
			collapsed = false,
		}

		if as_subtask and selected_id and todo_items[selected_id] then
			-- Add as subtask - selection stays on parent
			new_item.parent_id = selected_id
			todo_items[selected_id].collapsed = false -- Expand parent to show new child
			table.insert(todo_items[selected_id].children, next_id)
		elseif outdent and selected_id and todo_items[selected_id] then
			-- Add task at parent level of selected task
			local selected_item = todo_items[selected_id]

			if selected_item.parent_id then
				-- Selected task has a parent, so add as sibling to that parent
				local grandparent_id = todo_items[selected_item.parent_id].parent_id
				new_item.parent_id = grandparent_id

				if grandparent_id then
					-- Insert after the parent in the grandparent's children
					local grandparent_children = todo_items[grandparent_id].children
					local insert_pos = #grandparent_children + 1

					for i, child_id in ipairs(grandparent_children) do
						if child_id == selected_item.parent_id then
							insert_pos = i + 1
							break
						end
					end

					table.insert(grandparent_children, insert_pos, next_id)
				else
					-- Parent was a root item, so add as root item after the parent
					local insert_pos = #root_items + 1

					for i, root_id in ipairs(root_items) do
						if root_id == selected_item.parent_id then
							insert_pos = i + 1
							break
						end
					end

					table.insert(root_items, insert_pos, next_id)
				end

				selected_id = next_id
			else
				-- Selected task is already at root level, treat like normal Enter
				local insert_pos = #root_items + 1
				for i, root_id in ipairs(root_items) do
					if root_id == selected_id then
						insert_pos = i + 1
						break
					end
				end
				table.insert(root_items, insert_pos, next_id)
				selected_id = next_id
			end
		else
			-- Add as sibling or new root - select the new task
			if selected_id and todo_items[selected_id] then
				local selected_item = todo_items[selected_id]
				if selected_item.parent_id then
					-- Add as sibling
					new_item.parent_id = selected_item.parent_id
					table.insert(todo_items[selected_item.parent_id].children, next_id)
				else
					-- Add as root item after selected root item
					local insert_pos = #root_items + 1
					for i, root_id in ipairs(root_items) do
						if root_id == selected_id then
							insert_pos = i + 1
							break
						end
					end
					table.insert(root_items, insert_pos, next_id)
				end
			else
				-- Add as new root item
				table.insert(root_items, next_id)
			end

			-- Select the new task when adding siblings or new parents
			selected_id = next_id
		end

		todo_items[next_id] = new_item
		next_id = next_id + 1
		reorder_items()
	end
end

function delete_task(task_id)
	if task_id and todo_items[task_id] then
		save_state_for_undo("Delete task")

		local item = todo_items[task_id]

		local function delete_recursive(item_id)
			local item_to_delete = todo_items[item_id]
			if item_to_delete then
				for _, child_id in ipairs(item_to_delete.children) do
					delete_recursive(child_id)
				end
				todo_items[item_id] = nil
			end
		end

		delete_recursive(task_id)

		if item.parent_id and todo_items[item.parent_id] then
			local parent_children = todo_items[item.parent_id].children
			for i, child_id in ipairs(parent_children) do
				if child_id == task_id then
					table.remove(parent_children, i)
					break
				end
			end
		else
			for i, root_id in ipairs(root_items) do
				if root_id == task_id then
					table.remove(root_items, i)
					break
				end
			end
		end

		if selected_id == task_id then
			selected_id = nil
		end

		mark_cache_dirty()
		mark_needs_save()

		-- Clamp scroll offset to valid range
		local display_list = get_display_list()
		local max_scroll = get_scroll_limits(display_list)
		if scroll_offset > max_scroll then
			scroll_offset = max_scroll
		end
	end
end

function toggle_task_done(task_id)
	if todo_items[task_id] then
		save_state_for_undo("Toggle done")
		todo_items[task_id].done = not todo_items[task_id].done
		mark_cache_dirty()
		mark_needs_save()
	end
end

function draw_collapse_icon(x, y, collapsed)
	gfx.set(0.7, 0.7, 0.7, 1)

	local scale = calculate_scale_factor()
	local icon_size = math.floor(6 * scale + 0.5)
	local icon_offset = math.floor(3 * scale + 0.5)

	if collapsed then
		-- Draw right-pointing triangle (collapsed)
		gfx.triangle(x, y + icon_offset, x, y + icon_offset + icon_size, x + icon_size, y + icon_offset + icon_size / 2)
	else
		-- Draw down-pointing triangle (expanded)
		gfx.triangle(x, y + icon_offset, x + icon_size, y + icon_offset, x + icon_size / 2, y + icon_offset + icon_size)
	end
end

function get_hovered_toolbar_btn(mouse_x, mouse_y)
	local toolbar_y = toolbar_position == "top" and 0 or (gfx.h - input_height - toolbar_height)
	if mouse_y < toolbar_y or mouse_y >= toolbar_y + toolbar_height then
		return nil, nil
	end

	local tb_padding = 3
	local tb_btn_h = toolbar_height - tb_padding * 2
	local tb_btn_w = tb_btn_h
	local tb_btn_y = toolbar_y + tb_padding

	if mouse_y < tb_btn_y or mouse_y > tb_btn_y + tb_btn_h then
		return nil, nil
	end

	-- Left group: undo, redo
	local left_btns = {
		{key = "undo", label = "Undo"},
		{key = "redo", label = "Redo"},
	}
	for i, btn in ipairs(left_btns) do
		local bx = tb_padding + (i - 1) * (tb_btn_w + tb_padding)
		if mouse_x >= bx and mouse_x <= bx + tb_btn_w then
			return btn.key, btn.label
		end
	end

	-- Center group: trash, collapse, eye, wrap
	local group_gap      = tb_padding * 3
	local left_group_end = tb_padding + 2 * (tb_btn_w + tb_padding)
	local center_group_w = 4 * tb_btn_w + 3 * tb_padding
	local right_start    = gfx.w - tb_padding - tb_btn_w
	local ideal_center   = math.floor((gfx.w - center_group_w) / 2 + 0.5)
	local center_start   = math.max(ideal_center, left_group_end + group_gap)
	center_start         = math.min(center_start, right_start - group_gap - center_group_w)

	local center_btns = {
		{key = "trash",    label = "Clear All Tasks"},
		{key = "collapse", label = has_any_uncollapsed() and "Collapse All" or "Expand All"},
		{key = "eye",      label = show_completed and "Hide Completed" or "Show Completed"},
		{key = "wrap",     label = wrap_task_text and "Disable Text Wrap" or "Enable Text Wrap"},
	}
	for i, btn in ipairs(center_btns) do
		local bx = center_start + (i - 1) * (tb_btn_w + tb_padding)
		if mouse_x >= bx and mouse_x <= bx + tb_btn_w then
			return btn.key, btn.label
		end
	end

	-- Right group: dock
	if mouse_x >= right_start and mouse_x <= right_start + tb_btn_w then
		return "dock", is_docked() and "Undock Window" or "Dock Window"
	end

	return nil, nil
end

function draw_tooltip()
	if not tooltip_visible or tooltip_text == "" then return end

	set_font()
	local tw, th = gfx.measurestr(tooltip_text)
	local pad   = 5
	local box_w = tw + pad * 2
	local box_h = th + pad * 2

	-- Horizontally centre on mouse, clamped inside window with a 2px margin
	local tx = math.floor(tooltip_mouse_x - box_w / 2)
	tx = math.max(2, math.min(tx, gfx.w - box_w - 2))

	-- Place just below toolbar when it's on top, just above it when at bottom
	local ty
	if toolbar_position == "top" then
		ty = toolbar_height + 4
	else
		ty = gfx.h - input_height - toolbar_height - box_h - 4
	end

	-- Background
	gfx.set(0.12, 0.12, 0.12, 1)
	gfx.rect(tx, ty, box_w, box_h)

	-- Border
	gfx.set(0.55, 0.55, 0.55, 1)
	gfx.rect(tx,              ty,              box_w, 1)
	gfx.rect(tx,              ty,              1,     box_h)
	gfx.rect(tx + box_w - 1, ty,              1,     box_h)
	gfx.rect(tx,              ty + box_h - 1, box_w, 1)

	-- Text
	local tr, tg, tb = hex_to_rgb(text_color)
	gfx.set(tr, tg, tb, 1)
	gfx.x = tx + pad
	gfx.y = ty + pad
	gfx.drawstr(tooltip_text)
end

function draw_gui()
	needs_redraw = false -- Reset redraw flag
	
	-- Check for window resize and invalidate cache if needed
	if gfx.w ~= last_window_w or gfx.h ~= last_window_h then
		last_window_w = gfx.w
		last_window_h = gfx.h
		if wrap_task_text then
			mark_cache_dirty() -- Only need to invalidate if wrapping is enabled
		end
	end
	
	if current_view == "settings" then
		draw_settings_view()
		return
	end
	
	-- Clear background
	local bg_r, bg_g, bg_b = hex_to_rgb(bg_color)
	gfx.set(bg_r, bg_g, bg_b, 1)
	gfx.rect(0, 0, gfx.w, gfx.h)

	local display_list = get_display_list()
	local task_area_top    = toolbar_position == "top" and toolbar_height or 0
	local task_area_bottom = toolbar_position == "top" and (gfx.h - input_height) or (gfx.h - input_height - toolbar_height)
	local y = task_area_top + 10 - scroll_offset

	-- Draw drop indicator
	if dragging and drop_target then
		local temp_y = task_area_top + 10 - scroll_offset

		for _, display_item in ipairs(display_list) do
			if display_item.id == drop_target.id then
				local current_height = display_item.height
				
				if drop_target.position == "before" or drop_target.position == "after" then
					-- Blue color for sibling operations
					gfx.set(0.2, 0.5, 1, 0.8)

					-- Calculate x position based on target depth (where the dragged task will be)
					local x_indent = 10 + (display_item.level * indent_size)

					-- Draw horizontal drop line
					local line_y = drop_target.position == "before" and (temp_y - 1) or (temp_y + current_height - 1)
					gfx.rect(x_indent, line_y, gfx.w - x_indent, 2)

					-- Draw vertical connecting line showing hierarchy
					if drop_target.position == "after" then
						-- Vertical line from top of task down to drop line
						gfx.rect(x_indent, temp_y, 2, current_height)
					else -- before
						-- Vertical line from drop line down through task
						gfx.rect(x_indent, line_y, 2, current_height)
					end
				else -- child
					-- Orange highlight for child operation
					gfx.set(1, 0.5, 0, 0.8)
					gfx.rect(
						10 + (display_item.level * indent_size),
						temp_y,
						gfx.w - 20 - (display_item.level * indent_size),
						current_height
					)
				end
				break
			end
			temp_y = temp_y + display_item.height
		end
	end

	-- Draw tasks
	for i, display_item in ipairs(display_list) do
		local item = display_item.item
		local level = display_item.level
		local current_height = display_item.height
		local x = 10 + (level * indent_size)

		-- Skip if outside visible area (including toolbar), or if it's the item being dragged
		if y > task_area_top - current_height and y < task_area_bottom and display_item.id ~= drag_item_id then
			-- Selection highlight
			if display_item.id == selected_id then
				gfx.set(0.3, 0.3, 0.5, 1)
				gfx.rect(0, y, gfx.w, current_height)
			end

			-- Show drag preparation highlight
			if mouse_down_item == display_item.id and not dragging and mouse_down_time > 0 then
				local hold_time = r.time_precise() - mouse_down_time
				if hold_time > click_threshold_time then
					gfx.set(0.5, 0.3, 0.1, 0.3)
					gfx.rect(0, y, gfx.w, current_height)
				end
			end

			-- Check if this item or any ancestor is completed
			local ancestor_completed = is_ancestor_completed(display_item.id)
			local is_grayed = item.done or ancestor_completed

			-- Checkbox
			gfx.set(is_grayed and 0.4 or 0.6, is_grayed and 0.4 or 0.6, is_grayed and 0.4 or 0.6, 1)
			gfx.rect(x, y + checkbox_y_offset, checkbox_size, checkbox_size)

			if item.done then
				gfx.set(is_grayed and 0.15 or 0.2, is_grayed and 0.6 or 0.8, is_grayed and 0.15 or 0.2, 1)
				local inner_margin = math.floor(checkbox_size * 0.167 + 0.5) -- ~2px at base size
				gfx.rect(
					x + inner_margin,
					y + checkbox_y_offset + inner_margin,
					checkbox_size - inner_margin * 2,
					checkbox_size - inner_margin * 2
				)
			end

			-- Collapse icon (if has children)
			local has_children = #item.children > 0
			local collapse_icon_x_offset = math.floor(checkbox_size * 1.25 + 0.5) -- ~15px at base size
			local text_x_offset_with_icon = math.floor(checkbox_size * 2.33 + 0.5) -- ~28px at base size
			local text_x_offset_no_icon = math.floor(checkbox_size * 1.67 + 0.5) -- ~20px at base size

			if has_children then
				draw_collapse_icon(x + collapse_icon_x_offset, y + collapse_icon_y_offset, item.collapsed)
			end

			-- Text (adjust position based on whether there's a collapse icon)
			local text_x = has_children and (x + text_x_offset_with_icon) or (x + text_x_offset_no_icon)
			local text_r, text_g, text_b = hex_to_rgb(text_color)
			local brightness = is_grayed and 0.5 or 1.0
			gfx.set(text_r * brightness, text_g * brightness, text_b * brightness, 1)
			
			-- Draw text with wrapping if enabled
			if wrap_task_text then
				local available_width = gfx.w - text_x - 10
				local lines = wrap_text(item.text, available_width)
				local line_height = font_size + 2
				local text_y = y + task_text_y_offset  -- Use same offset as non-wrapped text for consistent centering
				
				for _, line in ipairs(lines) do
					gfx.x = text_x
					gfx.y = text_y
					gfx.drawstr(line)
					text_y = text_y + line_height
				end
			else
				gfx.x = text_x
				gfx.y = y + task_text_y_offset
				gfx.drawstr(item.text)
			end
		end

		y = y + current_height
	end

	-- Draw dragged item at mouse position
	if dragging and drag_item_id and todo_items[drag_item_id] then
		local drag_item = todo_items[drag_item_id]
		local drag_y = gfx.mouse_y - drag_offset_y

		-- Calculate indentation based on drop target
		local drag_level = 0
		if drop_target then
			drag_level = drop_target.level
		end

		local drag_x = 10 + (drag_level * indent_size)

		gfx.set(0.8, 0.8, 0.8, 0.8)
		gfx.rect(drag_x, drag_y, gfx.w - drag_x - 10, item_height)

		gfx.set(0, 0, 0, 1)
		gfx.x = drag_x + 5
		gfx.y = drag_y + task_text_y_offset
		gfx.drawstr(drag_item.text)
	end

	-- Toolbar (top or bottom)
	local toolbar_y = toolbar_position == "top" and 0 or (gfx.h - input_height - toolbar_height)
	local tb_bg_r, tb_bg_g, tb_bg_b = hex_to_rgb(toolbar_bg_color)
	gfx.set(tb_bg_r, tb_bg_g, tb_bg_b, 1)
	gfx.rect(0, toolbar_y, gfx.w, toolbar_height)

	-- Draw 6 small square icon buttons, left-aligned with padding
	local tb_padding = 3
	local tb_btn_h = toolbar_height - tb_padding * 2
	local tb_btn_w = tb_btn_h -- square buttons
	local tb_btn_y = toolbar_y + tb_padding

	local collapse_icon = has_any_uncollapsed() and "collapse" or "expand"
	local eye_icon      = show_completed and "eye_open" or "eye_closed"
	local dock_icon     = is_docked() and "undock" or "dock"

	-- Define the three groups
	local left_btns = {
		{icon = "undo", disabled = #undo_stack == 0},
		{icon = "redo", disabled = #redo_stack == 0},
	}
	local wrap_icon = wrap_task_text and "wrap_on" or "wrap_off"
	local center_btns = {
		{icon = "trash",       disabled = false},
		{icon = collapse_icon, disabled = false},
		{icon = eye_icon,      disabled = false},
		{icon = wrap_icon,     disabled = false},
	}
	local right_btns = {
		{icon = dock_icon, disabled = false},
	}

	-- Calculate group positions
	local group_gap      = tb_padding * 3 -- minimum space between groups
	local left_group_end = tb_padding + #left_btns * (tb_btn_w + tb_padding)
	local center_group_w = #center_btns * tb_btn_w + (#center_btns - 1) * tb_padding
	local right_start    = gfx.w - tb_padding - tb_btn_w
	local ideal_center   = math.floor((gfx.w - center_group_w) / 2 + 0.5)
	local center_start   = math.max(ideal_center, left_group_end + group_gap)
	center_start         = math.min(center_start, right_start - group_gap - center_group_w)

	local function draw_btn_group(btns, start_x)
		for i, btn in ipairs(btns) do
			local bx = start_x + (i - 1) * (tb_btn_w + tb_padding)
			local mo = not btn.disabled
				and gfx.mouse_x >= bx and gfx.mouse_x <= bx + tb_btn_w
				and gfx.mouse_y >= tb_btn_y and gfx.mouse_y <= tb_btn_y + tb_btn_h
			draw_icon_button(bx, tb_btn_y, tb_btn_w, tb_btn_h, btn.icon, false, mo, btn.disabled)
		end
	end

	draw_btn_group(left_btns,   tb_padding)
	draw_btn_group(center_btns, center_start)
	draw_btn_group(right_btns,  right_start)

	-- Input bar at bottom (always appears active)
	local input_y = gfx.h - input_height
	local input_r, input_g, input_b = hex_to_rgb(input_bar_bg_color)
	gfx.set(input_r, input_g, input_b, 1)
	gfx.rect(0, input_y, gfx.w, input_height)

	-- Draw input bar border
	local border_r, border_g, border_b = hex_to_rgb(input_bar_border_color)
	gfx.set(border_r, border_g, border_b, 1)
	-- Top border
	gfx.rect(0, input_y, gfx.w, input_bar_border_thickness)
	-- Left border
	gfx.rect(0, input_y, input_bar_border_thickness, input_height)
	-- Right border
	gfx.rect(gfx.w - input_bar_border_thickness, input_y, input_bar_border_thickness, input_height)
	-- Bottom border
	gfx.rect(0, gfx.h - input_bar_border_thickness, gfx.w, input_bar_border_thickness)

	local text_r, text_g, text_b = hex_to_rgb(text_color)
	gfx.set(text_r, text_g, text_b, 1)
	gfx.x = 5
	gfx.y = input_y + input_text_y_offset
	local display_text = input_text
	if math.floor(r.time_precise() * 2) % 2 == 0 then
		display_text = display_text .. "|"
	end
	gfx.drawstr(display_text)

	-- Tooltip drawn last so it sits on top of everything
	draw_tooltip()
end

function handle_mouse()
	local mouse_y = gfx.mouse_y
	local mouse_x = gfx.mouse_x
	local mouse_cap = gfx.mouse_cap
	local current_time = r.time_precise()

	-- Check if mouse state changed
	local mouse_moved = (mouse_x ~= last_mouse_x or mouse_y ~= last_mouse_y)
	local mouse_cap_changed = (mouse_cap ~= last_mouse_cap)

	-- Tooltip hover tracking (tasks view only) - must run before the early-return
	-- guard so the timer is checked even when the mouse is stationary
	if current_view == "tasks" then
		local btn_key, btn_label = get_hovered_toolbar_btn(mouse_x, mouse_y)
		if btn_key ~= tooltip_current_btn then
			tooltip_current_btn = btn_key
			tooltip_text        = btn_label or ""
			tooltip_hover_start = btn_key and r.time_precise() or 0
			tooltip_visible     = false
			tooltip_mouse_x     = mouse_x
			tooltip_mouse_y     = mouse_y
			needs_redraw        = true
		elseif btn_key then
			tooltip_mouse_x = mouse_x
			tooltip_mouse_y = mouse_y
			if not tooltip_visible and (r.time_precise() - tooltip_hover_start) >= tooltip_delay then
				tooltip_visible = true
				needs_redraw    = true
			end
		else
			if tooltip_visible then
				tooltip_visible = false
				needs_redraw    = true
			end
		end
	end

	if not mouse_moved and not mouse_cap_changed and not dragging and current_view == "tasks" then
		return -- Nothing to do
	end

	-- Handle settings view separately
	if current_view == "settings" then
		handle_settings_mouse()
		last_mouse_x = mouse_x
		last_mouse_y = mouse_y
		last_mouse_cap = mouse_cap
		request_immediate_update()
		return
	end

	-- Handle right mouse button - toggle to settings view (check BEFORE updating last_mouse_cap)
	if mouse_cap & 2 == 2 and last_mouse_cap & 2 == 0 then -- Right click
		current_view = "settings"
		settings_scroll_offset = 0 -- Reset scroll when entering settings
		last_mouse_x = mouse_x
		last_mouse_y = mouse_y
		last_mouse_cap = mouse_cap
		request_immediate_update()
		return
	end

	request_immediate_update()

	local display_list = get_display_list()

	-- Toolbar left-click handling (edge-triggered)
	if mouse_cap & 1 == 1 and last_mouse_cap & 1 == 0 then
		local toolbar_y = toolbar_position == "top" and 0 or (gfx.h - input_height - toolbar_height)
		if mouse_y >= toolbar_y and mouse_y < toolbar_y + toolbar_height then
			local tb_padding = 3
			local tb_btn_h = toolbar_height - tb_padding * 2
			local tb_btn_w = tb_btn_h -- square
			local tb_btn_y = toolbar_y + tb_padding

				-- Left group: undo, redo
			local left_actions = {"undo", "redo"}
			for i, action in ipairs(left_actions) do
				local bx = tb_padding + (i - 1) * (tb_btn_w + tb_padding)
				if mouse_x >= bx and mouse_x <= bx + tb_btn_w
					and mouse_y >= tb_btn_y and mouse_y <= tb_btn_y + tb_btn_h then
					if action == "undo" and #undo_stack > 0 then
						undo_last_action()
					elseif action == "redo" and #redo_stack > 0 then
						redo_last_action()
					end
					last_mouse_x = mouse_x
					last_mouse_y = mouse_y
					last_mouse_cap = mouse_cap
					request_immediate_update()
					return
				end
			end

			-- Center group: trash, collapse, eye, wrap
			local group_gap      = tb_padding * 3
			local left_group_end = tb_padding + 2 * (tb_btn_w + tb_padding)
			local center_group_w = 4 * tb_btn_w + 3 * tb_padding
			local right_start_c  = gfx.w - tb_padding - tb_btn_w
			local ideal_center   = math.floor((gfx.w - center_group_w) / 2 + 0.5)
			local center_start   = math.max(ideal_center, left_group_end + group_gap)
			center_start         = math.min(center_start, right_start_c - group_gap - center_group_w)
			local center_actions = {"trash", "collapse", "eye", "wrap"}
			for i, action in ipairs(center_actions) do
				local bx = center_start + (i - 1) * (tb_btn_w + tb_padding)
				if mouse_x >= bx and mouse_x <= bx + tb_btn_w
					and mouse_y >= tb_btn_y and mouse_y <= tb_btn_y + tb_btn_h then
					if action == "trash" then
						clear_all_tasks()
					elseif action == "collapse" then
						if has_any_uncollapsed() then
							collapse_all_tasks()
						else
							uncollapse_all_tasks()
						end
					elseif action == "eye" then
						save_state_for_undo("Toggle show completed")
						show_completed = not show_completed
						mark_cache_dirty()
						save_settings_deferred()
					elseif action == "wrap" then
						save_state_for_undo("Toggle text wrap")
						wrap_task_text = not wrap_task_text
						mark_cache_dirty()
						save_settings_deferred()
					end
					last_mouse_x = mouse_x
					last_mouse_y = mouse_y
					last_mouse_cap = mouse_cap
					request_immediate_update()
					return
				end
			end

			-- Right group: dock
			local right_x = gfx.w - tb_padding - tb_btn_w
			if mouse_x >= right_x and mouse_x <= right_x + tb_btn_w
				and mouse_y >= tb_btn_y and mouse_y <= tb_btn_y + tb_btn_h then
				toggle_dock()
				last_mouse_x = mouse_x
				last_mouse_y = mouse_y
				last_mouse_cap = mouse_cap
				request_immediate_update()
				return
			end
		end
	end

	-- Middle click for delete (edge-triggered, check BEFORE updating last_mouse_cap)
	if mouse_cap & 64 == 64 and last_mouse_cap & 64 == 0 then -- Middle mouse button press
		local click_info = get_item_at_position(mouse_x, mouse_y, display_list)
		if click_info then
			delete_task(click_info.item_id)
		end
		last_mouse_x = mouse_x
		last_mouse_y = mouse_y
		last_mouse_cap = mouse_cap
		return
	end

	last_mouse_x = mouse_x
	last_mouse_y = mouse_y
	last_mouse_cap = mouse_cap

	if mouse_cap & 1 == 1 then -- Left mouse down
		local task_area_top    = toolbar_position == "top" and toolbar_height or 0
		local task_area_bottom = toolbar_position == "top" and (gfx.h - input_height) or (gfx.h - input_height - toolbar_height)
		if not mouse_down_time or mouse_down_time == 0 then
			-- Start of mouse down
			mouse_down_time = current_time
			mouse_down_pos.x = mouse_x
			mouse_down_pos.y = mouse_y

			-- Ignore clicks outside the task area (toolbar or input bar)
			if mouse_y < task_area_top or mouse_y >= task_area_bottom then
				last_mouse_x = mouse_x
				last_mouse_y = mouse_y
				last_mouse_cap = mouse_cap
				return
			end

			local click_info = get_item_at_position(mouse_x, mouse_y, display_list)
			if click_info then
				mouse_down_item = click_info.item_id
				if not click_info.checkbox_clicked and not click_info.collapse_icon_clicked then
					selected_id = click_info.item_id
				end
			else
				mouse_down_item = nil
				selected_id = nil
			end
		else
			-- Mouse held down - check for drag conditions
			local hold_time = current_time - mouse_down_time
			local move_distance = math.sqrt((mouse_x - mouse_down_pos.x) ^ 2 + (mouse_y - mouse_down_pos.y) ^ 2)

			if
				not dragging
				and mouse_down_item
				and (hold_time > click_threshold_time or move_distance > move_threshold)
			then
				-- Start dragging
				dragging = true
				drag_item_id = mouse_down_item

				-- Calculate drag offset using actual accumulated heights
				local task_area_top = toolbar_position == "top" and toolbar_height or 0
				local accumulated_y = task_area_top + 10 - scroll_offset
				for _, display_item in ipairs(display_list) do
					if display_item.id == mouse_down_item then
						break
					end
					accumulated_y = accumulated_y + display_item.height
				end

				drag_offset_y = mouse_down_pos.y - accumulated_y
			end

			-- Update drop target while dragging
			if dragging then
				drop_target = get_drop_target(mouse_y, display_list)
			end
		end
	else -- Mouse up
		if mouse_down_time and mouse_down_time > 0 then
			local hold_time = current_time - mouse_down_time
			local move_distance = math.sqrt((mouse_x - mouse_down_pos.x) ^ 2 + (mouse_y - mouse_down_pos.y) ^ 2)

			if dragging and drop_target and drag_item_id then
				-- Perform the drop
				move_item(drag_item_id, drop_target.id, drop_target.position)
			elseif mouse_down_item and hold_time < click_threshold_time and move_distance < move_threshold then
				-- This was a click, not a drag
				local click_info = get_item_at_position(mouse_down_pos.x, mouse_down_pos.y, display_list)
				if click_info then
					if click_info.checkbox_clicked then
						toggle_task_done(click_info.item_id)
					elseif click_info.collapse_icon_clicked then
						toggle_collapse(click_info.item_id)
					else
						-- Check for double-click
						local time_since_last_click = current_time - last_click_time
						if last_click_item == click_info.item_id and time_since_last_click < double_click_threshold then
							-- Double-click detected
							toggle_collapse(click_info.item_id)
						end
						last_click_time = current_time
						last_click_item = click_info.item_id
					end
				end
			end

			-- Reset mouse state
			mouse_down_time = 0
			mouse_down_item = nil
		end

		-- Reset drag state
		dragging = false
		drag_item_id = nil
		drop_target = nil
	end

	-- Mouse wheel scrolling
	if gfx.mouse_wheel ~= 0 then
		local max_scroll = get_scroll_limits(display_list)
		-- Scroll by a fixed amount regardless of item height
		local scroll_amount = gfx.mouse_wheel > 0 and -30 or 30
		scroll_offset = math.max(0, math.min(scroll_offset + scroll_amount, max_scroll))
		gfx.mouse_wheel = 0
	end
end

function handle_keyboard()
	local char = gfx.getchar()

	-- Check if input changed
	local input_changed = false

	if char >= 32 and char <= 126 then
		-- All printable characters go to input
		input_text = input_text .. string.char(char)
		input_changed = true
	elseif char == 8 then
		-- Backspace
		input_text = input_text:sub(1, -2)
		input_changed = true
	elseif char == 13 then
		-- Enter - add regular task (sibling or new parent)
		if input_text ~= "" then
			add_task(input_text, false, false)
			input_text = ""
			input_changed = true
		end
	elseif char == 9 then
		local shift_held = gfx.mouse_cap & 8 == 8
		if shift_held then
			if input_text ~= "" then
				-- Shift+Tab with text - add task at parent level (outdent)
				add_task(input_text, false, true)
				input_text = ""
				input_changed = true
			elseif selected_id then
				-- Shift+Tab with no text - unindent selected task
				unindent_task(selected_id)
				input_changed = true
			end
		else
			if input_text ~= "" then
				-- Tab with text - add subtask (child)
				add_task(input_text, true, false)
				input_text = ""
				input_changed = true
			elseif selected_id then
				-- Tab with no text - indent selected task
				indent_task(selected_id)
				input_changed = true
			end
		end
	elseif char == 27 then -- Escape
		-- Clear input or cancel drag
		if input_text ~= "" then
			input_text = ""
			input_changed = true
		else
			dragging = false
			drag_item_id = nil
			drop_target = nil
			mouse_down_time = 0
			mouse_down_item = nil
		end
	end

	if input_changed then
		request_immediate_update()
	end

	return char
end

function main()
	local current_time = r.time_precise()

	-- Frame rate limiting - skip frame if too soon (unless forced)
	if target_fps > 0 and not force_next_frame then
		local elapsed = current_time - last_frame_time
		if elapsed < frame_time then
			-- Too early for next frame, defer and return
			r.defer(main)
			return
		end
	end

	-- Reset force flag
	force_next_frame = false
	last_frame_time = current_time

	-- Only reload project data if project changed
	if should_reload_project() then
		load_todo_data()
		needs_redraw = true
	end

	if not gui_open then
		gfx.init(window_name, window_w, window_h, default_dock_state)
		set_font()
		gui_open = true
		load_todo_data() -- Initial load
		needs_redraw = true
		last_frame_time = current_time -- Initialize frame timer
	end

	-- Check for deferred saves
	check_deferred_save()

	-- Blinking cursor needs periodic redraws
	if current_view == "tasks" then
		local blink_state = math.floor(r.time_precise() * 2) % 2
		if not last_blink_state or blink_state ~= last_blink_state then
			needs_redraw = true
			last_blink_state = blink_state
		end
	end

	-- Tooltip delay: keep redrawing while hovering and tooltip not yet visible
	if current_view == "tasks" and tooltip_current_btn and not tooltip_visible then
		needs_redraw = true
	end

	-- Handle input
	handle_mouse()
	local char = handle_keyboard()

	-- Only redraw if needed, but always call gfx.update() to keep window responsive
	if needs_redraw then
		draw_gui()
	end
	gfx.update()

	if char >= 0 then
		r.defer(main)
	else
		-- Save on exit
		if needs_save then
			save_todo_data()
			save_settings()
		end
		gui_open = false
	end
end

main()
 

--[[
@description reatask - reaper task manager
@version 1.1
@author captaincurrie
@date 2025 12 28
@about
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

-- Right-click menu
local menu_open = false
local menu_x = 0
local menu_y = 0
local menu_items = {}
local submenu_open = false

-- Undo system
local undo_stack = {}
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

-- GUI dimensions (base values at base_font_size)
local window_w = 300
local window_h = 400
local base_item_height = 24
local base_input_height = 24
local base_checkbox_size = 12
local base_indent = 20
local base_menu_width = 160
local base_menu_item_height = 20

-- Scaled dimensions (will be calculated)
local item_height = base_item_height
local input_height = base_input_height
local checkbox_size = base_checkbox_size
local indent_size = base_indent
local menu_width = base_menu_width
local menu_item_height = base_menu_item_height

-- Data file variables
local todolist_basename = "reatask"
local todolist_tasklist_suffix = ".tasks"
local todolist_settinglist_suffix = ".settings"
local unsaved_todolist_name = todolist_basename .. "-unsaved"

-- Window settings
local default_dock_state = 0 -- 0 = undocked (floating), 1 = docked

function get_project_identifier()
	local _, proj_file = r.EnumProjects(-1)
	local proj_path

	if not proj_file or proj_file == "" then
		-- Use Reaper's resource path for unsaved projects
		local resource_path = r.GetResourcePath()
		proj_path = resource_path .. "/" .. unsaved_todolist_name
	else
		-- Extract directory from the full project file path
		local proj_dir = proj_file:match("^(.*[/\\])")
		if not proj_dir then
			return nil
		end
		proj_path = proj_dir .. todolist_basename
	end

	return proj_path
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

function calculate_scale_factor()
	return font_size / base_font_size
end

function update_scaled_dimensions()
	local scale = calculate_scale_factor()

	-- Scale UI element sizes
	item_height = math.floor(base_item_height * scale + 0.5)
	input_height = math.floor(base_input_height * scale + 0.5)
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
end

function undo_last_action()
	if #undo_stack == 0 then
		return false -- Nothing to undo
	end

	local last_state = table.remove(undo_stack) -- Remove and get last state

	-- Preserve current selection if the task still exists
	local preserved_selection = nil
	if selected_id and last_state.todo_items[selected_id] then
		preserved_selection = selected_id
	end

	-- Restore the state
	todo_items = last_state.todo_items
	root_items = last_state.root_items
	next_id = last_state.next_id

	-- Apply preserved selection or fall back to saved selection
	selected_id = preserved_selection or last_state.selected_id

	mark_cache_dirty()
	mark_needs_save()

	return true, last_state.action
end

function load_settings()
	local proj_id = get_project_identifier()
	local settings_file = proj_id .. todolist_settinglist_suffix

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
					end
				end
			end
		end
	end

	set_font()
	mark_cache_dirty()
end

function save_settings()
	local proj_id = current_project_path
	if proj_id == "" then
		proj_id = get_project_identifier()
	end
	local settings_file = proj_id .. todolist_settinglist_suffix
	local file = io.open(settings_file, "w")
	if file then
		file:write(string.format("font_name:%s\n", font_name))
		file:write(string.format("font_size:%d\n", font_size))
		file:write(string.format("show_completed:%s\n", tostring(show_completed)))
		file:write(string.format("sort_mode:%s\n", sort_mode))
		file:write(string.format("target_fps:%d\n", target_fps))
		file:close()
	end
end

-- Internal version that marks for deferred save
function save_settings_deferred()
	mark_needs_save()
end

function load_todo_data()
	local proj_id = get_project_identifier()
	if proj_id ~= current_project_path then
		-- Save current project data before switching
		if current_project_path ~= "" then
			save_todo_data()
			save_settings()
		end

		current_project_path = proj_id
		local data_file = proj_id .. todolist_tasklist_suffix
		todo_items = {}
		root_items = {}
		next_id = 1
		undo_stack = {} -- Clear undo stack for new project
		mark_cache_dirty()

		if r.file_exists(data_file) then
			local file = io.open(data_file, "r")
			if file then
				local content = file:read("*all")
				file:close()

				-- First pass: create all items
				for line in content:gmatch("[^\r\n]+") do
					local id, parent_id, text, done, order, collapsed =
						line:match("^(%d+):([^:]*):([^:]*):(%w+):(%d+):([^:]*)")
					if id and parent_id and text and done and order then
						local item = {
							id = tonumber(id),
							parent_id = (parent_id == "" or parent_id == "0") and nil or tonumber(parent_id),
							text = text,
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
	local proj_id = current_project_path
	if proj_id == "" then
		proj_id = get_project_identifier()
	end
	local data_file = proj_id .. todolist_tasklist_suffix
	local file = io.open(data_file, "w")
	if file then
		for _, item in pairs(todo_items) do
			file:write(
				string.format(
					"%d:%s:%s:%s:%d:%s\n",
					item.id,
					item.parent_id and tostring(item.parent_id) or "",
					item.text,
					tostring(item.done),
					item.order,
					tostring(item.collapsed)
				)
			)
		end
		file:close()
	end
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

function get_display_list()
	if not cache_dirty and display_list_cache then
		return display_list_cache
	end

	display_list_cache = {}

	function add_item_recursive(item_id, level)
		local item = todo_items[item_id]
		if item then
			-- Skip completed tasks if they're hidden
			if not show_completed and item.done then
				return
			end

			table.insert(display_list_cache, {
				id = item_id,
				item = item,
				level = level,
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
	local available_height = gfx.h - input_height - 20 -- Account for margins and input bar
	local total_content_height = #display_list * item_height
	local max_scroll = math.max(0, total_content_height - available_height)
	return max_scroll
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

	function assign_order_recursive(item_id)
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
	function check_descendants(ancestor_id)
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
	local item_y = 10 - scroll_offset

	for i, display_item in ipairs(display_list) do
		local item_top = item_y
		local item_bottom = item_y + item_height

		if mouse_y >= item_top and mouse_y <= item_bottom then
			local relative_y = mouse_y - item_top
			local threshold = item_height * drop_zone_threshold

			if relative_y < threshold then
				return { id = display_item.id, position = "before", level = display_item.level }
			elseif relative_y > item_height - threshold then
				return { id = display_item.id, position = "after", level = display_item.level }
			else
				return { id = display_item.id, position = "child", level = display_item.level + 1 }
			end
		end

		item_y = item_y + item_height
	end

	return nil
end

function get_item_at_position(mouse_x, mouse_y, display_list)
	local item_y = 10 - scroll_offset

	for i, display_item in ipairs(display_list) do
		local item_top = item_y
		local item_bottom = item_y + item_height

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

		item_y = item_y + item_height
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

function show_context_menu(x, y)
	menu_open = true
	submenu_open = false
	menu_x = x
	menu_y = y

	menu_items = {
		{
			text = show_completed and "Hide Completed" or "Show Completed",
			action = function()
				-- Preserve selection when toggling completed visibility
				local preserved_selection = selected_id
				save_state_for_undo("Toggle show completed")
				show_completed = not show_completed
				mark_cache_dirty()

				-- Restore selection if the task still exists and is visible
				if preserved_selection and todo_items[preserved_selection] then
					if show_completed or not todo_items[preserved_selection].done then
						selected_id = preserved_selection
					end
				end

				save_settings_deferred()
				request_immediate_update()
			end,
		},
		{
			text = "Font Size +",
			action = function()
				font_size = math.min(font_size + font_size_increment, 48)
				set_font()
				mark_cache_dirty() -- Force recalculation of display list
				save_settings_deferred()
				request_immediate_update()
			end,
		},
		{
			text = "Font Size -",
			action = function()
				font_size = math.max(font_size - font_size_increment, 8)
				set_font()
				mark_cache_dirty() -- Force recalculation of display list
				save_settings_deferred()
				request_immediate_update()
			end,
		},
		{
			text = "Sort Custom",
			action = function()
				save_state_for_undo("Sort custom")
				sort_mode = "custom"
				mark_cache_dirty()
				save_settings_deferred()
			end,
		},
		{
			text = "Sort Alphabetical",
			action = function()
				save_state_for_undo("Sort alphabetical")
				sort_mode = "alphabetical"
				mark_cache_dirty()
				save_settings_deferred()
			end,
		},
		{
			text = is_docked() and "Undock" or "Dock", -- Dynamic text based on current state
			action = function()
				toggle_dock()
				request_immediate_update()
			end,
		},
		{
			text = "Quit",
			action = function()
				save_todo_data()
				save_settings()
				gfx.quit()
			end,
		},
		{
			text = #undo_stack > 0 and ("Undo: " .. undo_stack[#undo_stack].action) or "Nothing to Undo",
			action = function()
				if #undo_stack > 0 then
					undo_last_action()
					request_immediate_update()
				end
			end,
			enabled = #undo_stack > 0,
		},
		{
			text = "FPS: " .. target_fps,
			submenu = true,
		},
		{
			text = "  Set FPS: 15",
			action = function()
				target_fps = 15
				frame_time = 1.0 / target_fps
				save_settings_deferred()
				request_immediate_update()
			end,
			indent = true,
		},
		{
			text = "  Set FPS: 30",
			action = function()
				target_fps = 30
				frame_time = 1.0 / target_fps
				save_settings_deferred()
				request_immediate_update()
			end,
			indent = true,
		},
		{
			text = "  Set FPS: 60",
			action = function()
				target_fps = 60
				frame_time = 1.0 / target_fps
				save_settings_deferred()
				request_immediate_update()
			end,
			indent = true,
		},
		{
			text = "  Set FPS: Unlimited",
			action = function()
				target_fps = 0 -- 0 means unlimited
				frame_time = 0
				save_settings_deferred()
				request_immediate_update()
			end,
			indent = true,
		},
	}
end

function draw_menu()
	if not menu_open then
		return
	end

	local menu_height = #menu_items * menu_item_height

	-- Adjust menu position to stay on screen
	local adj_x = math.min(menu_x, gfx.w - menu_width)
	local adj_y = math.min(menu_y, gfx.h - menu_height)

	-- Draw menu background
	gfx.set(0.3, 0.3, 0.3, 1)
	gfx.rect(adj_x, adj_y, menu_width, menu_height)

	-- Draw menu border
	gfx.set(0.6, 0.6, 0.6, 1)
	gfx.rect(adj_x, adj_y, menu_width, 1)
	gfx.rect(adj_x, adj_y, 1, menu_height)
	gfx.rect(adj_x + menu_width - 1, adj_y, 1, menu_height)
	gfx.rect(adj_x, adj_y + menu_height - 1, menu_width, 1)

	-- Draw menu items
	for i, menu_item in ipairs(menu_items) do
		local item_y = adj_y + (i - 1) * menu_item_height
		local is_enabled = menu_item.enabled == nil or menu_item.enabled

		-- Check if mouse is over this item
		local mouse_over = gfx.mouse_x >= adj_x
			and gfx.mouse_x <= adj_x + menu_width
			and gfx.mouse_y >= item_y
			and gfx.mouse_y <= item_y + menu_item_height

		if mouse_over and is_enabled then
			gfx.set(0.4, 0.4, 0.5, 1)
			gfx.rect(adj_x, item_y, menu_width, menu_item_height)
		end

		-- Highlight current sorting mode
		local text_color = is_enabled and 0.9 or 0.5
		if
			(menu_item.text == "Sort Custom" and sort_mode == "custom")
			or (menu_item.text == "Sort Alphabetical" and sort_mode == "alphabetical")
		then
			text_color = 1.0
			gfx.set(0.2, 0.4, 0.2, 1)
			gfx.rect(adj_x + 2, item_y + 2, menu_width - 4, menu_item_height - 4)
		end

		gfx.set(text_color, text_color, text_color, 1)
		gfx.x = adj_x + 5
		gfx.y = item_y + menu_text_y_offset
		gfx.drawstr(menu_item.text)
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

		function delete_recursive(item_id)
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

function draw_gui()
	-- Clear background
	gfx.set(0.2, 0.2, 0.2, 1)
	gfx.rect(0, 0, gfx.w, gfx.h)

	needs_redraw = false -- Reset redraw flag

	local display_list = get_display_list()
	local y = 10 - scroll_offset

	-- Draw drop indicator
	if dragging and drop_target then
		local temp_y = 10 - scroll_offset

		for _, display_item in ipairs(display_list) do
			if display_item.id == drop_target.id then
				if drop_target.position == "before" or drop_target.position == "after" then
					-- Blue color for sibling operations
					gfx.set(0.2, 0.5, 1, 0.8)

					-- Calculate x position based on target depth (where the dragged task will be)
					local x_indent = 10 + (display_item.level * indent_size)

					-- Draw horizontal drop line
					local line_y = drop_target.position == "before" and (temp_y - 1) or (temp_y + item_height - 1)
					gfx.rect(x_indent, line_y, gfx.w - x_indent, 2)

					-- Draw vertical connecting line showing hierarchy
					if drop_target.position == "after" then
						-- Vertical line from top of task down to drop line
						gfx.rect(x_indent, temp_y, 2, item_height)
					else -- before
						-- Vertical line from drop line down through task
						gfx.rect(x_indent, line_y, 2, item_height)
					end
				else -- child
					-- Orange highlight for child operation
					gfx.set(1, 0.5, 0, 0.8)
					gfx.rect(
						10 + (display_item.level * indent_size),
						temp_y,
						gfx.w - 20 - (display_item.level * indent_size),
						item_height
					)
				end
				break
			end
			temp_y = temp_y + item_height
		end
	end

	-- Draw tasks
	for i, display_item in ipairs(display_list) do
		local item = display_item.item
		local level = display_item.level
		local x = 10 + (level * indent_size)

		-- Skip if outside visible area, or if it's the item being dragged
		if y > -item_height and y < gfx.h - input_height and display_item.id ~= drag_item_id then
			-- Selection highlight
			if display_item.id == selected_id then
				gfx.set(0.3, 0.3, 0.5, 1)
				gfx.rect(0, y, gfx.w, item_height)
			end

			-- Show drag preparation highlight
			if mouse_down_item == display_item.id and not dragging and mouse_down_time > 0 then
				local hold_time = r.time_precise() - mouse_down_time
				if hold_time > click_threshold_time then
					gfx.set(0.5, 0.3, 0.1, 0.3)
					gfx.rect(0, y, gfx.w, item_height)
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
			gfx.set(is_grayed and 0.5 or 0.9, is_grayed and 0.5 or 0.9, is_grayed and 0.5 or 0.9, 1)
			gfx.x = text_x
			gfx.y = y + task_text_y_offset
			gfx.drawstr(item.text)
		end

		y = y + item_height
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

	-- Input bar at bottom (always appears active)
	local input_y = gfx.h - input_height
	gfx.set(0.4, 0.4, 0.4, 1) -- Slightly brighter to show it's always active
	gfx.rect(0, input_y, gfx.w, input_height)

	gfx.set(0.9, 0.9, 0.9, 1)
	gfx.x = 5
	gfx.y = input_y + input_text_y_offset
	local display_text = input_text
	if math.floor(r.time_precise() * 2) % 2 == 0 then
		display_text = display_text .. "|"
	end
	gfx.drawstr("Add task: " .. display_text)

	-- Draw context menu last (on top)
	draw_menu()
end

function handle_mouse()
	local mouse_y = gfx.mouse_y
	local mouse_x = gfx.mouse_x
	local mouse_cap = gfx.mouse_cap
	local current_time = r.time_precise()

	-- Check if mouse state changed
	local mouse_moved = (mouse_x ~= last_mouse_x or mouse_y ~= last_mouse_y)
	local mouse_cap_changed = (mouse_cap ~= last_mouse_cap)

	if not mouse_moved and not mouse_cap_changed and not dragging and not menu_open then
		return -- Nothing to do
	end

	last_mouse_x = mouse_x
	last_mouse_y = mouse_y
	last_mouse_cap = mouse_cap
	request_immediate_update()

	local display_list = get_display_list()

	-- Handle right mouse button (simple logic)
	if mouse_cap & 2 == 2 then -- Right mouse button down
		-- Check if clicking on input bar
		local input_y = gfx.h - input_height
		if mouse_y >= input_y then
			-- Right-click on input bar - perform undo
			undo_last_action()
		else
			-- Right-click anywhere else - show context menu
			if not menu_open then
				show_context_menu(mouse_x, mouse_y)
			end
		end
		return
	end

	-- Handle menu clicks first
	if menu_open and mouse_cap & 1 == 1 then
		local menu_height = #menu_items * menu_item_height

		-- Adjust menu position to stay on screen
		local adj_x = math.min(menu_x, gfx.w - menu_width)
		local adj_y = math.min(menu_y, gfx.h - menu_height)

		-- Check if clicking on menu
		local clicking_menu = mouse_x >= adj_x
			and mouse_x <= adj_x + menu_width
			and mouse_y >= adj_y
			and mouse_y <= adj_y + menu_height

		if clicking_menu then
			-- Find which menu item was clicked
			for i, menu_item in ipairs(menu_items) do
				local item_y = adj_y + (i - 1) * menu_item_height
				local is_enabled = menu_item.enabled == nil or menu_item.enabled

				if mouse_y >= item_y and mouse_y <= item_y + menu_item_height and is_enabled then
					menu_item.action()
					menu_open = false
					return
				end
			end
		else
			-- Clicking outside menu, close it
			menu_open = false
			return
		end
	end

	-- Middle click for delete
	if mouse_cap & 64 == 64 then -- Middle mouse button
		local click_info = get_item_at_position(mouse_x, mouse_y, display_list)
		if click_info then
			delete_task(click_info.item_id)
		end
		return
	end

	if mouse_cap & 1 == 1 then -- Left mouse down
		if not mouse_down_time or mouse_down_time == 0 then
			-- Start of mouse down
			mouse_down_time = current_time
			mouse_down_pos.x = mouse_x
			mouse_down_pos.y = mouse_y

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

				-- Calculate drag offset
				local clicked_item_index = 0
				for i, display_item in ipairs(display_list) do
					if display_item.id == mouse_down_item then
						clicked_item_index = i
						break
					end
				end

				drag_offset_y = mouse_down_pos.y - (10 - scroll_offset + (clicked_item_index - 1) * item_height)
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
		local scroll_amount = gfx.mouse_wheel > 0 and -item_height or item_height
		scroll_offset = math.max(0, math.min(scroll_offset + scroll_amount, max_scroll))
		gfx.mouse_wheel = 0
	end
end

function is_window_focused()
	if is_docked() then
		-- If docked, check if mouse is over our window area
		-- This is a workaround since there's no direct focus detection for docked windows
		return gfx.mouse_x >= 0 and gfx.mouse_x <= gfx.w and gfx.mouse_y >= 0 and gfx.mouse_y <= gfx.h
	else
		-- If undocked, assume it has focus when it's the active window
		return true
	end
end

function handle_keyboard()
	-- Only handle keyboard input if window has focus
	if not is_window_focused() then
		return gfx.getchar() -- Still need to call getchar to prevent buildup, but don't process
	end

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
		-- Tab - add subtask (child)
		if input_text ~= "" then
			add_task(input_text, true, false)
			input_text = ""
			input_changed = true
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
		gfx.init(todolist_basename, window_w, window_h, 1)
		gfx.dock(default_dock_state)
		set_font()
		gui_open = true
		load_todo_data() -- Initial load
		needs_redraw = true
		last_frame_time = current_time -- Initialize frame timer
	end

	-- Check for deferred saves
	check_deferred_save()

	-- Handle input
	handle_mouse()
	local char = handle_keyboard()

	-- Only redraw if needed
	if needs_redraw then
		draw_gui()
		gfx.update()
	end

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

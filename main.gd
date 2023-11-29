extends Control
@export var cell_scene: PackedScene
@onready var play_grid : GridContainer = $HBoxContainer/GridContainer
var rows:=3
var cols:=3
var cell_list:=[]
# Called when the node enters the scene tree for the first time.
func _ready():
	IDP.initialize() # Replace with function body.
	
	initialize()
			


# Called every frame. 'delta' is the elapsed time since the previous frame.
func _process(delta):
	pass
	

func get_new_init_cells():
	var new_inits = []
	for r in range(rows):
		for c in range(cols):
			if cell_list[r][c].get_text() != "" and !cell_list[r][c].has_background():
				new_inits.append([r,c,int(cell_list[r][c].get_text())])
	return new_inits
	
func get_solution(inits):
	IDP.set_initaized_cells(inits)
	var answer = IDP.call_os()
	return answer

func expand_grid(solution,inits):
	if len(solution["models"]) == 0:
		print("no solution possible")
		for r in range(rows):
			for c in range(cols):
				if cell_list[r][c].has_background():
					cell_list[r][c].reset()
		$Label.visible = true
		$ColorRect.visible = true
		await get_tree().create_timer(3).timeout
		$Label.visible = false
		$ColorRect.visible = false
		return
	var model = solution["models"][randi()%len(solution["models"])]
	var cell_vals = model["cellValue"]
	
	for cel_val in cell_vals:
		var r = cel_val[0][0]
		var c = cel_val[0][1]
		var v = cel_val[1]
		if cell_list[r][c].get_text() == "" or cell_list[r][c].has_background(): #TODO: fix invalid index when one col
			cell_list[r][c].set_text(v)
			cell_list[r][c].set_background(true)
	
	
func _on_button_pressed():
	var new_inits = get_new_init_cells()
	var solution = get_solution(new_inits)
	expand_grid(solution,new_inits)

func initialize():
	var init_cells = IDP.get_initialized_cells()
	var dims = IDP.get_dims()
	rows = dims[0]
	cols = dims[1]
	update_show_col(cols,true)
	update_show_row(rows,true)
	play_grid.columns = cols
	for row in range(rows):
		var cell_col = []
		for col in range(cols):
			var cell = cell_scene.instantiate()
			play_grid.add_child(cell)
			cell_col.append(cell)
		cell_list.append(cell_col)
	for init_cell in init_cells:
		var r = init_cell[0]
		var c = init_cell[1]
		var v = init_cell[2]
		cell_list[r][c].set_text(v)
		
func _on_button_2_pressed():
	for r in range(rows):
		for c in range(cols):
			cell_list[r][c].queue_free()
	IDP.set_initaized_cells([])
	cell_list = []
	IDP.set_dims([get_slider_row(),get_slider_col()])
	initialize()
	
func get_slider_col():
	return int($HBoxContainer/VBoxContainer/Col_slider.value)
	
func get_slider_row():
	return int($HBoxContainer/VBoxContainer/Row_slider.value)
	
func update_show_col(val,manual=false):
	$HBoxContainer/VBoxContainer/ShowCol.text = "Num Columns: %d" % int(val) # Replace with function body.
	if manual:
		$HBoxContainer/VBoxContainer/Col_slider.value = val
	
func update_show_row(val,manual=false):
	$HBoxContainer/VBoxContainer/ShowRow.text = "Num Rows: %d" % int(val) # Replace with function body.
	if manual:
		$HBoxContainer/VBoxContainer/Row_slider.value = val
	
func _on_col_slider_value_changed(value):
	update_show_col(int(value))


func _on_row_slider_value_changed(value):
	update_show_row(int(value)) # Replace with function body.

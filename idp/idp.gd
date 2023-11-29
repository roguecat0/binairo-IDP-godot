extends Node

var out:= []
var err:= []
var file_mem:=[]
var struct_index: int
var row_index:int
var col_index:int
# Called when the node enters the scene tree for the first time.
func _ready():
	pass

func initialize():
	file_mem = _load("test-idp.idp").split("\n")

func save(path,content):
	var file = FileAccess.open(path, FileAccess.WRITE)
	file.store_string(content)

func _load(path):
	var file = FileAccess.open(path, FileAccess.READ)
	var content = file.get_as_text()
	return content

func change_structure():
	file_mem = _load("test-idp.idp").split("\n")
	var vals = get_initialized_cells()
	#vals.pop_back()
	set_initaized_cells(vals)
	
func get_dims():
	var row_line = ""
	var col_line = ""
	var vals = []
	for i in range(len(file_mem)):
		var line = file_mem[i]
		if "type Row := " in line:
			row_line = file_mem[i]
			row_index = i
		if "type Col := " in line:
			col_line = file_mem[i]
			col_index = i
	print(row_line,col_line)
	var regex = RegEx.new()
	regex.compile(":= {0..(\\d+)}")
	var result1 = regex.search(row_line)
	var result2 = regex.search(col_line)
	var dims = [int(result1.get_string(1))+1,int(result2.get_string(1))+1]
	return dims

func set_dims(dims=[3,4],do_save=true):
	var regex = RegEx.new()
	regex.compile(":= {0..(\\d+)}")
	file_mem[col_index] = regex.sub(file_mem[col_index],":= {0..%d}" % (dims[1]-1))
	file_mem[row_index] = regex.sub(file_mem[row_index],":= {0..%d}" % (dims[0]-1))
	if do_save:
		save("test-idp.idp","\n".join(file_mem))
	
func get_initialized_cells():
	var struct_line = ""
	var vals = []
	for i in range(len(file_mem)):
		var line = file_mem[i]
		if "structure" in line:
			struct_line = file_mem[i+1]
			struct_index = i+1
			break
	var hello = "(1,2)"
	var regex = RegEx.new()
	regex.compile("(((\\d+,\\s*)+\\d+))") #\(((\d+,\s)*\d+)\)  \\w-(\\d+)
	for result in regex.search_all(struct_line):
		vals.append(Array(result.get_string().split(",")).map(func(x): return int(x)))
	return vals

func set_initaized_cells(vals=[],do_save=true):
	var line = file_mem[struct_index]
	var new_index = line.find(":= ")+3
	var start = line.substr(0,new_index)
	var vals_str = vals.map(func(x): return str(x).replace("[","(").replace("]",")"))
	vals_str = "{"+", ".join(vals_str) + "}."
	file_mem[struct_index] = start + vals_str
	if do_save:
		save("test-idp.idp","\n".join(file_mem))
		
	
	
func call_os():
	OS.execute("./.venv/Scripts/python.exe",["test-py.py"],out)
	var testing = false
	var json_string = out[len(out)-1]
	var data_received = null
	# OS.execute(".\.venv\Scripts\idp-engine.exe",[".\test-idp.idp"],out)
	if testing:
		var json = JSON.new()
		var error = json.parse(json_string)
		if error == OK:
			data_received = json.data
			if typeof(data_received) == TYPE_ARRAY:
				print(data_received) # Prints array
			else:
				print(data_received)
		else:
			print("JSON Parse Error: ", json.get_error_message(), " in ", json_string, " at line ", json.get_error_line())
	else:
		data_received = JSON.parse_string(json_string)
	print(data_received)
	return data_received
# Called every frame. 'delta' is the elapsed time since the previous frame.
func _process(delta):
	pass

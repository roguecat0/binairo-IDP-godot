extends Control


# Called when the node enters the scene tree for the first time.
func _ready():
	pass # Replace with function body.


# Called every frame. 'delta' is the elapsed time since the previous frame.
func _process(delta):
	pass

func reset():
	set_background(false)
	set_text("")

func set_background(B: bool):
	$Background.visible = B
func has_background():
	return $Background.visible
func _on_button_pressed():
	if has_background():
		set_background(false)
		return
	if get_text() == '1':
		set_text('')
	elif get_text() == '0':
		set_text('1')
	else:
		set_text('0')
func set_text(t):
	$Button.text = str(t)
func get_text():
	return $Button.text

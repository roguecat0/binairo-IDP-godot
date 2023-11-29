from idp_engine import IDP, Theory
import json
import re

import re
import json

def convert_to_json(input_string):
    # Define a pattern to extract key-value pairs
    pattern = r'(\w+) := {(.*?)}'
    pattern2 = r'\(((\d+,\s)*\d+)\) -> (\d+)'
    
    result = []

    matches = re.findall(pattern, input_string)
    for key, value_str in matches:
        if value_str == "":
            tmp = f'"{key}":[]'
        elif "->" in value_str and "(" in value_str:
            matches2 = re.findall(pattern2, value_str)
            tmp = f'"{key}":{[[ [int(inp) for inp in inputs.split(",")],int(output)]for inputs,_,output in matches2]}'
            
        elif "(" in value_str:
            tmp = f'"{key}":[{value_str.replace("(","[").replace(")","]")}]'
        elif "->" in value_str:
            tmp = f'"{key}":[[[{value_str.replace(", ","], [[").replace(" ->","], ")}]]'
        result.append(tmp)
    result = "{"+",\n".join(result)+"}"
    json.loads(result)
    return result


def parse_to_json(models):
    out = {"satifiable":True,"error_message":"","models":[]}
    for model in models:
        if "models" in model:
            break
        else:
            tmp = convert_to_json(str(model))
            out["models"].append(json.loads(tmp))
    return json.dumps(out)
inp = """
cellValue := {(0, 0) -> 1, (0, 1) -> 0, (0, 2) -> 1}.
cellValue2 := {0 -> 1, 1 -> 0, 2 -> 1}.
initialValue := {(0, 0, 1), (0, 1, 0), (0, 2, 1)}.
horizontalEdge := {(0, 1, 0, 0), (0, 2, 0, 1)}.
verticalEdge := {}.
"""
out = """
{"cellValue":[[[0, 0], 1], [[0, 1], 0], [[0, 2], 1]],
"cellValue2":[[[0],  1], [[1],  0], [[2],  1]],
"initialValue":[[0, 0, 1], [0, 1, 0], [0, 2, 1]],
"horizontalEdge":[[0, 1, 0, 0], [0, 2, 0, 1]],
"verticalEdge":{}}
"""
kb = IDP.from_file("test-idp.idp")
T, S = kb.get_blocks("T, S")
theory = Theory(T, S)
models = theory.expand(max=1)
jsn = parse_to_json(models)
print(jsn)
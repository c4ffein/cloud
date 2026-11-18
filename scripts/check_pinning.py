#!/usr/bin/env python

"""Fail if cloud.py's make_pinned_ssl_context drifted from the canonical version in c4ffein/python-snippets"""

import ast
import urllib.request
from difflib import unified_diff
from pathlib import Path
from sys import exit

CANONICAL_URL = "https://raw.githubusercontent.com/c4ffein/python-snippets/main/src/pinned_ssl_context.py"
FUNCTION_NAME = "make_pinned_ssl_context"


def extract_function(source, origin):
    for node in ast.parse(source).body:
        if isinstance(node, ast.FunctionDef) and node.name == FUNCTION_NAME:
            return ast.get_source_segment(source, node)
    exit(f"{FUNCTION_NAME} not found in {origin}")


local_source = (Path(__file__).parent.parent / "cloud.py").read_text()
with urllib.request.urlopen(CANONICAL_URL) as response:
    canonical_source = response.read().decode("utf-8")
local_function = extract_function(local_source, "cloud.py")
canonical_function = extract_function(canonical_source, CANONICAL_URL)
if local_function != canonical_function:
    diff = unified_diff(
        canonical_function.splitlines(), local_function.splitlines(), "canonical", "cloud.py", lineterm=""
    )
    exit(f"{FUNCTION_NAME} drifted from the canonical version:\n" + "\n".join(diff))
print(f"{FUNCTION_NAME} matches the canonical version")

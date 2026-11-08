#!/usr/bin/env python3
"""Extract the constructor-reachable source pairs for a small Rocq checker.

The input is the compiler worker's already-exported CompilerData.v.  The
generated ConstructorData.v is only an untrusted lookup accelerator: Rocq
checks every selected pair against CompilerData.source_graph before using it.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent

def generate():
    text = (HERE / "CompilerData.v").read_text()
    table = text.split("Definition source_graph : list source_pair := [", 1)[1].split("].", 1)[0]
    atom = r"(?:\((?:SNode|SInc|SDec|SBreak|SContinue) \d+\)|SHalt)"
    row = re.compile(rf"^\s*\(({atom}), ({atom})\);?\s*$")
    graph = []
    for line in table.splitlines():
        if not line.strip():
            continue
        match = row.fullmatch(line)
        if not match:
            raise ValueError(f"unrecognized graph row {line!r}")
        graph.append(match.groups())

    roots = re.search(r"Definition source_token_roots : list \(nat \* nat\) := \[(.*?)\]\.", text).group(1)
    queue = [int(root) for _, root in re.findall(r"\((\d+),(\d+)\)", roots)]
    queue.extend(int(n) for n in re.findall(r"Definition source_(?:pushwff|cons)_root : nat := (\d+)\.", text))
    seen = set()
    while queue:
        n = queue.pop()
        if n in seen:
            continue
        seen.add(n)
        for child in graph[n]:
            match = re.fullmatch(r"\(SNode (\d+)\)", child)
            if match:
                queue.append(int(match.group(1)))

    lines = [
        "(* Generated subset of CompilerData.source_graph; verified by ConstructorGraph.v. *)",
        "From Stdlib Require Import Lists.List.",
        "From Berkeley Require Import CompilerSyntax.",
        "Import ListNotations.",
        "Definition constructor_nodes : list (nat * source_pair) := [",
        ";\n".join(f"  ({n}, ({graph[n][0]}, {graph[n][1]}))" for n in sorted(seen)),
        "].",
    ]
    output = HERE / "ConstructorData.v"
    output.write_text("\n".join(lines) + "\n")
    return {"nodes": len(seen), "sha256": hashlib.sha256(output.read_bytes()).hexdigest()}

if __name__ == "__main__":
    print(json.dumps(generate(), indent=2))

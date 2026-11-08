#!/usr/bin/env python3
"""Regenerate the committed finite witnesses; their correctness is checked in Rocq."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("Data.v", "CompilerData.v", "ConstructorData.v", "SyntaxData.v", "RuntimeProgramData.v")
with tempfile.TemporaryDirectory(prefix="berkeley1399-certificates-") as tmp:
    work = Path(tmp) / "construction"
    shutil.copytree(ROOT / "construction", work, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    shutil.copytree(ROOT / "machine", work / "repairs/guarded-distinction")
    folder = work / "rocq-repair"
    for generator in ("export_repair.py", "export_compiler.py", "export_constructors.py", "export_syntax.py", "export_runtime.py"):
        subprocess.run([sys.executable, str(folder / generator)], cwd=work, check=True)
    for name in NAMES:
        if (folder / name).read_bytes() != (ROOT / "coq/Repair" / name).read_bytes():
            raise SystemExit("CERTIFICATE MISMATCH: " + name)
        print("MATCH", name)
print("Finite witnesses reproduced. BootstrapReplay.v is a separate committed compressed trace, checked by the default Rocq build.")

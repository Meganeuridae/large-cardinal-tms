#!/usr/bin/env python3
"""Rebuild the machine in a temporary copy and compare frozen output bytes."""
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NAMES = ("machine.json", "machine.tm", "before-quotient.json", "certificate.json",
         "axioms.json", "axioms.sexpr", "berkeley-pure.sexpr", "state-labels.json",
         "before-quotient-labels.json")

with tempfile.TemporaryDirectory(prefix="berkeley1399-rebuild-") as tmp:
    work = Path(tmp) / "construction"
    shutil.copytree(ROOT / "construction", work, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    out = work / "output"
    subprocess.run([sys.executable, str(work / "repair_logic.py"), "--out", str(out)], check=True)
    for name in NAMES:
        actual = (out / name).read_bytes()
        expected = (ROOT / "machine" / name).read_bytes()
        if actual != expected:
            raise SystemExit("REBUILD MISMATCH: " + name)
        print("MATCH", name, hashlib.sha256(actual).hexdigest())
print("Machine and construction certificates reproduced byte for byte. This is not a proof check; use python3 verify.py.")

#!/usr/bin/env python3
"""Maintainer operation: explicitly rebaseline package inputs after reviewed edits.

Verification never calls this script. Refreshing hashes is not verification.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = [ROOT / name for name in ("verify.py", "toolchain.lock.json", "provenance.json")]
for directory in ("coq", "vendor", "machine", "construction", "pins", "tools", "tests"):
    paths += [p for p in (ROOT / directory).rglob("*") if p.is_file()
              and "__pycache__" not in p.parts and p.suffix not in (".pyc", ".log")]
manifest = {"format": 1, "machine": "Berkeley1399",
            "main_theorem": "Repair.TheoryTheorem.repaired_blank_halts_iff_ZF_Berkeley_inconsistent",
            "files": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(set(paths))}}
(ROOT / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(f"Rebaselined {len(manifest['files'])} files. Run python3 verify.py to verify this snapshot.")

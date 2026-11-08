"""Negative controls for the published verifier, using disposable package copies."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class RejectionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="berkeley-verifier-control-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "package"
        shutil.copytree(ROOT, self.root, ignore=shutil.ignore_patterns(".build", "_opam", "__pycache__", ".git", ".latex-build"))

    def write(self, name, text, repin=False):
        p = self.root / name
        p.write_text(text)
        if repin:
            manifest = json.loads((self.root / "manifest.json").read_text())
            manifest["files"][name] = hashlib.sha256(p.read_bytes()).hexdigest()
            (self.root / "manifest.json").write_text(json.dumps(manifest))

    def reject(self, message):
        result = subprocess.run([sys.executable, str(self.root / "verify.py"), "--sources-only"],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(message, result.stdout)

    def test_unpinned_edit(self):
        name = "machine/machine.tm"
        self.write(name, (self.root / name).read_text() + "\n")
        self.reject("Input hash mismatch")

    def test_rehashed_wrong_table(self):
        name = "machine/machine.tm"
        rows = (self.root / name).read_text().splitlines()
        fields = rows[2].split()
        fields[2] = str(1 - int(fields[2]))
        rows[2] = " ".join(fields)
        self.write(name, "\n".join(rows) + "\n", repin=True)
        self.reject(".tm and JSON tables differ")

    def test_rehashed_wrong_rocq_literal(self):
        name = "coq/Repair/Data.v"
        text = (self.root / name).read_text()
        start = text.index("Definition new_table : list row := [")
        prefix, body = text[:start], text[start:]
        body = body.replace("((true,", "((false,", 1)
        self.write(name, prefix + body, repin=True)
        self.reject("Rocq literal and JSON differ")

    def test_rehashed_axiom(self):
        name = "coq/Repair/TheoryTheorem.v"
        self.write(name, (self.root / name).read_text() + "\nAxiom injected : False.\n", repin=True)
        self.reject("Forbidden proof escape")

    def test_missing_endpoint_audit(self):
        name = "coq/Repair/TheoryTheorem.v"
        text = (self.root / name).read_text().replace(
            "Print Assumptions repaired_blank_halts_iff_ZF_Berkeley_inconsistent.", "")
        self.write(name, text, repin=True)
        self.reject("Missing final theorem assumption audit")


if __name__ == "__main__":
    unittest.main()

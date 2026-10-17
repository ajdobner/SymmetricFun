"""Negative regression checks for the project acceptance guard."""
import json
from pathlib import Path
import tempfile
import unittest

from check_project import validate


class ProjectGuardTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "docs").mkdir()
        (self.root / "SymmetricFunctions").mkdir()
        (self.root / "docs/tasks.json").write_text(json.dumps({"tasks": [
            {"id": "A", "status": "planned", "depends_on": []}
        ]}))
        (self.root / "SymmetricFunctions.lean").write_text("import SymmetricFunctions.Basic\n")
        self.basic = self.root / "SymmetricFunctions/Basic.lean"
        self.basic.write_text("theorem good : True := by trivial\n")

    def test_omitted_module(self):
        (self.root / "SymmetricFunctions/Omitted.lean").write_text("example : False := by trivial\n")
        with self.assertRaisesRegex(ValueError, "Root import does not cover"):
            validate(self.root)

    def test_hidden_hole_after_nested_comment(self):
        self.basic.write_text('/- outer /- nested -/ end -/\ntheorem bad : False := by sorry\n')
        with self.assertRaisesRegex(ValueError, "Forbidden proof token"):
            validate(self.root)

    def test_legacy_import(self):
        self.basic.write_text("import SymmetricPoly.SymmFunc.Basic\n")
        with self.assertRaisesRegex(ValueError, "inherited draft"):
            validate(self.root)

    def test_dependency_cycle(self):
        (self.root / "docs/tasks.json").write_text(json.dumps({"tasks": [
            {"id": "A", "status": "planned", "depends_on": ["B"]},
            {"id": "B", "status": "planned", "depends_on": ["A"]}
        ]}))
        with self.assertRaisesRegex(ValueError, "cycle"):
            validate(self.root)

    def test_upstream_unimported_module(self):
        (self.root / "SymmetricFun").mkdir()
        (self.root / "SymmetricFun.lean").write_text("-- Empty facade\n")
        (self.root / "SymmetricFun/Omitted.lean").write_text("theorem good : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "Root import does not cover"):
            validate(self.root)

    def test_upstream_proof_hole(self):
        (self.root / "SymmetricFun").mkdir()
        (self.root / "SymmetricFun.lean").write_text("public import SymmetricFun.Bad\n")
        (self.root / "SymmetricFun/Bad.lean").write_text("theorem bad : False := by sorry\n")
        with self.assertRaisesRegex(ValueError, "Forbidden proof token"):
            validate(self.root)

    def test_transitive_facade_coverage(self):
        (self.root / "SymmetricFunctions/Helper.lean").write_text("theorem helper : True := by trivial\n")
        self.basic.write_text("import SymmetricFunctions.Helper\n")
        self.assertEqual(len(validate(self.root)), 3)

    def test_comments_are_not_proof_holes(self):
        self.basic.write_text('/- A comment mentioning sorry. -/\ntheorem good : True := by trivial\n')
        self.assertEqual(len(validate(self.root)), 2)


if __name__ == "__main__":
    unittest.main()

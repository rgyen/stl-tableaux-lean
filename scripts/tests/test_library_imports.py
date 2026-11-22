"""Check the production import boundary and the Lean header reader."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_library_imports import check_imports, parse_imports


class LibraryImportsTests(unittest.TestCase):
    def test_root_and_unreferenced_module_cannot_import_tests(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            library = root / 'STLTableaux'
            library.mkdir()
            entry = root / 'STLTableaux.lean'
            leaf = library / 'Unreferenced.lean'
            for source in (entry, leaf):
                for dependency in ('STLTableauxTest', 'STLTableauxTest.Axioms.Claims'):
                    with self.subTest(source=source.name, dependency=dependency):
                        entry.write_text('import Mathlib\n')
                        leaf.write_text('import Mathlib\n')
                        source.write_text(f'public import\n  {dependency}\n')
                        with self.assertRaisesRegex(ValueError, 'imports test module'):
                            check_imports(root)

    def test_comments_strings_and_similar_names_are_allowed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'STLTableaux.lean').write_text(
                '/- outer /- import STLTableauxTest -/ -/\n'
                'import Mathlib STLTableauxTestTools.Helpers -- import STLTableauxTest\n'
                'def s := "import STLTableauxTest.Other"\n')
            self.assertEqual(check_imports(root), 1)

    def test_import_parser_keeps_the_whole_header(self):
        self.assertEqual(parse_imports(
            'public\n import /- note -/\n STLTableaux.A\n STLTableaux.B\nrun_elab do\n pure ()'),
            ['STLTableaux.A', 'STLTableaux.B'])
        for malformed in ('/- unterminated', 'def s := "unterminated'):
            with self.subTest(source=malformed), self.assertRaises(ValueError):
                parse_imports(malformed)

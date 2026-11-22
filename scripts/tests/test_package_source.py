"""A source release is deterministic and excludes machine-specific caches."""
import hashlib
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from package_source import ROOT_FILES, package


class SourcePackageTests(unittest.TestCase):
    def test_archive_identity_and_cache_exclusions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'source'
            root.mkdir()
            for name in ROOT_FILES:
                (root / name).write_text('fixture\n')
            for name in ['STLTableaux/Example.lean', 'docs/correspondence.md',
                         'STLTableauxTest/Interfaces/ExampleChecks.lean',
                         'docs/draft.txt', 'docs/history/old.md',
                         'scripts/example.py', '.lake/build/cache', '.git/config',
                         'scripts/__pycache__/example.pyc']:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('fixture\n')
            first = package(Path(directory) / 'first.tar.gz', root)
            second = package(Path(directory) / 'different-name.tar.gz', root)
            self.assertEqual(first['sha256'], second['sha256'])
            with tarfile.open(first['archive']) as archive:
                names = archive.getnames()
                for name in ['STLTableaux/Example.lean', 'docs/correspondence.md',
                             'STLTableauxTest/Interfaces/ExampleChecks.lean']:
                    self.assertIn('stl-tableaux-lean-source/' + name, names)
                self.assertNotIn('stl-tableaux-lean-source/docs/draft.txt', names)
                self.assertNotIn('stl-tableaux-lean-source/docs/history/old.md', names)
                self.assertFalse(any('/.lake/' in n or '/.git/' in n or
                                     '__pycache__' in n for n in names))
                manifest = json.load(archive.extractfile('stl-tableaux-lean-source/SOURCE-MANIFEST.json'))
                for name, digest in manifest['sha256'].items():
                    contents = archive.extractfile('stl-tableaux-lean-source/' + name).read()
                    self.assertEqual(hashlib.sha256(contents).hexdigest(), digest)


if __name__ == '__main__':
    unittest.main()

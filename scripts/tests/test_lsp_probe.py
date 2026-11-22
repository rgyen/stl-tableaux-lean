"""Regressions for complete diagnostics after a clean prefix."""
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts'))
from lean_lsp_probe import probe


@unittest.skipUnless(shutil.which('lake') or (Path.home() / '.elan/bin/lake').is_file(),
                     'Lean toolchain required')
class LspCompletionTests(unittest.TestCase):
    def test_final_diagnostic_can_follow_empty_file_progress(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'LateReport.lean'
            source.write_text('import Lean\n')
            document = {'uri': source.resolve().as_uri(), 'version': 1}
            replies = [{'id': ident, 'result': {}} for ident in range(1, 6)]
            early = {'method': 'textDocument/publishDiagnostics',
                     'params': {**document, 'diagnostics': []}}
            progress = {'method': '$/lean/fileProgress',
                        'params': {'textDocument': document, 'processing': []}}
            error = {'severity': 1, 'message': 'late diagnostic'}
            final = {'method': 'textDocument/publishDiagnostics',
                     'params': {**document, 'diagnostics': [error]}}
            messages = [replies[0], early, *replies[1:4], progress, final, replies[4]]
            wire = io.BytesIO()
            for message in messages:
                data = json.dumps({'jsonrpc': '2.0', **message}).encode()
                wire.write(f'Content-Length: {len(data)}\r\n\r\n'.encode() + data)
            wire.seek(0)
            with patch('lean_lsp_probe.subprocess.Popen') as popen:
                popen.return_value.stdout = wire
                popen.return_value.stdin = io.BytesIO()
                results = probe(source)
            self.assertEqual(results[-1]['diagnostics']['diagnostics'], [error])

    def test_late_error_is_reported_and_cli_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'LateError.lean'
            source.write_text('import Lean\n#eval IO.sleep 300\n'
                              '#check missing_example_identifier\n')
            result = subprocess.run(
                [sys.executable, str(ROOT / 'scripts/lean_lsp_probe.py'), str(source),
                 '--timeout', '30'], cwd=ROOT, capture_output=True, text=True, timeout=40)
            self.assertEqual(result.returncode, 1, result.stderr)
            snapshots = [json.loads(line) for line in result.stdout.splitlines()]
            final = snapshots[-1]
            self.assertTrue(final['document_complete'])
            self.assertTrue(final['processing_done'])
            self.assertTrue(any(d.get('severity') == 1 and
                                'missing_example_identifier' in d['message']
                                for d in final['diagnostics']['diagnostics']))

    def test_clean_document_reaches_reporting_completion(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'Clean.lean'
            source.write_text('import Lean\n#eval IO.sleep 100\n'
                              'theorem example_identity (n : Nat) : n = n := rfl\n')
            results = probe(source, line=1, timeout=30)
            self.assertIn({'request': 'documentSymbol', 'completed': True}, results)
            self.assertIn({'request': 'waitForDiagnostics', 'completed': True}, results)
            self.assertTrue(results[-1]['processing_done'])
            self.assertFalse(any(d.get('severity', 1) <= 2
                                 for d in results[-1]['diagnostics']['diagnostics']))


if __name__ == '__main__':
    unittest.main()

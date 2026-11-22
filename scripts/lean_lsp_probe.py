#!/usr/bin/env python3
"""Wait for a complete Lean LSP check; source positions are 1-based."""
import argparse
import json
import os
from pathlib import Path
import queue
import shutil
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[1]


def probe(file, line=1, column=1, timeout=90, lean_executable=None):
    """Wait for all command snapshots and diagnostic reporting, not just hover."""
    file = Path(file).resolve()
    source = file.read_text()
    lake = Path.home() / '.elan/bin/lake'
    if not lake.is_file():
        found = shutil.which('lake')
        if not found:
            raise RuntimeError('lake not found; install the pinned Lean toolchain')
        lake = Path(found)
    env = dict(os.environ)
    env['PATH'] = str(lake.parent) + os.pathsep + env.get('PATH', '')
    command = ([str(lean_executable), '--server'] if lean_executable else
               [str(lake), 'env', 'lean', '--server'])
    proc = subprocess.Popen(command, cwd=ROOT, env=env, stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    messages = queue.Queue()

    def read():
        try:
            while True:
                headers = {}
                while True:
                    raw = proc.stdout.readline()
                    if not raw:
                        return
                    if raw == b'\r\n':
                        break
                    key, value = raw.decode().split(':', 1)
                    headers[key.lower()] = value.strip()
                messages.put(json.loads(proc.stdout.read(int(headers['content-length']))))
        except (ValueError, KeyError) as exc:
            messages.put(exc)
        finally:
            messages.put(None)

    threading.Thread(target=read, daemon=True).start()

    def write(data):
        body = json.dumps(data).encode()
        proc.stdin.write(f'Content-Length: {len(body)}\r\n\r\n'.encode() + body)
        proc.stdin.flush()

    def send(method, params, ident=None):
        data = {'jsonrpc': '2.0', 'method': method, 'params': params}
        if ident is not None:
            data['id'] = ident
        write(data)

    deadline = time.monotonic() + timeout

    def receive():
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise TimeoutError(f'Lean LSP timed out after {timeout}s')
        try:
            msg = messages.get(timeout=remaining)
        except queue.Empty as exc:
            raise TimeoutError(f'Lean LSP timed out after {timeout}s') from exc
        if msg is None:
            raise RuntimeError('Lean LSP exited before completing the document')
        if isinstance(msg, Exception):
            raise RuntimeError(f'Invalid Lean LSP message: {msg}')
        if 'method' in msg and 'id' in msg:
            write({'jsonrpc': '2.0', 'id': msg['id'], 'result': None})
        return msg

    try:
        send('initialize', {'processId': os.getpid(), 'rootUri': ROOT.as_uri(),
                            'capabilities': {}}, 1)
        while True:
            msg = receive()
            if 'method' not in msg and msg.get('id') == 1:
                if 'error' in msg:
                    raise RuntimeError(msg['error'])
                break
        send('initialized', {})
        uri = file.as_uri()
        send('textDocument/didOpen', {'textDocument': {'uri': uri,
             'languageId': 'lean4', 'version': 1, 'text': source}})
        pos = {'textDocument': {'uri': uri},
               'position': {'line': line - 1, 'character': column - 1}}
        send('textDocument/hover', pos, 2)
        send('$/lean/plainGoal', pos, 3)
        # Lean 4's documentSymbol handler waits for all command snapshots.
        send('textDocument/documentSymbol', {'textDocument': {'uri': uri}}, 4)
        # File progress can become empty before the reporter publishes diagnostics.
        send('textDocument/waitForDiagnostics', {'uri': uri, 'version': 1}, 5)
        pending = {2: 'hover', 3: 'plainGoal', 4: 'documentSymbol', 5: 'waitForDiagnostics'}
        responses = []
        latest_diagnostics = None
        processing_done = False
        while pending or latest_diagnostics is None or not processing_done:
            msg = receive()
            params = msg.get('params', {})
            if msg.get('method') == 'textDocument/publishDiagnostics':
                if params.get('uri') == uri and params.get('version', 1) == 1:
                    # No incremental diagnostic capability was advertised.
                    latest_diagnostics = params
            if msg.get('method') == '$/lean/fileProgress':
                doc = params.get('textDocument', {})
                if doc.get('uri') == uri and doc.get('version', 1) == 1:
                    processing_done = params.get('processing') == []
                    if any(item.get('kind') == 2 for item in params.get('processing', [])):
                        raise RuntimeError('Lean LSP reported a fatal processing error')
            if 'method' not in msg and msg.get('id') in pending:
                name = pending.pop(msg['id'])
                if 'error' in msg:
                    raise RuntimeError(f'{name} failed: {msg["error"]}')
                if name in ('documentSymbol', 'waitForDiagnostics'):
                    responses.append({'request': name, 'completed': True})
                else:
                    responses.append({'request': name, 'response': msg})
        responses.append({'document_complete': True, 'processing_done': True,
                          'diagnostics': latest_diagnostics})
        return responses
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()
        proc.stdin.close()
        proc.stdout.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file', type=Path)
    parser.add_argument('--line', type=int, default=1)
    parser.add_argument('--column', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=90)
    parser.add_argument('--lean-executable', type=Path,
                        help='Use this Lean executable for the language server')
    parser.add_argument('--warnings-as-errors', action='store_true')
    args = parser.parse_args(argv)
    if args.line < 1 or args.column < 1 or args.timeout <= 0:
        parser.error('line, column, and timeout must be positive')
    try:
        results = probe(args.file, args.line, args.column, args.timeout,
                        lean_executable=args.lean_executable)
    except (OSError, RuntimeError, TimeoutError) as exc:
        parser.exit(1, f'LSP check failed: {exc}\n')
    for result in results:
        print(json.dumps(result, ensure_ascii=False))
    threshold = 2 if args.warnings_as_errors else 1
    return int(any(d.get('severity', 1) <= threshold
                   for d in results[-1]['diagnostics']['diagnostics']))


if __name__ == '__main__':
    sys.exit(main())

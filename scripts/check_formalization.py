#!/usr/bin/env python3
"""Check the Lean formalization locally or in CI and save a log for each step."""
import argparse
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
GATES = ['STLTableauxTest/Axioms/Claims.lean', 'STLTableauxTest/Interfaces/Rules.lean',
         'STLTableauxTest/Interfaces/Tableau.lean', 'STLTableauxTest/Axioms/ClosureProofDependencies.lean',
         'STLTableauxTest/Axioms/Correspondence.lean', 'STLTableauxTest/Axioms/Examples.lean',
         'STLTableauxTest/Axioms/Library.lean', 'STLTableauxTest/Interfaces/FiniteInventory.lean']


def log_diagnostics(text):
    """Count final LSP diagnostics as well as ordinary compiler warning lines."""
    counts = {'warnings': sum(line.startswith('warning:') for line in text.splitlines())}
    for line in text.splitlines():
        try:
            item = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(item, dict) and item.get('document_complete'):
            diagnostics = item['diagnostics']['diagnostics']
            counts.update(document_complete=True,
                          errors=sum(d.get('severity', 1) == 1 for d in diagnostics),
                          warnings=sum(d.get('severity') == 2 for d in diagnostics))
    return counts


def failure_excerpt(text):
    """Show the first error and the end of a failed step's log."""
    lines = text.splitlines()
    tail_start = max(0, len(lines) - 25)
    first_error = next((i for i, line in enumerate(lines[:tail_start])
                        if line.startswith(('error:', 'fatal:'))), None)
    if first_error is None:
        return '\n'.join(lines[tail_start:])
    start = max(0, first_error - 2)
    end = min(tail_start, first_error + 11)
    return '\n'.join(lines[start:end] + ['...'] + lines[tail_start:])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--smoke', action='store_true', help='Build the Lean library and check its recorded results (default)')
    group.add_argument('--full', action='store_true', help='Build all library modules and run all regression gates')
    parser.add_argument('--lsp', action='store_true', help='Also wait for complete diagnostics on three public modules')
    parser.add_argument('--log-dir', type=Path)
    args = parser.parse_args(argv)
    mode = 'full' if args.full else 'smoke'
    log_dir = (args.log_dir or ROOT / '.formalization-build/validation' / mode).resolve()
    log_dir.mkdir(parents=True, exist_ok=True)
    lake = shutil.which('lake')
    if lake is None:
        fallback = Path.home() / '.elan/bin/lake'
        if not fallback.is_file():
            parser.exit(1, 'lake not found; follow README.md installation instructions.\n')
        lake = str(fallback)
    env = dict(os.environ)
    env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    summary = {'mode': mode, 'platform': platform.platform(), 'python': platform.python_version(),
               'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
               'steps': [], 'passed': False}
    started = time.monotonic()

    def run(name, command):
        index = len(summary['steps']) + 1
        log = log_dir / f'{index:03d}-{name}.log'
        print(f'[{index}] {name} ...', flush=True)
        begin = time.monotonic()
        with log.open('w') as output:
            proc = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                  stderr=subprocess.STDOUT)
        text = log.read_text(errors='replace')
        row = {'name': name, 'exit_code': proc.returncode,
               'seconds': round(time.monotonic() - begin, 2), 'log': str(log),
               **log_diagnostics(text)}
        summary['steps'].append(row)
        print(f'    {"PASS" if proc.returncode == 0 else "FAIL"} ({row["seconds"]}s; {log.name})', flush=True)
        if proc.returncode:
            print(failure_excerpt(text), file=sys.stderr)
            raise RuntimeError(f'{name} failed; see {log}')

    try:
        run('library-imports', [sys.executable, str(ROOT / 'scripts/check_library_imports.py')])
        targets = ['STLTableaux', 'STLTableauxTest'] if args.full else ['STLTableaux']
        run('lean-build', [lake, 'build', *targets])
        for gate in GATES if args.full else GATES[:1]:
            run(Path(gate).stem, [lake, 'env', 'lean', '-DwarningAsError=true', gate])
        tests = (sorted((ROOT / 'STLTableauxTest/Regression').glob('*.lean')) if args.full
                 else [ROOT / 'STLTableauxTest/Regression/LibraryImportChecks.lean'])
        if args.full:
            tests += sorted((ROOT / 'STLTableauxTest/Audit').glob('*.lean'))
        for path in tests:
            # Supplemental checks retain their diagnostic output.
            options = [] if path.parent.name == 'Audit' else ['-DwarningAsError=true']
            run(path.stem, [lake, 'env', 'lean', *options, str(path)])
        run('python-regressions', [sys.executable, '-m', 'unittest', 'discover', '-s', 'scripts/tests', '-v'])
        if args.lsp:
            for name in ['STLTableaux.lean', 'STLTableaux/Closure/Expansion/BranchwiseRank.lean',
                         'STLTableaux/ModelChecking/Reduction/CanonicalModelChecking.lean']:
                run('lsp-' + Path(name).stem,
                    [sys.executable, str(ROOT / 'scripts/lean_lsp_probe.py'),
                     str(ROOT / name), '--timeout', '180'])
        summary['passed'] = True
    except (RuntimeError, OSError) as exc:
        print(str(exc), file=sys.stderr)
    finally:
        summary['seconds'] = round(time.monotonic() - started, 2)
        output = log_dir / 'summary.json'
        output.write_text(json.dumps(summary, indent=2) + '\n')
        print(f'{mode}: {"PASS" if summary["passed"] else "FAIL"}; summary: {output}', flush=True)
    return 0 if summary['passed'] else 1


if __name__ == '__main__':
    sys.exit(main())

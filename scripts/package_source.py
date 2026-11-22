#!/usr/bin/env python3
"""Create a deterministic source archive with proofs, tests, and documentation.

Build products, dependency downloads, Git internals and evaluation logs are not
included. SOURCE-MANIFEST.json records the exact packaged file bytes.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[1]
DIRECTORIES = ['STLTableaux', 'STLTableauxTest', 'scripts', '.github']
ROOT_FILES = ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain', '.gitignore',
              'README.md', 'LICENSE', 'STLTableaux.lean']


def source_files(root=ROOT):
    paths = {root / name for name in ROOT_FILES}
    for name in DIRECTORIES:
        paths.update((root / name).rglob('*'))
    paths.update((root / 'docs').glob('*.md'))
    result = []
    for path in sorted(paths):
        if not path.is_file() or any(part == '__pycache__' for part in path.parts):
            continue
        if path.suffix in {'.pyc', '.pyo'} or path.name == '.DS_Store':
            continue
        if path.is_symlink():
            raise ValueError(f'Source archive does not accept symlinks: {path}')
        result.append(path)
    return result


def package(output, root=ROOT):
    files = source_files(root)
    contents = {p.relative_to(root).as_posix(): p.read_bytes() for p in files}
    try:
        commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root,
                                         stderr=subprocess.DEVNULL, text=True).strip()
    except (OSError, subprocess.CalledProcessError):
        commit = None
    manifest = {'format': 1, 'base_commit': commit,
                'identity': 'The SHA-256 file list identifies the packaged working tree.',
                'toolchain': (root / 'lean-toolchain').read_text().strip(),
                'sha256': {name: hashlib.sha256(data).hexdigest()
                           for name, data in contents.items()}}
    contents['SOURCE-MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    output = output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open('wb') as raw, gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as zipped:
        with tarfile.open(fileobj=zipped, mode='w') as archive:
            for name, data in sorted(contents.items()):
                info = tarfile.TarInfo('stl-tableaux-lean-source/' + name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    output.with_name(output.name + '.sha256').write_text(f'{digest}  {output.name}\n')
    return {'archive': str(output), 'sha256': digest, 'source_files': len(files),
            'bytes': output.stat().st_size}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / '.formalization-build/stl-tableaux-lean-source.tar.gz')
    args = parser.parse_args()
    print(json.dumps(package(args.output), indent=2))


if __name__ == '__main__':
    main()

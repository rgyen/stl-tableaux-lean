#!/usr/bin/env python3
"""Check the production library for imports of test modules."""
import re
from pathlib import Path


def parse_imports(text):
    """Remove nested Lean comments and strings before reading import commands."""
    out = []
    index, depth, string = 0, 0, False
    while index < len(text):
        pair = text[index:index + 2]
        char = text[index]
        if depth:
            if pair == '/-':
                depth += 1
                index += 2
            elif pair == '-/':
                depth -= 1
                index += 2
            else:
                out.append('\n' if char == '\n' else ' ')
                index += 1
        elif string:
            if char == '\\':
                index += 2
            else:
                if char == '"':
                    string = False
                out.append('\n' if char == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            out.append(' ')
            index += 2
        elif pair == '--':
            end = text.find('\n', index)
            index = len(text) if end < 0 else end
        elif char == '"':
            string = True
            out.append(' ')
            index += 1
        else:
            out.append(char)
            index += 1
    if depth or string:
        raise ValueError('Unterminated Lean comment or string')
    cleaned = ''.join(out)
    # Lean whitespace includes newlines: imports are not line-based commands.
    # Parse the entire restricted header, then reject misplaced imports. Any
    # unsupported module spelling/modifier fails rather than hiding a dependency.
    tokens = re.findall(r'\S+', cleaned)
    imports, cursor = [], 0
    body_starts = {
        'open', 'namespace', 'section', 'end', 'universe', 'universes',
        'variable', 'variables', 'def', 'abbrev', 'theorem', 'lemma',
        'example', 'instance', 'class', 'structure', 'inductive', 'axiom',
        'constant', 'constants', 'opaque', 'noncomputable', 'private',
        'protected', 'unsafe', 'partial', 'mutual', 'attribute', 'set_option',
        'local', 'scoped', 'notation', 'infix', 'infixl', 'infixr', 'prefix',
        'postfix', 'syntax', 'macro', 'macro_rules', 'elab', 'elab_rules',
        'initialize', 'builtin_initialize', 'export', 'deriving', 'run_elab', 'run_cmd',
    }
    module_pattern = r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*'
    if tokens and tokens[0] == 'prelude':
        cursor += 1
    while cursor < len(tokens):
        token = tokens[cursor]
        if token in body_starts or token.startswith(('@[', '#')):
            break
        if token == 'public':
            cursor += 1
            if cursor == len(tokens) or tokens[cursor] != 'import':
                raise ValueError('Unsupported public header command')
        elif token != 'import':
            raise ValueError(f'Unsupported Lean header syntax: {token}')
        cursor += 1
        count = 0
        while cursor < len(tokens):
            token = tokens[cursor]
            if (token in body_starts or token in {'import', 'public', 'prelude'}
                    or token.startswith(('@[', '#'))):
                break
            if not re.fullmatch(module_pattern, token):
                raise ValueError(f'Unsupported import syntax: {token}')
            imports.append(token)
            count += 1
            cursor += 1
        if not count:
            raise ValueError('Import command requires at least one module')
    if any(token == 'import' for token in tokens[cursor:]):
        raise ValueError('Import outside the supported Lean header')
    return imports


def check_imports(root):
    sources = [root / 'STLTableaux.lean', *sorted((root / 'STLTableaux').rglob('*.lean'))]
    for source in sources:
        for dependency in parse_imports(source.read_text()):
            if dependency == 'STLTableauxTest' or dependency.startswith('STLTableauxTest.'):
                raise ValueError(f'{source.relative_to(root)} imports test module {dependency}')
    return len(sources)


if __name__ == '__main__':
    try:
        count = check_imports(Path(__file__).resolve().parents[1])
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
    print(f'Checked imports in {count} production modules.')

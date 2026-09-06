#!/usr/bin/env python3
"""Package preflight; actual proof dependencies are checked by Audit.lean.

This is an accidental-regression guard, not a hostile-submission sandbox.
Requires Python 3.11+; uses only the standard library.
"""

import argparse
import json
from pathlib import Path
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def code_only(source):
    """Remove nested Lean comments and ordinary strings for token checks."""
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            result.append(' ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            result.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            result.append(' ')
            i += 1
            while i < len(source):
                char = source[i]
                i += 1
                if char == '\\':
                    i += 1
                elif char == '"':
                    break
        else:
            result.append(source[i])
            i += 1
    require(depth == 0, 'Unclosed block comment')
    return ''.join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse', type=Path, help='validate an existing dependency installation')
    args = parser.parse_args()
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    require(not (ROOT / 'lakefile.lean').exists(), 'Keep exactly one Lakefile')
    require(manifest['name'] == config['name'], 'Package names differ')
    packages = manifest['packages']
    for package in packages:
        require(package['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                f"Unpinned dependency: {package['name']}")
        require(re.fullmatch(r'https://github\.com/[\w.-]+/[\w.-]+', package['url']),
                f"Nonportable dependency URL: {package['name']}")
        require(package['subDir'] is None, 'Unexpected dependency subdirectory')
    direct = [p for p in packages if not p['inherited']]
    require(len(direct) == 1 and len(config['require']) == 1, 'Unexpected direct dependencies')
    for field in ['name', 'rev']:
        require(config['require'][0][field] == direct[0][field], f'Mathlib {field} mismatch')
    require(config['require'][0]['git'] == direct[0]['url'], 'Mathlib URL mismatch')
    require(direct[0]['inputRev'] == direct[0]['rev'], 'Mathlib input revision is not exact')

    files = {p.stem: p for p in (ROOT / 'lean').glob('*.lean')}
    require(len(config['lean_lib']) == 1, 'Unexpected proof libraries')
    roots = config['lean_lib'][0]['roots']
    require(len(roots) == len(set(roots)) and set(roots) == set(files), 'Lake roots omit/duplicate sources')
    imports = re.findall(r'^import (\w+)$', files['CurveSymmetry'].read_text(), re.M)
    require(len(imports) == len(set(imports)) and set(imports) == set(files) - {'CurveSymmetry'},
            'Aggregate imports omit/duplicate sources')
    seen = set()
    for module in imports:
        source = code_only(files[module].read_text())
        for dep in re.findall(r'^import (\w+)$', source, re.M):
            require(dep not in files or dep in seen, f'Local build order fails: {module} imports {dep}')
        seen.add(module)
        require(not re.search(r'\b(sorry|admit|axiom|native_decide|sorryAx)\b', source),
                f'Forbidden proof token in {module}')
        require(source.count('namespace CurveSymmetry') == 1 and
                source.count('end CurveSymmetry') == 1, f'Axiom-audit scope changed: {module}')
        before, body = source.split('namespace CurveSymmetry')
        _, after = body.split('end CurveSymmetry')
        declaration = r'\b(def|lemma|theorem|instance|opaque|abbrev|inductive|structure)\b'
        require(not re.search(declaration, before + after), f'Declaration outside audit scope: {module}')
        require('namespace ' not in body, f'Unexpected namespace command: {module}')

    if args.reuse:
        require(args.reuse.is_absolute(), 'Reuse path must be absolute')
        require((args.reuse / 'lean-toolchain').read_text().strip() ==
                (ROOT / 'lean-toolchain').read_text().strip(), 'Reused Lean toolchain differs from pin')
        for package in packages:
            checkout = args.reuse / '.lake/packages' / package['name']
            actual = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'], text=True).strip()
            require(actual == package['rev'], f"Reused dependency revision differs: {package['name']}")
    print(f'Package preflight passed: {len(files)} modules, {len(packages)} exact dependency revisions')


if __name__ == '__main__':
    main()

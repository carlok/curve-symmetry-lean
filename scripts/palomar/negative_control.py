#!/usr/bin/env python3
"""Disposable negative controls for the Theorem 1 entry (Sprint 6 gate).

Run from palomar/theorem1 in a throwaway CI checkout; nothing is committed.

  negative_control.py mutate CONTROL   edit the checkout so that exactly one
                                       pre-check must fail
  negative_control.py expect CONTROL   run that pre-check; succeed only if it
                                       fails for the intended reason

Controls: theorem-type (the Challenge states a different theorem),
forbidden-axiom (the Solution proves a compared theorem from a new axiom),
forbidden-import (the Challenge imports the proof library). Each mutation
keeps the project compiling, so the failure comes from the checker, not from
a broken build. These are pre-checks, not the Palomar Comparator.
"""
import pathlib
import subprocess
import sys

CONTROLS = ('theorem-type', 'forbidden-axiom', 'forbidden-import')


def replace_once(path, old, new):
    p = pathlib.Path(path)
    text = p.read_text(encoding='utf-8')
    if text.count(old) != 1:
        sys.exit(f'{path}: expected exactly one occurrence of {old!r}')
    p.write_text(text.replace(old, new), encoding='utf-8')


def mutate(control):
    if control == 'theorem-type':
        # `sharp_bounds` in the Challenge now bounds the full group by 3d, not 2d.
        replace_once('Challenge.lean', 'ncard ≤ 2 * f.totalDegree := by',
                     'ncard ≤ 3 * f.totalDegree := by')
    elif control == 'forbidden-axiom':
        # `full_bound_sharp` keeps its statement but is proved from a new axiom.
        replace_once('Solution.lean', '\ntheorem full_bound_sharp',
                     '\naxiom forbiddenAxiom {p : Prop} : p\n\ntheorem full_bound_sharp')
        replace_once('Solution.lean',
                     'exact ⟨f, hf, hfd, hinf, (not_circle_iff f).mpr hnc, '
                     '(ncard_symmetries _).trans hc⟩',
                     'exact forbiddenAxiom')
    elif control == 'forbidden-import':
        # The Challenge would see the proof library.
        replace_once('Challenge.lean', 'import Mathlib\n', 'import Mathlib\nimport PaperBounds\n')
    print(f'mutated for control {control}')


def run(cmd):
    result = subprocess.run(cmd, capture_output=True, text=True)
    return result.returncode, result.stdout, result.stderr


def expect(control):
    if control == 'theorem-type':
        dumps = []
        for module in ('Challenge', 'Solution'):
            code, out, err = run(['lake', 'env', 'sh', '../../scripts/palomar/dump_decls.sh', module])
            if code != 0:
                sys.exit(f'dumping {module} failed, so this control tests nothing:\n{out}{err}')
            dumps.append(out)
        failed = dumps[0] != dumps[1]
        evidence = '\n'.join(sorted(set(dumps[0].splitlines()) ^ set(dumps[1].splitlines())))
    elif control == 'forbidden-axiom':
        code, out, err = run(['lake', 'env', 'lean', '../../scripts/palomar/CheckSolutionAxioms.lean'])
        evidence = out + err
        failed = code != 0 and 'Forbidden axiom' in evidence
    else:
        code, out, err = run(['sh', '../../scripts/palomar/check_challenge_imports.sh', 'Challenge.lean'])
        evidence = out + err
        failed = code != 0 and 'Forbidden Challenge import' in evidence
    if not failed:
        sys.exit(f'negative control {control} did NOT fail as required:\n{evidence}')
    print(f'negative control {control} failed as required:\n{evidence[:4000]}')


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ('mutate', 'expect') or sys.argv[2] not in CONTROLS:
        sys.exit(f'usage: negative_control.py mutate|expect {"|".join(CONTROLS)}')
    (mutate if sys.argv[1] == 'mutate' else expect)(sys.argv[2])


if __name__ == '__main__':
    main()

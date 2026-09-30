"""Checks that the Theorem 1 negative controls still apply to the entry files.

The controls themselves run in the palomar-negative-controls workflow; this only
guards their text anchors and the import pre-check, without building Lean.
"""

import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
ENTRY = ROOT / 'palomar' / 'theorem1'
CONTROL = ROOT / 'scripts' / 'palomar' / 'negative_control.py'
IMPORTS = ROOT / 'scripts' / 'palomar' / 'check_challenge_imports.sh'


def mutated_copy(control):
    work = pathlib.Path(tempfile.mkdtemp())
    for name in ('Challenge.lean', 'Solution.lean'):
        shutil.copy(ENTRY / name, work / name)
    subprocess.run([sys.executable, str(CONTROL), 'mutate', control], cwd=work,
                   check=True, capture_output=True)
    return work


def import_check(directory):
    return subprocess.run(['sh', str(IMPORTS), 'Challenge.lean'], cwd=directory,
                          capture_output=True, text=True)


class NegativeControlTests(unittest.TestCase):
    def test_real_challenge_imports_only_mathlib(self):
        self.assertEqual(import_check(ENTRY).returncode, 0)

    def test_forbidden_import_is_rejected(self):
        result = import_check(mutated_copy('forbidden-import'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Forbidden Challenge import', result.stderr)

    def test_theorem_type_mutation_applies(self):
        text = (mutated_copy('theorem-type') / 'Challenge.lean').read_text(encoding='utf-8')
        self.assertIn('ncard ≤ 3 * f.totalDegree := by', text)

    def test_forbidden_axiom_mutation_applies(self):
        text = (mutated_copy('forbidden-axiom') / 'Solution.lean').read_text(encoding='utf-8')
        self.assertIn('axiom forbiddenAxiom {p : Prop} : p', text)
        self.assertIn('exact forbiddenAxiom', text)


if __name__ == '__main__':
    unittest.main()

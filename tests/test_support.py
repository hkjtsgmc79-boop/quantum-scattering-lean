import unittest,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from build_support import parse_axioms,uncomment,inventory,MODULES
class SupportTests(unittest.TestCase):
    def test_standard(self):
        self.assertEqual(parse_axioms("'T' depends on axioms: [propext, Classical.choice, Quot.sound]",['T'])['T'],['Classical.choice','Quot.sound','propext'])
    def test_empty(self):
        with self.assertRaises(ValueError):parse_axioms('', ['T'])
    def test_no_axioms(self):self.assertEqual(parse_axioms("'T' does not depend on any axioms",['T']),{'T':[]})
    def test_sorry(self):
        with self.assertRaises(ValueError):parse_axioms("'T' depends on axioms: [sorryAx]",['T'])
    def test_added_axiom(self):
        with self.assertRaises(ValueError):parse_axioms("'T' depends on axioms: [QuantumScattering.assumeUnitary]",['T'])
    def test_compiler_trust(self):
        with self.assertRaises(ValueError):parse_axioms("'T' depends on axioms: [Lean.trustCompiler]",['T'])
    def test_duplicate(self):
        with self.assertRaises(ValueError):parse_axioms("'T' depends on axioms: []\n'T' depends on axioms: []",['T'])
    def test_extra(self):
        with self.assertRaises(ValueError):parse_axioms("'T' depends on axioms: []\n'X' depends on axioms: []",['T'])
    def test_error(self):
        with self.assertRaises(ValueError):parse_axioms("error: broken\n'T' depends on axioms: []",['T'])
    def test_unclosed(self):
        with self.assertRaises(ValueError):uncomment('/- test')
    def test_nested(self):self.assertEqual(uncomment('/- a /- b -/ c -/X'),'X')
    def test_inventory(self):
        i=inventory(ROOT)
        self.assertEqual(i['module_count'],len(MODULES))
        self.assertFalse(i['duplicate_names']);self.assertFalse(i['forbidden_tokens'])
if __name__=='__main__':unittest.main(verbosity=2)

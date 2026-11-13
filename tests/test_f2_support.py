"""Tooling tests, not Lean theorem tests."""
import json,re,sys,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from build_support import MODULES,CORE_MODULES,BRIDGE_MODULES,dependency_order,inventory,export
class F2SupportTests(unittest.TestCase):
 def test_release_list(self):
  self.assertEqual(len(MODULES),25)
  self.assertEqual(len(CORE_MODULES),23)
  self.assertEqual(set(BRIDGE_MODULES),{'RectangularBridge','ReleaseAcceptance'})
 def test_legacy_dependency_closure(self):
  order=dependency_order(ROOT,'QuantumTunneling')
  self.assertEqual(len(order),40)
  for name in order:
   text=(ROOT/'QuantumTunneling'/(name+'.lean')).read_text()
   for dep in re.findall(r'^import QuantumTunneling\.(\w+)',text,re.M):
    self.assertLess(order.index(dep),order.index(name))
 def test_inherited_hashes_match_the_handoff_baseline(self):
  record=json.loads((ROOT/'inherited-sources.json').read_text())
  self.assertEqual(len(record['F1']),15);self.assertEqual(len(record['Q5']),40)
  baseline=json.loads((ROOT/'migration-baseline.json').read_text())['proof_modules']
  for group in record.values():
   for rel,sha in group.items():self.assertEqual(baseline[rel],sha,msg=rel)
 def test_core_has_no_legacy_dependency(self):
  for name in CORE_MODULES:
   text=(ROOT/'QuantumScattering'/(name+'.lean')).read_text()
   self.assertNotRegex(text,re.compile(r'^import QuantumTunneling\.',re.M),msg=name)
 def test_aggregates_are_fresh(self):
  before={name:(ROOT/name).read_bytes() for name in ['Quantum_Scattering_F2_Core_All.lean','Quantum_Scattering_F2_All.lean']}
  export(ROOT)
  for name,old in before.items():self.assertEqual(old,(ROOT/name).read_bytes())
 def test_audit_counts(self):
  names=[]
  for file,count in [('Audit.lean',45),('BridgeAudit.lean',9),('ReleaseAudit.lean',1)]:
   got=re.findall(r'^#print axioms (\S+)',(ROOT/file).read_text(),re.M)
   self.assertEqual(len(got),count);names+=got
  self.assertEqual(len(names),len(set(names)))
 def test_public_contracts_preserved(self):
  for item in json.loads((ROOT/'contracts.json').read_text()):
   text=(ROOT/item['file']).read_text();i=text.index(item['start']);j=text.index(item['end'],i)
   self.assertEqual(text[i:j],item['expected'])
if __name__=='__main__':unittest.main(verbosity=2)

"""Unit tests of migration tooling/configuration only; never proof verification."""
import hashlib,json,re,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from migration_support import (load_lock,version_matches,manifest_revisions,
    require_manifest,package_candidates,expected_audits,classify_failure,EnvironmentBlocked)

class Migration435Tests(unittest.TestCase):
    def test_exact_version(self): self.assertTrue(version_matches('Lean (version 4.35.0, x86_64-unknown-linux-gnu)','4.35.0'))
    def test_old_rejected(self): self.assertFalse(version_matches('Lean (version 4.30.0, arm64)','4.35.0'))
    def test_rc_rejected(self): self.assertFalse(version_matches('Lean (version 4.35.0-rc1, arm64)','4.35.0'))
    def test_prefix_rejected(self): self.assertFalse(version_matches('Lean (version 4.35.01, arm64)','4.35.0'))
    def test_lock(self):
        l=load_lock(ROOT)
        self.assertEqual(l['target_toolchain'],'leanprover/lean4:v4.35.0')
        self.assertEqual(l['mathlib']['commit'],'56a005855ea17e0b0958f73ec801ae140b0a1679')
        self.assertEqual(len(l['transitive_packages']),8)
    def test_current_toolchain_matches(self):
        self.assertEqual((ROOT/'lean-toolchain').read_text().strip(),load_lock(ROOT)['target_toolchain'])
    def test_lake_pin_matches(self):
        self.assertIn('rev = "'+load_lock(ROOT)['mathlib']['commit']+'"',(ROOT/'lakefile.toml').read_text())
    def test_full_lake_entry(self):
        self.assertIn('defaultTargets = ["QuantumScatteringRelease"]',(ROOT/'lakefile.toml').read_text())
        self.assertIn('import QuantumScattering.ReleaseAcceptance',(ROOT/'QuantumScatteringRelease.lean').read_text())
    def test_all_math_sources_match_the_release_snapshot(self):
        baseline=json.loads((ROOT/'migration-baseline.json').read_text())['proof_modules']
        snapshot=json.loads((ROOT/'SHA256SUMS.json').read_text())
        source_files={str(p.relative_to(ROOT)) for namespace in ('QuantumScattering','QuantumTunneling')
                      for p in (ROOT/namespace).glob('*.lean')}
        self.assertEqual(len(baseline),65)
        self.assertEqual(source_files,set(baseline))
        for file in sorted(source_files):
            want=snapshot[file]
            self.assertEqual(hashlib.sha256((ROOT/file).read_bytes()).hexdigest(),want,msg=file)
    def test_contract_file_preserved(self):
        b=json.loads((ROOT/'migration-baseline.json').read_text())
        self.assertEqual(hashlib.sha256((ROOT/'contracts.json').read_bytes()).hexdigest(),b['contracts_sha256'])
    def test_all_audits(self):
        self.assertEqual(len(expected_audits(ROOT,['Audit.lean','BridgeAudit.lean','ReleaseAudit.lean'])),55)
    def test_project_and_standalone_cache_layouts(self):
        roots=package_candidates(Path('/work/project'),Path('/work/mathlib'),'batteries')
        self.assertIn(Path('/work/mathlib/.lake/packages/batteries'),roots)
        self.assertIn(Path('/work/batteries'),roots)
        self.assertIn(Path('/work/project/.lake/packages/batteries'),roots)
    def test_manifest_exact(self):
        wanted=load_lock(ROOT)['transitive_packages']
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'manifest.json';p.write_text(json.dumps({'packages':[{'name':n,'rev':r,'type':'git'} for n,r in wanted.items()]}))
            self.assertEqual(require_manifest(p,wanted),wanted)
    def test_manifest_wrong_commit(self):
        wanted=load_lock(ROOT)['transitive_packages']
        rows=[{'name':n,'rev':r,'type':'git'} for n,r in wanted.items()];rows[0]['rev']='0'*40
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'manifest.json';p.write_text(json.dumps({'packages':rows}))
            with self.assertRaises(EnvironmentBlocked):require_manifest(p,wanted)
    def test_manifest_duplicate(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'manifest.json';p.write_text(json.dumps({'packages':[{'name':'x','rev':'0'*40,'type':'git'}]*2}))
            with self.assertRaises(ValueError):manifest_revisions(p)
    def test_manifest_missing(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t)/'manifest.json';p.write_text('{"packages":[]}')
            with self.assertRaises(EnvironmentBlocked):require_manifest(p,{'x':'0'*40})
    def test_partial_failure_not_full_pass(self):
        self.assertEqual(classify_failure(True,False),'CORE_PASS_RELEASE_FAILED')
        self.assertEqual(classify_failure(True,True),'CORE_PASS_RELEASE_BLOCKED')
        self.assertEqual(classify_failure(False,True),'BLOCKED')
    def test_no_old_active_runner_pin(self):
        text=(ROOT/'scripts/verify.py').read_text()
        self.assertNotIn('c5ea00351',text)
        self.assertNotIn("require Lean 4.30.0",text)
        self.assertNotIn('4\\.30\\.0',text)
    def test_no_global_default_change(self):
        text=(ROOT/'scripts/prepare_lean435.sh').read_text()
        commands=[x.strip() for x in text.splitlines() if not x.lstrip().startswith('#')]
        self.assertFalse(any('elan default ' in x for x in commands))
    def test_import_probe_has_real_derivative(self):
        self.assertIn('HasDerivAt',(ROOT/'Compatibility435.lean').read_text())
        self.assertIn('deriv f x = f\' := h.deriv',(ROOT/'Compatibility435.lean').read_text())
if __name__=='__main__':unittest.main(verbosity=2)

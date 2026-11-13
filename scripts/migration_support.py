"""Exact version, dependency and package-layout checks. Not a Lean checker."""
from __future__ import annotations
import json, os, re, subprocess
from pathlib import Path

class EnvironmentBlocked(RuntimeError):
    pass

def load_lock(root: Path) -> dict:
    data = json.loads((root/'toolchain-lock.json').read_text(encoding='utf-8'))
    if data['target_toolchain'] != 'leanprover/lean4:v'+data['target_lean_version']:
        raise ValueError('Inconsistent Lean toolchain lock')
    for rev in [data['mathlib']['commit'], *data['transitive_packages'].values()]:
        if not re.fullmatch(r'[0-9a-f]{40}', rev):
            raise ValueError('Lock must contain complete Git commit IDs')
    return data

def version_matches(text: str, version: str) -> bool:
    # Exclude RC/nightly versions, and also 4.35.01 / 4.35.0-rc1.
    return re.search(r'\bversion\s+'+re.escape(version)+r'(?=[\s,)])', text) is not None

def manifest_revisions(path: Path) -> dict[str, str]:
    doc = json.loads(path.read_text(encoding='utf-8'))
    result = {}
    for p in doc.get('packages', []):
        if p['name'] in result:
            raise ValueError('Duplicate package name in '+str(path))
        if p.get('type') != 'git' or not re.fullmatch(r'[0-9a-f]{40}',p.get('rev','')):
            raise ValueError('Non-Git or unpinned dependency in '+str(path))
        result[p['name']] = p['rev']
    return result

def require_manifest(path: Path, expected: dict[str, str]) -> dict[str, str]:
    got = manifest_revisions(path)
    if got != expected:
        mismatch = {n: {'expected': expected.get(n), 'actual': got.get(n)}
                    for n in set(expected)|set(got) if expected.get(n)!=got.get(n)}
        raise EnvironmentBlocked('Dependency manifest does not match 4.35.0 lock: '+json.dumps(mismatch))
    return got

def package_candidates(project: Path, mathroot: Path, name: str) -> list[Path]:
    # Lake puts dependencies next to mathlib in a project checkout; standalone
    # Mathlib checkouts instead use mathlib/.lake/packages. Support both.
    candidates = [mathroot.parent/name, mathroot/'.lake/packages'/name,
                  project/'.lake/packages'/name]
    out=[]
    for p in candidates:
        p=p.absolute()
        if p not in out: out.append(p)
    return out

def local_mathlib_imports(root: Path) -> set[str]:
    imports=set()
    for ns in ['QuantumScattering','QuantumTunneling']:
        for p in (root/ns).glob('*.lean'):
            imports.update(re.findall(r'^import (Mathlib(?:\.\S+)?)',p.read_text(),re.M))
    return imports

def check_import_sources(root: Path, mathroot: Path) -> dict:
    imports = sorted(local_mathlib_imports(root))
    missing = [n for n in imports if not (mathroot/(n.replace('.','/')+'.lean')).is_file()]
    if missing:
        raise EnvironmentBlocked('Pinned Mathlib source has missing import paths: '+', '.join(missing))
    return {'import_count':len(imports), 'imports':imports, 'source_paths_found':True}

def expected_audits(root: Path, specs: list[str]) -> list[str]:
    names=[]
    for file in specs:
        names += re.findall(r'^#print axioms (\S+)\s*$',(root/file).read_text(),re.M)
    if not names or len(names)!=len(set(names)):
        raise ValueError('Empty or duplicate audit declaration list')
    return names

def classify_failure(core_verified: bool, blocked: bool) -> str:
    if core_verified: return 'CORE_PASS_RELEASE_BLOCKED' if blocked else 'CORE_PASS_RELEASE_FAILED'
    return 'BLOCKED' if blocked else 'FAIL'

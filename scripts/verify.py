#!/usr/bin/env python3
"""Fresh Lean 4.35.0 verification. Network-free; use prepare_lean435.sh first.
A success record requires real Lean invocations; source and tooling tests cannot
set it. Shared 4.30 caches are rejected, never upgraded or deleted in place.
"""
from __future__ import annotations
import argparse,json,os,re,shutil,subprocess,time,zipfile
from datetime import datetime,timezone
from pathlib import Path
from build_support import (MODULES,CORE_MODULES,BRIDGE_MODULES,sha256,inventory,
                           export,parse_axioms,dependency_order,uncomment)
from migration_support import (EnvironmentBlocked,load_lock,version_matches,
    require_manifest,package_candidates,check_import_sources,expected_audits,classify_failure)
ROOT=Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lean',default=os.environ.get('LEAN_BIN'))
    ap.add_argument('--mathlib-root',default=os.environ.get('MATHLIB_ROOT'))
    ap.add_argument('--target',choices=['core','release'],default='release')
    ap.add_argument('--timeout',type=int,default=900,help='Seconds per actual command; timeout is a failure, not a pass.')
    ap.add_argument('--preflight-only',action='store_true',help='Environment only. Never certifies proofs.')
    args=ap.parse_args()
    if args.timeout<=0: ap.error('--timeout must be positive')
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'reports'/('lean435_'+stamp);out.mkdir(parents=True,exist_ok=False)
    build=ROOT/'.build-local'/('lean435_'+stamp);build.mkdir(parents=True,exist_ok=False)
    report={'run_id':stamp,'target':args.target,'status':'BLOCKED','lean_verified':False,
            'core_verified':False,'release_verified':False,'compiler_started':False,
            'proof_compilation_started':False,'commands':[],
            'required_framework_modules':MODULES if args.target=='release' else CORE_MODULES,
            'source_hashes':{},'source_hashes_after':{},
            'warning':'Only the actual command chain can establish compilation. This is not external semantic review.'}
    env=os.environ.copy()
    def sources():
        paths=list((ROOT/'QuantumScattering').glob('*.lean'))+list((ROOT/'QuantumTunneling').glob('*.lean'))
        paths+=list(ROOT.glob('*.lean'))+list((ROOT/'scripts').glob('*.py'))+list((ROOT/'scripts').glob('*.sh'))
        paths += [ROOT/n for n in ['lean-toolchain','lakefile.toml','lake-manifest.json','contracts.json','toolchain-lock.json']]
        return {str(p.relative_to(ROOT)):sha256(p) for p in sorted(paths) if p.is_file()}
    def persist():
        (out/'verification.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    def run(tag,argv,cwd=ROOT):
        report['current_stage']=tag;persist();start=time.monotonic()
        try:
            proc=subprocess.run(argv,cwd=cwd,env=env,capture_output=True,text=True,timeout=args.timeout)
            code=proc.returncode;txt=proc.stdout+proc.stderr
        except subprocess.TimeoutExpired as ex:
            def txt(x): return x.decode(errors='replace') if isinstance(x,bytes) else (x or '')
            code=124;txt=txt(ex.stdout)+txt(ex.stderr)+'\nTIMEOUT: '+str(ex)+'\n'
        except OSError as ex: code=127;txt=str(ex)+'\n'
        log=out/(tag+'.log');log.write_text(txt,encoding='utf-8')
        report['commands'].append({'tag':tag,'argv':argv,'exit_code':code,
          'seconds':time.monotonic()-start,'log':log.name,'log_sha256':sha256(log)})
        print(tag,'exit',code,flush=True);persist()
        if code: print(txt[-6000:],flush=True)
        return code,txt
    def checked_repo(label,path,rev):
        rc,txt=run(label+'-commit',['git','-C',str(path),'rev-parse','HEAD'])
        if rc or txt.strip()!=rev: raise EnvironmentBlocked('Pinned commit mismatch: '+label)
        rc,txt=run(label+'-tracked-clean',['git','-C',str(path),'status','--porcelain','--untracked-files=no'])
        if rc or txt.strip(): raise EnvironmentBlocked('Tracked dependency source modified: '+label)
    def compile_file(tag,path,audit_specs=()):
        if tag!='Compatibility435': report['proof_compilation_started']=True
        rel=path.relative_to(ROOT);target=build/rel.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        rc,txt=run(tag,[lean,'-o',str(target),'-i',str(target.with_suffix('.ilean')),str(rel)])
        if rc or re.search(r"declaration uses ['`]?sorry|\bsorryAx\b",txt):
            report['failed_stage']=tag;raise RuntimeError('Proof build failed: '+tag)
        if not target.is_file(): raise RuntimeError('Lean returned success but expected olean is missing: '+tag)
        report.setdefault('compiled_artifacts',{})[str(rel)]={'olean_sha256':sha256(target)}
        if audit_specs:
            expected=expected_audits(ROOT,list(audit_specs))
            result=parse_axioms(txt,expected)
            (out/(tag+'-axioms.json')).write_text(json.dumps(result,indent=2)+'\n')
            report.setdefault('audits',{})[tag]={'count':len(result),'passed':True,'declarations':result}
        persist()
    try:
        lock=load_lock(ROOT);PIN=lock['mathlib']['commit'];tc=lock['target_toolchain']
        report.update(target_toolchain=tc,mathlib_pin=PIN,lock_sha256=sha256(ROOT/'toolchain-lock.json'))
        if (ROOT/'lean-toolchain').read_text().strip()!=tc: raise RuntimeError('Project toolchain differs from lock')
        lake_text=(ROOT/'lakefile.toml').read_text()
        if not re.search(r'rev\s*=\s*"'+PIN+r'"',lake_text): raise RuntimeError('Lake Mathlib pin differs from lock')
        export(ROOT)
        inv=inventory(ROOT);(out/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
        if inv['forbidden_tokens'] or inv['duplicate_names']: raise RuntimeError('Framework source guard failed')
        for path in list((ROOT/'QuantumTunneling').glob('*.lean'))+list(ROOT.glob('*.lean')):
            code=uncomment(path.read_text())
            if re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',code) or 'skipKernel' in code:
                raise RuntimeError('Forbidden proof escape: '+str(path.relative_to(ROOT)))
        for item in json.loads((ROOT/'contracts.json').read_text()):
            txt=(ROOT/item['file']).read_text();i=txt.index(item['start']);j=txt.index(item['end'],i)
            if txt[i:j]!=item['expected']: raise RuntimeError('Protected public statement changed: '+item['file'])
        report['source_hashes']=sources()
        baseline=json.loads((ROOT/'inherited-sources.json').read_text())
        report['inherited_source_changes']={label:[n for n,h in fs.items() if sha256(ROOT/n)!=h] for label,fs in baseline.items()}
        migration=json.loads((ROOT/'migration-baseline.json').read_text())
        report['migration_proof_changes']=[n for n,h in migration['proof_modules'].items() if sha256(ROOT/n)!=h]
        lean=args.lean
        if not lean and shutil.which('elan'):
            rc,txt=run('elan-exact-lean',['elan','run',tc,'elan','which','lean'])
            if not rc: lean=txt.strip()
        if not lean: lean=shutil.which('lean')
        if not lean: raise EnvironmentBlocked('No Lean executable; proof compiler was not started')
        # Preserve a lean/elan proxy's invocation basename. Resolving its symlink
        # to an elan executable before invoking it can change command semantics.
        lean=os.path.abspath(os.path.expanduser(lean))
        rc,txt=run('lean-version',[lean,'--version'])
        report['compiler_started']=(rc==0)
        if rc or not version_matches(txt,lock['target_lean_version']):
            raise EnvironmentBlocked('Require exact Lean '+lock['target_lean_version']+'; old cache is not acceptable')
        report['lean_executable_sha256']=sha256(Path(lean))
        mathroot=Path(args.mathlib_root).expanduser().resolve() if args.mathlib_root else ROOT/'.lake/packages/mathlib'
        if not (mathroot/'lean-toolchain').is_file(): raise EnvironmentBlocked('Mathlib source checkout missing')
        if (mathroot/'lean-toolchain').read_text().strip()!=tc: raise EnvironmentBlocked('Mathlib toolchain is not '+tc)
        checked_repo('mathlib',mathroot,PIN)
        manifest=mathroot/'lake-manifest.json'
        require_manifest(manifest,lock['transitive_packages'])
        shutil.copy2(manifest,out/'resolved-mathlib-manifest.json')
        expected=dict(lock['transitive_packages']);expected['mathlib']=PIN
        own_manifest=ROOT/'lake-manifest.json'
        if own_manifest.is_file():
            require_manifest(own_manifest,expected)
            shutil.copy2(own_manifest,out/'resolved-project-manifest.json')
        if not (mathroot/'.lake/build/lib/lean/Mathlib.olean').is_file():
            raise EnvironmentBlocked('Exact-version Mathlib.olean cache missing')
        dep_paths=[];dep_records={}
        for name,rev in lock['transitive_packages'].items():
            options=[p for p in package_candidates(ROOT,mathroot,name) if (p/'.git').exists()]
            if not options: raise EnvironmentBlocked('Dependency checkout missing: '+name)
            # Select the first candidate, then verify; never silently accept an
            # unrelated wrong-version sibling just because its cache exists.
            selected=options[0];checked_repo('dependency-'+name,selected,rev)
            cache=selected/'.lake/build/lib/lean'
            if not cache.is_dir(): raise EnvironmentBlocked('Dependency Lean cache missing: '+name)
            dep_paths.append(cache);dep_records[name]={'root':str(selected),'commit':rev}
        report['dependencies']=dep_records
        report['import_preflight']=check_import_sources(ROOT,mathroot)
        paths=[build,mathroot/'.lake/build/lib/lean',*dep_paths]
        env['LEAN_PATH']=os.pathsep.join(str(p) for p in paths)
        report['lean_path']=env['LEAN_PATH']
        # A real import-only probe also rejects incompatible binary caches.
        compile_file('Compatibility435',ROOT/'Compatibility435.lean')
        if args.preflight_only:
            report.update(status='PREFLIGHT_PASS',lean_verified=False,
                          note='Environment/import probe only; NO project theorem has passed this target.')
        else:
            for name in CORE_MODULES:compile_file('core-'+name,ROOT/'QuantumScattering'/(name+'.lean'))
            for name in ['QuantumScattering','Examples','FrameworkExamples']:compile_file(name,ROOT/(name+'.lean'))
            compile_file('Audit',ROOT/'Audit.lean',['Audit.lean'])
            compile_file('CoreAll',ROOT/'Quantum_Scattering_F2_Core_All.lean',['Audit.lean'])
            report['core_verified']=True;persist()
            if args.target=='release':
                vendor_order=dependency_order(ROOT,'QuantumTunneling');report['vendored_Q5_modules']=vendor_order
                for name in vendor_order:compile_file('Q5-'+name,ROOT/'QuantumTunneling'/(name+'.lean'))
                for name in BRIDGE_MODULES:compile_file('bridge-'+name,ROOT/'QuantumScattering'/(name+'.lean'))
                compile_file('QuantumTunneling',ROOT/'QuantumTunneling.lean')
                compile_file('QuantumScatteringRelease',ROOT/'QuantumScatteringRelease.lean')
                compile_file('BridgeExamples',ROOT/'BridgeExamples.lean')
                compile_file('BridgeAudit',ROOT/'BridgeAudit.lean',['BridgeAudit.lean'])
                compile_file('ReleaseAudit',ROOT/'ReleaseAudit.lean',['ReleaseAudit.lean'])
                compile_file('FullAll',ROOT/'Quantum_Scattering_F2_All.lean',['Audit.lean','BridgeAudit.lean','ReleaseAudit.lean'])
                report.update(status='RELEASE_PASS',lean_verified=True,release_verified=True)
            else:
                report.update(status='CORE_PASS',lean_verified=True,note='Core-only: complete framework not verified.')
    except EnvironmentBlocked as ex:
        report.update(status=classify_failure(report['core_verified'],True),reason=str(ex))
        print('BLOCKED:',ex,flush=True)
    except (RuntimeError,ValueError,OSError,KeyError,subprocess.SubprocessError) as ex:
        report.update(status=classify_failure(report['core_verified'],False),reason=str(ex))
        print('FAIL:',ex,flush=True)
    except KeyboardInterrupt:
        report.update(status='INTERRUPTED',reason='Stopped by operator')
    finally:
        report['source_hashes_after']=sources()
        report['source_unchanged']=report['source_hashes']==report['source_hashes_after'] if report['source_hashes'] else None
        if report['source_hashes'] and not report['source_unchanged']:
            report.update(status='FAIL',lean_verified=False,core_verified=False,release_verified=False,
                          reason='Source changed during verification; rerun required')
        report['finished_utc']=datetime.now(timezone.utc).isoformat();persist()
        target=ROOT/'reports'/('Quantum_Scattering_Lean435_return_'+stamp+'.zip')
        with zipfile.ZipFile(target,'w',zipfile.ZIP_DEFLATED) as z:
            for p in ROOT.rglob('*'):
                if not p.is_file() or any(x in p.relative_to(ROOT).parts for x in
                  ['.lake','.build-local','reports','history','__pycache__','.git']):continue
                z.write(p,'project/'+str(p.relative_to(ROOT)))
            for p in out.iterdir():
                if p.is_file():z.write(p,'verification/'+p.name)
        print('RESULT:',report['status'],'\nRETURN:',target,flush=True)
    return 0 if report['status'] in ['RELEASE_PASS','CORE_PASS','PREFLIGHT_PASS'] else 2 if 'BLOCKED' in report['status'] else 1
if __name__=='__main__':raise SystemExit(main())

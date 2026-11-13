"""Text inventory, source export and axiom log parsing. Not a Lean checker."""
from pathlib import Path
import hashlib,json,re
BASE_MODULES=['State','RealTransfer','LocalFlow','Layers','Channels','Scattering',
         'Splicing','StackWave','FiniteScattering','PhysicalModel','LocalUniqueness',
         'StackUniqueness','ExteriorModes','EvolutionInterface','Framework']
NEW_CORE_MODULES=['TransferComposition','FlowComposition','Refinement','Radiation',
         'EvolutionUniqueness','EvolutionSegment','SmoothBackend','FrameworkCompletion']
BRIDGE_MODULES=['RectangularBridge','ReleaseAcceptance']
CORE_MODULES=BASE_MODULES+NEW_CORE_MODULES
MODULES=CORE_MODULES+BRIDGE_MODULES
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha256(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def uncomment(t):
    out=[];i=depth=0;string=False
    while i<len(t):
        if depth:
            if t.startswith('/-',i):depth+=1;i+=2
            elif t.startswith('-/',i):depth-=1;i+=2
            else:
                if t[i]=='\n':out.append('\n')
                i+=1
        elif string:
            if t[i]=='\\':i+=2
            elif t[i]=='"':string=False;i+=1
            else:i+=1
        elif t.startswith('/-',i):depth=1;i+=2
        elif t.startswith('--',i):
            k=t.find('\n',i);i=len(t) if k<0 else k
        elif t[i]=='"':string=True;i+=1
        else:out.append(t[i]);i+=1
    if depth or string:raise ValueError('Unterminated source comment/string')
    return ''.join(out)
def inventory(root):
    mods=[];seen={};duplicates=[];forbidden=[];imports=[];decl=[]
    for name in MODULES:
        path=root/'QuantumScattering'/(name+'.lean');text=path.read_text();code=uncomment(text)
        ns=[];local=[]
        for n,line in enumerate(code.splitlines(),1):
            m=re.match(r'^namespace (\w+)',line)
            if m:ns.append(m.group(1))
            m=re.match(r'^end (\w+)',line)
            if m and ns:
                if ns[-1]!=m.group(1):raise ValueError('Namespace mismatch '+name)
                ns.pop()
            m=re.match(r'^(?:@\[[^\]]*\]\s*)?(lemma|theorem|def|structure)\s+([\w.]+)',line)
            if m:
                q='.'.join(ns+[m.group(2)]);d={'kind':m.group(1),'name':q,'file':str(path.relative_to(root)),'line':n}
                if q in seen:duplicates.append(q)
                seen[q]=d;local.append(d);decl.append(d)
        forbidden += [{'file':name,'token':x} for x in re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',code)]
        imps=re.findall(r'^import (\S+)',code,re.M)
        imports.extend((name,i) for i in imps)
        mods.append({'name':name,'lines':len(text.splitlines()),'proofs':sum(d['kind'] in ['lemma','theorem'] for d in local),'imports':imps})
    ordered=set()
    for name,imp in imports:
        if imp.startswith('QuantumScattering.') and MODULES.index(imp.split('.')[-1])>=MODULES.index(name):
            raise ValueError('Import order/cycle: '+name+' -> '+imp)
    inv={'status':'TEXT_ONLY_NOT_LEAN','modules':mods,'module_count':len(mods),
         'lines_including_comments':sum(x['lines'] for x in mods),'proof_declarations':sum(x['proofs'] for x in mods),
         'declarations':decl,'duplicate_names':duplicates,'forbidden_tokens':forbidden}
    return inv

def dependency_order(root,namespace):
    folder=root/namespace
    names={p.stem:p for p in folder.glob('*.lean')}
    visited=set();active=set();ordered=[]
    def visit(name):
        if name in visited:return
        if name in active:raise ValueError('Import cycle: '+namespace+'.'+name)
        if name not in names:raise ValueError('Missing local dependency '+namespace+'.'+name)
        active.add(name)
        for imp in re.findall(r'^import (\S+)',names[name].read_text(),re.M):
            if imp.startswith(namespace+'.'):visit(imp.split('.')[-1])
        active.remove(name);visited.add(name);ordered.append(name)
    for name in sorted(names):visit(name)
    return ordered

def export_one(root,names,filename,audits,legacy=False):
    external_imports = dict.fromkeys(
        line
        for name in names
        for line in (root/'QuantumScattering'/(name+'.lean')).read_text().splitlines()
        if line == 'import Mathlib' or line.startswith('import Mathlib.')
    )
    chunks=['/- F2 Lean 4.35.0. Generated from canonical modules. -/\n',
            ''.join(line+'\n' for line in external_imports)]
    if legacy:chunks+=['import QuantumTunneling.BidirectionalProject\n']
    for name in names:
        t=(root/'QuantumScattering'/(name+'.lean')).read_text()
        t=re.sub(r'^import .*\n','',t,flags=re.M)
        if t.count('noncomputable section\n')!=1:raise ValueError('Unexpected section count: '+name)
        t=t.replace('noncomputable section\n','noncomputable section Bundle_'+name+'\n',1)
        chunks+=['\n/- MODULE '+name+' -/\n',t,'\nend Bundle_'+name+'\n']
    for audit in audits:
        chunks+=['\n'+'\n'.join(x for x in (root/audit).read_text().splitlines() if x.startswith('#print axioms'))+'\n']
    (root/filename).write_text(''.join(chunks))

def export(root):
    export_one(root,CORE_MODULES,'Quantum_Scattering_F2_Core_All.lean',['Audit.lean'])
    export_one(root,MODULES,'Quantum_Scattering_F2_All.lean',
               ['Audit.lean','BridgeAudit.lean','ReleaseAudit.lean'],legacy=True)

def parse_axioms(text,expected):
    if not expected or len(expected)!=len(set(expected)):raise ValueError('Invalid empty/duplicate audit specification')
    out=re.sub(r'\x1b\[[0-9;]*m','',text)
    if re.search(r'\berror\s*:',out,re.I):raise ValueError('Error in Lean output')
    matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",out,re.S)
    matches += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",out)]
    result={}
    for name,raw in matches:
        if name in result:raise ValueError('Duplicate axiom entry')
        used={x.strip() for x in raw.split(',') if x.strip()}
        if used-ALLOWED:raise ValueError('Untrusted axioms: '+str(used-ALLOWED))
        result[name]=sorted(used)
    if set(result)!=set(expected):raise ValueError('Incomplete/extra axiom output')
    return result

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    export(root);inv=inventory(root)
    (root/'reports/source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
    print(json.dumps({k:v for k,v in inv.items() if k not in ['declarations','modules']},indent=2))
    if inv['duplicate_names'] or inv['forbidden_tokens']:raise SystemExit(1)

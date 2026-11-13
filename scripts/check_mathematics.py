#!/usr/bin/env python3
"""Independent formula and model checks. NEVER a Lean proof certificate."""
from __future__ import annotations
import json, math
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import expm

ROOT=Path(__file__).resolve().parents[1]
checks=[]
def exact(name, expr):
    z=s.factor(s.expand(expr))
    ok=z==0
    checks.append({'name':name,'passed':bool(ok),'residual':str(z)})
    if not ok: raise AssertionError((name,z))
a,b,c,d,e,f,g,h=s.symbols('a b c d e f g h',real=True)
x,y,u,v=s.symbols('x y u v',real=True)
P=s.Matrix([[a,b],[c,d]]); Q=s.Matrix([[e,f],[g,h]])
exact('real determinant multiplicativity',(Q*P).det()-Q.det()*P.det())
exact('flux transforms by real determinant', (a*x+b*u)*(c*y+d*v)-(a*y+b*v)*(c*x+d*u)-(a*d-b*c)*(x*v-y*u))
A=(a+d)/2+s.I*(b-c)/2; B=(a-d)/2+s.I*(-b-c)/2
ab=lambda z:s.expand(s.conjugate(z)*z)
exact('SU11 balance from real determinant',ab(A)-ab(B)-(a*d-b*c))
z=x+s.I*y;w=u+s.I*v
value=z+w;slope=s.I*(z-w)
exact('canonical forward state value',(A*z+B*w)+(s.conjugate(B)*z+s.conjugate(A)*w)-(a*value+b*slope))
exact('canonical forward state derivative',s.I*((A*z+B*w)-(s.conjugate(B)*z+s.conjugate(A)*w))-(c*value+d*slope))
exact('canonical flux',s.im(s.conjugate(value)*slope)-(ab(z)-ab(w)))
# Verify unitarity up to the necessary determinant-one factor, not sampled phases.
alpha=x+s.I*y;beta=u+s.I*v
rL=-s.conjugate(beta)/s.conjugate(alpha);t=1/s.conjugate(alpha);rR=beta/s.conjugate(alpha)
exact('unitary off-diagonal',s.cancel(s.conjugate(rL)*t+s.conjugate(t)*rR))
exact('unitary diagonal under balance',s.cancel((ab(rL)+ab(t)-1)*ab(alpha))-(ab(beta)+1-ab(alpha)))
exact('second boundary equation',s.cancel(s.conjugate(beta)*z+s.conjugate(alpha)*(rL*z+t*w)-w))
exact('first boundary residual factors by balance',s.cancel((alpha*z+beta*(rL*z+t*w)-(t*z+rR*w))*s.conjugate(alpha))-(ab(alpha)-ab(beta)-1)*z)
# Three local regimes, including the exact zero-frequency one.
q,k,L=s.symbols('q k L',positive=True,real=True)
for name,delta,C,S in [('oscillatory',q*q,s.cos(q*L),s.sin(q*L)/q),('evanescent',-k*k,s.cosh(k*L),s.sinh(k*L)/k),('threshold',0,s.Integer(1),L)]:
    for label,expr in [('Wronskian',s.trigsimp(C*C+delta*S*S-1)),('C derivative',s.diff(C,L)+delta*S),('S derivative',s.diff(S,L)-C)]:
        exact(name+' '+label,s.simplify(expr))
# Unequal-lead normalization has determinant one and preserves flux.
l,r=s.symbols('l r',positive=True,real=True)
N=s.diag(r,1/r)*P*s.diag(1/l,l)
exact('unequal lead normalization determinant',N.det()-P.det())


def local(delta:float,length:float)->np.ndarray:
    if delta>0:
        q=math.sqrt(delta);C=math.cos(q*length);S=math.sin(q*length)/q
    elif delta<0:
        q=math.sqrt(-delta);C=math.cosh(q*length);S=math.sinh(q*length)/q
    else:C=1.;S=length
    return np.array([[C,S],[-delta*S,C]],float)

def enc(k:float)->np.ndarray:
    z=math.sqrt(k)
    return np.array([[1/z,1/z],[1j*z,-1j*z]],complex)

def stack_transfer(layers):
    P=np.eye(2)
    for delta,width in layers:P=local(delta,width)@P
    return P

def scattering(P,kL,kR):
    B=np.diag([math.sqrt(kR),1/math.sqrt(kR)])@P@np.diag([1/math.sqrt(kL),math.sqrt(kL)])
    a,b,c,d=B.ravel()
    alpha=complex((a+d)/2,(b-c)/2);beta=complex((a-d)/2,(-b-c)/2)
    den=alpha.conjugate()
    S=np.array([[-beta.conjugate()/den,1/den],[1/den,beta/den]],complex)
    return alpha,beta,S

def direct_matching(layers,kL,kR,il,ir):
    """Independent 2N+2 system: unknown outgoing and EACH local Cauchy pair.
    Every local map is computed using scipy.expm, not closed-form code above.
    """
    n=len(layers);size=2*n+2
    mat=np.zeros((size,size),complex);rhs=np.zeros(size,complex)
    EL,ER=enc(kL),enc(kR)
    if n==0:
        mat[:,0]=EL[:,1];mat[:,1]=-ER[:,0]
        rhs[:]=ER[:,1]*ir-EL[:,0]*il
    else:
        mat[:2,0]=-EL[:,1];mat[:2,2:4]=np.eye(2);rhs[:2]=EL[:,0]*il
        for j,(delta,width) in enumerate(layers):
            P=expm(np.array([[0.,1.],[-delta,0.]])*width)
            row=2*(j+1);mat[row:row+2,2+2*j:4+2*j]=P
            if j<n-1:mat[row:row+2,4+2*j:6+2*j]=-np.eye(2)
            else:mat[row:row+2,1]=-ER[:,0];rhs[row:row+2]=ER[:,1]*ir
    return np.linalg.solve(mat,rhs)

rng=np.random.default_rng(20261113)
max_errors={x:0. for x in ['unitarity','boundary_matching','current','composition','expm_agreement','local_ODE','C1_junction']}
case_records=[];position_count=0
for j in range(112):
    n=[0,1,2,3,5,8,12][j%7]
    kL=float(rng.uniform(.5,2.5));kR=float(rng.uniform(.5,2.5))
    layers=[(float(rng.uniform(-2.5,3.0)),float(rng.uniform(.06,.3))) for _ in range(n)]
    if n and j%3==0:layers[j%n]=(0.,layers[j%n][1])
    il=complex(*rng.normal(size=2));ir=complex(*rng.normal(size=2))
    P=stack_transfer(layers);alpha,beta,S=scattering(P,kL,kR)
    o=S@np.array([il,ir]);direct=direct_matching(layers,kL,kR,il,ir)
    max_errors['unitarity']=max(max_errors['unitarity'],float(np.linalg.norm(S.conj().T@S-np.eye(2))))
    max_errors['boundary_matching']=max(max_errors['boundary_matching'],float(np.linalg.norm(direct[:2]-o)/(1+np.linalg.norm(o))))
    cut=n//2;pc=stack_transfer(layers[cut:])@stack_transfer(layers[:cut])
    max_errors['composition']=max(max_errors['composition'],float(np.linalg.norm(P-pc)/(1+np.linalg.norm(P))))
    target=abs(il)**2-abs(o[0])**2
    state=enc(kL)@np.array([il,o[0]])
    if n:
        max_errors['C1_junction']=max(max_errors['C1_junction'],float(np.linalg.norm(state-direct[2:4])/(1+np.linalg.norm(state))))
    for idx,(delta,width) in enumerate(layers):
        pm=local(delta,width);pe=expm(np.array([[0.,1.],[-delta,0.]])*width)
        max_errors['expm_agreement']=max(max_errors['expm_agreement'],float(np.linalg.norm(pm-pe)/(1+np.linalg.norm(pe))))
        for fraction in [0.,.2,.5,.8,1.]:
            pos=fraction*width
            yy=local(delta,pos)@state
            cur=float((yy[0].conjugate()*yy[1]).imag)
            max_errors['current']=max(max_errors['current'],abs(cur-target)/(1+abs(target)))
            # Analytic matrix derivative check against independent expm generator.
            pz=local(delta,pos);Cp=-delta*pz[0,1];Sp=pz[0,0]
            pprime=np.array([[Cp,Sp],[-delta*Sp,Cp]])
            rhs=np.array([[0.,1.],[-delta,0.]])@pz
            max_errors['local_ODE']=max(max_errors['local_ODE'],float(np.linalg.norm(pprime-rhs)))
            position_count+=1
        state=pm@state
        expected=direct[4+2*idx:6+2*idx] if idx<n-1 else enc(kR)@np.array([o[1],ir])
        max_errors['C1_junction']=max(max_errors['C1_junction'],float(np.linalg.norm(state-expected)/(1+np.linalg.norm(expected))))
    case_records.append({'layers':n,'k_left':kL,'k_right':kR,'threshold_count':sum(d==0 for d,_ in layers)})
assert max(max_errors.values())<1e-9,max_errors

# Negative controls: a deliberately invalid model must be rejected, not "close enough".
mutations=[]
def detected(name,amount):
    if not amount>1e-5:raise AssertionError((name,amount))
    mutations.append({'name':name,'detected':True,'witness_residual':float(amount)})
P=stack_transfer([(-2.,.5),(3.,.4),(-.5,.2)])
a,b,S=scattering(P,.7,2.1)
detected('force_equal_left_right_reflection',abs(S[0,0]-S[1,1]))
raw=np.diag([1/math.sqrt(.7),1/math.sqrt(2.1)])@S@np.diag([math.sqrt(.7),math.sqrt(2.1)])
detected('omit_velocity_weights_for_raw_amplitudes',abs(abs(raw[0,0])**2+abs(raw[1,0])**2-1))
rev=stack_transfer(list(reversed([(-2.,.5),(3.,.4),(-.5,.2)])))
detected('reverse_noncommuting_layer_order',np.linalg.norm(rev-P))
bad=np.array([[1.,0.],[0.,1.]])
detected('drop_linear_threshold_propagation',np.linalg.norm(local(0.,.8)-bad))
badS=np.array([[.6,.8],[.8,.6]],complex)
detected('single_input_probabilities_do_not_imply_unitarity',np.linalg.norm(badS.conj().T@badS-np.eye(2)))
layers=[(-3.,.7),(2.,1.2),(-3.,.7)]
T=abs(scattering(stack_transfer(layers),1.,1.)[2][1,0])**2
Tprod=np.prod([abs(scattering(local(d,w),1.,1.)[2][1,0])**2 for d,w in layers])
detected('multiply_probabilities_instead_of_amplitudes',abs(T-Tprod))
# A plus sign in the lower row changes oscillatory evolution into the wrong equation.
delta=1.3;width=.4;wrong=local(delta,width).copy();wrong[1,0]*=-1
detected('wrong_sign_in_local_schrodinger_propagator',np.linalg.norm(wrong-local(delta,width)))

out={'kind':'SYMBOLIC_AND_NUMERICAL_CHECKS_NOT_LEAN','exact_count':len(checks),'exact':checks,
     'finite_stack_cases':len(case_records),'spatial_points':position_count,'layer_counts':sorted({r['layers'] for r in case_records}),
     'max_errors':max_errors,'negative_controls':mutations,'negative_control_count':len(mutations),
     'baseline_Q5_source_modified':False,'lean_verified':False}
(ROOT/'reports/mathematical-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['exact','negative_controls']},indent=2))

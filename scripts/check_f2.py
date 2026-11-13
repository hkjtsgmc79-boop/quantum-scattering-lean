#!/usr/bin/env python3
"""F2 exact algebra + independent numerical regressions. NEVER a Lean proof."""
from __future__ import annotations
import json, math
from pathlib import Path
import numpy as np
import sympy as s
from scipy.linalg import expm
from scipy.integrate import solve_ivp
ROOT=Path(__file__).resolve().parents[1]
checks=[]
def exact(name,expression,relations=None):
    num=s.fraction(s.cancel(expression))[0]
    value=s.expand(num)
    if relations is not None:
        value=relations.reduce(value)[1]
    value=s.factor(value)
    checks.append({'name':name,'passed':bool(value==0),'numerator_residual':str(value)})
    if value!=0:raise AssertionError((name,value))
a,ac,b,bc,c,cc,d,dc=s.symbols('a ac b bc c cc d dc')
G=s.groebner([a*ac-b*bc-1,c*cc-d*dc-1],a,c,ac,cc,b,bc,d,dc)
alpha=c*a+d*bc; alphac=cc*ac+dc*b; beta=c*b+d*ac; betac=cc*bc+dc*a
D=1+b*dc/(ac*cc)
exact('channel balance composes',alpha*alphac-beta*betac-1,G)
exact('feedback determinant factor',D-alphac/(ac*cc))
exact('coherent transmission cascade',1/alphac-(1/cc)*(1/ac)/D)
exact('coherent reflection left',-betac/alphac-(-bc/ac+(1/ac)**2*(-dc/cc)/D),G)
exact('coherent reflection right',beta/alphac-(d/cc+(1/cc)**2*(b/ac)/D),G)
exact('local t^2-rL*rR phase relation',1/ac**2-(-bc/ac)*(b/ac)-a/ac,G)
x=s.symbols('x',real=True)
E=s.Matrix([[1+x*x,(x+(1+x*x)*s.atan(x))/2],[2*x,1+x*s.atan(x)]])
delta=-2/(1+x*x)
A=s.Matrix([[0,1],[-delta,0]])
for i in range(2):
 for j in range(2):exact(f'nonconstant fundamental ODE {i}{j}',s.diff(E,x)[i,j]-(A*E)[i,j])
exact('nonconstant fundamental determinant',E.det()-1)
for i in range(2):
 for j in range(2):exact(f'nonconstant initial condition {i}{j}',E.subs(x,0)[i,j]-s.eye(2)[i,j])
C,S,k,dd=s.symbols('C S k dd',real=True,nonzero=True)
P=s.Matrix([[C,S],[-dd*S,C]])
Pnorm=s.diag(s.sqrt(k),1/s.sqrt(k))*P*s.diag(1/s.sqrt(k),s.sqrt(k))
ca=(Pnorm[0,0]+Pnorm[1,1])/2+s.I*(Pnorm[0,1]-Pnorm[1,0])/2
cb=(Pnorm[0,0]-Pnorm[1,1])/2+s.I*(-Pnorm[0,1]-Pnorm[1,0])/2
oldA=C-s.I*(k*k+dd)*S/(2*k); oldB=s.I*(dd-k*k)*S/(2*k)
exact('single layer alpha is legacy conjugate A',ca-s.conjugate(oldA))
exact('single layer beta is legacy B',cb-oldB)
exact('single layer complex transmission',1/s.conjugate(ca)-1/oldA)
exact('single layer complex reflection left',-s.conjugate(cb)/s.conjugate(ca)-oldB/oldA)
exact('single layer complex reflection right',cb/s.conjugate(ca)-oldB/oldA)
Ca,Sa,Cb,Sb=s.symbols('Ca Sa Cb Sb',real=True)
F=lambda c,t:s.Matrix([[c,t],[-dd*t,c]])
prod=F(Cb,Sb)*F(Ca,Sa);direct=F(Ca*Cb-dd*Sa*Sb,Ca*Sb+Sa*Cb)
for i in range(2):
 for j in range(2):exact(f'exact refinement transfer entry {i}{j}',prod[i,j]-direct[i,j])
# Undoing normalized free propagation reconstructs the true state, not a label.
r=s.symbols('r',nonzero=True,real=True)
enc=s.Matrix([[1/r,1/r],[s.I*r,-s.I*r]])
y0,y1=s.symbols('y0 y1')
y=s.Matrix([y0,y1]); inv=enc.inv(); rec=enc*inv*y
for i in range(2):exact(f'normalized channel state reconstruction {i}',rec[i]-y[i])


def flow(delta,width):
 if abs(delta)<1e-15:return np.array([[1.,width],[0.,1.]])
 q=math.sqrt(abs(delta))
 C=math.cos(q*width) if delta>0 else math.cosh(q*width)
 S=(math.sin(q*width) if delta>0 else math.sinh(q*width))/q
 return np.array([[C,S],[-delta*S,C]])
def encoded(k):
 r=math.sqrt(k);return np.array([[1/r,1/r],[1j*r,-1j*r]],complex)
def scat(P,kl,kr):
 H=np.diag([math.sqrt(kr),1/math.sqrt(kr)])@P@np.diag([1/math.sqrt(kl),math.sqrt(kl)])
 aa=(H[0,0]+H[1,1])/2+1j*(H[0,1]-H[1,0])/2
 bb=(H[0,0]-H[1,1])/2+1j*(-H[0,1]-H[1,0])/2
 return np.array([[-bb.conjugate()/aa.conjugate(),1/aa.conjugate()],
                  [1/aa.conjugate(),bb/aa.conjugate()]])
def transfer(layers):
 P=np.eye(2)
 for dd,ll in layers:P=flow(dd,ll)@P
 return P
def direct_matching(layers,kl,kr,il,ir):
 """2N+2 unknowns. Each cell uses expm, not the proposed closed-form S."""
 n=len(layers);mat=np.zeros((2*n+2,2*n+2),complex);rhs=np.zeros(2*n+2,complex)
 L,R=encoded(kl),encoded(kr)
 if not n:
  mat[:,0]=L[:,1];mat[:,1]=-R[:,0];rhs=R[:,1]*ir-L[:,0]*il
 else:
  mat[:2,0]=-L[:,1];mat[:2,2:4]=np.eye(2);rhs[:2]=L[:,0]*il
  for j,(dd,ll) in enumerate(layers):
   row=2*(j+1);mat[row:row+2,2+2*j:4+2*j]=expm([[0,ll],[-dd*ll,0]])
   if j+1<n:mat[row:row+2,4+2*j:6+2*j]=-np.eye(2)
   else:mat[row:row+2,1]=-R[:,0];rhs[row:row+2]=R[:,1]*ir
 return np.linalg.solve(mat,rhs)
def state(layers,kl,kr,il,ol,x):
 y=encoded(kl)@np.array([il,ol])
 if x<0:return flow(kl**2,x)@y
 for dd,ll in layers:
  if x<ll:return flow(dd,x)@y
  y=flow(dd,ll)@y;x-=ll
 return flow(kr**2,x)@y
errs={k:0. for k in ['cascade','direct_matching','refined_transfer','refined_wave',
 'legacy_wave','legacy_derivative','radiation_channels','smooth_ivp','smooth_current','smooth_boundary']}
def err(key,a,b):
 value=float(np.linalg.norm(np.asarray(a)-np.asarray(b))/(1+np.linalg.norm(np.asarray(b))))
 errs[key]=max(errs[key],value)
 if value>2e-9:raise AssertionError((key,value))
rng=np.random.default_rng(20261113)
counts={'cascade_structures':0,'refined_states':0,'legacy_parameter_cases':0,
        'legacy_spatial_points':0,'radiation_samples':0,'smooth_cases':0,'smooth_spatial_points':0}
for j in range(64):
 kl,km,kr=map(float,rng.uniform(.5,2.3,3))
 xs=[(float(rng.uniform(-2,3)),float(rng.uniform(.05,.35))) for _ in range(1+j%4)]
 ys=[(float(rng.uniform(-2,3)),float(rng.uniform(.05,.35))) for _ in range(1+j%3)]
 if j%4==0:xs[0]=(0.,xs[0][1])
 M,N=scat(transfer(xs),kl,km),scat(transfer(ys),km,kr)
 den=1-M[1,1]*N[0,0]
 cas=np.array([[M[0,0]+M[0,1]**2*N[0,0]/den,N[0,1]*M[0,1]/den],
               [N[0,1]*M[0,1]/den,N[1,1]+N[0,1]**2*M[1,1]/den]])
 allcells=xs+ys;full=scat(transfer(allcells),kl,kr);err('cascade',cas,full)
 il=complex(*rng.normal(size=2));ir=complex(*rng.normal(size=2));out=full@[il,ir]
 direct=direct_matching(allcells,kl,kr,il,ir);err('direct_matching',out,direct[:2])
 idx=j%len(allcells);dd,ll=allcells[idx];frac=.37
 refined=allcells[:idx]+[(dd,ll*frac),(dd,ll*(1-frac))]+allcells[idx+1:]
 err('refined_transfer',transfer(refined),transfer(allcells))
 for pos in [-.3,0.,.31*sum(w for _,w in allcells),.74*sum(w for _,w in allcells),sum(w for _,w in allcells)+.4]:
  err('refined_wave',state(refined,kl,kr,il,out[0],pos),state(allcells,kl,kr,il,out[0],pos));counts['refined_states']+=1
 for pos in [-.25,-1.8]:
  true=state(allcells,kl,kr,il,out[0],pos)
  decoded=np.linalg.solve(encoded(kl),flow(kl**2,-pos)@true)
  err('radiation_channels',decoded,[il,out[0]]);counts['radiation_samples']+=1
 for offset in [.3,1.7]:
  width=sum(w for _,w in allcells);pos=width+offset;true=state(allcells,kl,kr,il,out[0],pos)
  decoded=np.linalg.solve(encoded(kr),flow(kr**2,-offset)@true)
  err('radiation_channels',decoded,[out[1],ir]);counts['radiation_samples']+=1
 counts['cascade_structures']+=1
# Independently evaluate the old exit-normalized exact wave and derivative.
def old_left(k,delta,width,x):
 P=flow(delta,width);C,S=P[0];A=C-1j*(k*k+delta)*S/(2*k);B=1j*(delta-k*k)*S/(2*k)
 if x<0:
  f=A*np.exp(1j*k*x)+B*np.exp(-1j*k*x);v=1j*k*(A*np.exp(1j*k*x)-B*np.exp(-1j*k*x))
 elif x<width:
  f,v=flow(delta,x-width)@np.array([1.,1j*k])
 else:f=np.exp(1j*k*(x-width));v=1j*k*f
 return np.array([f,v])/A
for j in range(48):
 h,m,E,V,width=map(float,rng.uniform(.4,2.1,5))
 if j%3==0:E=V
 k=math.sqrt(2*m*E)/h;delta=2*m*(E-V)/h**2
 a,b=complex(*rng.normal(size=2)),complex(*rng.normal(size=2))
 il,ir=math.sqrt(k)*a,math.sqrt(k)*b
 direct=direct_matching([(delta,width)],k,k,il,ir)
 for x in [-.4,0.,width*.29,width*.8,width,width+.3]:
  old=a*old_left(k,delta,width,x)+b*old_left(k,delta,width,width-x)*np.array([1.,-1.])
  new=state([(delta,width)],k,k,il,direct[0],x)
  err('legacy_wave',new[0],old[0]);err('legacy_derivative',new[1],old[1]);counts['legacy_spatial_points']+=1
 counts['legacy_parameter_cases']+=1
# Nonconstant backend: independent adaptive IVP integration, then independent
# boundary solve for the outgoing amplitudes. No matrix from the proof is input.
def smooth(x):return np.array([[1+x*x,(x+(1+x*x)*math.atan(x))/2],[2*x,1+x*math.atan(x)]])
for j in range(24):
 L,kl,kr=map(float,rng.uniform(.2,2.0,3));il,ir=complex(*rng.normal(size=2)),complex(*rng.normal(size=2))
 def rhs(x,y):return (np.array([[0,1],[2/(1+x*x),0.]])@y.reshape(2,2)).ravel()
 ivp=solve_ivp(rhs,[0,L],np.eye(2).ravel(),rtol=2e-12,atol=3e-13,dense_output=True)
 assert ivp.success
 Pe=ivp.y[:,-1].reshape(2,2);Pc=smooth(L);err('smooth_ivp',Pc,Pe)
 EL,ER=encoded(kl),encoded(kr)
 mat=np.column_stack([Pe@EL[:,1],-ER[:,0]]);rhsb=ER[:,1]*ir-Pe@EL[:,0]*il
 out=np.linalg.solve(mat,rhsb);err('smooth_boundary',scat(Pc,kl,kr)@[il,ir],out)
 yy=EL@[il,out[0]];target=abs(il)**2-abs(out[0])**2
 for fraction in [0.,.13,.4,.75,1.]:
  x=L*fraction;Y=smooth(x)@yy;err('smooth_ivp',Y,ivp.sol(x).reshape(2,2)@yy)
  err('smooth_current',(Y[0].conjugate()*Y[1]).imag,target);counts['smooth_spatial_points']+=1
 counts['smooth_cases']+=1
neg=[]
def reject(name,value):
 if value<=1e-6:raise AssertionError(('negative control not detected',name,value))
 neg.append({'name':name,'detected':True,'witness_residual':float(value)})
M=scat(transfer([(-2.,.6)]),1.,1.);N=scat(transfer([(1.3,.7),(-.7,.4)]),1.,1.)
correct=scat(transfer([(-2.,.6),(1.3,.7),(-.7,.4)]),1.,1.)
reject('drop_coherent_feedback_denominator',abs(M[0,1]*N[0,1]-correct[0,1]))
reject('reverse_noncommuting_cascade',np.linalg.norm(correct-scat(transfer([(1.3,.7),(-.7,.4),(-2.,.6)]),1.,1.)))
reject('omit_sqrt_k_input_in_legacy_bridge',abs(math.sqrt(2.)-1.))
reject('replace_threshold_segment_with_identity',np.linalg.norm(flow(0.,.8)-np.eye(2)))
reject('replace_variable_coefficient_by_initial_constant',np.linalg.norm(smooth(1.2)-flow(-2.,1.2)))
reject('wrong_arctan_fundamental_derivative',abs((1+1.2*math.atan(1.2))-2*1.2))
result={'kind':'AUXILIARY_CHECKS_NOT_LEAN','exact_count':len(checks),'exact_checks':checks,
 'numerical_counts':counts,'max_scaled_errors':errs,'negative_controls':neg,'lean_verified':False,
 'note':'These support mathematical identities and regression behavior, not Lean syntax, proof tactics, or kernel acceptance.'}
(ROOT/'reports/f2-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['exact_checks','negative_controls']},indent=2))

import json, math, sys
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import linprog, root

N=6
R,XP,XM,P,M,G=range(N)
PARS=np.array([-3.9031348710732705,-3.8871594592294065,-1.599734247939875,-1.1837272899417237,-4.133666822544351,-0.4460201649848132,-3.302373009718023,0.6449841235663758,-0.8970212734804717,-2.855272916415038,-1.6150771094133503,-2.189714516425959])
W=np.array([1.0,1.0,-1.0,1.0,1.0,1.0,-0.6924282320351625])
CYC=[(R,XP),(XP,G),(G,XM),(XM,R),(R,P),(P,G),(G,M),(M,R)]

def rates(): return np.exp(PARS)

def rhs_factory(eps,sign):
 g=sign*eps;a,b=(1+g)/2,(1-g)/2;am,bm=(1-eps)/2,(1+eps)/2
 ub,vb=am/bm*.1,am/bm*.1; rr=rates(); tr=rr[:8];gp,gn,hp,hn=rr[8:12]
 def f(t,y):
  y=np.maximum(y,0);r,xp,xm,pp,mm,gg=y;o=np.zeros(N)
  z=a*xp*r;o[XP]+=z;o[R]-=z
  z=a*xm*r;o[XM]+=z;o[R]-=z
  z=1.5*a*xp*xm;o[XP]-=z;o[XM]-=z;o[R]+=2*z
  z=.1*a*r;o[XP]+=z;o[R]-=z
  z=ub*b*r;o[XM]+=z;o[R]-=z
  z=.1*a*r;o[P]+=z;o[R]-=z
  z=vb*b*r;o[M]+=z;o[R]-=z
  z=.5*a*pp*mm;o[P]-=z;o[M]-=z;o[R]+=2*z
  for rate,(i,j) in zip(tr,CYC): z=rate*y[i];o[i]-=z;o[j]+=z
  for rate,fac,i in [(gp,b,XP),(gn,a,XM),(hp,b,P),(hn,a,M)]: z=rate*fac*y[i];o[i]-=z;o[R]+=z
  return o
 return f

def all_starts(seed=10208):
 rng=np.random.default_rng(seed); out=[]; names=[]
 for i in range(N):out.append(np.eye(N)[i]);names.append(f'vertex:{i}')
 for i in range(N):
  for j in range(i+1,N):
   y=np.zeros(N);y[i]=y[j]=.5;out.append(y);names.append(f'edge:{i},{j}')
 for mask in range(1,1<<N):
  ids=[i for i in range(N) if mask>>i&1];y=np.zeros(N);y[ids]=1/len(ids);out.append(y);names.append(f'face:{mask}')
 for j in range(80):out.append(rng.dirichlet(np.ones(N)));names.append(f'random:{j}')
 return np.array(out),names

def integrate(eps,sign,Y0,T=1200.0):
 f=rhs_factory(eps,sign);m=len(Y0)
 def batch(t,flat):return np.concatenate([f(t,y) for y in flat.reshape(m,N)])
 ts=np.unique(np.r_[np.linspace(.75*T,T,80),np.geomspace(1e-6,T,180)])
 sol=solve_ivp(batch,(0,T),Y0.ravel(),method='LSODA',t_eval=ts,rtol=2e-9,atol=2e-11)
 if not sol.success:raise RuntimeError(sol.message)
 return ts,sol.y.T.reshape(len(ts),m,N)

def physical(eps,sign,V):
 a=(1+sign*eps)/2;b=(1-sign*eps)/2
 return np.concatenate([a*V,np.full(V.shape[:-1]+(1,),b)],axis=-1)

def lp_margin(eps,neg,pos):
 Xn=physical(eps,-1,neg).reshape(-1,N+1);Xp=physical(eps,1,pos).reshape(-1,N+1)
 c=np.zeros(N+2);c[-1]=-1;A=[np.r_[x,1] for x in Xn]+[np.r_[-x,1] for x in Xp]
 z=linprog(c,A_ub=np.array(A),b_ub=np.zeros(len(A)),bounds=[(-1,1)]*(N+1)+[(0,1)],method='highs')
 if not z.success:return None
 return dict(margin=float(z.x[-1]),weights=z.x[:-1].tolist())

def equilibrium(eps,sign,guess):
 f=rhs_factory(eps,sign)
 def ff(x):
  y=np.r_[x,1-x.sum()];return f(0,y)[:N-1]
 z=root(ff,guess[:N-1],method='hybr')
 y=np.r_[z.x,1-z.x.sum()]
 h=1e-6;J=np.empty((N-1,N-1))
 for j in range(N-1):
  e=np.zeros(N-1);e[j]=h
  J[:,j]=(ff(z.x+e)-ff(z.x-e))/(2*h)
 return dict(success=bool(z.success),state=y.tolist(),resid=float(np.max(np.abs(f(0,y)))),
  eig_real=sorted([float(q.real) for q in np.linalg.eigvals(J)],reverse=True),
  sigma=sorted([float(q) for q in np.linalg.svd(J,compute_uv=False)]))

def closure(mask):
 S={i for i in range(N) if mask>>i&1};changed=True
 while changed:
  changed=False
  for i,j in CYC:
   if i in S and j not in S:S.add(j);changed=True
 return sum(1<<i for i in S)

def face_audit(eps):
 ans=[]
 for sign in (-1,1):
  f=rhs_factory(eps,sign);mn=1e99;worst=None;closed=[]
  for mask in range(1,1<<N):
   if closure(mask)==mask:closed.append(mask)
   if mask==(1<<N)-1:continue
   ids=[i for i in range(N) if mask>>i&1];y=np.zeros(N);y[ids]=1/len(ids);dy=f(0,y)
   leak=sum(max(dy[j],0) for j in range(N) if not(mask>>j&1))
   if leak<mn:mn=leak;worst=mask
  ans.append(dict(sign=sign,closed=closed,min_barycenter_leak=float(mn),worst_mask=worst))
 return ans

def run(eps,out):
 Y0,names=all_starts();ts,Vn=integrate(eps,-1,Y0);_,Vp=integrate(eps,1,Y0)
 late=ts>=.9*ts[-1];Pn=physical(eps,-1,Vn[late]);Pp=physical(eps,1,Vp[late])
 hn=Pn@W;hp=Pp@W
 lp=lp_margin(eps,Vn[late],Vp[late])
 en=equilibrium(eps,-1,Vn[-1].mean(axis=0));ep=equilibrium(eps,1,Vp[-1].mean(axis=0))
 spread_n=float(np.max(np.ptp(Vn[-1],axis=0)));spread_p=float(np.max(np.ptp(Vp[-1],axis=0)))
 ans=dict(eps=eps,rates=rates().tolist(),weights=W.tolist(),starts=len(Y0),faces=face_audit(eps),
  fixed_readout=dict(negative_max=float(hn.max()),negative_min=float(hn.min()),positive_min=float(hp.min()),positive_max=float(hp.max()),margin=min(float(-hn.max()),float(hp.min()))),
  optimal_sampled_readout=lp,endpoint_spread=dict(negative=spread_n,positive=spread_p),
  equilibrium_negative=en,equilibrium_positive=ep,
  equilibrium_distance=float(np.linalg.norm(np.array(en['state'])-np.array(ep['state']))),
  diagnostics=dict(mass_drift=float(max(np.max(np.abs(Vn.sum(axis=2)-1)),np.max(np.abs(Vp.sum(axis=2)-1)))),min_concentration=float(min(Vn.min(),Vp.min()))))
 Path(out).write_text(json.dumps(ans,indent=2,sort_keys=True));print(json.dumps(ans,sort_keys=True))
if __name__=='__main__':run(float(sys.argv[1]),sys.argv[2])

import json, math, sys
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import linprog
N=6
R,XP,XM,P,M,G=range(N)
def rhs_factory(eps,sign,pars):
 g=sign*eps;a,b=(1+g)/2,(1-g)/2;am,bm=(1-eps)/2,(1+eps)/2
 ub,vb=am/bm*.1,am/bm*.1;tr=np.exp(pars[:8]);gp,gn,hp,hn=np.exp(pars[8:12])
 cyc=[(R,XP),(XP,G),(G,XM),(XM,R),(R,P),(P,G),(G,M),(M,R)]
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
  for rate,(i,j) in zip(tr,cyc):z=rate*y[i];o[i]-=z;o[j]+=z
  for rate,fac,i in [(gp,b,XP),(gn,a,XM),(hp,b,P),(hn,a,M)]:z=rate*fac*y[i];o[i]-=z;o[R]+=z
  return o
 return f
def starts(seed):
 rng=np.random.default_rng(seed);return np.array([*np.eye(N),np.ones(N)/N,*[rng.dirichlet(np.ones(N)) for _ in range(10)]])
def integrate(eps,sign,pars,Y0,T=260,samples=40):
 f=rhs_factory(eps,sign,pars);m=len(Y0)
 def batch(t,flat):return np.concatenate([f(t,y) for y in flat.reshape(m,N)])
 sol=solve_ivp(batch,(0,T),Y0.ravel(),method='LSODA',t_eval=np.linspace(.72*T,T,samples),rtol=8e-7,atol=8e-9)
 if not sol.success:raise RuntimeError(sol.message)
 return sol.y.T.reshape(samples,m,N)
def readout(eps,neg,pos):
 an,bn=(1-eps)/2,(1+eps)/2;ap,bp=(1+eps)/2,(1-eps)/2
 Xn=np.c_[an*neg.reshape(-1,N),np.full(neg.shape[0]*neg.shape[1],bn)];Xp=np.c_[ap*pos.reshape(-1,N),np.full(pos.shape[0]*pos.shape[1],bp)]
 nv=N+1;c=np.zeros(nv+1);c[-1]=-1;A=[np.r_[x,1] for x in Xn]+[np.r_[-x,1] for x in Xp]
 z=linprog(c,A_ub=np.array(A),b_ub=np.zeros(len(A)),bounds=[(-1,1)]*nv+[(0,1)],method='highs')
 return (-1,None) if not z.success else (float(z.x[-1]),z.x[:-1])
def evaluate(pars,seed):
 eps=1e-3;Y0=starts(seed);neg=integrate(eps,-1,pars,Y0);pos=integrate(eps,1,pars,Y0);margin,w=readout(eps,neg[-8:],pos[-8:])
 if w is None:return -9,{}
 sw=integrate(eps,1,pars,neg[-1],T=170,samples=34);an,bn=(1-eps)/2,(1+eps)/2;ap,bp=(1+eps)/2,(1-eps)/2
 hn=np.c_[an*neg[-8:].reshape(-1,N),np.full(8*len(Y0),bn)]@w;hpv=np.c_[ap*pos[-8:].reshape(-1,N),np.full(8*len(Y0),bp)]@w
 hs=(np.c_[ap*sw.reshape(-1,N),np.full(sw.shape[0]*sw.shape[1],bp)]@w).reshape(sw.shape[0],sw.shape[1])
 nmax,pmin,swmin=float(hn.max()),float(hpv.min()),float(hs[-7:].min());s=min(-nmax,pmin,swmin)
 return s,dict(score=s,margin_lp=margin,nmax=nmax,pmin=pmin,swmin=swmin,weights=w.tolist(),pars=pars.tolist())
def main(job,count,out):
 rng=np.random.default_rng(1020800+job);best=(-1e9,None);records=[]
 for i in range(count):
  pars=rng.uniform(math.log(.01),math.log(5),12)
  if i<8:
   base=np.array([.15,.8,.15,.8,.15,.8,.15,.8,.2,.2,.2,.2]);pars=np.log(base)+rng.normal(0,.5,12)
  try:s,info=evaluate(pars,1000*job+i)
  except Exception:continue
  if s>best[0]:best=(s,info)
  if s>-.15:records.append(info)
 Path(out).write_text(json.dumps(dict(job=job,best=best[1],records=sorted(records,key=lambda x:x['score'],reverse=True)[:8]),indent=2));print(json.dumps(best[1]))
if __name__=='__main__':main(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3])

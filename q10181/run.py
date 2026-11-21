import json, math, sys, hashlib
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp

RTOL = 1e-10
ATOL = 1e-12
N_DIRICHLET = 50
N_RANDOM_CORNER = 16
N_RANDOM_INTERIOR = 16


def lab(i, sign):
    return 2 * i - 1 if sign > 0 else 2 * i


def build_model(k, eps):
    m, n = 2 * k + 1, 4 * k + 2
    delta = eps ** (1.0 / k) / (256.0 * k * k)
    idx = lambda c, l: c * m + l
    rows = []

    def add(re, pr, raw, kind, stage, polarity):
        rows.append((tuple(sorted(re)), tuple(sorted(pr)), raw,
                     kind, stage, polarity))

    for c in range(2):
        for ell in range(m):
            add([idx(c, 0), idx(0, ell)],
                [idx(c, lab(1, 1)), idx(0, ell)], 1.0, "prod", 1, 1)
            add([idx(c, 0), idx(1, ell)],
                [idx(c, lab(1, -1)), idx(1, ell)], 1.0, "prod", 1, -1)
    for stage in range(2, k + 1):
        for c in range(2):
            for d in range(2):
                for sign in (1, -1):
                    p = idx(d, lab(stage - 1, sign))
                    add([idx(c, 0), p], [idx(c, lab(stage, sign)), p],
                        1.0, "prod", stage, sign)
    for stage in range(1, k + 1):
        for c in range(2):
            for sign in (1, -1):
                for d in range(2):
                    for ell in range(m):
                        p = idx(d, ell)
                        add([idx(c, lab(stage, sign)), p], [idx(c, 0), p],
                            delta, "reset", stage, sign)
    for stage in range(1, k + 1):
        for c in range(2):
            for d in range(2):
                add([idx(c, lab(stage, 1)), idx(d, lab(stage, -1))],
                    [idx(c, 0), idx(d, 0)], 1.0, "cancel", stage, 0)

    merged = {}
    for re, pr, raw, kind, stage, polarity in rows:
        key = (re, pr)
        if key in merged:
            old = merged[key]
            assert old[1:] == [kind, stage, polarity]
            old[0] += raw
        else:
            merged[key] = [raw, kind, stage, polarity]
    C = len(merged)
    ra = np.empty(C, int); rb = np.empty(C, int); raw = np.empty(C)
    stage = np.empty(C, int); polarity = np.empty(C, int); kind = []
    S = np.zeros((n, C))
    for j, ((re, pr), (coef, kd, st, po)) in enumerate(merged.items()):
        ra[j], rb[j] = re; raw[j] = coef; kind.append(kd)
        stage[j] = st; polarity[j] = po
        for x in re: S[x, j] -= 1.0
        for x in pr: S[x, j] += 1.0
    assert np.all(S.sum(axis=0) == 0.0)
    for c in range(2):
        assert np.all(S[c*m:(c+1)*m].sum(axis=0) == 0.0)
    plus = np.array([idx(c, lab(i, 1)) for c in range(2)
                     for i in range(1, k + 1)])
    minus = np.array([idx(c, lab(i, -1)) for c in range(2)
                      for i in range(1, k + 1)])
    return dict(k=k, eps=eps, m=m, n=n, delta=delta, ra=ra, rb=rb,
                raw=raw, stage=stage, polarity=polarity,
                kind=np.array(kind), S=S, plus=plus, minus=minus,
                channels=C, descriptions=len(rows), duplicates=len(rows)-C)


def conditional_starts(k, sign, random_count):
    m = 2 * k + 1
    eye = np.eye(m)
    out = [(f"corner:{a}|{b}", eye[a], eye[b])
           for a in range(m) for b in range(m)]
    wrong = -1 if sign > 0 else 1
    p = np.zeros(m); p[[lab(i, wrong) for i in range(1, k+1)]] = 1.0/k
    out.append(("all-wrong", p.copy(), p.copy()))
    p = np.zeros(m); p[1:] = 1.0/(2*k)
    out.append(("empty-pool", p.copy(), p.copy()))
    p = np.zeros(m); p[lab(k, wrong)] = 1.0
    out.append(("final-stage-wrong", p.copy(), p.copy()))
    rng = np.random.default_rng(1018100 + 100*k + (1 if sign > 0 else 2))
    for j in range(random_count):
        out.append((f"dirichlet:{j}", rng.dirichlet(np.ones(m)),
                    rng.dirichlet(np.ones(m))))
    return out


def panel(k, eps, full):
    ys, signs, names = [], [], []
    for sign in (1, -1):
        g = sign * eps; a, b = (1+g)/2, (1-g)/2
        starts = conditional_starts(k, sign, N_DIRICHLET if full else 0)
        if not full:
            wanted = {"corner:0|0", "all-wrong", "empty-pool", "final-stage-wrong"}
            starts = [x for x in starts if x[0] in wanted]
            m = 2*k+1; eye = np.eye(m)
            for u, v in [(1,1),(2,2),(m-2,m-2),(m-1,m-1),(1,m-1),(m-1,1)]:
                starts.append((f"corner:{u}|{v}", eye[u], eye[v]))
        for name, pa, pb in starts:
            ys.append(np.r_[a*pa, b*pb]); signs.append(sign)
            names.append(("+" if sign > 0 else "-") + ":" + name)
    return np.array(ys), np.array(signs, int), names


def deadline(model, theta):
    k, eps, d = model["k"], model["eps"], model["delta"]
    q = k*math.log(4/eps) + k*(k+1)*math.log(16)/2 + 0.5
    return 2*math.exp(theta)*(1.25 + q/d)


def evaluate(model, Y0, signs, names, exponents, theta, mult):
    ntr, n = len(Y0), model["n"]
    rates = model["raw"] * np.exp(theta*exponents) / (2*math.exp(theta))
    ra, rb, S = model["ra"], model["rb"], model["S"]
    def rhs(t, flat):
        Y = flat.reshape(ntr, n)
        F = Y[:, ra] * Y[:, rb] * rates
        return (F @ S.T).ravel()
    T = mult * deadline(model, theta)
    sol = solve_ivp(rhs, (0,T), Y0.ravel(), method="LSODA", rtol=RTOL,
                    atol=ATOL, dense_output=True, lband=n-1, uband=n-1)
    if not sol.success: raise RuntimeError(sol.message)
    lo = max(1e-10, min(1e-3, T*1e-10))
    ts = np.unique(np.r_[0.0, np.geomspace(lo,T,420), sol.t])
    V = sol.sol(ts).reshape(ntr,n,-1)
    h = V[:,model["plus"],:].sum(axis=1)-V[:,model["minus"],:].sum(axis=1)
    sh = signs[:,None]*h
    tail = sh[:,int(0.8*len(ts)):].min(axis=1)
    final = sh[:,-1]
    good = tail >= 0.25-2e-7
    worst = int(np.argmin(tail))
    ca = V[:,:model["m"],:].sum(axis=1); cb=V[:,model["m"]:,:].sum(axis=1)
    return dict(passed=int(good.sum()), total=ntr,
                min_tail=float(tail[worst]), min_final=float(final.min()),
                worst=names[worst], worst_sign=int(signs[worst]),
                mass_drift=float(np.max(np.abs(V.sum(axis=1)-1))),
                color_drift=float(max(np.max(np.abs(ca-Y0[:,:model["m"]].sum(axis=1)[:,None])),
                                      np.max(np.abs(cb-Y0[:,model["m"]:].sum(axis=1)[:,None])))),
                min_concentration=float(V.min()),
                end_resid=float(np.max(np.abs(rhs(T,sol.y[:,-1])))), horizon=float(T))


def structured(model, pattern, cancel):
    u = np.zeros(model["channels"])
    for j,(kd,st,po) in enumerate(zip(model["kind"],model["stage"],model["polarity"])):
        if kd == "prod": u[j] = -1 if po == pattern[st-1] else 1
        elif kd == "reset": u[j] = 1 if po == pattern[st-1] else -1
        else: u[j] = cancel
    return u


def checker(model, seed):
    u=np.empty(model["channels"])
    for j,(a,b,st,po) in enumerate(zip(model["ra"],model["rb"],model["stage"],model["polarity"])):
        u[j]=1 if (17*int(a)+31*int(b)+13*int(st)+7*int(po)+19*seed+3*j)%2==0 else -1
    return u


def candidates(model, seed):
    k=model["k"]; out=[]
    for mask in range(2**k):
        pat=tuple(1 if (mask>>i)&1 else -1 for i in range(k))
        for cancel in (-1,1):
            desc="stage-pattern:"+",".join(str(x) for x in pat)+f";cancel:{cancel}"
            out.append((desc,structured(model,pat,cancel)))
    for s in range(4): out.append((f"checker:{s}",checker(model,s)))
    rng=np.random.default_rng(seed)
    for i in range(N_RANDOM_CORNER):
        out.append((f"random-corner:{i}",rng.choice([-1.0,1.0],model["channels"])))
    for i in range(N_RANDOM_INTERIOR):
        out.append((f"random-interior:{i}",rng.uniform(-1,1,model["channels"])))
    return out


def run_case(k,eps,ratio,path):
    model=build_model(k,eps); theta=ratio*eps
    Yr,sr,nr=panel(k,eps,False); Yf,sf,nf=panel(k,eps,True)
    cand=candidates(model,101810000+100000*k+int(round(1e7*eps))+int(100*ratio))
    ranked=[]
    for desc,u in cand:
        st=evaluate(model,Yr,sr,nr,u,theta,2.5)
        ranked.append((st["min_tail"],desc,u,st))
    ranked.sort(key=lambda z:z[0]); chosen=ranked[:8]
    for target in (1,-1):
        desc="stage-pattern:"+",".join([str(target)]*k)+";cancel:-1"
        for item in ranked:
            if item[1]==desc and all(x[1]!=desc for x in chosen): chosen.append(item)
    verified=[]
    for _,desc,u,small in chosen:
        st=evaluate(model,Yf,sf,nf,u,theta,4.0)
        verified.append(dict(description=desc,stats=st,reduced=small["min_tail"],
            sha256=hashlib.sha256(np.asarray(u,np.float64).tobytes()).hexdigest()))
    verified.sort(key=lambda x:x["stats"]["min_tail"])
    nominal=evaluate(model,Yf,sf,nf,np.zeros(model["channels"]),0.0,4.0)
    ans=dict(k=k,eps=eps,ratio=ratio,theta=theta,delta=model["delta"],
             channels=model["channels"],descriptions=model["descriptions"],
             duplicates=model["duplicates"],full_starts=len(Yf),reduced_starts=len(Yr),
             candidate_count=len(cand),nominal=nominal,verified=verified,rtol=RTOL,atol=ATOL)
    Path(path).write_text(json.dumps(ans,indent=2,sort_keys=True))


def summarize(indir,jout,tout):
    cases=[json.loads(p.read_text()) for p in sorted(Path(indir).glob("case-*.json"))]
    lines=[]; allstats=[]
    for c in cases:
        allstats.append(c["nominal"]); allstats += [x["stats"] for x in c["verified"]]
        w=c["verified"][0]; s=w["stats"]
        lines.append(f"CASE k={c['k']} eps={c['eps']:.1e} ratio={c['ratio']:.2f} candidates={c['candidate_count']} verified={len(c['verified'])} pass={s['passed']}/{s['total']} min_tail={s['min_tail']:.12g} min_final={s['min_final']:.12g} worst={s['worst']} assignment={w['description']} sha={w['sha256']}")
        for x in c["verified"][:5]:
            t=x["stats"]
            lines.append(f"ASSIGN k={c['k']} eps={c['eps']:.1e} ratio={c['ratio']:.2f} desc={x['description']} pass={t['passed']}/{t['total']} min_tail={t['min_tail']:.12g} min_final={t['min_final']:.12g} worst={t['worst']} sha={x['sha256']}")
    diag=dict(max_mass_drift=max(x["mass_drift"] for x in allstats),
              max_color_drift=max(x["color_drift"] for x in allstats),
              min_concentration=min(x["min_concentration"] for x in allstats),
              max_end_resid=max(x["end_resid"] for x in allstats))
    Path(jout).write_text(json.dumps(dict(cases=cases,diagnostics=diag),indent=2,sort_keys=True))
    lines.append("DIAGNOSTICS "+" ".join(f"{k}={v:.6g}" for k,v in diag.items()))
    Path(tout).write_text("\n".join(lines)+"\n")


if __name__=="__main__":
    if sys.argv[1]=="case": run_case(int(sys.argv[2]),float(sys.argv[3]),float(sys.argv[4]),sys.argv[5])
    elif sys.argv[1]=="summarize": summarize(sys.argv[2],sys.argv[3],sys.argv[4])
    else: raise SystemExit("bad mode")

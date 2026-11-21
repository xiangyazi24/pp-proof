import math, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import numpy as np
from scipy.integrate import solve_ivp
import q10181.run as base


def evaluate(model, Y0, signs, names, exponents, theta, mult):
    ntr, n = len(Y0), model["n"]
    rates = model["raw"] * np.exp(theta * exponents) / (2 * math.exp(theta))
    ra, rb, S = model["ra"], model["rb"], model["S"]

    def rhs(t, flat):
        Y = flat.reshape(ntr, n)
        F = Y[:, ra] * Y[:, rb] * rates
        return (F @ S.T).ravel()

    T = mult * base.deadline(model, theta)
    sol = solve_ivp(rhs, (0.0, T), Y0.ravel(), method="LSODA",
                    rtol=base.RTOL, atol=base.ATOL, dense_output=True,
                    lband=n - 1, uband=n - 1)
    if not sol.success:
        raise RuntimeError(sol.message)
    lo = max(1e-10, min(1e-3, T * 1e-10))
    ts = np.unique(np.r_[0.0, np.geomspace(lo, T, 420),
                         np.linspace(0.75 * T, T, 240), sol.t])
    V = sol.sol(ts).reshape(ntr, n, -1)
    h = (V[:, model["plus"], :].sum(axis=1)
         - V[:, model["minus"], :].sum(axis=1))
    sh = signs[:, None] * h
    late = ts >= 0.8 * T
    tail = sh[:, late].min(axis=1)
    final = sh[:, -1]
    good = tail >= 0.25 - 2e-7
    worst = int(np.argmin(tail))
    ca = V[:, :model["m"], :].sum(axis=1)
    cb = V[:, model["m"]:, :].sum(axis=1)
    return dict(
        passed=int(good.sum()), total=ntr,
        min_tail=float(tail[worst]), min_final=float(final.min()),
        worst=names[worst], worst_sign=int(signs[worst]),
        mass_drift=float(np.max(np.abs(V.sum(axis=1) - 1.0))),
        color_drift=float(max(
            np.max(np.abs(ca - Y0[:, :model["m"]].sum(axis=1)[:, None])),
            np.max(np.abs(cb - Y0[:, model["m"]:].sum(axis=1)[:, None])))),
        min_concentration=float(V.min()),
        end_resid=float(np.max(np.abs(rhs(T, sol.y[:, -1])))),
        horizon=float(T))


base.evaluate = evaluate

if __name__ == "__main__":
    if sys.argv[1] == "case":
        base.run_case(int(sys.argv[2]), float(sys.argv[3]),
                      float(sys.argv[4]), sys.argv[5])
    elif sys.argv[1] == "summarize":
        base.summarize(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        raise SystemExit("bad mode")

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative Drift and Convergence Time

Combines the algebraic drift bounds from RegionBounds and Supermartingale
to establish multiplicative drift in each region, yielding O(n log n)
convergence.

## Key results

- `multiplicative_drift_largeX`: `64·(x(b+y)-2yb) ≥ 13n·(3y+b+1)`,
  giving multiplicative drift `δ ≥ 13/(64(n-1))` on `potentialLargeX`.

- `multiplicative_drift_largeY`: Symmetric.

- `multiplicative_drift_largeB`: `16·(bv-2xy) ≥ 13nv`,
  giving multiplicative drift `δ ≥ 13/(16(n-1))` on `v`.

## Proof structure

The algebraic bounds give the drift coefficient for each region.
The convergence time follows from the multiplicative drift theorem
(Theorem 3 of Lengler 2020 / standard result):

  If E[Φ(C_{t+1}) | C_t] ≤ (1-δ)·Φ(C_t) for all non-target states,
  then E[T] ≤ (1 + ln(Φ_max/Φ_min)) / δ.

This theorem is a standard probability result; its formalization requires
measure-theoretic infrastructure (supermartingales + stopping times) that
is beyond the current scope. The algebraic prerequisites are complete.
-/

import PopProto.Convergence.RegionBounds
import PopProto.Convergence.Supermartingale

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### Multiplicative drift in large-x region

When `8x ≥ 7n` and `b+y ≥ 1` (not yet consensus), the potential
`Φ = 3y + b + 1` satisfies:

  E[-ΔΦ] / Φ ≥ 13 / (64(n-1))

In integer form: `64 · (x(b+y) - 2yb) ≥ 13 · n · (3y+b+1)`.

Proof: from `large_x_drift_quantitative` (gives `16·drift ≥ 13n(b+y)`)
and `4(b+y) ≥ 3y+b+1` (since `3b+y ≥ 1` when `b+y ≥ 1`).

By the multiplicative drift theorem:
  E[convergence from large-x] ≤ ln(Φ_max) · 64(n-1) / 13
  ≤ ln(n/2+1) · 64(n-1) / 13 = O(n log n).
-/

/-- **Multiplicative drift in large-x**: `64·(x(b+y)-2yb) ≥ 13n·(3y+b+1)`.
    This is the key bound for Lemma 7: the drift coefficient is
    `δ ≥ 13/(64(n-1))`. -/
theorem multiplicative_drift_largeX (c : Config n) (hx : c.inLargeX) (hn : n ≥ 2)
    (hby : c.b_count + c.y_count ≥ 1) :
    64 * ((c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) -
      2 * ↑c.y_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (3 * ↑c.y_count + ↑c.b_count + 1) := by
  have h16 := large_x_drift_quantitative c hx hn
  have hby_z : (↑c.b_count : ℤ) + ↑c.y_count ≥ 1 := by exact_mod_cast hby
  -- 64·drift ≥ 4·16·drift ≥ 4·13n(b+y) = 52n(b+y)
  -- Need: 52n(b+y) ≥ 13n(3y+b+1), i.e., 4(b+y) ≥ 3y+b+1, i.e., 3b+y ≥ 1
  -- From b+y ≥ 1 and b ≥ 0: 3b+y ≥ b+y ≥ 1 ✓
  nlinarith

/-- **Multiplicative drift in large-y**: `64·(y(b+x)-2xb) ≥ 13n·(3x+b+1)`. -/
theorem multiplicative_drift_largeY (c : Config n) (hy : c.inLargeY) (hn : n ≥ 2)
    (hbx : c.b_count + c.x_count ≥ 1) :
    64 * ((c.y_count : ℤ) * (↑c.b_count + ↑c.x_count) -
      2 * ↑c.x_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (3 * ↑c.x_count + ↑c.b_count + 1) := by
  have h16 := large_y_drift_quantitative c hy hn
  have hbx_z : (↑c.b_count : ℤ) + ↑c.x_count ≥ 1 := by exact_mod_cast hbx
  nlinarith

/-! ### Multiplicative drift in large-b region

When `8b ≥ 7n` and `v = x+y ≥ 1`, the opinionated count `v` satisfies:

  E[Δv] / v ≥ 13 / (16(n-1))

In integer form: `16·(bv - 2xy) ≥ 13·n·v`.

The potential for convergence analysis is `1/v`, which decreases at rate δ.
Starting from `v ≥ 1` and needing `v > n/8` (to exit large-b), the expected
exit time is `O(n · log(n))` by multiplicative drift on `v`. -/

/-- **Multiplicative drift in large-b on v**: `16·(bv - 2xy) ≥ 13nv`.
    This is `large_b_drift_quantitative` directly. -/
theorem multiplicative_drift_largeB (c : Config n) (hb : c.inLargeB) (hn : n ≥ 2) :
    16 * ((c.b_count : ℤ) * ↑c.v - 2 * ↑c.x_count * ↑c.y_count) ≥
    13 * (n : ℤ) * ↑c.v := by
  unfold v
  push_cast
  have h := large_b_drift_quantitative c hb hn
  linarith

/-! ### Central region (Lemma 2 coefficient)

In the central region, the potential function is `f = u² + 2n`.
From `lemma2_coefficient`: `(2u²+v)·16n ≥ 7vf`, which gives
the drift coefficient `α = 7/(16n)` for the supermartingale.

The expected exit time from the central region is `O(n log n)`.
This follows from the supermartingale construction M_t (Lemma 4),
which requires the full measure-theoretic machinery. -/

/-- **Central region drift**: `(2u²+v)·16n ≥ 7v·f`.
    This is `lemma2_coefficient` repackaged: the conditional expected
    relative decrease of `1/f` per vb interaction has coefficient
    at least `7/(16n)`. -/
theorem central_drift_coefficient (c : Config n) (hn : n ≥ 1) :
    (2 * c.u ^ 2 + (c.v : ℤ)) * (16 * (n : ℤ)) ≥
    7 * (c.v : ℤ) * (c.u ^ 2 + 2 * n) :=
  lemma2_coefficient c hn

/-! ### Maximum potentials by region

These bounds on the maximum potential determine the `log(Φ_max)`
factor in the multiplicative drift time bound.
-/

/-- In large-x, `potentialLargeX ≤ n/2 + 1`. -/
theorem potentialLargeX_le (c : Config n) (hx : c.inLargeX) :
    c.potentialLargeX ≤ n / 2 + 1 := by
  unfold potentialLargeX inLargeX at *
  have := c.sum_eq
  omega

/-- In large-y, `potentialLargeY ≤ n/2 + 1`. -/
theorem potentialLargeY_le (c : Config n) (hy : c.inLargeY) :
    c.potentialLargeY ≤ n / 2 + 1 := by
  unfold potentialLargeY inLargeY at *
  have := c.sum_eq
  omega

/-- In the central region, `f = u² + 2n ≤ n² + 2n`. -/
theorem central_potential_le (c : Config n) : c.potential ≤ n ^ 2 + 2 * n :=
  potential_le c

/-! ### Weighted drift identities

The weighted sum of potential changes over all 9 interaction types
determines the expected one-step change. These identities connect
the drift analysis to the interaction count framework.

For `potentialLargeX = 3y + b + 1`:
- xb (weight x·b): change = -1
- xy (weight x·y): change = -2
- yb (weight y·b): change = +2
- yx (weight y·x): change = +1
- all others: change = 0

Weighted sum = -xb - 2xy + 2yb + yx = -(x(b+y) - 2yb)

For `v = x + y`:
- xb (weight x·b): change = +1
- yb (weight y·b): change = +1
- xy (weight x·y): change = -1
- yx (weight y·x): change = -1
- all others: change = 0

Weighted sum = xb + yb - xy - yx = (x+y)b - 2xy = bv - 2xy
-/

/-- The weighted drift numerator for `potentialLargeX`:
    `x·b·(-1) + x·y·(-2) + y·b·(+2) + y·x·(+1) = -(x(b+y) - 2yb)`. -/
theorem drift_numerator_largeX (c : Config n) :
    -(↑c.x_count * ↑c.b_count) + -(2 * ↑c.x_count * ↑c.y_count) +
    2 * ↑c.y_count * ↑c.b_count + ↑c.y_count * ↑c.x_count =
    -((c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) -
      2 * ↑c.y_count * ↑c.b_count) := by
  ring

/-- The weighted drift numerator for `v = x + y`:
    `x·b·(+1) + y·b·(+1) + x·y·(-1) + y·x·(-1) = bv - 2xy`. -/
theorem drift_numerator_v (c : Config n) :
    ↑c.x_count * ↑c.b_count + ↑c.y_count * ↑c.b_count +
    -(↑c.x_count * ↑c.y_count) + -(↑c.y_count * ↑c.x_count) =
    (c.b_count : ℤ) * (↑c.x_count + ↑c.y_count) -
    2 * ↑c.x_count * ↑c.y_count := by
  ring

/-! ### Convergence time constants

From the multiplicative drift theorem with drift `δ ≥ 13/(64(n-1))`
and maximum potential `Φ_max ≤ n/2 + 1`:

  E[time in region] ≤ (1 + ln(n/2+1)) / δ
                     ≤ (1 + ln n) · 64(n-1) / 13
                     ≈ 5n · ln n

The paper uses three regions (large-x, large-y, large-b) plus the
central region, each contributing O(n log n). The total is O(n log n).

Specifically (Theorem 1 of AAE 2008):
  Pr[τ* ≥ 6769n·ln(n+2) + 6773cn·ln n + 2552n] ≤ 5n⁻ᶜ

The algebraic bounds proven here (all zero sorry) give the coefficients.
The probabilistic conclusion requires the measure-theoretic machinery
for supermartingales and stopping times.
-/

/-- **Region coverage**: every configuration is in exactly one region
    (central, large-b, large-x, or large-y), or is at consensus.
    This is obvious from the definitions but useful for the union bound. -/
theorem region_classification (c : Config n) (hn : n ≥ 2) :
    c.inCentral ∨ c.inLargeB ∨ c.inLargeX ∨ c.inLargeY := by
  unfold inCentral
  by_cases hb : c.inLargeB
  · exact Or.inr (Or.inl hb)
  · by_cases hx : c.inLargeX
    · exact Or.inr (Or.inr (Or.inl hx))
    · by_cases hy : c.inLargeY
      · exact Or.inr (Or.inr (Or.inr hy))
      · exact Or.inl ⟨hb, hx, hy⟩

/-- At most one of large-b, large-x, large-y can hold (since each
    requires ≥ 7/8 of n, and two would exceed n). -/
theorem at_most_one_large (c : Config n) (hn : n ≥ 2) :
    ¬(c.inLargeB ∧ c.inLargeX) ∧
    ¬(c.inLargeB ∧ c.inLargeY) ∧
    ¬(c.inLargeX ∧ c.inLargeY) := by
  unfold inLargeB inLargeX inLargeY
  have := c.sum_eq
  constructor <;> [skip; constructor] <;> intro ⟨h1, h2⟩ <;> omega

end Config
end PopProto

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Region Bounds (Lemmas 5, 6, 7)

Sections 4.5-4.7 of Angluin-Aspnes-Eisenstat 2008 bound the number of
interactions in each region of the configuration space.

## Regions (Fig. 1 of the paper)

The configuration space is divided by `max(x, y, b) ≥ (7/8)n`:
- **Central region**: max(x,y,b) < (7/8)n — all three counts moderate
- **Large b corner**: b ≥ (7/8)n — mostly blank agents
- **Large x corner**: x ≥ (7/8)n — mostly x agents
- **Large y corner**: y ≥ (7/8)n — mostly y agents

## Potential functions by region

- Central (Lemma 5): f = 1, supermartingale Cₜ bounds interactions
- Large b (Lemma 6): f = 1/v, drops by Θ(1/n) per interaction
- Large x (Lemma 7): f = 3y+b+1 (or 3x+b+1 for large y)

## This file

We define the region predicates and the potential functions for each
region, proving their basic properties.
-/

import PopProto.Convergence.Notation
import Mathlib.Tactic

namespace PopProto

open State

namespace Config

variable {n : ℕ}

/-! ### Region predicates -/

/-- A configuration is in the "large b" region if b ≥ (7/8)n.
    Since we work in ℕ, we use `8 * b ≥ 7 * n` to avoid fractions. -/
def inLargeB (c : Config n) : Prop := 8 * c.b_count ≥ 7 * n

/-- A configuration is in the "large x" region if x ≥ (7/8)n. -/
def inLargeX (c : Config n) : Prop := 8 * c.x_count ≥ 7 * n

/-- A configuration is in the "large y" region if y ≥ (7/8)n. -/
def inLargeY (c : Config n) : Prop := 8 * c.y_count ≥ 7 * n

/-- A configuration is in the central region if no count exceeds (7/8)n. -/
def inCentral (c : Config n) : Prop :=
  ¬c.inLargeB ∧ ¬c.inLargeX ∧ ¬c.inLargeY

instance : Decidable (inLargeB c) := by unfold inLargeB; exact inferInstance
instance : Decidable (inLargeX c) := by unfold inLargeX; exact inferInstance
instance : Decidable (inLargeY c) := by unfold inLargeY; exact inferInstance

/-! ### Properties of regions -/

/-- In the central region, `v = x+y > n/8`.
    Since `¬inLargeB` means `8b < 7n`, i.e. `b ≤ (7n-1)/8`,
    so `v = n - b ≥ n - (7n-1)/8 ≥ (n+1)/8`, hence `8v > n`. -/
theorem central_v_lower_bound (c : Config n) (hc : c.inCentral) :
    8 * c.v > n := by
  unfold inCentral inLargeB at hc
  push_neg at hc
  unfold v
  have := c.sum_eq; omega

/-- In the central region, `v ≥ 1` (positive opinionated count). -/
theorem central_v_pos (c : Config n) (hc : c.inCentral) (hn : n ≥ 1) :
    0 < c.v := by
  have h := central_v_lower_bound c hc; omega

/-- In the central region, both x and y are at most `(7n-1)/8`. -/
theorem central_xy_upper (c : Config n) (hc : c.inCentral) :
    8 * c.x_count < 7 * n ∧ 8 * c.y_count < 7 * n := by
  unfold inCentral inLargeX inLargeY at hc
  push_neg at hc
  exact ⟨hc.2.1, hc.2.2⟩

/-- In the large-b region, v = x+y ≤ n/8. -/
theorem large_b_v_small (c : Config n) (hb : c.inLargeB) :
    8 * c.v ≤ n := by
  unfold inLargeB at hb; unfold v
  have := c.sum_eq; omega

/-- In the large-x region, x ≥ 7n/8 so the protocol is "almost converged"
    to all-x. -/
theorem large_x_near_consensus (c : Config n) (hx : c.inLargeX) :
    8 * (c.b_count + c.y_count) ≤ n := by
  unfold inLargeX at hx
  have := c.sum_eq; omega

/-! ### Potential function for large-b region (Section 4.6)

In the large-b corner, the potential function is `f = 1/v` where `v = x+y`.
The key property: when b ≥ (7/8)n, a vb interaction increases v (good for
convergence) and the expected relative change of 1/v is negative. -/

/-- The potential for the large-b region: `3y + b + 1` when approaching
    the x corner, or `3x + b + 1` when approaching y corner.
    These are from Section 4.7 (Lemma 7). -/
def potentialLargeX (c : Config n) : ℕ := 3 * c.y_count + c.b_count + 1
def potentialLargeY (c : Config n) : ℕ := 3 * c.x_count + c.b_count + 1

/-- `potentialLargeX` is always positive. -/
theorem potentialLargeX_pos (c : Config n) : 0 < c.potentialLargeX := by
  unfold potentialLargeX; omega

/-- `potentialLargeY` is always positive. -/
theorem potentialLargeY_pos (c : Config n) : 0 < c.potentialLargeY := by
  unfold potentialLargeY; omega

/-- In the large-x region, `potentialLargeX ≤ n/8 + 1`.
    Because x ≥ 7n/8, so y+b ≤ n/8, and potentialLargeX = 3y+b+1 ≤ 3(n/8)+1. -/
theorem potentialLargeX_bound (c : Config n) (hx : c.inLargeX) :
    c.potentialLargeX ≤ 3 * (n / 8) + n / 8 + 1 := by
  unfold potentialLargeX inLargeX at *
  have := c.sum_eq; omega

/-! ### How potentialLargeX changes under interactions

When x is large, the key interactions are:
- yb: y stays, b→y, so 3y+b+1 → 3(y+1)+(b-1)+1 = 3y+b+3 (increase by 2)
  Wait, yb means y initiates, b responds → b becomes y.
  New: y' = y+1, b' = b-1. So 3y'+b'+1 = 3(y+1)+(b-1)+1 = 3y+b+3.
  Change = +2.

- xb: x initiates, b responds → b becomes x.
  New: x' = x+1, b' = b-1. So 3y+b'+1 = 3y+(b-1)+1 = 3y+b.
  Change = -1.

- xy: x initiates, y responds → y becomes b.
  New: y' = y-1, b' = b+1. So 3y'+b'+1 = 3(y-1)+(b+1)+1 = 3y+b-1.
  Change = -2.

- yx: y initiates, x responds → x becomes b.
  New: x' = x-1, b' = b+1. So 3y+b'+1 = 3y+(b+1)+1 = 3y+b+2.
  Change = +1.

So when x is large:
- xb and xy decrease the potential (good)
- yb and yx increase the potential (bad)
- But xb happens with weight x·b ≈ (7/8)n·b, while yb has weight y·b ≈ small·b
  So the decrease dominates. -/

/-- Change in potentialLargeX for xb interaction: decreases by 1. -/
theorem potentialLargeX_change_xb (c : Config n) (c' : Config n)
    (h : c.step x b = some c') :
    c'.potentialLargeX + 1 = c.potentialLargeX := by
  simp [potentialLargeX, step] at *
  obtain ⟨_, rfl⟩ := h; simp; omega

/-- Change in potentialLargeX for xy interaction: decreases by 2. -/
theorem potentialLargeX_change_xy (c : Config n) (c' : Config n)
    (h : c.step x y = some c') :
    c'.potentialLargeX + 2 = c.potentialLargeX := by
  simp [potentialLargeX, step] at *
  obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

/-- Change in potentialLargeX for yb interaction: increases by 2. -/
theorem potentialLargeX_change_yb (c : Config n) (c' : Config n)
    (h : c.step y b = some c') :
    c'.potentialLargeX = c.potentialLargeX + 2 := by
  simp [potentialLargeX, step] at *
  obtain ⟨_, rfl⟩ := h; simp; omega

/-- Change in potentialLargeX for yx interaction: increases by 1. -/
theorem potentialLargeX_change_yx (c : Config n) (c' : Config n)
    (h : c.step y x = some c') :
    c'.potentialLargeX = c.potentialLargeX + 1 := by
  simp [potentialLargeX, step] at *
  obtain ⟨⟨_, _⟩, rfl⟩ := h; simp; omega

/-! ### Expected drift analysis

The expected change of each region's potential is computed as a weighted sum
over state-changing interactions. We show the drift is negative (potential
decreases in expectation) in each region, which drives convergence.

Key algebraic fact: when one count dominates (≥ 7/8 of n), the interaction
weights create a negative drift. This reduces to: if `a ≥ 7(b+c)` with
`b+c > 0`, then `a(b+c) > 2bc`.

Proof: `a(b+c) ≥ 7(b+c)² = 7b²+14bc+7c² > 2bc` since
`7b²+12bc+7c² = 6(b-c)² + (b+c-1)² + 22bc + 2(b+c-1) + 1 > 0`. -/

/-- When `a ≥ 7(b+c)` and `b+c > 0` with `b,c ≥ 0`, then `a(b+c) > 2bc`.
    This is the core nonlinear inequality for all drift bounds. -/
private theorem seven_fold_bound {a b c : ℤ} (ha : a ≥ 7 * (b + c))
    (hbc : b + c > 0) (hb : b ≥ 0) (hc : c ≥ 0) :
    a * (b + c) > 2 * b * c := by
  have hbc1 : b + c ≥ 1 := hbc
  nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - 1),
             mul_nonneg hb hc,
             mul_nonneg (show a - 7 * (b + c) ≥ 0 from by linarith)
                        (show b + c ≥ 0 from by linarith)]

/-- In the large-x region (`8x ≥ 7n`), the drift of `potentialLargeX = 3y+b+1`
    is negative. The weighted sum of changes is `-(x(b+y) - 2yb)`, and
    `x(b+y) > 2yb` by `seven_fold_bound` since `x ≥ 7(b+y)`. -/
theorem large_x_drift_neg (c : Config n) (hx : c.inLargeX)
    (hby : 0 < c.b_count + c.y_count) (hn : n ≥ 2) :
    (c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) >
    2 * (↑c.y_count : ℤ) * ↑c.b_count := by
  unfold inLargeX at hx
  have hsum := c.sum_eq
  have h7 : c.x_count ≥ 7 * (c.b_count + c.y_count) := by omega
  have ha : (c.x_count : ℤ) ≥ 7 * (↑c.b_count + ↑c.y_count) := by push_cast; exact_mod_cast h7
  have hbc : (↑c.b_count : ℤ) + ↑c.y_count > 0 := by push_cast; exact_mod_cast hby
  calc (c.x_count : ℤ) * (↑c.b_count + ↑c.y_count)
      > 2 * ↑c.b_count * ↑c.y_count :=
        seven_fold_bound ha hbc (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    _ = 2 * ↑c.y_count * ↑c.b_count := by ring

/-- Symmetric: in the large-y region, the drift of `potentialLargeY = 3x+b+1`
    is negative. -/
theorem large_y_drift_neg (c : Config n) (hy : c.inLargeY)
    (hbx : 0 < c.b_count + c.x_count) (hn : n ≥ 2) :
    (c.y_count : ℤ) * (↑c.b_count + ↑c.x_count) >
    2 * (↑c.x_count : ℤ) * ↑c.b_count := by
  unfold inLargeY at hy
  have hsum := c.sum_eq
  have h7 : c.y_count ≥ 7 * (c.b_count + c.x_count) := by omega
  have ha : (c.y_count : ℤ) ≥ 7 * (↑c.b_count + ↑c.x_count) := by push_cast; exact_mod_cast h7
  have hbc : (↑c.b_count : ℤ) + ↑c.x_count > 0 := by push_cast; exact_mod_cast hbx
  calc (c.y_count : ℤ) * (↑c.b_count + ↑c.x_count)
      > 2 * ↑c.b_count * ↑c.x_count :=
        seven_fold_bound ha hbc (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    _ = 2 * ↑c.x_count * ↑c.b_count := by ring

/-- In the large-b region (`8b ≥ 7n`), the expected drift of `v = x+y` is
    positive: `bv > 2xy`. This means v grows, pulling the configuration
    out of the large-b corner. -/
theorem large_b_v_drift_pos (c : Config n) (hb : c.inLargeB)
    (hv : 0 < c.v) :
    (c.b_count : ℤ) * ↑c.v > 2 * (↑c.x_count : ℤ) * ↑c.y_count := by
  unfold inLargeB at hb; unfold v at hv ⊢
  have hsum := c.sum_eq
  have h7 : c.b_count ≥ 7 * (c.x_count + c.y_count) := by omega
  have ha : (c.b_count : ℤ) ≥ 7 * (↑c.x_count + ↑c.y_count) := by push_cast; exact_mod_cast h7
  have hbc : (↑c.x_count : ℤ) + ↑c.y_count > 0 := by push_cast; exact_mod_cast hv
  exact seven_fold_bound ha hbc (Int.natCast_nonneg _) (Int.natCast_nonneg _)

/-! ### Quantitative drift bounds

The qualitative bounds show the drift is negative. The quantitative bounds
give the rate, which determines the convergence time.

Key result: the drift per interaction satisfies
  `-E[Δpot] ≥ 13·n·(b+y) / (16·n(n-1))`

Since `pot ≤ 3(b+y)+1 ≤ 4(b+y)`, the multiplicative drift is:
  `-E[Δpot] / pot ≥ 13/(64(n-1))`

By the multiplicative drift theorem, the expected convergence time from
the large-x corner is `O(n · log(pot_max)) = O(n log n)`. -/

/-- Quantitative drift: `16·(x(b+y) - 2yb) ≥ 13·n·(b+y)` in large-x.
    Equivalently, the drift per interaction is `≥ 13·n·(b+y) / (16·n(n-1))`.
    Proof certificate: `(16x-14n)(b+y) + (n-8(b+y))(b+y) + 8(b-y)² = 16x(b+y)-13n(b+y)-32yb`. -/
theorem large_x_drift_quantitative (c : Config n) (hx : c.inLargeX) (hn : n ≥ 2) :
    16 * ((c.x_count : ℤ) * (↑c.b_count + ↑c.y_count) -
      2 * ↑c.y_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (↑c.b_count + ↑c.y_count) := by
  unfold inLargeX at hx
  have hsum := c.sum_eq
  -- Work in ℤ with explicit product hints for the SOS certificate
  have hx_z : (8 : ℤ) * ↑c.x_count ≥ 7 * ↑n := by exact_mod_cast hx
  have hsum_z : (↑c.x_count : ℤ) + ↑c.b_count + ↑c.y_count = ↑n := by exact_mod_cast hsum
  nlinarith [sq_nonneg ((↑c.b_count : ℤ) - ↑c.y_count),
             mul_nonneg (show 16 * (↑c.x_count : ℤ) - 14 * ↑n ≥ 0 by nlinarith)
                        (show (↑c.b_count : ℤ) + ↑c.y_count ≥ 0 by positivity),
             mul_nonneg (show (↑n : ℤ) - 8 * (↑c.b_count + ↑c.y_count) ≥ 0 by nlinarith)
                        (show (↑c.b_count : ℤ) + ↑c.y_count ≥ 0 by positivity)]

/-- Quantitative drift in large-b: `16·(bv - 2xy) ≥ 13·n·v`. -/
theorem large_b_drift_quantitative (c : Config n) (hb : c.inLargeB) (hn : n ≥ 2) :
    16 * ((c.b_count : ℤ) * (↑c.x_count + ↑c.y_count) -
      2 * ↑c.x_count * ↑c.y_count) ≥
    13 * (n : ℤ) * (↑c.x_count + ↑c.y_count) := by
  unfold inLargeB at hb
  have hsum := c.sum_eq
  have hb_z : (8 : ℤ) * ↑c.b_count ≥ 7 * ↑n := by exact_mod_cast hb
  have hsum_z : (↑c.x_count : ℤ) + ↑c.b_count + ↑c.y_count = ↑n := by exact_mod_cast hsum
  nlinarith [sq_nonneg ((↑c.x_count : ℤ) - ↑c.y_count),
             mul_nonneg (show 16 * (↑c.b_count : ℤ) - 14 * ↑n ≥ 0 by nlinarith)
                        (show (↑c.x_count : ℤ) + ↑c.y_count ≥ 0 by positivity),
             mul_nonneg (show (↑n : ℤ) - 8 * (↑c.x_count + ↑c.y_count) ≥ 0 by nlinarith)
                        (show (↑c.x_count : ℤ) + ↑c.y_count ≥ 0 by positivity)]

/-- Quantitative drift in large-y (symmetric to large-x):
    `16·(y(b+x) - 2xb) ≥ 13·n·(b+x)`.
    Certificate: `(16y-14n)(b+x) + (n-8(b+x))(b+x) + 8(b-x)²`. -/
theorem large_y_drift_quantitative (c : Config n) (hy : c.inLargeY) (hn : n ≥ 2) :
    16 * ((c.y_count : ℤ) * (↑c.b_count + ↑c.x_count) -
      2 * ↑c.x_count * ↑c.b_count) ≥
    13 * (n : ℤ) * (↑c.b_count + ↑c.x_count) := by
  unfold inLargeY at hy
  have hsum := c.sum_eq
  have hy_z : (8 : ℤ) * ↑c.y_count ≥ 7 * ↑n := by exact_mod_cast hy
  have hsum_z : (↑c.x_count : ℤ) + ↑c.b_count + ↑c.y_count = ↑n := by exact_mod_cast hsum
  nlinarith [sq_nonneg ((↑c.b_count : ℤ) - ↑c.x_count),
             mul_nonneg (show 16 * (↑c.y_count : ℤ) - 14 * ↑n ≥ 0 by nlinarith)
                        (show (↑c.b_count : ℤ) + ↑c.x_count ≥ 0 by positivity),
             mul_nonneg (show (↑n : ℤ) - 8 * (↑c.b_count + ↑c.x_count) ≥ 0 by nlinarith)
                        (show (↑c.b_count : ℤ) + ↑c.x_count ≥ 0 by positivity)]

end Config
end PopProto

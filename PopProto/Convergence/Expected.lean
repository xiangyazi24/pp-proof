/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Expected Value Bridge

Connects the integer weighted drift (from Drift.lean) to the Bochner
integral over the step distribution PMF. This is the key lemma that
bridges the algebraic drift analysis to the probabilistic statement
needed for the multiplicative drift theorem.

## Main results

- `integral_stepDist_eq_sum`: The integral over `stepDist` equals a weighted
  sum over `State × State`, where the weights are the PMF probabilities.

- `interactionPMF_toReal`: PMF values in ℝ equal `count / totalPairs`.

## Dependencies

Requires `Mathlib.Probability.ProbabilityMassFunction.Integrals` for
`PMF.integral_eq_sum` (finite type expected value formula).
-/

import PopProto.Convergence.Drift
import PopProto.Probability.StepDist
import PopProto.Probability.MarkovChain
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace PopProto

open State MeasureTheory

/-! ### Measurable space instances for State

State is a finite type with 3 elements. We equip it with the discrete
σ-algebra so that all functions from State are measurable. -/

noncomputable instance instMeasurableSpaceState : MeasurableSpace State := ⊤

instance instDiscreteMeasurableSpaceState : DiscreteMeasurableSpace State where
  forall_measurableSet _ := trivial

namespace Config

variable {n : ℕ}

/-! ### Measurability helpers

With discrete σ-algebras on State and Config, all functions are measurable. -/

private theorem measurable_from_state {β : Type*} [MeasurableSpace β]
    (f : State × State → β) : Measurable f :=
  fun _ _ => DiscreteMeasurableSpace.forall_measurableSet _

private theorem measurable_from_config {β : Type*} [MeasurableSpace β]
    (f : Config n → β) : Measurable f :=
  fun _ _ => instDiscreteMeasurableSpaceConfig.forall_measurableSet _

/-! ### Integral over stepDist = sum over interactions -/

/-- The integral over `stepDist` equals a sum over interactions weighted by
    the interaction PMF. -/
theorem integral_stepDist_eq_sum (c : Config n) (hn : n ≥ 2) (f : Config n → ℝ) :
    ∫ c', f c' ∂(c.stepDist hn).toMeasure =
    ∑ p : State × State,
      ((c.interactionPMF hn) p).toReal • f (c.stepOrSelf p.1 p.2) := by
  unfold stepDist
  set g : State × State → Config n := fun p => c.stepOrSelf p.1 p.2
  -- (PMF.map g p).toMeasure = Measure.map g p.toMeasure
  rw [← PMF.toMeasure_map g _ (measurable_from_state g)]
  -- ∫ f d(map g μ) = ∫ (f ∘ g) dμ  [change of variables]
  rw [integral_map (measurable_from_state g).aemeasurable
      (measurable_from_config f).aestronglyMeasurable]
  -- ∫ (f ∘ g) d(pmf.toMeasure) = ∑ p, pmf(p).toReal • f(g(p))
  exact PMF.integral_eq_sum _ _

/-! ### PMF values as real rationals -/

/-- The `interactionPMF` value at `(s₁, s₂)` in `ℝ` is
    `interactionCount s₁ s₂ / totalPairs n`. -/
theorem interactionPMF_toReal (c : Config n) (hn : n ≥ 2) (s₁ s₂ : State) :
    ((c.interactionPMF hn) (s₁, s₂)).toReal =
    (c.interactionCount s₁ s₂ : ℝ) / (totalPairs n : ℝ) := by
  change (c.interactionProb hn s₁ s₂).toReal = _
  unfold interactionProb
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]

end Config
end PopProto

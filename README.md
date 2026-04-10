# PP-Proof: Formal Verification of Population Protocol Convergence

A Lean 4 + Mathlib formalization of the O(n log n) convergence bound for the 3-state approximate majority population protocol from:

> D. Angluin, J. Aspnes, and D. Eisenstat. "A simple population protocol for fast robust approximate majority." *Distributed Computing*, 21(2):87–102, 2008.

**Status:** Complete. All proofs compile with **zero `sorry`** (Lean 4.27.0, Mathlib v4.27.0).

## Key Discovery

During formalization, we found that a key intermediate step in the original proof is **false**: the per-step multiplicative drift E[1/f'] ≤ (1−δ)/f does not hold in the central region.

**Counterexample:** n = 4, x = 1, b = 0, y = 3. The ratio E[1/f']/(1/f) = 103/102 > 1.

The issue is that 1/x is convex, so Jensen's inequality goes the wrong way when step sizes are comparable to the potential f = u² + 2n. This drift *does* hold in the three corner regions (large-x, large-y, large-b), but fails in the central region.

The correct proof for the central region uses the **exponential supermartingale** on an augmented state tracking cumulative interaction counts (as described in Lemma 4 of the paper). The final theorem — O(n log n) convergence with high probability — is correct.

See [the blog post](https://infsup.com/math/formalizing-population-protocol/) for a detailed write-up.

## Structure

```
PopProto/
├── Config.lean              # State space (x, y, b counts), potential function
├── State.lean               # State properties, region definitions
├── Step.lean                # Single-step transitions
├── Transition.lean          # Markov kernel on configurations
├── Convergence/
│   ├── DeltaF.lean          # Drift of potential (Δf per interaction type)
│   ├── RelativeChange.lean  # Relative change bounds
│   ├── Drift.lean           # Corner region drift analysis
│   ├── RegionBounds.lean    # Region-specific bounds
│   ├── Expected.lean        # Expected value infrastructure
│   ├── GeometricDrift.lean  # Generic geometric decay framework
│   ├── Supermartingale.lean # Algebraic supermartingale bounds (Lemma 4)
│   ├── CentralSupermartingale.lean  # Per-step supermartingale on kernel
│   ├── AugmentedState.lean  # Augmented state, central region proof (~2,380 lines)
│   ├── ConvergenceTime.lean # Corner region convergence + main theorem
│   └── Notation.lean        # Shared notation
└── ...
```

~6,650 lines of Lean across 23 files.

## Main Results

### Central region (supermartingale approach)

```lean
theorem prob_in_activeCentral_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelCentral hn ^ t) c₀ activeCentral ≤
    3 * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ t) *
    potentialCentralTrunc c₀
```

### Corner regions (multiplicative drift)

```lean
theorem prob_in_activeLargeX_le (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    (absorbedKernelLargeX hn ^ t) c₀ activeLargeX ≤
    ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ t) *
    potentialLargeXTrunc c₀
```

Analogous theorems for large-y and large-b regions.

### Supermartingale algebraic core (all n ≥ 1)

```lean
theorem supermartingale_factor_vb_le (u : ℤ) (v n : ℕ) (hn : n ≥ 1) (hv : v ≤ n) :
    (16 * (n : ℤ) + 7) * (u ^ 2 + 2 * n) *
    ((v : ℤ) * (u ^ 2 + 2 * n + 1) - 2 * u ^ 2) ≤
    16 * (n : ℤ) * (v : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2)

theorem supermartingale_factor_xy_le (u : ℤ) (n : ℕ) (hn : n ≥ 1) :
    (16 * (n : ℤ) - 5) * (u ^ 2 + 2 * n) * (u ^ 2 + 2 * n + 1) ≤
    16 * (n : ℤ) * ((u ^ 2 + 2 * n + 1) ^ 2 - 4 * u ^ 2)
```

## Building

```bash
# Install Lean 4.27.0 via elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build (first build downloads Mathlib cache, may take a while)
lake exe cache get
lake build
```

## Constants

The formalization uses a contraction rate of 1/(15000n) where the paper's implicit constants are tighter. This larger constant provides more margin for formal inequalities without affecting the asymptotic O(n log n) bound.

## Author

Zinan Huang

## License

Apache 2.0

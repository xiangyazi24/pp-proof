# PP-Proof: Three-State Approximate Majority Consensus Time

A Lean 4 formalization of the high-probability O(n log n) consensus-time
bound for the three-state population protocol of:

> D. Angluin, J. Aspnes, and D. Eisenstat. “A simple population protocol for
> fast robust approximate majority.” *Distributed Computing*, 21(2):87–102, 2008.

## Result and scope

`PopProto.Config.convergence_time_bound_exp` proves, for n ≥ 16 and any
initial configuration containing at least one nonblank opinion,

\[
\Pr[\text{not all-X or all-Y after }4k\text{ interactions}]
\le 3n^2\exp\!\left(-\frac{k}{15000n}\right).
\]

The probability is under the original protocol's uniform ordered-pair
scheduler, with distinct agents and denominator n(n−1). One step is one
interaction, not a parallel round. The initial state may contain blanks;
no initial majority-gap assumption is needed for this consensus-time bound.
All-blank is excluded because it is absorbing without reaching all-X or all-Y.

`convergence_time_high_probability` consequently proves failure probability
at most n^(-r) whenever

\[
k\ge15000n\bigl(\log(3n^2)+r\log n\bigr).
\]

For a fixed positive r, take the natural ceiling of this threshold and run
4k interactions. This is the explicit O(n log n) high-probability guarantee.
The constants are conservative; this does not reproduce the paper's exact
constants. Populations below 16 and correctness of the winning opinion are
outside these headline statements.

## Proof architecture

The proof records cumulative counts along the original execution, including
all exits from and returns to a region. Regional first-exit bounds alone do
not control the complete execution.

- `AugmentedState.lean` extends the interaction-product supermartingale to
  the original chain and proves blank-count conservation and exact marginals.
- `OccupationTime.lean`, `CornerCharge.lean`, and `BlankOccupation.lean`
  establish exponential moments for cumulative central, X, Y, and blank
  occupation charges. `WeightedOccupation.lean` provides their common step
  and iteration argument; each use supplies a concrete protocol inequality.
- `OccupationAssembly.lean` proves that a non-consensus execution of length
  t has recorded exactly t active-region visits, with no reset on re-entry.
- `InteractionProduct.lean` transports the product bound to this same
  counting process. The projected configuration law remains exactly the
  original kernel law.
- `GlobalConvergence.lean` proves the quantitative global tail: either the
  interaction count is large, or at least one occupation charge is large.
  `GlobalConvergenceRate.lean` derives the uniform exponential and polynomial
  failure bounds above.

All results are exported by `PopProto.lean`. The corresponding Ripple
modules use the prefix `Ripple.PopulationProtocol.Majority.PopProto`.

## Correction to the earlier completion claim

Revision `b072efb` advertised completion while its headline was
`convergence_time_bound : True := trivial`. The supporting regional proofs
were substantive, but this placeholder proved no consensus-time guarantee.
The current theorem replaces it with the original-kernel bound above.

The earlier README also incorrectly described the failed naive drift of
1/f as a defect in the paper. The paper already uses an interaction-product
supermartingale and cumulative counts. The missing global assembly was in
this formalization. Compilation and absence of `sorry` did not detect the
old placeholder; acceptance also checks the actual compiled theorem types,
assumptions, original-kernel connection, and transitive axioms.

## Toolchain and verification

The project pins Lean **4.30.0** and Mathlib
**c5ea00351c28e24afc9f0f84379aa41082b1188f**, with transitive revisions in
`lake-manifest.json`.

On a suitably provisioned build host:

```bash
lake exe cache get
lake build PopProto
```

Full builds for this workspace run remotely on uisai2. Local checks should
target one file rather than building the complete dependency graph.

The complete 34-module subtree and umbrella passed a fresh remote build on
2026-09-13, followed by compiled headline-type inspection and transitive axiom
checks for all three results. A non-consensus 8-X/8-Y configuration and a
consumer supplying the natural-ceiling time threshold also compiled. Ripple's
corresponding subtree passed the same gates. Exact source hashes, commands,
logs and type readbacks are retained in the IPS project under
`arena/prove2me-validation/pp-proof-global-20260913/verification/`.

To inspect the three actual headlines, import `PopProto` and run `#check`
and `#print axioms` on `PopProto.Config.convergence_time_bound`,
`PopProto.Config.convergence_time_bound_exp`, and
`PopProto.Config.convergence_time_high_probability`. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed in their transitive axioms.

## Author

Zinan Huang

## License

Apache 2.0

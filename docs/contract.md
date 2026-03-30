# The Admissibility Contract

**Given.** Hilbert space *E*. Orthogonal projections *P* + *Q* = 1. Bounded operator *H*.

**Checked.**

- *QHQ* coercive with floor γ > 0
- ‖*PHQ*‖ ≤ λ
- Regime parameter χ = (λ/γ)²

**Returned.**

- χ < 1 (subcritical): *H*_eff = *PHP* − *PHQ*(*QHQ*)⁻¹*QHP* is a bounded reduction. Error bound δ = λ²/γ. Security margin γ(1 − χ).
- χ ≥ 1 (supercritical): reduction unlicensed.
- No valid setup (pre-admissible): *QHQ* not boundedly invertible. No regime evaluated.

**Layering.** Setup existence is prior to regime classification. χ is evaluated only on admitted setups. Pre-admissible is non-construction of a setup, not failure of a regime test.

## Fukushima Correspondence

The bounded contract is not the bottom layer. Below it sits the exact quotient question.

Fix a full carrier with an exact invariant form. A proposed quotient is licensed when that form
descends as a closed object on the retained quotient carrier. Failure of proper discontinuity
blocks that descent. On the actual quotient carrier, exact pullback then fixes the descended
Markov energy uniquely. At the next exact tier, the public theorem surface places the
quotient-side generator, realized effective semigroup, Hunt realization, and boundary package on
that forced carrier. Exact obstruction blocks bounded
reduction. This exact layer is carried by:

- `licensed_quotient_theorem`
- `quotient_obstruction_theorem`
- `licensed_markov_quotient_theorem`
- `descended_markov_energy_unique_theorem`
- `descended_markov_generator_unique_theorem`
- `licensed_dirichlet_quotient_theorem`
- `descended_dirichlet_generator_exists_theorem`
- `descended_analytic_semigroup_exists_theorem`
- `descended_hunt_process_exists_theorem`
- `descended_capacity_and_trace_theorem`
- `descended_boundary_realization_exists_theorem`
- `descended_strong_markov_theorem`
- `feller_boundary_classification_theorem`
- `ForcedCarrierReductionData.forced_carrier_bounded_reduction_theorem`
- `ForcedCarrierCascadeData.forced_carrier_cascade_theorem`
- `ForcedCarrierProcessData.forced_carrier_process_theorem`
- `ForcedCarrierBoundaryData.forced_carrier_boundary_theorem`
- `ForcedCarrierCascadeProcessData.forced_carrier_cascade_process_theorem`
- `ForcedCarrierCascadeBoundaryData.forced_carrier_cascade_boundary_theorem`

Focused note: [`docs/fukushima-correspondence.md`](fukushima-correspondence.md).
Protocol: [`docs/protocol.md`](protocol.md).

## Boundary Problem

The contract answers a boundary question for reduction. Fix a proposed split `1 = P + Q`. The
question is whether the retained sector remains a licensed object once the omitted sector is
eliminated and fed back through the Schur term.

`gamma` measures control on the omitted side of the boundary. `lambda` measures leakage across that
boundary. The ratio

$$
\chi = \left(\frac{\lambda}{\gamma}\right)^2
$$

is therefore not a heuristic score. It is the criterion deciding whether the proposed reduced
description stays within control.

## Public Regime Witnesses

The three branches are exposed as public proof artifacts in
`OperatorEstimates/Examples/Regimes.lean`:

- `quarterTurn_preAdmissible`
- `stable_subcritical`
- `unstable_supercritical`

These witness the exact classification trichotomy on explicit finite-dimensional systems.

The exact quotient layer is exposed in `OperatorEstimates/Examples/FuchsianQuotient.lean`, and the
symbolic exact-reduction witness remains public in `OperatorEstimates/Examples/FischerProjection.lean`.
The Fuchsian module now includes the actual-quotient Markov witness, the quotient-side
generator, realized effective semigroup, and process layers, and the killed-half-line boundary classification on the
forced quotient.

## Forcing Order

Bounded Schur licensing is not primary in the public stack. It is evaluated only after exact
quotient licensing. If no exact descended form is licensed on the proposed quotient, then no
descended realized effective semigroup, Hunt realization, or boundary object is in scope on that carrier,
and no bounded Schur question is in scope. If an exact descended form is licensed, then the quotient
carrier is fixed first and the quotient-side exact layer enters only there.
Only on that forced carrier does the bounded admissibility contract apply, with `chi` deciding
whether the Schur return is licensed.

The new bridge layer makes that order explicit inside the repo: exact licensing first, then the
bounded Schur setup and the hierarchy-indexed cascade theorems on that same forced carrier.
The process and boundary layers are then kept downstream of that same forced-carrier interface.

## Stack

| Repository | Role | Language |
|---|---|---|
| [`operator-estimates`](https://github.com/EmetLabsReal/operator-estimates) | Proof layer. Defines `ClosedSemiboundedForm`, exact quotient descent data, `EffectiveReductionSetup`, `AdmittedReductionSetup`, `StaticAdmissible`, `PreAdmissible`, `Subcritical`, `Supercritical`. Proves exact quotient licensing, bounded reduction, threshold activation, boundary closure, boundary obstruction. | Lean 4 |
| [`QuantOE`](https://github.com/EmetLabsReal/QuantOE) | Numeric certification engine + domain instantiations (QKD, GR, phonon, FCA). Matrix + partition → regime classification + effective matrix. | Rust + Python |

## Dependencies

```
operator-estimates
└── QuantOE
    └── quantoe.domains.{qkd, gr, phonon, fca}
```

The public contract is carried by these two repositories.

## Extension Criterion

The contract does not depend on domain semantics. It applies exactly to problems that supply:

- a retained/omitted partition
- omitted-sector control `gamma`
- cross-sector coupling `lambda`

This is the shared form behind the current QKD, GR, phonon, and FCA instantiations, and the same
form governs graph coarsening, neural layer or block reduction, and model compression when those
systems expose a concrete split with computable control/coupling bounds.

## Scope Boundary

The contract certifies a given partition and nothing beyond it. It does not discover the right
partition, and it does not construct a replacement reduction when `chi >= 1`. Those questions
remain external to the present theorem surface.

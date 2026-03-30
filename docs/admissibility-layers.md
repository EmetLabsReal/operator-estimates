# Admissibility Layers

`OperatorEstimates` studies admissibility-obstruction for effective operators of the form

$$
H_{\mathrm{eff}} = P H P - P H Q R_{\mathrm{inv}} Q H P.
$$

The central issue is the boundary problem for reduction: whether a retained sector remains licensed
after the omitted sector is eliminated and returned through the Schur term.

## Effective Operator

The two operator terms are:

- `P H P`: retained block
- `P H Q Rinv Q H P`: omitted-sector return term

`EffectiveReductionSetup` is the typed object that provides the data needed to define and control
this operator.

## Layer Split

### 0. Exact quotient licensing

Before any Schur reduction, the exact layer asks whether a proposed quotient is licensed at all.

At this layer, the exact invariant is a closed semibounded form. The quotient is licensed when the
form descends exactly to the retained quotient carrier. If proper discontinuity fails and
accumulation persists, no exact descended form is licensed on the proposed quotient.
On the actual quotient carrier, exact pullback fixes the descended Markov energy uniquely, and the
descended generator is then unique as well. At the next exact tier, the public theorem surface
places the quotient-side generator, realized effective semigroup, Hunt realization, and boundary
capacity/trace package on that forced carrier. Exact
obstruction blocks every lower layer.

The repo now also exposes the handoff point explicitly: once the exact carrier is forced, bounded
Schur data and the hierarchy-indexed cascade endpoint theorems are attached only there. The
bridge objects are `ForcedCarrierReductionData` and `ForcedCarrierCascadeData`.

Below the same handoff, the public process and boundary objects are kept on that forced carrier as
downstream layers. The single-scale bridge objects there are
`ForcedCarrierProcessData` and `ForcedCarrierBoundaryData`, and the hierarchy-indexed cascade
bridge objects are `ForcedCarrierCascadeProcessData` and `ForcedCarrierCascadeBoundaryData`.

This is the Fukushima correspondence layer carried by `OperatorEstimates.Core.ClosedForms` and
`OperatorEstimates.Reduction.FormDescent`.

### 1. Static admissibility

The static layer asks whether explicit sector data are strong enough to build an
`AdmittedReductionSetup`, equivalently whether the candidate operator satisfies
`StaticAdmissible`.

That setup packages:

- a proposed sectorization `1 = P + Q`
- bounded cross-sector couplings
- omitted-sector control through the inverse/coercivity bundle

### 2. Subcritical regime

Once a valid setup exists, the derived parameter

$$
\chi = \left(\frac{\lambda}{\gamma}\right)^2
$$

and the reduction scale

$$
\delta = \frac{\lambda^2}{\gamma}
$$

measure the regime.

At this layer, the public regime predicates are `Subcritical cfg` and `Supercritical cfg`.

At this layer:

- `Subcritical cfg` iff `χ < 1`, iff `λ < γ`, iff `δ < γ`
- `Supercritical cfg` iff `1 ≤ χ`, iff `γ ≤ δ`

`χ` is evaluated only after a valid setup exists. It is not a condition for admissibility; it is
a regime filter applied to an already-admissible setup.

### 3. Asymptotic admissibility

The asymptotic layer asks whether admissibility persists along a family.

In the public stack, this layer is carried by scale-indexed budget control in
`OperatorEstimates.Reduction.Cascade` together with endpoint transport in
`OperatorEstimates.Reduction.HierarchyEndpoint`.

### 4. Endpoint closure and obstruction

The endpoint layer asks whether closure follows from a typed rigidity implication, or whether
deterministic saturation obstructs that closure.

This is the boundary pair:

- `boundary_closure_theorem`
- `boundary_obstruction_theorem`

## Classification (Reduction Regimes)

Fix a proposed sectorization `(P, Q)`. Any candidate system on that split falls into exactly one of the
following regimes:

1. **Pre-admissible obstruction**  
   No admitted reduction setup exists on the chosen split. Equivalently, the candidate operator is
   `PreAdmissible`, so no `χ` regime is evaluated.

2. **Admissible but supercritical**  
   A valid reduction setup exists, and the omitted-sector return scale satisfies `γ ≤ δ`.

3. **Admissible and subcritical**  
   A valid reduction setup exists, and the omitted-sector return scale satisfies `δ < γ`.

## Concrete Realizations

These branches are exhibited in the public stack through:

- `OperatorEstimates.Examples.FuchsianQuotient` — exact quotient licensing and obstruction
  witnesses for the exact form layer, together with actual-quotient Markov uniqueness,
  quotient-side generator/effective-semigroup/process layers, and killed-half-line boundary classification
- `OperatorEstimates.Examples.FischerProjection` — exact symbolic reduction witness by preserved
  orientation sign
- `OperatorEstimates.Examples.Regimes` — explicit finite-dimensional public witnesses for
  pre-admissible, supercritical, and subcritical behavior on fixed splits
- `OperatorEstimates.Examples.ThresholdCrossing` — threshold-activated setup existence and explicit
  `chi` / `delta` consequences after crossing
- `OperatorEstimates.Examples.ToyInstantiation` — geometric decay, bounded cascade budget, and
  residual-gap survival under a summable scale budget
- `QuantOE` domain witnesses — finite-dimensional retained/omitted certifications for QKD, GR,
  phonon, and FCA under the same contract

## Boundary Conditions

The bounded reduction engine has the following exact boundary conditions:

1. **Supercritical regime** — when `χ ≥ 1`, residual gap survival is not guaranteed.
2. **Non-summable budget** — when `δ` is not summable, no finite total budget exists.
3. **Pre-admissible non-construction** — when no `EffectiveReductionSetup` can be constructed,
   the candidate is not in the classification domain.
4. **Asymptotic-only limit certification** — limit objects are certified only via `Tendsto`;
   no finite-stage realization theorems are present.
5. **External rigidity hypothesis** — closure requires an application-supplied rigidity
   implication that the framework does not provide.

## Extension Criterion

The same layered contract applies exactly when a system exposes:

- a concrete retained/omitted split
- a quantitative omitted-sector control floor
- a quantitative cross-sector coupling bound

That is the only structural requirement. The framework is indifferent to whether the underlying
system is a covariance model, a graph operator, a neural block decomposition, or another partitioned
operator family.

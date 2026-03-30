/-
  **OperatorEstimates** — library index (public re-exports).

  Public role:
  - an admissibility-obstruction calculus for effective operators
    `P H P - P H Q Rinv Q H P` from explicit sector data and coupling/coercivity bounds

  Public theorem spine:
  - **licensed_quotient_theorem** / **quotient_obstruction_theorem** — exact quotient licensing
    by descended closed forms, with obstruction when accumulation destroys proper discontinuity
  - **licensed_markov_quotient_theorem** / **descended_markov_energy_unique_theorem** /
    **descended_markov_generator_unique_theorem** — actual-quotient Markov descent, uniqueness
    of the descended energy, and uniqueness of the descended generator
  - **licensed_dirichlet_quotient_theorem** / **descended_dirichlet_generator_exists_theorem** /
    **descended_analytic_semigroup_exists_theorem** / **descended_hunt_process_exists_theorem** /
    **descended_capacity_and_trace_theorem** / **descended_boundary_realization_exists_theorem**
    / **descended_strong_markov_theorem** / **feller_boundary_classification_theorem** —
    actual-quotient Dirichlet descent together with quotient-side generator, realized
    effective semigroup, Hunt realization, and boundary package on the forced carrier
  - **ForcedCarrierReductionData.forced_carrier_bounded_reduction_theorem** /
    **ForcedCarrierCascadeData.forced_carrier_cascade_theorem** — exact-to-bounded handoff:
    once the quotient is licensed, the bounded Schur setup and cascade endpoint theorems are
    evaluated only on that forced carrier
  - **ForcedCarrierProcessData.forced_carrier_process_theorem** /
    **ForcedCarrierBoundaryData.forced_carrier_boundary_theorem** /
    **ForcedCarrierCascadeProcessData.forced_carrier_cascade_process_theorem** /
    **ForcedCarrierCascadeBoundaryData.forced_carrier_cascade_boundary_theorem** —
    downstream forcing: the public Hunt and boundary layers sit on the same forced carrier and
    the same realized effective semigroup/cascade interface
  - **EffectiveReductionSetup.bounded_reduction_theorem** — bounded reduction theorem:
    effective operator, Schur-scale error, residual gap survival under `chi < 1`, and locality
    from supplied complement decay
  - **Constitutive.ThresholdDomain.threshold_to_reduction_theorem** — constitutive
    threshold-activation theorem
  - **boundary_closure_theorem** / **boundary_obstruction_theorem** — the endpoint boundary
    pair, centered on `Cascade.conditional_regularity_from_rigidity` and
    `NoGo.no_go_saturation`

  Public entry routes:
  - **Constitutive.ThresholdDomain** — threshold-dependent admissibility
  - **Generators.BoundedDecomposition** — bounded `H = localOp + jump + killing`
  - **Instantiations.Steklov** — canonical concrete path `H = T + B`
  - **Instantiations.SelfAdjointSpectralInduction.fromGap** — finite-dimensional complement gap
  - **Instantiations.Oseen** / **ShiftedResolvent** / **SpectralCutoff** — named alternative
    routes into the same engine

  The lower layers remain support infrastructure:
  - **Reduction** — exact form descent, bounded theorem spine, block reduction, coercivity
    constructors, cascade, no-go, hierarchy endpoint
  - **Hierarchy** — scale-family carriers and observables
  - **Core** — closed forms, transfer, perturbation, quadratic forms, algebraic splitting,
    coercive inverses

  Boundary:
  - geometry, semantics, and application-specific rigidity mechanisms remain external because
    they are not part of the bounded-operator theorem surface formalized here

  **Examples** are *not* imported here.
  Public example modules:
  - **Examples.FuchsianQuotient**
  - **Examples.FischerProjection**
  - **Examples.ToyInstantiation**
  - **Examples.ThresholdCrossing**
  - **Examples.Regimes**
-/

-- Core
import OperatorEstimates.Core.ClosedForms
import OperatorEstimates.Core.DirichletForms
import OperatorEstimates.Core.Transfer
import OperatorEstimates.Core.Perturbation
import OperatorEstimates.Core.QuadraticForms
import OperatorEstimates.Core.Splitting
import OperatorEstimates.Core.CoerciveInverse
import OperatorEstimates.Core.CoerciveInverseRangeQ

-- Generators
import OperatorEstimates.Generators.BoundedDecomposition

-- Constitutive
import OperatorEstimates.Constitutive.ThresholdDomain

-- Reduction
import OperatorEstimates.Reduction.FormDescent
import OperatorEstimates.Reduction.SemigroupCorrespondence
import OperatorEstimates.Reduction.ForcedCarrierBridge
import OperatorEstimates.Reduction.ProcessBoundaryBridge
import OperatorEstimates.Reduction.BlockReduction
import OperatorEstimates.Reduction.EffectiveFromCoercivity
import OperatorEstimates.Reduction.TheoremSpine
import OperatorEstimates.Reduction.Cascade
import OperatorEstimates.Reduction.NoGo
import OperatorEstimates.Reduction.HierarchyEndpoint

-- Hierarchy
import OperatorEstimates.Hierarchy.ScaleHierarchy

-- Instantiations
import OperatorEstimates.Instantiations.SpectralCutoff
import OperatorEstimates.Instantiations.Steklov
import OperatorEstimates.Instantiations.ShiftedResolvent
import OperatorEstimates.Instantiations.Oseen
import OperatorEstimates.Instantiations.SelfAdjointSpectralInduction

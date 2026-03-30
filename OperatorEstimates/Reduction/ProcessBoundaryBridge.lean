import OperatorEstimates.Reduction.ForcedCarrierBridge

/-!
  **Reduction / process-boundary bridge.** Downstream forcing layer from the forced carrier and
  realized effective semigroup to the public process and boundary objects.

  This module records the public forcing order:

  - exact license fixes the carrier;
  - the realized effective semigroup is attached there;
  - quasi-regularity places the public Hunt realization on that same carrier;
  - regularity and 1D specialization place the public boundary package on that same carrier.
-/

namespace OperatorEstimates

open scoped InnerProductSpace Topology

noncomputable section

section ProcessBridge

variable {Γ : Type*} {E : Type*} [SMul Γ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Forced-carrier process data: the exact-to-bounded bridge together with quasi-regularity on the
licensed descended quotient. -/
structure ForcedCarrierProcessData where
  bridge : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)
  hqr : (ForcedCarrierReductionData.descendedForm bridge).quotientForm.quasiRegular

namespace ForcedCarrierProcessData

/-- The descended Dirichlet form used by the process bridge. -/
abbrev descendedForm
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :=
  ForcedCarrierReductionData.descendedForm data.bridge

/-- The realized effective semigroup remains prior to the process layer. -/
theorem effective_semigroup_exists
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (DescendedAnalyticSemigroup data.bridge.exactSetup.form
      data.bridge.exactSetup.rel data.descendedForm) :=
  ForcedCarrierReductionData.exact_semigroup_exists data.bridge

/-- Public Hunt realization on the forced carrier. -/
theorem hunt_process_exists
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (DescendedHuntProcess data.bridge.exactSetup.form
      data.bridge.exactSetup.rel data.descendedForm) :=
  descended_hunt_process_exists_theorem data.descendedForm data.hqr

/-- The process transition is exactly the realized effective semigroup evolution. -/
theorem transition_matches_effective_semigroup
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :
    (descended_hunt_process data.descendedForm data.hqr).transition =
      (descended_analytic_semigroup data.descendedForm).evolve :=
  descended_hunt_process_transition_exact data.descendedForm data.hqr

/-- The public strong Markov statement remains downstream of the realized semigroup carrier. -/
theorem strong_markov
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :
    (descended_hunt_process data.descendedForm data.hqr).strongMarkov :=
  descended_strong_markov_theorem data.hqr

/-- Exact license, realized semigroup, Hunt realization, and strong Markov all sit on the same
forced carrier. -/
theorem forced_carrier_process_theorem
    (data : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (QuotientDescendedDirichletForm data.bridge.exactSetup.form data.bridge.exactSetup.rel) ∧
      Nonempty (DescendedAnalyticSemigroup data.bridge.exactSetup.form
        data.bridge.exactSetup.rel data.descendedForm) ∧
      Nonempty (DescendedHuntProcess data.bridge.exactSetup.form
        data.bridge.exactSetup.rel data.descendedForm) ∧
      ((descended_hunt_process data.descendedForm data.hqr).transition =
        (descended_analytic_semigroup data.descendedForm).evolve) ∧
      (descended_hunt_process data.descendedForm data.hqr).strongMarkov := by
  refine ⟨ForcedCarrierReductionData.exact_license data.bridge,
    effective_semigroup_exists data, hunt_process_exists data, ?_, strong_markov data⟩
  exact transition_matches_effective_semigroup data

end ForcedCarrierProcessData

end ProcessBridge

section BoundaryBridge

variable {Γ : Type*} {E : Type*} [SMul Γ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Forced-carrier boundary data: the process bridge together with regularity and a 1D
specialization. -/
structure ForcedCarrierBoundaryData where
  process : ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F)
  hreg : (ForcedCarrierProcessData.descendedForm process).quotientForm.regular
  spec : FellerBoundarySpecialization

namespace ForcedCarrierBoundaryData

/-- The descended Dirichlet form used by the boundary bridge. -/
abbrev descendedForm
    (data : ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F)) :=
  ForcedCarrierProcessData.descendedForm data.process

/-- Public capacity/trace package on the forced carrier. -/
noncomputable def capacityAndTrace
    (data : ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F)) :
    CapacityAndTrace BoundaryEndpoint :=
  descended_capacity_and_trace_theorem data.descendedForm data.hreg

/-- Public boundary realization on the forced carrier. -/
theorem boundary_exists
    (data : ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (BoundaryRealization data.process.bridge.exactSetup.form
      data.process.bridge.exactSetup.rel data.descendedForm) :=
  descended_boundary_realization_exists_theorem data.descendedForm data.hreg data.spec

/-- The 1D taxonomy remains the specialization of the forced-carrier boundary realization. -/
noncomputable def taxonomy
    (data : ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F)) :
    BoundaryTaxonomy :=
  feller_boundary_classification_theorem data.hreg data.spec

/-- The boundary layer sits downstream of exact license, realized semigroup, and process
realization on one forced carrier. -/
theorem forced_carrier_boundary_theorem
    (data : ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (QuotientDescendedDirichletForm data.process.bridge.exactSetup.form
      data.process.bridge.exactSetup.rel) ∧
      Nonempty (DescendedHuntProcess data.process.bridge.exactSetup.form
        data.process.bridge.exactSetup.rel data.descendedForm) ∧
      Nonempty (BoundaryRealization data.process.bridge.exactSetup.form
        data.process.bridge.exactSetup.rel data.descendedForm) := by
  refine ⟨ForcedCarrierReductionData.exact_license data.process.bridge, ?_, boundary_exists data⟩
  exact ForcedCarrierProcessData.hunt_process_exists data.process

end ForcedCarrierBoundaryData

end BoundaryBridge

section CascadeCompatibility

variable {Γ : Type*} {E : Type*} [SMul Γ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*}

/-- Cascade-level process data: the hierarchy-indexed exact-to-bounded bridge together with
quasi-regularity on the licensed descended quotient. -/
structure ForcedCarrierCascadeProcessData where
  cascade : ForcedCarrierCascadeData (Γ := Γ) (E := E) (F := F) (ι := ι)
  hqr : (ForcedCarrierReductionData.descendedForm cascade.bridge).quotientForm.quasiRegular

namespace ForcedCarrierCascadeProcessData

/-- The underlying forced-carrier process bridge. -/
def process
    (data : ForcedCarrierCascadeProcessData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    ForcedCarrierProcessData (Γ := Γ) (E := E) (F := F) where
  bridge := data.cascade.bridge
  hqr := data.hqr

/-- On the cascade carrier, the exact license and the hierarchy endpoint remain prior to the
public Hunt realization. -/
theorem forced_carrier_cascade_process_theorem
    (data : ForcedCarrierCascadeProcessData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    Nonempty (QuotientDescendedDirichletForm data.cascade.bridge.exactSetup.form
      data.cascade.bridge.exactSetup.rel) ∧
      ((Hierarchy.strongly_local_regime data.cascade.S ∧
          Hierarchy.suppression_regime data.cascade.S ∧
          (∀ K, ∀ x : F,
            (data.cascade.μ - data.cascade.B) * ‖x‖ ^ 2 ≤
              ⟪x, data.cascade.Hflow K x⟫_ℝ) ∧
          (∀ n,
            ‖(data.cascade.scaleData (data.cascade.chain.node n)).effectiveOperator -
                (data.cascade.scaleData (data.cascade.chain.node n)).decomp.P *
                  (data.cascade.scaleData (data.cascade.chain.node n)).H *
                  (data.cascade.scaleData (data.cascade.chain.node n)).decomp.P‖ ≤
              data.cascade.S.δ n))
        ∨ ¬ Hierarchy.strongly_local_regime data.cascade.S) ∧
      Nonempty (DescendedHuntProcess data.cascade.bridge.exactSetup.form
        data.cascade.bridge.exactSetup.rel
        (ForcedCarrierReductionData.descendedForm data.cascade.bridge)) ∧
      ((descended_hunt_process (ForcedCarrierReductionData.descendedForm data.cascade.bridge) data.hqr).transition =
        (descended_analytic_semigroup
          (ForcedCarrierReductionData.descendedForm data.cascade.bridge)).evolve) ∧
      (descended_hunt_process
        (ForcedCarrierReductionData.descendedForm data.cascade.bridge) data.hqr).strongMarkov := by
  refine ⟨ForcedCarrierCascadeData.exact_license data.cascade,
    ?_, ForcedCarrierProcessData.hunt_process_exists data.process, ?_,
    ForcedCarrierProcessData.strong_markov data.process⟩
  · exact (ForcedCarrierCascadeData.forced_carrier_cascade_theorem data.cascade).2
  · exact ForcedCarrierProcessData.transition_matches_effective_semigroup data.process

end ForcedCarrierCascadeProcessData

/-- Cascade-level boundary data: the hierarchy-indexed forced carrier, the public Hunt
realization, and regularity/1D specialization on that same carrier. -/
structure ForcedCarrierCascadeBoundaryData where
  process : ForcedCarrierCascadeProcessData (Γ := Γ) (E := E) (F := F) (ι := ι)
  hreg :
    (ForcedCarrierReductionData.descendedForm process.cascade.bridge).quotientForm.regular
  spec : FellerBoundarySpecialization

namespace ForcedCarrierCascadeBoundaryData

/-- The underlying forced-carrier boundary bridge. -/
def boundary
    (data : ForcedCarrierCascadeBoundaryData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    ForcedCarrierBoundaryData (Γ := Γ) (E := E) (F := F) where
  process := data.process.process
  hreg := data.hreg
  spec := data.spec

/-- On the cascade carrier, the public boundary package is downstream of exact licensing, the
hierarchy endpoint, and the realized Hunt process. -/
theorem forced_carrier_cascade_boundary_theorem
    (data : ForcedCarrierCascadeBoundaryData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    Nonempty (QuotientDescendedDirichletForm data.process.cascade.bridge.exactSetup.form
      data.process.cascade.bridge.exactSetup.rel) ∧
      ((Hierarchy.strongly_local_regime data.process.cascade.S ∧
          Hierarchy.suppression_regime data.process.cascade.S ∧
          (∀ K, ∀ x : F,
            (data.process.cascade.μ - data.process.cascade.B) * ‖x‖ ^ 2 ≤
              ⟪x, data.process.cascade.Hflow K x⟫_ℝ) ∧
          (∀ n,
            ‖(data.process.cascade.scaleData (data.process.cascade.chain.node n)).effectiveOperator -
                (data.process.cascade.scaleData (data.process.cascade.chain.node n)).decomp.P *
                  (data.process.cascade.scaleData (data.process.cascade.chain.node n)).H *
                  (data.process.cascade.scaleData (data.process.cascade.chain.node n)).decomp.P‖ ≤
              data.process.cascade.S.δ n))
        ∨ ¬ Hierarchy.strongly_local_regime data.process.cascade.S) ∧
      Nonempty (DescendedHuntProcess data.process.cascade.bridge.exactSetup.form
        data.process.cascade.bridge.exactSetup.rel
        (ForcedCarrierReductionData.descendedForm data.process.cascade.bridge)) ∧
      Nonempty (BoundaryRealization data.process.cascade.bridge.exactSetup.form
        data.process.cascade.bridge.exactSetup.rel
        (ForcedCarrierReductionData.descendedForm data.process.cascade.bridge)) := by
  refine ⟨ForcedCarrierCascadeData.exact_license data.process.cascade,
    ?_, ForcedCarrierProcessData.hunt_process_exists data.process.process, ?_⟩
  · exact (ForcedCarrierCascadeData.forced_carrier_cascade_theorem data.process.cascade).2
  · exact ForcedCarrierBoundaryData.boundary_exists data.boundary

end ForcedCarrierCascadeBoundaryData

end CascadeCompatibility

end

end OperatorEstimates

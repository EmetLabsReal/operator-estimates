import OperatorEstimates.Reduction.SemigroupCorrespondence
import OperatorEstimates.Reduction.HierarchyEndpoint
import OperatorEstimates.Generators.BoundedDecomposition

/-!
  **Reduction / forced carrier bridge.** Exact-to-bounded handoff on a carrier whose quotient has
  already been licensed upstream.

  This module does not claim that the bounded Schur data are derivable from the exact form axioms
  alone. It formalizes the public forcing order:

  - exact descent fixes the carrier first;
  - a bounded reduction setup is then attached on that forced carrier;
  - the existing bounded and cascade theorems apply only after that handoff.
-/

namespace OperatorEstimates

open Filter
open scoped InnerProductSpace Topology

noncomputable section

section SingleScale

variable {Γ : Type*} {E : Type*} [SMul Γ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Exact-to-bounded handoff on a forced carrier.

`realization` and `observable` record how the forced quotient carrier is seen inside the bounded
carrier used by the Schur engine. The exact layer remains prior: the bounded reduction data are
only interpreted after `hproper` licenses the quotient. -/
structure ForcedCarrierReductionData where
  exactSetup : QuotientDirichletFormDescentSetup Γ E
  hproper : exactSetup.action.properlyDiscontinuous
  realization : Quotient exactSetup.rel → F
  observable : F → ℝ
  observable_exact :
    ∀ q : Quotient exactSetup.rel,
      observable (realization q) =
        descended_dirichlet_generator (exactSetup.descend hproper) q
  reduction : Generators.BoundedDecomposition.GeneratorReductionData F

namespace ForcedCarrierReductionData

/-- The licensed descended Dirichlet form carried by the bridge. -/
def descendedForm
    (data : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)) :
    QuotientDescendedDirichletForm data.exactSetup.form data.exactSetup.rel :=
  data.exactSetup.descend data.hproper

/-- Exact licensing is prior in the bridge. -/
theorem exact_license
    (data : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (QuotientDescendedDirichletForm data.exactSetup.form data.exactSetup.rel) :=
  licensed_dirichlet_quotient_theorem data.exactSetup data.hproper

/-- The realized observable agrees with the exact descended generator on the forced quotient. -/
theorem observable_agrees_with_generator
    (data : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F))
    (q : Quotient data.exactSetup.rel) :
    data.observable (data.realization q) =
      descended_dirichlet_generator (descendedForm data) q :=
  data.observable_exact q

/-- Once the exact carrier is licensed, the realized effective semigroup is in scope there. -/
theorem exact_semigroup_exists
    (data : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (DescendedAnalyticSemigroup data.exactSetup.form data.exactSetup.rel (descendedForm data)) :=
  descended_analytic_semigroup_exists_theorem (descendedForm data)

/-- Exact licensing first, then the bounded Schur theorem on the forced carrier. -/
theorem forced_carrier_bounded_reduction_theorem
    (data : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)) :
    Nonempty (QuotientDescendedDirichletForm data.exactSetup.form data.exactSetup.rel) ∧
      Nonempty (DescendedAnalyticSemigroup data.exactSetup.form data.exactSetup.rel (descendedForm data)) ∧
      (∀ q : Quotient data.exactSetup.rel,
        data.observable (data.realization q) =
          descended_dirichlet_generator (descendedForm data) q) ∧
      ‖data.reduction.effectiveOperator -
          data.reduction.decomp.P * data.reduction.H * data.reduction.decomp.P‖ ≤
        data.reduction.setup.delta ∧
      (data.reduction.setup.chi < 1 →
        0 < data.reduction.setup.γ - data.reduction.setup.delta) := by
  refine ⟨exact_license data, exact_semigroup_exists data, ?_, ?_, ?_⟩
  · intro q
    exact observable_agrees_with_generator data q
  · exact data.reduction.error_bound_delta
  · intro hchi
    exact data.reduction.gap_survives_of_chi hchi

end ForcedCarrierReductionData

end SingleScale

section ScaleCascade

variable {Γ : Type*} {E : Type*} [SMul Γ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*}

/-- Scale-indexed exact-to-bounded handoff.

This packages the exact forced-carrier bridge together with the hierarchy-indexed data already
used by the cascade and endpoint layers. -/
structure ForcedCarrierCascadeData where
  bridge : ForcedCarrierReductionData (Γ := Γ) (E := E) (F := F)
  hierarchy : Hierarchy.ScaleHierarchy ι
  chain : Hierarchy.ScaleChain hierarchy
  scaleData : ι → Generators.BoundedDecomposition.GeneratorReductionData F
  Hflow : ℕ → (F →L[ℝ] F)
  S : Hierarchy.ScaleFamily
  μ : ℝ
  B : ℝ
  C : ℝ
  a : ℝ
  γ0 : ℝ
  ha : 0 < a
  hγ0 : 0 < γ0
  hδ_model : ∀ n, S.δ n = (scaleData (chain.node n)).setup.delta
  hstep : ∀ n, ‖Hflow (n + 1) - Hflow n‖ ≤ S.δ n
  hbudget : ∀ K, ∑ n ∈ Finset.range K, S.δ n ≤ B
  hcoercive : ∀ x : F, μ * ‖x‖ ^ 2 ≤ ⟪x, Hflow 0 x⟫_ℝ
  hΓ_nn : ∀ n, 0 ≤ S.Γ n
  hΓlocal_nn : ∀ n, 0 ≤ S.Γ_local n
  hΓjump_nn : ∀ n, 0 ≤ S.Γ_jump n
  hΓ_le : ∀ n, S.Γ n ≤ C * S.ratio n ^ 2
  hcase :
    Tendsto S.ratio atTop (nhds 0) ∨
      (Hierarchy.balanced_regime S ∧
        (∀ᶠ n in atTop, γ0 ≤ (scaleData (chain.node n)).setup.γ) ∧
        ∀ᶠ n in atTop,
          a * S.ratio n ^ 2 * (scaleData (chain.node n)).setup.γ ≤ S.Γ_jump n)

namespace ForcedCarrierCascadeData

/-- Exact licensing remains prior throughout the cascade. -/
theorem exact_license
    (data : ForcedCarrierCascadeData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    Nonempty (QuotientDescendedDirichletForm data.bridge.exactSetup.form data.bridge.exactSetup.rel) :=
  ForcedCarrierReductionData.exact_license data.bridge

/-- Exact-to-`chi` cascade bridge: once the quotient is licensed, the hierarchy-indexed cascade
and endpoint dichotomy are evaluated on the forced carrier. -/
theorem forced_carrier_cascade_theorem
    (data : ForcedCarrierCascadeData (Γ := Γ) (E := E) (F := F) (ι := ι)) :
    Nonempty (QuotientDescendedDirichletForm data.bridge.exactSetup.form data.bridge.exactSetup.rel) ∧
      ((Hierarchy.strongly_local_regime data.S ∧
          Hierarchy.suppression_regime data.S ∧
          (∀ K, ∀ x : F, (data.μ - data.B) * ‖x‖ ^ 2 ≤ ⟪x, data.Hflow K x⟫_ℝ) ∧
          (∀ n,
            ‖(data.scaleData (data.chain.node n)).effectiveOperator -
                (data.scaleData (data.chain.node n)).decomp.P *
                  (data.scaleData (data.chain.node n)).H *
                  (data.scaleData (data.chain.node n)).decomp.P‖ ≤
              data.S.δ n))
        ∨ ¬ Hierarchy.strongly_local_regime data.S) := by
  refine ⟨exact_license data, ?_⟩
  simpa [data.hδ_model] using
    HierarchyEndpoint.hierarchical_endpoint_locality_dichotomy
      data.hierarchy
      data.chain
      (fun i => (data.scaleData i).setup)
      data.Hflow
      data.S
      data.μ
      data.B
      data.C
      data.a
      data.γ0
      data.ha
      data.hγ0
      data.hδ_model
      data.hstep
      data.hbudget
      data.hcoercive
      data.hΓ_nn
      data.hΓlocal_nn
      data.hΓjump_nn
      data.hΓ_le
      data.hcase

end ForcedCarrierCascadeData

end ScaleCascade

end

end OperatorEstimates

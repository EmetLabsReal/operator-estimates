/- 
  **Reduction / hierarchy endpoint.** Thin integration layer for hierarchy-indexed endpoint
  conclusions.

  This file packages the local/jump split carried by `Hierarchy.ScaleFamily` with the existing
  reduction, cascade, and no-go machinery. The main result is a hierarchy-indexed endpoint
  locality dichotomy: ratio decay yields suppression and vanishing jump transfer, while a
  balanced jump scale obstructs strong locality.
-/
import OperatorEstimates.Reduction.BlockReduction
import OperatorEstimates.Reduction.Cascade
import OperatorEstimates.Reduction.NoGo

namespace OperatorEstimates.HierarchyEndpoint

open Filter
open scoped InnerProductSpace Topology

/-- Nonnegative local contribution forces the jump contribution to lie below the total
observable. -/
lemma jump_le_total
    (S : Hierarchy.ScaleFamily)
    (hΓlocal_nn : ∀ N, 0 ≤ S.Γ_local N) :
    ∀ N, S.Γ_jump N ≤ S.Γ N := by
  intro N
  have hdecomp := S.decomp N
  nlinarith [hΓlocal_nn N, hdecomp]

/-- Suppression of the total observable forces strong locality once the local/jump split is
nonnegative. -/
theorem strongly_local_of_suppression
    (S : Hierarchy.ScaleFamily)
    (hΓlocal_nn : ∀ N, 0 ≤ S.Γ_local N)
    (hΓjump_nn : ∀ N, 0 ≤ S.Γ_jump N)
    (hsupp : Hierarchy.suppression_regime S) :
    Hierarchy.strongly_local_regime S :=
  squeeze_zero hΓjump_nn (jump_le_total S hΓlocal_nn) hsupp

/-- The effective localization bound carried by `EffectiveReductionSetup`, read along a
hierarchy chain and recorded in the scale budget `δ`. -/
lemma chain_localization_bound
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Hierarchy.ScaleHierarchy ι}
    (chain : Hierarchy.ScaleChain H)
    (setup : ι → EffectiveReductionSetup ℝ E)
    (S : Hierarchy.ScaleFamily)
    (hδ_model : ∀ n, S.δ n = (setup (chain.node n)).lam ^ 2 / (setup (chain.node n)).γ) :
    ∀ n,
      ‖(setup (chain.node n)).effectiveOperator
          - (setup (chain.node n)).decomp.P * (setup (chain.node n)).H *
              (setup (chain.node n)).decomp.P‖ ≤ S.δ n := by
  intro n
  simpa [hδ_model n] using (setup (chain.node n)).error_bound

/-- Hierarchy-indexed endpoint locality dichotomy.

If the cascade ratio decays, then the total observable suppresses and the jump component
vanishes, so the endpoint is strongly local. If instead the scale data stay in a balanced
nondegenerate jump regime, then strong locality is obstructed. In both cases the per-scale
effective localization and cascade gap control come from the existing reduction stack. -/
theorem hierarchical_endpoint_locality_dichotomy
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Hierarchy.ScaleHierarchy ι)
    (chain : Hierarchy.ScaleChain H)
    (setup : ι → EffectiveReductionSetup ℝ E)
    (Hflow : ℕ → (E →L[ℝ] E))
    (S : Hierarchy.ScaleFamily)
    (μ B C a γ0 : ℝ)
    (ha : 0 < a)
    (hγ0 : 0 < γ0)
    (hδ_model : ∀ n, S.δ n = (setup (chain.node n)).lam ^ 2 / (setup (chain.node n)).γ)
    (hstep : ∀ n, ‖Hflow (n + 1) - Hflow n‖ ≤ S.δ n)
    (hbudget : ∀ K, ∑ n ∈ Finset.range K, S.δ n ≤ B)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, Hflow 0 x⟫_ℝ)
    (hΓ_nn : ∀ n, 0 ≤ S.Γ n)
    (hΓlocal_nn : ∀ n, 0 ≤ S.Γ_local n)
    (hΓjump_nn : ∀ n, 0 ≤ S.Γ_jump n)
    (hΓ_le : ∀ n, S.Γ n ≤ C * S.ratio n ^ 2)
    (hcase :
      Tendsto S.ratio atTop (nhds 0) ∨
      (Hierarchy.balanced_regime S ∧
        (∀ᶠ n in atTop, γ0 ≤ (setup (chain.node n)).γ) ∧
        ∀ᶠ n in atTop, a * S.ratio n ^ 2 * (setup (chain.node n)).γ ≤ S.Γ_jump n)) :
    (Hierarchy.strongly_local_regime S ∧
      Hierarchy.suppression_regime S ∧
      (∀ K, ∀ x : E, (μ - B) * ‖x‖ ^ 2 ≤ ⟪x, Hflow K x⟫_ℝ) ∧
      (∀ n,
        ‖(setup (chain.node n)).effectiveOperator
            - (setup (chain.node n)).decomp.P * (setup (chain.node n)).H *
                (setup (chain.node n)).decomp.P‖ ≤ S.δ n))
    ∨ ¬ Hierarchy.strongly_local_regime S := by
  have hgap :
      ∀ K, ∀ x : E, (μ - B) * ‖x‖ ^ 2 ≤ ⟪x, Hflow K x⟫_ℝ :=
    Cascade.cascade_gap_survives Hflow S.δ μ B hstep hcoercive hbudget
  have hloc :
      ∀ n,
        ‖(setup (chain.node n)).effectiveOperator
            - (setup (chain.node n)).decomp.P * (setup (chain.node n)).H *
                (setup (chain.node n)).decomp.P‖ ≤ S.δ n :=
    chain_localization_bound chain setup S hδ_model
  rcases hcase with hratio | ⟨hbal, hgamma_lower, hjump_lower⟩
  · have hsupp : Hierarchy.suppression_regime S :=
      Cascade.suppression_regime_of_ratio S C hΓ_nn hΓ_le hratio
    have hstrong : Hierarchy.strongly_local_regime S :=
      strongly_local_of_suppression S hΓlocal_nn hΓjump_nn hsupp
    exact Or.inl ⟨hstrong, hsupp, hgap, hloc⟩
  · exact Or.inr <|
      NoGo.not_strongly_local_of_balanced_jump_family
        S (fun n => (setup (chain.node n)).γ) a γ0 ha hγ0 hbal hgamma_lower hjump_lower

end OperatorEstimates.HierarchyEndpoint

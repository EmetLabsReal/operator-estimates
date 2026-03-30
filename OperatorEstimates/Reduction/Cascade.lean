/-
  **Reduction / cascade.** Scale-indexed stability, budget failure, suppression dichotomy,
  conditional decay, balance estimates, and summable-budget infrastructure. Builds on Core
  transfer and perturbation tools.
-/
import OperatorEstimates.Hierarchy.ScaleHierarchy
import OperatorEstimates.Core.Transfer
import OperatorEstimates.Core.Perturbation
import Mathlib.Topology.Order.Compact

namespace OperatorEstimates.Cascade

open Filter ContinuousLinearMap
open scoped InnerProductSpace

/-! ### Scale Flow

This file studies scale-indexed transfer through `Hierarchy.ScaleFamily`. Persistence corresponds
to nonvanishing transfer across scales; suppression corresponds to collapse of the transfer
observable `Γ`; balance lemmas describe the transition between active cascade and projected or
localized behavior.
-/

/-! ### Cascade Side: budgets and persistence -/
section CascadeStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cumulative instability budget spent through stage `K`. -/
def spentBudget (δ : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range K, δ n

/-- The residual coercive window after spending budget through stage `K`. -/
def residualWindow (μ : ℝ) (δ : ℕ → ℝ) (K : ℕ) : ℝ :=
  μ - spentBudget δ K

/-- The total instability budget of a summable cascade. -/
noncomputable def totalBudget (δ : ℕ → ℝ) : ℝ :=
  ∑' n, δ n

/-- Nonnegative step budgets accumulate monotonically. -/
theorem spentBudget_monotone
    (δ : ℕ → ℝ)
    (hδ_nn : ∀ n, 0 ≤ δ n) :
    Monotone (spentBudget δ) := by
  intro m n hmn
  induction hmn with
  | refl =>
      rfl
  | @step n hmn ih =>
      calc
        spentBudget δ m ≤ spentBudget δ n := ih
        _ ≤ spentBudget δ n + δ n := by
          linarith [hδ_nn n]
        _ = spentBudget δ (n + 1) := by
          simp [spentBudget, Finset.sum_range_succ]

/-- The residual window can only decrease as instability spends budget forward. -/
theorem ratchet_exhaustion
    (μ : ℝ) (δ : ℕ → ℝ)
    (hδ_nn : ∀ n, 0 ≤ δ n) :
    Antitone (residualWindow μ δ) := by
  intro m n hmn
  dsimp [residualWindow]
  have hspent : spentBudget δ m ≤ spentBudget δ n :=
    spentBudget_monotone δ hδ_nn hmn
  linarith

/-- Cumulative operator perturbation bound. -/
theorem cascade_perturbation_bound
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N) (K : ℕ) :
    ‖H K - H 0‖ ≤ ∑ N ∈ Finset.range K, δ N := by
  induction K with
  | zero => simp
  | succ K ih =>
    calc ‖H (K + 1) - H 0‖
        = ‖(H (K + 1) - H K) + (H K - H 0)‖ := by congr 1; abel
      _ ≤ ‖H (K + 1) - H K‖ + ‖H K - H 0‖ := norm_add_le _ _
      _ ≤ δ K + ∑ N ∈ Finset.range K, δ N := add_le_add (hδ K) ih
      _ = ∑ N ∈ Finset.range (K + 1), δ N := by rw [Finset.sum_range_succ]; ring

/-- Uniform cumulative bound. -/
theorem cascade_flow_stable
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (S : ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hS : ∀ K, ∑ N ∈ Finset.range K, δ N ≤ S) :
    ∀ K, ‖H K - H 0‖ ≤ S :=
  fun K => le_trans (cascade_perturbation_bound H δ hδ K) (hS K)

/-- Cascaded Rayleigh quotient bound. -/
theorem cascade_rayleigh_bound
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (x : E) (hx : ‖x‖ = 1) (K : ℕ) :
    |⟪x, H K x⟫_ℝ - ⟪x, H 0 x⟫_ℝ| ≤ ∑ N ∈ Finset.range K, δ N :=
  rayleigh_perturbation (H K) (H 0) x _ hx (cascade_perturbation_bound H δ hδ K)

/-- Cascaded coercivity bound. -/
theorem cascade_coercivity_bound
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ : ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ) (K : ℕ) :
    ∀ x : E, (μ - ∑ N ∈ Finset.range K, δ N) * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ :=
  coercivity_perturbation (H K) (H 0) μ _ hcoercive
    (cascade_perturbation_bound H δ hδ K)

/-- Cascaded coercivity bound stated using `residualWindow`. -/
theorem cascade_gap_survives_residualWindow
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ : ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ) :
    ∀ K, ∀ x : E, residualWindow μ δ K * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ := by
  intro K x
  simpa [residualWindow, spentBudget] using cascade_coercivity_bound H δ μ hδ hcoercive K x

/-- Gap survival through the cascade. -/
theorem cascade_gap_survives
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ S : ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ)
    (hS : ∀ K, ∑ N ∈ Finset.range K, δ N ≤ S) :
    ∀ K, ∀ x : E, (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ := by
  intro K x
  have h := cascade_coercivity_bound H δ μ hδ hcoercive K x
  nlinarith [hS K, sq_nonneg ‖x‖]

/-- Cascade dichotomy: gap survives or budget exhausted. -/
theorem cascade_dichotomy
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ S : ℝ)
    (hδ : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ)
    (hS : ∀ K, ∑ N ∈ Finset.range K, δ N ≤ S) :
    (0 < μ - S ∧ ∀ (K : ℕ) (x : E), (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ) ∨
    μ ≤ S := by
  by_cases h : S < μ
  · exact Or.inl ⟨by linarith, cascade_gap_survives H δ μ S hδ hcoercive hS⟩
  · exact Or.inr (by linarith)

end CascadeStability

/-! ### Budget Failure -/
section BudgetFailure

/-- Partial sums unbounded from eventually positive terms. -/
theorem partial_sums_unbounded_of_eventually_positive
    (a : ℕ → ℝ) (c : ℝ) (N₀ : ℕ)
    (hc : 0 < c) (ha : ∀ n, N₀ ≤ n → c ≤ a n) :
    Tendsto (fun K => ∑ n ∈ Finset.range K, a n) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  set S₀ := ∑ n ∈ Finset.range N₀, a n
  obtain ⟨M, hM⟩ := exists_nat_gt ((b - S₀) / c + 1)
  use N₀ + M
  intro K hK
  have hKN' : N₀ ≤ K := by omega
  have hsplit : ∑ n ∈ Finset.range K, a n =
      S₀ + ∑ n ∈ Finset.Ico N₀ K, a n := by
    rw [← Finset.sum_range_add_sum_Ico a hKN']
  rw [hsplit]
  have htail : (K - N₀ : ℝ) * c ≤ ∑ n ∈ Finset.Ico N₀ K, a n := by
    have hcard : (Finset.Ico N₀ K).card = K - N₀ := Nat.card_Ico N₀ K
    calc (K - N₀ : ℝ) * c
        = ↑(K - N₀) * c := by push_cast [Nat.cast_sub hKN']; ring
      _ = ↑(Finset.Ico N₀ K).card * c := by rw [hcard]
      _ = ∑ _n ∈ Finset.Ico N₀ K, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.Ico N₀ K, a n :=
          Finset.sum_le_sum fun n hn => ha n (Finset.mem_Ico.mp hn).1
  have hKM : (K - N₀ : ℝ) ≥ M := by
    have : K - N₀ ≥ M := by omega
    exact_mod_cast this
  have : (K - N₀ : ℝ) * c > ((b - S₀) / c + 1) * c := by
    have := lt_of_lt_of_le hM hKM; nlinarith
  have : ((b - S₀) / c + 1) * c > b - S₀ := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hc)]; linarith
  linarith

/-- Finite budgets fail under persistent perturbation. -/
theorem finite_budgets_fail
    (δ : ℕ → ℝ) (c : ℝ) (N₀ : ℕ)
    (hc : 0 < c) (hδ : ∀ n, N₀ ≤ n → c ≤ δ n) :
    ¬ ∃ S, ∀ K, ∑ n ∈ Finset.range K, δ n ≤ S := by
  intro ⟨S, hS⟩
  have h_unbounded := partial_sums_unbounded_of_eventually_positive δ c N₀ hc hδ
  have hev := (tendsto_atTop.mp h_unbounded) (S + 1)
  obtain ⟨K, hK⟩ := hev.exists
  linarith [hS K]

end BudgetFailure

/-! ### Scale Flow: persistence vs suppression -/
section Dichotomy

/-- Cascade alternative: ratio vanishes or persists. -/
theorem cascade_alternative
    (Γ ratio : ℕ → ℝ) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2) :
    (Tendsto ratio atTop (nhds 0) ∧ Tendsto Γ atTop (nhds 0)) ∨
    ¬ Tendsto ratio atTop (nhds 0) := by
  by_cases h : Tendsto ratio atTop (nhds 0)
  · exact Or.inl ⟨h, tendsto_zero_of_le_const_mul_sq Γ ratio C hΓ_nn hΓ_le h⟩
  · exact Or.inr h

/-- Persistent lower bound forces non-suppression. -/
theorem persistent_lower_bound_forces_nonsuppression
    (Γ ratio : ℕ → ℝ) (C c₀ : ℝ) (hc₀ : 0 < c₀)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2)
    (hΓ_lower : ∀ N, c₀ ≤ Γ N) :
    ¬ Tendsto ratio atTop (nhds 0) := by
  intro h
  have hzero := tendsto_zero_of_le_const_mul_sq Γ ratio C hΓ_nn hΓ_le h
  have hev := hzero (Iio_mem_nhds hc₀)
  rw [Filter.mem_map, Filter.mem_atTop_sets] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  have : Γ N₀ < c₀ := Set.mem_Iio.mp (hN₀ N₀ le_rfl)
  linarith [hΓ_lower N₀]

/-- Persistent lower bound (eventually). -/
theorem persistent_lower_bound_eventually_forces_nonsuppression
    (Γ ratio : ℕ → ℝ) (C c₀ : ℝ) (hc₀ : 0 < c₀)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2)
    (hΓ_lower : ∀ᶠ N in atTop, c₀ ≤ Γ N) :
    ¬ Tendsto ratio atTop (nhds 0) := by
  intro h_supp
  have h_zero := tendsto_zero_of_le_const_mul_sq Γ ratio C hΓ_nn hΓ_le h_supp
  have hev_small := h_zero (Iio_mem_nhds hc₀)
  rw [Filter.mem_map] at hev_small
  have hev_both := hΓ_lower.and hev_small
  obtain ⟨N₀, hge, hlt⟩ := hev_both.exists
  exact absurd (Set.mem_Iio.mp hlt) (not_lt.mpr hge)

/-- Eventual persistence of the transfer observable places a scale family in the cascade
regime. -/
theorem cascade_regime_of_persistence
    (S : Hierarchy.ScaleFamily) (c₀ : ℝ)
    (hc₀ : 0 < c₀)
    (hΓ_lower : ∀ᶠ N in atTop, c₀ ≤ S.Γ N) :
    Hierarchy.cascade_regime S := by
  intro hzero
  have hsmall : ∀ᶠ N in atTop, S.Γ N < c₀ := by
    simpa using hzero (Iio_mem_nhds hc₀)
  rcases (hΓ_lower.and hsmall).exists with ⟨N, hge, hlt⟩
  linarith

/-- Ratio collapse places a scale family in the suppression regime. -/
theorem suppression_regime_of_ratio
    (S : Hierarchy.ScaleFamily) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ S.Γ N)
    (hΓ_le : ∀ N, S.Γ N ≤ C * S.ratio N ^ 2)
    (hratio : Tendsto S.ratio atTop (nhds 0)) :
    Hierarchy.suppression_regime S :=
  tendsto_zero_of_le_const_mul_sq S.Γ S.ratio C hΓ_nn hΓ_le hratio

/-- Scale-family wrapper for the cascade alternative. -/
theorem scale_transition_dichotomy
    (S : Hierarchy.ScaleFamily) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ S.Γ N)
    (hΓ_le : ∀ N, S.Γ N ≤ C * S.ratio N ^ 2) :
    (Tendsto S.ratio atTop (nhds 0) ∧ Hierarchy.suppression_regime S) ∨
    ¬ Tendsto S.ratio atTop (nhds 0) := by
  simpa [Hierarchy.suppression_regime] using
    cascade_alternative S.Γ S.ratio C hΓ_nn hΓ_le

end Dichotomy

/-! ### Suppression Side: endpoint closure -/
section ConditionalDecay

/-- **Conditional decay from a rigidity hypothesis.**

This is the application-facing entry point. The hypothesis `h_rigidity`
is the single interface to system-specific structure. -/
theorem conditional_regularity_from_rigidity
    (Γ ratio : ℕ → ℝ) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2)
    (h_rigidity : ¬ Tendsto ratio atTop (nhds 0) →
                    Tendsto Γ atTop (nhds 0)) :
    Tendsto Γ atTop (nhds 0) := by
  by_cases h : Tendsto ratio atTop (nhds 0)
  · exact tendsto_zero_of_le_const_mul_sq Γ ratio C hΓ_nn hΓ_le h
  · exact h_rigidity h

end ConditionalDecay

/-! ### Balance and Crossover -/
section BalanceLaw

/-- Crossover transfer ceiling. -/
theorem crossover_transfer_ceiling
    (ν_hi : ℝ) (hν : 0 ≤ ν_hi)
    (AB_over_Δ : ℝ) (h_crossover : AB_over_Δ ≤ 1) (h_nn : 0 ≤ AB_over_Δ)
    (ψ_norm : ℝ) :
    ν_hi * AB_over_Δ ^ 2 * ψ_norm ^ 2 ≤ ν_hi * ψ_norm ^ 2 := by
  have h1 : AB_over_Δ ^ 2 ≤ 1 := by
    calc AB_over_Δ ^ 2 ≤ 1 ^ 2 := sq_le_sq' (by linarith [h_nn]) h_crossover
      _ = 1 := one_pow 2
  have hψsq : 0 ≤ ψ_norm ^ 2 := sq_nonneg ψ_norm
  have h2 : AB_over_Δ ^ 2 * ψ_norm ^ 2 ≤ ψ_norm ^ 2 := by
    nlinarith
  have h3 : ν_hi * (AB_over_Δ ^ 2 * ψ_norm ^ 2) ≤ ν_hi * ψ_norm ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hν
  simpa [mul_assoc] using h3

/-- Dissipation dominance. -/
theorem rigidity_dominance
    (C_T C_D X : ℝ) (h_X : 0 < X)
    (h_dom : C_T < C_D)
    (transfer dissipation : ℝ)
    (h_trans : transfer ≤ C_T * X)
    (h_diss : C_D * X ≤ dissipation) :
    transfer < dissipation := by
  have : C_T * X < C_D * X := by nlinarith
  linarith

/-- Balance squeeze. -/
theorem balance_squeeze
    (Γ_N D_N ρ_N : ℝ)
    (h_Γ_pos : 0 < Γ_N)
    (h_D_ge : ρ_N * Γ_N ≤ D_N)
    (h_ρ : 1 < ρ_N) :
    Γ_N - D_N < 0 := by
  have : Γ_N < D_N := by
    calc Γ_N = 1 * Γ_N := by ring
      _ < ρ_N * Γ_N := by nlinarith
      _ ≤ D_N := h_D_ge
  linarith

/-- Asymptotic balance squeeze. -/
theorem balance_squeeze_filter
    (Γ : ℕ → ℝ) (ρ : ℕ → ℝ) (C : ℝ)
    (h_Γ_nn : ∀ N, 0 ≤ Γ N)
    (h_Γ_le : ∀ N, Γ N ≤ C / ρ N)
    (h_ρ : Tendsto ρ atTop atTop) :
    Tendsto Γ atTop (nhds 0) := by
  apply squeeze_zero h_Γ_nn h_Γ_le
  have h_inv : Tendsto (fun N => (ρ N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_ρ
  have h_mul : Tendsto (fun N => C * (ρ N)⁻¹) atTop (nhds (C * 0)) :=
    h_inv.const_mul C
  simp only [mul_zero] at h_mul
  exact h_mul.congr (fun N => by rw [div_eq_mul_inv])

end BalanceLaw

/-! ### Summable Budgets -/
section SummableBudget

/-- If the per-scale error is summable, the total budget is finite and the cascade gap
theorem applies. -/
theorem cascade_gap_of_summable_budget
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ : ℝ)
    (hδ_nn : ∀ N, 0 ≤ δ N)
    (hδ_sum : Summable δ)
    (hstep : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ) :
    ∀ K, ∀ x : E, (μ - ∑' n, δ n) * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ := by
  have hbudget : ∀ K, ∑ n ∈ Finset.range K, δ n ≤ ∑' n, δ n := by
    intro K
    exact hδ_sum.sum_le_tsum (Finset.range K) (fun i _ => hδ_nn i)
  exact cascade_gap_survives H δ μ (∑' n, δ n) hstep hcoercive hbudget

/-- Geometric decay `δ N ≤ C * q^N` with `0 ≤ q < 1` produces a summable budget. -/
theorem summable_of_geometric_decay
    (C q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (δ : ℕ → ℝ) (hδ : ∀ N, δ N ≤ C * q ^ N) (hδ_nn : ∀ N, 0 ≤ δ N) :
    Summable δ :=
  Summable.of_nonneg_of_le hδ_nn hδ (Summable.mul_left C (summable_geometric_of_lt_one hq_nn hq_lt))

/-- Combined theorem: geometric decay in step sizes implies cascade gap survival. -/
theorem cascade_gap_of_geometric_decay
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ C q : ℝ)
    (hδ_nn : ∀ N, 0 ≤ δ N)
    (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (hδ_geom : ∀ N, δ N ≤ C * q ^ N)
    (hstep : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ) :
    ∀ K, ∀ x : E, (μ - ∑' n, δ n) * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ :=
  cascade_gap_of_summable_budget H δ μ hδ_nn
    (summable_of_geometric_decay C q hq_nn hq_lt δ hδ_geom hδ_nn)
    hstep hcoercive

end SummableBudget

/-! ### Finite-Key Certification -/
section FiniteKey

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Finite-key certification.** After `K` rounds, if the spent budget stays below the
initial coercive floor `μ`, the residual window is positive and coercivity survives.
This is the finite-stage analogue of the asymptotic cascade gap theorem. -/
theorem finite_key_certification
    (H : ℕ → (E →L[ℝ] E)) (δ : ℕ → ℝ) (μ : ℝ)
    (_hδ_nn : ∀ N, 0 ≤ δ N)
    (hstep : ∀ N, ‖H (N + 1) - H N‖ ≤ δ N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, H 0 x⟫_ℝ)
    (K : ℕ) (hK : spentBudget δ K < μ) :
    0 < residualWindow μ δ K ∧
    ∀ x : E, residualWindow μ δ K * ‖x‖ ^ 2 ≤ ⟪x, H K x⟫_ℝ := by
  constructor
  · simp [residualWindow]; linarith
  · exact cascade_gap_survives_residualWindow H δ μ hstep hcoercive K

/-- The residual window at stage `K` is the usable security margin after `K` protocol rounds. -/
theorem finite_key_margin_positive
    (δ : ℕ → ℝ) (μ : ℝ) (K : ℕ)
    (hK : spentBudget δ K < μ) :
    0 < residualWindow μ δ K := by
  simp [residualWindow]; linarith

end FiniteKey

end OperatorEstimates.Cascade

/-
  **Examples / toy instantiation.** Geometric off-diagonal decay, uniform gap, geometric
  perturbation budget, cascade gap survival, and a rigidity implication discharged by ratio
  decay in `conditional_regularity_from_rigidity`. Not imported from the library root.

  - real Hilbert space, `P + Q = 1`
  - scale-indexed operators, coupling `≤ lambda0 * decay^N`, uniform `gap > 0`, `0 ≤ decay < 1`

  Pipeline: `EffectiveReductionSetup` → geometric budget → `Cascade` → conditional decay.
-/
import OperatorEstimates.Reduction.BlockReduction
import OperatorEstimates.Reduction.Cascade
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

namespace OperatorEstimates.ToyInstantiation

open ContinuousLinearMap Filter
open scoped BigOperators InnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform bound for a finite geometric sum with ratio in `[0, 1)`. -/
private theorem geometric_sum_bound
    (q : ℝ) (hq_nonneg : 0 ≤ q) (hq_lt_one : q < 1) (K : ℕ) :
    ∑ N ∈ Finset.range K, q ^ N ≤ 1 / (1 - q) := by
  have hq_ne_one : q ≠ 1 := by linarith
  have hden : 0 < 1 - q := by linarith
  have hpow_le_one : q ^ K ≤ 1 := pow_le_one₀ hq_nonneg hq_lt_one.le
  calc
    ∑ N ∈ Finset.range K, q ^ N = (q ^ K - 1) / (q - 1) := geom_sum_eq hq_ne_one K
    _ = (1 - q ^ K) / (1 - q) := by
      rw [show q ^ K - 1 = -(1 - q ^ K) by ring]
      rw [show q - 1 = -(1 - q) by ring]
      rw [neg_div_neg_eq]
    _ ≤ 1 / (1 - q) := by
      have hpow_nonneg : 0 ≤ q ^ K := pow_nonneg hq_nonneg K
      have hnum_le : 1 - q ^ K ≤ 1 := by nlinarith
      exact div_le_div_of_nonneg_right hnum_le hden.le

/-- Bundled data for a scale-indexed family with geometric off-diagonal decay. -/
structure GeometricDecayFamily (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  decomp : ComplementaryProjections ℝ E
  ops : ℕ → (E →L[ℝ] E)
  rinv : ℕ → (E →L[ℝ] E)
  lambda0 : ℝ
  decay : ℝ
  gap : ℝ
  gap_pos : 0 < gap
  lambda0_nonneg : 0 ≤ lambda0
  decay_nonneg : 0 ≤ decay
  decay_lt_one : decay < 1
  PHQ_bound : ∀ N, ‖decomp.P * ops N * decomp.Q‖ ≤ lambda0 * decay ^ N
  QHP_bound : ∀ N, ‖decomp.Q * ops N * decomp.P‖ ≤ lambda0 * decay ^ N
  rinv_bound : ∀ N, ‖rinv N‖ ≤ gap⁻¹

namespace GeometricDecayFamily

/-- Off-diagonal coupling envelope at scale `N`. -/
def coupling (fam : GeometricDecayFamily E) (N : ℕ) : ℝ :=
  fam.lambda0 * fam.decay ^ N

/-- The scale budget extracted from the effective-operator error. -/
noncomputable def delta (fam : GeometricDecayFamily E) (N : ℕ) : ℝ :=
  fam.coupling N ^ 2 / fam.gap

/-- A uniform cap for the total geometric budget. -/
noncomputable def budgetCap (fam : GeometricDecayFamily E) : ℝ :=
  (fam.lambda0 ^ 2 / fam.gap) * (1 / (1 - fam.decay ^ 2))

/-- The bundled reduction setup at scale `N`. -/
def setup (fam : GeometricDecayFamily E) (N : ℕ) : EffectiveReductionSetup ℝ E where
  decomp := fam.decomp
  H := fam.ops N
  Rinv := fam.rinv N
  γ := fam.gap
  lam := fam.coupling N
  gamma_pos := fam.gap_pos
  lam_nonneg := by
    exact mul_nonneg fam.lambda0_nonneg (pow_nonneg fam.decay_nonneg N)
  PHQ_bound := fam.PHQ_bound N
  QHP_bound := fam.QHP_bound N
  Rinv_bound := fam.rinv_bound N

/-- The coupling envelope is nonnegative. -/
theorem coupling_nonneg (fam : GeometricDecayFamily E) (N : ℕ) :
    0 ≤ fam.coupling N :=
  mul_nonneg fam.lambda0_nonneg (pow_nonneg fam.decay_nonneg N)

/-- The scale budget is nonnegative. -/
theorem delta_nonneg (fam : GeometricDecayFamily E) (N : ℕ) :
    0 ≤ fam.delta N :=
  div_nonneg (sq_nonneg _) fam.gap_pos.le

/-- The effective-operator error at scale `N`. -/
theorem error_at_scale (fam : GeometricDecayFamily E) (N : ℕ) :
    ‖(fam.setup N).effectiveOperator - fam.decomp.P * fam.ops N * fam.decomp.P‖ ≤
      fam.delta N :=
  (fam.setup N).error_bound

/-- Gap survival at scale `N` under the small-coupling condition. -/
theorem gap_survives_at_scale (fam : GeometricDecayFamily E) (N : ℕ)
    (hsmall : fam.coupling N ^ 2 < fam.gap ^ 2) :
    0 < fam.gap - fam.delta N :=
  (fam.setup N).gap_survives hsmall

/-- The budget sequence is geometric in the scale index. -/
theorem delta_geometric (fam : GeometricDecayFamily E) (N : ℕ) :
    fam.delta N = (fam.lambda0 ^ 2 / fam.gap) * (fam.decay ^ 2) ^ N := by
  unfold delta coupling
  rw [mul_pow, div_eq_mul_inv, div_eq_mul_inv, ← pow_mul]
  rw [Nat.mul_comm N 2, pow_mul]
  ring

/-- The squared decay factor still lies below one. -/
theorem decay_sq_lt_one (fam : GeometricDecayFamily E) :
    fam.decay ^ 2 < 1 := by
  simpa using pow_lt_one₀ fam.decay_nonneg fam.decay_lt_one two_ne_zero

/-- The bounded geometric budget available to the cascade layer. -/
theorem budget_bounded (fam : GeometricDecayFamily E) (K : ℕ) :
    ∑ N ∈ Finset.range K, fam.delta N ≤ fam.budgetCap := by
  have hcoeff : 0 ≤ fam.lambda0 ^ 2 / fam.gap := by
    exact div_nonneg (sq_nonneg _) fam.gap_pos.le
  calc
    ∑ N ∈ Finset.range K, fam.delta N
        = ∑ N ∈ Finset.range K, (fam.lambda0 ^ 2 / fam.gap) * (fam.decay ^ 2) ^ N := by
            refine Finset.sum_congr rfl ?_
            intro N _
            exact fam.delta_geometric N
    _ = (fam.lambda0 ^ 2 / fam.gap) * ∑ N ∈ Finset.range K, (fam.decay ^ 2) ^ N := by
          rw [Finset.mul_sum]
    _ ≤ (fam.lambda0 ^ 2 / fam.gap) * (1 / (1 - fam.decay ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (geometric_sum_bound (fam.decay ^ 2) (sq_nonneg _) fam.decay_sq_lt_one K)
            hcoeff
    _ = fam.budgetCap := rfl

/-- A cascade with step size controlled by `delta` keeps the residual gap. -/
theorem cascade_gap_survives_from_budget
    (fam : GeometricDecayFamily E)
    (Hcascade : ℕ → (E →L[ℝ] E))
    (hstep : ∀ N, ‖Hcascade (N + 1) - Hcascade N‖ ≤ fam.delta N)
    (mu : ℝ)
    (hcoercive : ∀ x : E, mu * ‖x‖ ^ 2 ≤ ⟪x, Hcascade 0 x⟫_ℝ) :
    ∀ K, ∀ x : E, (mu - fam.budgetCap) * ‖x‖ ^ 2 ≤ ⟪x, Hcascade K x⟫_ℝ :=
  Cascade.cascade_gap_survives Hcascade fam.delta mu fam.budgetCap
    hstep hcoercive fam.budget_bounded

/-- If the initial coercivity exceeds the geometric budget cap, the residual gap is positive. -/
theorem residual_gap_positive
    (fam : GeometricDecayFamily E) {mu : ℝ} (hmu : fam.budgetCap < mu) :
    0 < mu - fam.budgetCap := by
  linarith

/-- The coupling envelope tends to zero because `0 ≤ decay < 1`. -/
theorem coupling_tendsto_zero (fam : GeometricDecayFamily E) :
    Tendsto fam.coupling atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => fam.decay ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one fam.decay_nonneg fam.decay_lt_one
  simpa [coupling] using (tendsto_const_nhds.mul hpow)

/-- In this toy model the ratio sequence is just the coupling envelope. -/
theorem ratio_vanishes (fam : GeometricDecayFamily E) :
    Tendsto fam.coupling atTop (nhds 0) :=
  fam.coupling_tendsto_zero

/-- The conditional-decay square bound is immediate from the definition of `delta`. -/
theorem square_dominance (fam : GeometricDecayFamily E) :
    ∀ N, fam.delta N ≤ (1 / fam.gap) * fam.coupling N ^ 2 := by
  intro N
  exact le_of_eq <| by
    rw [delta, one_div, div_eq_mul_inv, mul_comm]

/-- The rigidity implication follows because the ratio already tends to zero. -/
theorem rigidity_implication_of_ratio_limit (fam : GeometricDecayFamily E) :
    ¬ Tendsto fam.coupling atTop (nhds 0) → Tendsto fam.delta atTop (nhds 0) := by
  intro hratio
  exact False.elim (hratio fam.coupling_tendsto_zero)

/-- The observable decays by chaining the generic conditional-decay theorem
with the rigidity implication supplied by geometric decay. -/
theorem observable_decays (fam : GeometricDecayFamily E) :
    Tendsto fam.delta atTop (nhds 0) :=
  Cascade.conditional_regularity_from_rigidity
    fam.delta fam.coupling (1 / fam.gap)
    fam.delta_nonneg
    fam.square_dominance
    fam.rigidity_implication_of_ratio_limit

end GeometricDecayFamily

end OperatorEstimates.ToyInstantiation

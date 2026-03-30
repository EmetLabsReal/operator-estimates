/-
  **Instantiations / Steklov.** Scale-dependent cutoff family, `H = T + B` with `T`
  decoupled off-diagonal (`P * T * Q = 0`, `Q * T * P = 0`), coupling scale
  `lambda = ‖P * B * Q‖` (reflexive `PHQ_bound`), substantive `‖Q * B * P‖` bound, and
  abstract `Rinv` with `‖Rinv N‖ ≤ (gamma N)⁻¹`. Feeds the generic
  `EffectiveReductionSetup.error_bound` from `OperatorEstimates.Reduction.BlockReduction`.

  Interpretation: `T` is the diagonal or projected part of the dynamics, `B` is the
  transfer or coupling part, and bounds on `B` control how strongly the cascade can
  communicate across the `P/Q` split.
-/
import OperatorEstimates.Instantiations.SpectralCutoff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace OperatorEstimates.Instantiations.Steklov

open ContinuousLinearMap Filter
open scoped InnerProductSpace Topology

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ### Helper lemmas: off-diagonal of `T + B` is that of `B` when `T` decouples -/

private lemma phq_T_add_B (Pn Qn : E →L[𝕜] E) (T B : E →L[𝕜] E)
    (h : Pn * T * Qn = 0) :
    Pn * (T + B) * Qn = Pn * B * Qn := by
  have spl : Pn * (T + B) * Qn = Pn * T * Qn + Pn * B * Qn := by
    ext x
    simp only [mul_apply, add_apply, map_add]
  rw [spl, h, zero_add]

private lemma qhp_T_add_B (Pn Qn : E →L[𝕜] E) (T B : E →L[𝕜] E)
    (h : Qn * T * Pn = 0) :
    Qn * (T + B) * Pn = Qn * B * Pn := by
  have spl : Qn * (T + B) * Pn = Qn * T * Pn + Qn * B * Pn := by
    ext x
    simp only [mul_apply, add_apply, map_add]
  rw [spl, h, zero_add]

/-! ### Coupling strength -/

/-- Coupling envelope (fixed here to `‖P N * B * Q N‖`; only `QHP_bound` needs extra input). -/
noncomputable def coupling
    (cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E))
    (B : E →L[𝕜] E) (N : ℕ) : ℝ :=
  ‖cutoff.P N * B * cutoff.Q N‖

/-! ### Projections and setup (exact field names) -/

noncomputable def steklovProjections
    (cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E))
    (N : ℕ) : OperatorEstimates.ComplementaryProjections 𝕜 E :=
  cutoff.toComplementaryProjections N

noncomputable def steklovSetup
    (T B : E →L[𝕜] E)
    (cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E))
    (gamma : ℕ → ℝ)
    (h_gamma_pos : ∀ N, 0 < gamma N)
    (Rinv : ℕ → E →L[𝕜] E)
    (h_Rinv_bound : ∀ N, ‖Rinv N‖ ≤ (gamma N)⁻¹)
    (h_T_PQ_zero : ∀ N, cutoff.P N * T * cutoff.Q N = 0)
    (h_T_QP_zero : ∀ N, cutoff.Q N * T * cutoff.P N = 0)
    (h_B_QP_bound : ∀ N, ‖cutoff.Q N * B * cutoff.P N‖ ≤ coupling cutoff B N)
    (N : ℕ) : OperatorEstimates.EffectiveReductionSetup 𝕜 E where
  decomp := steklovProjections cutoff N
  H := T + B
  Rinv := Rinv N
  γ := gamma N
  lam := coupling cutoff B N
  gamma_pos := h_gamma_pos N
  lam_nonneg := by
    simp [coupling]
  PHQ_bound := by
    change ‖cutoff.P N * (T + B) * cutoff.Q N‖ ≤ coupling cutoff B N
    rw [phq_T_add_B (cutoff.P N) (cutoff.Q N) T B (h_T_PQ_zero N), coupling]
  QHP_bound := by
    change ‖cutoff.Q N * (T + B) * cutoff.P N‖ ≤ coupling cutoff B N
    rw [qhp_T_add_B (cutoff.P N) (cutoff.Q N) T B (h_T_QP_zero N)]
    exact h_B_QP_bound N
  Rinv_bound := h_Rinv_bound N

/-! ### Reduction error -/

lemma steklov_error_bound
    (T B : E →L[𝕜] E)
    (cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E))
    (gamma : ℕ → ℝ)
    (h_gamma_pos : ∀ N, 0 < gamma N)
    (Rinv : ℕ → E →L[𝕜] E)
    (h_Rinv_bound : ∀ N, ‖Rinv N‖ ≤ (gamma N)⁻¹)
    (h_T_PQ_zero : ∀ N, cutoff.P N * T * cutoff.Q N = 0)
    (h_T_QP_zero : ∀ N, cutoff.Q N * T * cutoff.P N = 0)
    (h_B_QP_bound : ∀ N, ‖cutoff.Q N * B * cutoff.P N‖ ≤ coupling cutoff B N)
    (N : ℕ) :
    ‖(steklovSetup T B cutoff
          gamma h_gamma_pos Rinv h_Rinv_bound
          h_T_PQ_zero h_T_QP_zero
          h_B_QP_bound N).effectiveOperator
        - cutoff.P N * (T + B) * cutoff.P N‖
      ≤ (coupling cutoff B N) ^ 2 / gamma N := by
  exact (steklovSetup T B cutoff
      gamma h_gamma_pos Rinv h_Rinv_bound
      h_T_PQ_zero h_T_QP_zero
      h_B_QP_bound N).error_bound

/-! ### Suppression -/

theorem steklov_error_tendsto_zero
    (cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E))
    (B : E →L[𝕜] E) (gamma : ℕ → ℝ)
    (C : ℝ) (hC_nonneg : 0 ≤ C)
    (h_lam_decay : ∀ᶠ N in atTop, coupling cutoff B N ≤ C / N)
    (h_suppression_ratio : Tendsto (fun N => coupling cutoff B N / gamma N) atTop (nhds 0)) :
    Tendsto (fun N => (coupling cutoff B N) ^ 2 / gamma N) atTop (nhds 0) := by
  have _ : (0 : ℝ) ≤ C + 1 := by linarith [hC_nonneg]
  have h_pointwise (N : ℕ) :
      (coupling cutoff B N) ^ 2 / gamma N =
        coupling cutoff B N * (coupling cutoff B N / gamma N) := by
    dsimp [coupling]
    simp only [div_eq_mul_inv, sq, mul_assoc]
  have h_coupling_nonneg (N : ℕ) : 0 ≤ coupling cutoff B N := norm_nonneg _
  have h_div : Tendsto (fun N : ℕ => C / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have h_coupling_zero : Tendsto (fun N => coupling cutoff B N) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall h_coupling_nonneg) h_lam_decay h_div
  have h_mul :
      Tendsto (fun N => coupling cutoff B N * (coupling cutoff B N / gamma N)) atTop (nhds 0) := by
    simpa [mul_zero] using h_coupling_zero.mul h_suppression_ratio
  have hev : ∀ᶠ N in atTop,
      coupling cutoff B N * (coupling cutoff B N / gamma N) =
        (coupling cutoff B N) ^ 2 / gamma N :=
    Eventually.of_forall fun N => (h_pointwise N).symm
  exact (Tendsto.congr' hev h_mul)

end OperatorEstimates.Instantiations.Steklov

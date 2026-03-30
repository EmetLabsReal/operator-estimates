/-
  **Core / perturbation.** Rayleigh and coercivity stability (`RCLike 𝕜`); resolvent-difference
  and spectral-window material over `ℝ`. Support lemmas for the reduction pipeline.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

namespace OperatorEstimates

/-! ### Rayleigh Perturbation -/
section RayleighPerturbation
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Rayleigh quotient perturbation bound.**
Works over any `RCLike` field (ℝ or ℂ). -/
theorem rayleigh_perturbation
    (A B : E →L[𝕜] E) (x : E) (δ : ℝ)
    (hx : ‖x‖ = 1) (hδ : ‖A - B‖ ≤ δ) :
    |RCLike.re ⟪x, A x⟫_𝕜 - RCLike.re ⟪x, B x⟫_𝕜| ≤ δ := by
  have key : RCLike.re ⟪x, A x⟫_𝕜 - RCLike.re ⟪x, B x⟫_𝕜 =
      RCLike.re ⟪x, (A - B) x⟫_𝕜 := by
    simp [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
  rw [key]
  calc |RCLike.re ⟪x, (A - B) x⟫_𝕜|
      ≤ ‖⟪x, (A - B) x⟫_𝕜‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖(A - B) x‖ := norm_inner_le_norm x ((A - B) x)
    _ ≤ ‖x‖ * (‖A - B‖ * ‖x‖) := by gcongr; exact le_opNorm _ _
    _ = ‖A - B‖ := by rw [hx]; ring
    _ ≤ δ := hδ

/-- **Rayleigh quotient perturbation (symmetric form).** -/
theorem rayleigh_perturbation_two_sided
    (A B : E →L[𝕜] E) (x : E) (δ : ℝ)
    (hx : ‖x‖ = 1) (hδ : ‖A - B‖ ≤ δ) :
    RCLike.re ⟪x, B x⟫_𝕜 - δ ≤ RCLike.re ⟪x, A x⟫_𝕜 ∧
      RCLike.re ⟪x, A x⟫_𝕜 ≤ RCLike.re ⟪x, B x⟫_𝕜 + δ := by
  have h := rayleigh_perturbation A B x δ hx hδ
  exact ⟨by linarith [abs_le.mp h], by linarith [abs_le.mp h]⟩

/-- **Quadratic form sandwich under perturbation.** -/
theorem coercivity_perturbation
    (A B : E →L[𝕜] E) (μ δ : ℝ)
    (hB : ∀ x : E, μ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, B x⟫_𝕜)
    (hδ : ‖A - B‖ ≤ δ) :
    ∀ x : E, (μ - δ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, A x⟫_𝕜 := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have key : RCLike.re ⟪x, A x⟫_𝕜 - RCLike.re ⟪x, B x⟫_𝕜 =
        RCLike.re ⟪x, (A - B) x⟫_𝕜 := by
      simp [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    have hpert : |RCLike.re ⟪x, (A - B) x⟫_𝕜| ≤ δ * ‖x‖ ^ 2 := by
      calc |RCLike.re ⟪x, (A - B) x⟫_𝕜|
          ≤ ‖⟪x, (A - B) x⟫_𝕜‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(A - B) x‖ := norm_inner_le_norm x _
        _ ≤ ‖x‖ * (‖A - B‖ * ‖x‖) := by gcongr; exact le_opNorm _ _
        _ ≤ ‖x‖ * (δ * ‖x‖) := by gcongr
        _ = δ * ‖x‖ ^ 2 := by ring
    have : RCLike.re ⟪x, A x⟫_𝕜 ≥ RCLike.re ⟪x, B x⟫_𝕜 - δ * ‖x‖ ^ 2 := by
      have := abs_le.mp hpert
      linarith [key]
    linarith [hB x]

end RayleighPerturbation

/-! ### Resolvent Difference -/
section ResolventDiff
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Four-fold composition norm bound.** -/
theorem norm_comp_four_le (A B C D : E →L[ℝ] E) :
    ‖A.comp (B.comp (C.comp D))‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by
  calc ‖A.comp (B.comp (C.comp D))‖
      ≤ ‖A‖ * ‖B.comp (C.comp D)‖ := opNorm_comp_le A _
    _ ≤ ‖A‖ * (‖B‖ * ‖C.comp D‖) := by gcongr; exact opNorm_comp_le B _
    _ ≤ ‖A‖ * (‖B‖ * (‖C‖ * ‖D‖)) := by gcongr; exact opNorm_comp_le C D
    _ = ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by ring

/-- **Scaled composition bound.** -/
theorem norm_smul_comp_four_le (z : ℝ) (A B C D : E →L[ℝ] E) :
    ‖z • A.comp (B.comp (C.comp D))‖ ≤ |z| * ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by
  calc ‖z • A.comp (B.comp (C.comp D))‖
      = |z| * ‖A.comp (B.comp (C.comp D))‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |z| * (‖A‖ * ‖B‖ * ‖C‖ * ‖D‖) := by
        gcongr; exact norm_comp_four_le A B C D
    _ = |z| * ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by ring

/-- **Resolvent difference norm bound (abstract).** -/
theorem resolvent_diff_bound
    (A Minv₀ Minv_z B : E →L[ℝ] E) (z α δ₀ δ_z β : ℝ)
    (hA : ‖A‖ ≤ α) (hMinv₀ : ‖Minv₀‖ ≤ δ₀)
    (hMinv_z : ‖Minv_z‖ ≤ δ_z) (hB : ‖B‖ ≤ β) :
    ‖z • A.comp (Minv₀.comp (Minv_z.comp B))‖ ≤ |z| * α * δ₀ * δ_z * β := by
  calc ‖z • A.comp (Minv₀.comp (Minv_z.comp B))‖
      ≤ |z| * ‖A‖ * ‖Minv₀‖ * ‖Minv_z‖ * ‖B‖ :=
        norm_smul_comp_four_le z A Minv₀ Minv_z B
    _ ≤ |z| * α * δ₀ * δ_z * β := by
        have hα : 0 ≤ α := le_trans (norm_nonneg _) hA
        have hδ₀ : 0 ≤ δ₀ := le_trans (norm_nonneg _) hMinv₀
        have hδ_z : 0 ≤ δ_z := le_trans (norm_nonneg _) hMinv_z
        gcongr

/-- **Effective operator z-dependence.** -/
theorem effective_operator_z_bound
    (A Minv₀ Minv_z B : E →L[ℝ] E) (z ε γ : ℝ)
    (hγε : ε < γ) (hz : |z| < γ - ε)
    (hA : ‖A‖ ≤ ε) (hB : ‖B‖ ≤ ε)
    (hMinv₀ : ‖Minv₀‖ ≤ (γ - ε)⁻¹)
    (hMinv_z : ‖Minv_z‖ ≤ (γ - ε - |z|)⁻¹) :
    ‖z • A.comp (Minv₀.comp (Minv_z.comp B))‖ ≤
      |z| * ε ^ 2 / ((γ - ε) * (γ - ε - |z|)) := by
  have hgap : 0 < γ - ε := by linarith
  have hgapz : 0 < γ - ε - |z| := by linarith
  calc ‖z • A.comp (Minv₀.comp (Minv_z.comp B))‖
      ≤ |z| * ε * (γ - ε)⁻¹ * (γ - ε - |z|)⁻¹ * ε :=
        resolvent_diff_bound A Minv₀ Minv_z B z ε (γ - ε)⁻¹ (γ - ε - |z|)⁻¹ ε
          hA hMinv₀ hMinv_z hB
    _ = |z| * ε ^ 2 / ((γ - ε) * (γ - ε - |z|)) := by
        field_simp

end ResolventDiff

/-! ### Spectral Window -/
section SpectralWindow
open ContinuousLinearMap Filter
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Spectral window inverse bound.** -/
theorem spectral_window_inverse_bound
    (resolvent_norm Δ ε z : ℝ) (hz : |z| < Δ - ε)
    (hres : resolvent_norm ≤ (Δ - ε)⁻¹) :
    0 < Δ - ε - |z| ∧ resolvent_norm ≤ (Δ - ε - |z|)⁻¹ := by
  have hgap : 0 < Δ - ε - |z| := by linarith
  constructor
  · exact hgap
  · calc resolvent_norm ≤ (Δ - ε)⁻¹ := hres
      _ ≤ (Δ - ε - |z|)⁻¹ := inv_anti₀ hgap (by linarith [abs_nonneg z])

/-- **Effective operator error bound.** -/
theorem effective_operator_error_bound
    (coupling resolvent_norm Δ ε : ℝ)
    (hε_lt : ε < Δ)
    (hcoupling : coupling ≤ ε)
    (hresolvent : resolvent_norm ≤ (Δ - ε)⁻¹)
    (hcoupling_nn : 0 ≤ coupling) :
    coupling * resolvent_norm * coupling ≤ ε ^ 2 / (Δ - ε) := by
  have hgap : 0 < Δ - ε := by linarith
  have hε_nn : 0 ≤ ε := le_trans hcoupling_nn hcoupling
  have hgap_inv_nonneg : 0 ≤ (Δ - ε)⁻¹ := by positivity
  by_cases hres_nn : 0 ≤ resolvent_norm
  · have h1 : coupling * resolvent_norm * coupling ≤ coupling * resolvent_norm * ε := by
      gcongr
    have h2 : coupling * resolvent_norm * ε ≤ ε * resolvent_norm * ε := by
      gcongr
    have h3 : ε * resolvent_norm * ε ≤ ε * ((Δ - ε)⁻¹) * ε := by
      gcongr
    calc coupling * resolvent_norm * coupling
        ≤ ε * ((Δ - ε)⁻¹) * ε := le_trans h1 (le_trans h2 h3)
      _ = ε ^ 2 * (Δ - ε)⁻¹ := by ring
      _ = ε ^ 2 / (Δ - ε) := by rw [div_eq_mul_inv]
  · have hleft_nonpos : coupling * resolvent_norm * coupling ≤ 0 := by
      have hres_nonpos : resolvent_norm ≤ 0 := le_of_not_ge hres_nn
      have hsq_nn : 0 ≤ coupling * coupling := by nlinarith [hcoupling_nn]
      have hrewrite : coupling * resolvent_norm * coupling = (coupling * coupling) * resolvent_norm := by ring
      rw [hrewrite]
      exact mul_nonpos_of_nonneg_of_nonpos hsq_nn hres_nonpos
    have hright_nonneg : 0 ≤ ε ^ 2 / (Δ - ε) := by
      exact div_nonneg (sq_nonneg _) hgap.le
    linarith

/-- **Energy window separation.** -/
theorem energy_window_separation
    (E_low E_high : ℝ) (hgap : E_low < E_high) :
    0 < E_high - E_low ∧
    ∀ (η : ℝ), 0 < η → η < (E_high - E_low) / 2 →
      E_low + η < E_high - η := by
  constructor
  · linarith
  · intro η hη hη_small
    linarith

/-- **Eventual smallness from a vanishing quotient.** -/
theorem eventually_lt_mul_of_tendsto_zero_quotient
    (ε_sq Δ η_sq : ℕ → ℝ)
    (hΔ : ∀ n, 0 < Δ n) (hη : ∀ n, 0 < η_sq n)
    (h_tend : Tendsto (fun n => ε_sq n / (Δ n * η_sq n)) atTop (nhds 0)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ε_sq n < δ * (Δ n * η_sq n) := by
  intro δ hδ
  have hev : ∀ᶠ n in atTop, ε_sq n / (Δ n * η_sq n) < δ :=
    h_tend (Iio_mem_nhds hδ)
  exact hev.mono fun n hn => by
    have h_pos : 0 < Δ n * η_sq n := mul_pos (hΔ n) (hη n)
    rwa [div_lt_iff₀ h_pos] at hn

end SpectralWindow

/-! ### Quotient Bounds -/
section ControlParameter
open Real Filter

/-- **Exponential upper bound for a quadratic quotient.** -/
theorem exp_quadratic_quotient_upper_bound
    (coupling Δ C S : ℝ) (hΔ : 0 < Δ)
    (hcoupling_nn : 0 ≤ coupling)
    (hcoupling : coupling ≤ C * exp (-S)) :
    coupling ^ 2 / Δ ≤ C ^ 2 * exp (-2 * S) / Δ := by
  have h_sq : coupling ^ 2 ≤ (C * exp (-S)) ^ 2 :=
    sq_le_sq' (by linarith) hcoupling
  have hexp : (C * exp (-S)) ^ 2 = C ^ 2 * exp (-2 * S) := by
    rw [mul_pow]; congr 1; rw [sq, ← exp_add]; congr 1; ring
  rw [hexp] at h_sq
  exact div_le_div_of_nonneg_right h_sq (by positivity)

/-- **Eventual domination from a divergent quotient.** -/
theorem eventual_domination_of_divergent_quotient
    (coupling gap : ℕ → ℝ) (hgap : ∀ n, 0 < gap n)
    (h_div : Tendsto (fun n => coupling n ^ 2 / gap n) atTop atTop) :
    ∀ K : ℝ, ∀ᶠ n in atTop, K * gap n ≤ coupling n ^ 2 := by
  intro K
  have hev := (tendsto_atTop.mp h_div) K
  exact hev.mono fun n hn => by
    rwa [le_div_iff₀ (hgap n)] at hn

end ControlParameter

end OperatorEstimates

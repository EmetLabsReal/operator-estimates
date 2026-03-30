/-
  **Core / transfer.** Norm and quadratic-form estimates for composed operators `A ∘ R ∘ B`;
  headline lemmas include transfer bounds, locality, and `tendsto_zero_of_le_const_mul_sq`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OperatorEstimates

/-! ### Transfer Bounds -/
section TransferBounds
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Transfer operator norm bound.**
If `T = A ∘ R ∘ B` and `‖R‖ ≤ Δ⁻¹`, then `‖T‖ ≤ ‖A‖ * ‖B‖ / Δ`. -/
theorem transfer_norm_bound
    (A R B : E →L[𝕜] E) (Δ : ℝ)
    (hR : ‖R‖ ≤ Δ⁻¹) :
    ‖A.comp (R.comp B)‖ ≤ ‖A‖ * ‖B‖ / Δ := by
  calc ‖A.comp (R.comp B)‖
      ≤ ‖A‖ * ‖R.comp B‖ := opNorm_comp_le A (R.comp B)
    _ ≤ ‖A‖ * (‖R‖ * ‖B‖) := by gcongr; exact opNorm_comp_le R B
    _ ≤ ‖A‖ * (Δ⁻¹ * ‖B‖) := by gcongr
    _ = ‖A‖ * ‖B‖ / Δ := by ring

theorem coercive_inverse_norm_le
    (M Minv : E →L[𝕜] E) (Δ : ℝ) (hΔ : 0 < Δ)
    (hcoercive : ∀ x : E, Δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hright : M.comp Minv = ContinuousLinearMap.id 𝕜 E) :
    ‖Minv‖ ≤ Δ⁻¹ := by
  rw [opNorm_le_iff (by positivity : (0 : ℝ) ≤ Δ⁻¹)]
  intro x
  set y := Minv x
  have hMy : M y = x := by
    have : (M.comp Minv) x = x := by rw [hright]; simp
    exact this
  by_cases hy : y = 0
  · simp [show y = 0 from hy] at hMy ⊢
    rw [← hMy]; positivity
  · have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hCS : RCLike.re ⟪y, M y⟫_𝕜 ≤ ‖y‖ * ‖M y‖ :=
      le_trans (le_abs_self _)
        (le_trans (RCLike.abs_re_le_norm _) (norm_inner_le_norm y (M y)))
    have key : Δ * ‖y‖ ≤ ‖x‖ := by
      have h1 : Δ * (‖y‖ * ‖y‖) ≤ ‖y‖ * ‖x‖ := by
        have := calc Δ * ‖y‖ ^ 2
              ≤ RCLike.re ⟪y, M y⟫_𝕜 := hcoercive y
            _ ≤ ‖y‖ * ‖M y‖ := hCS
            _ = ‖y‖ * ‖x‖ := by rw [hMy]
        rwa [sq] at this
      exact le_of_mul_le_mul_left (by linarith) hynorm
    calc ‖y‖ = Δ⁻¹ * (Δ * ‖y‖) := by field_simp
      _ ≤ Δ⁻¹ * ‖x‖ := by gcongr

/-- **Full transfer bound with coercivity.** -/
theorem transfer_norm_bound_from_coercivity
    (A B M Minv : E →L[𝕜] E) (Δ : ℝ) (hΔ : 0 < Δ)
    (hcoercive : ∀ x : E, Δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hright : M.comp Minv = ContinuousLinearMap.id 𝕜 E) :
    ‖A.comp (Minv.comp B)‖ ≤ ‖A‖ * ‖B‖ / Δ :=
  transfer_norm_bound A Minv B Δ
    (coercive_inverse_norm_le M Minv Δ hΔ hcoercive hright)

end TransferBounds

/-! ### Transfer Lower Bound (Exact) -/
section TransferLowerExact
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Transfer lower bound (exact eigenvector).** -/
theorem transfer_lower_exact
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (ψ : E₁) (φ : E₂) (r a b ε_B : ℝ)
    (hRφ : R φ = (r : 𝕜) • φ)
    (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_B) :
    ‖A (R (B ψ))‖ ≥ a * b * r - ‖A‖ * ‖R‖ * ε_B := by
  set α := ⟪φ, B ψ⟫_𝕜 with hα_def
  set η := B ψ - α • φ with hη_def
  have hBψ : B ψ = α • φ + η := by simp [η]
  have hRBψ : R (B ψ) = (α * (r : 𝕜)) • φ + R η := by
    rw [hBψ, map_add, map_smul, hRφ, smul_smul]
  have hARBψ : A (R (B ψ)) = (α * (r : 𝕜)) • A φ + A (R η) := by
    rw [hRBψ, map_add, map_smul]
  have hARη : ‖A (R η)‖ ≤ ‖A‖ * ‖R‖ * ε_B := by
    calc ‖A (R η)‖ ≤ ‖A‖ * ‖R η‖ := le_opNorm A (R η)
      _ ≤ ‖A‖ * (‖R‖ * ‖η‖) := by gcongr; exact le_opNorm R η
      _ ≤ ‖A‖ * (‖R‖ * ε_B) := by gcongr
      _ = ‖A‖ * ‖R‖ * ε_B := by ring
  have hlead : a * b * r ≤ ‖α‖ * r * ‖A φ‖ := by
    have h1 : a * b ≤ ‖α‖ * ‖A φ‖ :=
      calc a * b ≤ ‖A φ‖ * ‖α‖ := mul_le_mul ha hb hb_nn (norm_nonneg _)
        _ = ‖α‖ * ‖A φ‖ := mul_comm _ _
    calc a * b * r ≤ (‖α‖ * ‖A φ‖) * r := by gcongr
      _ = ‖α‖ * r * ‖A φ‖ := by ring
  have hnorm_lead : ‖(α * (r : 𝕜)) • A φ‖ = ‖α‖ * r * ‖A φ‖ := by
    rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hr]
  have hrev : ‖(α * (r : 𝕜)) • A φ‖ ≤ ‖A (R (B ψ))‖ + ‖A (R η)‖ := by
    rw [hARBψ]
    have := norm_sub_le ((α * (r : 𝕜)) • A φ + A (R η)) (A (R η))
    simp only [add_sub_cancel_right] at this
    linarith
  linarith [hnorm_lead]

end TransferLowerExact

/-! ### Transfer Lower Bound (Approximate) -/
section TransferLowerApprox
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Transfer lower bound (approximate eigenvector).** -/
theorem transfer_lower_approx
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (ψ : E₁) (φ : E₂) (r a b ε_B ε_R' : ℝ)
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (hRφ : ‖R φ - (r : 𝕜) • φ‖ ≤ ε_R')
    (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_B) :
    ‖A (R (B ψ))‖ ≥ a * b * r - ‖B‖ * ‖A‖ * ε_R' - ‖A‖ * ‖R‖ * ε_B := by
  set α := ⟪φ, B ψ⟫_𝕜 with hα_def
  set η := B ψ - α • φ with hη_def
  have hε_R'_nn : 0 ≤ ε_R' := le_trans (norm_nonneg _) hRφ
  have hαRφ : α • R φ = (α * (r : 𝕜)) • φ + α • (R φ - (r : 𝕜) • φ) := by
    rw [smul_sub, smul_smul]; abel
  have hRBψ : R (B ψ) = (α * (r : 𝕜)) • φ + (α • (R φ - (r : 𝕜) • φ) + R η) := by
    have : B ψ = α • φ + η := by simp [η]
    rw [this, map_add, map_smul, hαRφ]; abel
  have hARBψ : A (R (B ψ)) = (α * (r : 𝕜)) • A φ + (α • A (R φ - (r : 𝕜) • φ) + A (R η)) := by
    rw [hRBψ, map_add, map_smul, map_add, map_smul]
  have hα_le : ‖α‖ ≤ ‖B‖ := by
    calc ‖α‖ ≤ ‖φ‖ * ‖B ψ‖ := norm_inner_le_norm φ (B ψ)
      _ ≤ 1 * (‖B‖ * ‖ψ‖) := by
          gcongr
          · exact hφ ▸ le_refl _
          · exact le_opNorm B ψ
      _ = ‖B‖ := by rw [one_mul, hψ, mul_one]
  have herr1 : ‖α • A (R φ - (r : 𝕜) • φ)‖ ≤ ‖α‖ * (‖A‖ * ε_R') := by
    rw [norm_smul]
    gcongr
    exact le_trans (le_opNorm A _) (by gcongr)
  have herr2 : ‖A (R η)‖ ≤ ‖A‖ * ‖R‖ * ε_B := by
    calc ‖A (R η)‖ ≤ ‖A‖ * ‖R η‖ := le_opNorm A _
      _ ≤ ‖A‖ * (‖R‖ * ‖η‖) := by gcongr; exact le_opNorm R η
      _ ≤ ‖A‖ * (‖R‖ * ε_B) := by gcongr
      _ = ‖A‖ * ‖R‖ * ε_B := by ring
  have herr_total : ‖α • A (R φ - (r : 𝕜) • φ) + A (R η)‖ ≤
      ‖B‖ * ‖A‖ * ε_R' + ‖A‖ * ‖R‖ * ε_B := by
    calc ‖α • A (R φ - (r : 𝕜) • φ) + A (R η)‖
        ≤ ‖α • A (R φ - (r : 𝕜) • φ)‖ + ‖A (R η)‖ := norm_add_le _ _
      _ ≤ ‖α‖ * (‖A‖ * ε_R') + ‖A‖ * ‖R‖ * ε_B := add_le_add herr1 herr2
      _ ≤ ‖B‖ * (‖A‖ * ε_R') + ‖A‖ * ‖R‖ * ε_B := by
          gcongr
      _ = ‖B‖ * ‖A‖ * ε_R' + ‖A‖ * ‖R‖ * ε_B := by ring
  have hlead : a * b * r ≤ ‖α‖ * r * ‖A φ‖ := by
    calc a * b * r ≤ ‖A φ‖ * ‖α‖ * r := by
          gcongr
      _ = ‖α‖ * r * ‖A φ‖ := by ring
  have hnorm_lead : ‖(α * (r : 𝕜)) • A φ‖ = ‖α‖ * r * ‖A φ‖ := by
    rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg hr]
  have hrev : ‖(α * (r : 𝕜)) • A φ‖ ≤ ‖A (R (B ψ))‖ + ‖α • A (R φ - (r : 𝕜) • φ) + A (R η)‖ := by
    have : (α * (r : 𝕜)) • A φ =
        A (R (B ψ)) - (α • A (R φ - (r : 𝕜) • φ) + A (R η)) := by
      rw [hARBψ]; abel
    rw [this]
    exact norm_sub_le _ _
  linarith

end TransferLowerApprox

/-! ### Alignment -/
section Alignment
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Orthogonality of residual.** -/
theorem alignment_orthogonal (ω e : E) (he : ‖e‖ = 1) :
    ⟪ω - ⟪ω, e⟫_ℝ • e, e⟫_ℝ = 0 := by
  simp [inner_sub_left, inner_smul_left, he]

/-- **Pythagorean decomposition.** -/
theorem alignment_pythagorean (ω e : E) (he : ‖e‖ = 1) :
    ‖ω‖ ^ 2 = ⟪ω, e⟫_ℝ ^ 2 + ‖ω - ⟪ω, e⟫_ℝ • e‖ ^ 2 := by
  set φ := ⟪ω, e⟫_ℝ
  set r := ω - φ • e
  have hdecomp : ω = φ • e + r := by simp [r]
  have hortho : ⟪φ • e, r⟫_ℝ = 0 := by
    simp only [r, φ, inner_smul_left, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, he]
    simp only [real_inner_comm e ω]; ring
  have hnorm_smul : ‖φ • e‖ ^ 2 = φ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he, one_pow, mul_one]
  have key := @norm_add_sq_real E _ _ (φ • e) r
  rw [← hdecomp] at key
  linarith [hortho, hnorm_smul]

/-- **Alignment lower bound.** -/
theorem alignment_lower_bound (ω e : E) (he : ‖e‖ = 1) (δ : ℝ)
    (hδ_nn : 0 ≤ δ) (hδ_lt : δ < 1)
    (hresid : ‖ω - ⟪ω, e⟫_ℝ • e‖ ≤ δ * ‖ω‖) :
    Real.sqrt (1 - δ ^ 2) * ‖ω‖ ≤ |⟪ω, e⟫_ℝ| := by
  set φ := ⟪ω, e⟫_ℝ
  have hpyth := alignment_pythagorean ω e he
  have hresid_sq : ‖ω - φ • e‖ ^ 2 ≤ δ ^ 2 * ‖ω‖ ^ 2 := by
    calc ‖ω - φ • e‖ ^ 2 ≤ (δ * ‖ω‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (ω - φ • e)]) hresid
      _ = δ ^ 2 * ‖ω‖ ^ 2 := by ring
  have hφ_sq : (1 - δ ^ 2) * ‖ω‖ ^ 2 ≤ φ ^ 2 := by linarith
  have h1δ : 0 ≤ 1 - δ ^ 2 := by nlinarith
  have hlhs_nn : 0 ≤ Real.sqrt (1 - δ ^ 2) * ‖ω‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hsq_le : (Real.sqrt (1 - δ ^ 2) * ‖ω‖) ^ 2 ≤ φ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1δ]; exact hφ_sq
  have h := Real.sqrt_le_sqrt hsq_le
  rwa [Real.sqrt_sq hlhs_nn, Real.sqrt_sq_eq_abs] at h

end Alignment

/-! ### Transfer Locality -/
section TransferLocality
open ContinuousLinearMap Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Transfer locality bound.** -/
theorem transfer_locality
    (PiA Minv_ij BPj : E →L[ℝ] E)
    (C_a C_r C_b α d : ℝ)
    (hC_a : 0 ≤ C_a)
    (hPiA : ‖PiA‖ ≤ C_a)
    (hMinv : ‖Minv_ij‖ ≤ C_r * exp (-α * d))
    (hBPj : ‖BPj‖ ≤ C_b) :
    ‖PiA.comp (Minv_ij.comp BPj)‖ ≤ C_a * C_r * C_b * exp (-α * d) := by
  have hC_r_exp_nn : 0 ≤ C_r * exp (-α * d) := le_trans (norm_nonneg _) hMinv
  have hC_b : 0 ≤ C_b := le_trans (norm_nonneg _) hBPj
  calc ‖PiA.comp (Minv_ij.comp BPj)‖
      ≤ ‖PiA‖ * ‖Minv_ij.comp BPj‖ := opNorm_comp_le PiA _
    _ ≤ ‖PiA‖ * (‖Minv_ij‖ * ‖BPj‖) := by gcongr; exact opNorm_comp_le _ _
    _ ≤ C_a * (C_r * exp (-α * d) * C_b) := by
        apply mul_le_mul hPiA _ (by positivity) hC_a
        exact mul_le_mul hMinv hBPj (norm_nonneg _) hC_r_exp_nn
    _ = C_a * C_r * C_b * exp (-α * d) := by ring

/-- **Transfer locality (summed version).** -/
theorem transfer_locality_bound
    (PiA Minv_ij BPj : E →L[ℝ] E) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hPiA : ‖PiA‖ ≤ 1)
    (hMinv : ‖Minv_ij‖ ≤ bound)
    (hBPj : ‖BPj‖ ≤ 1) :
    ‖PiA.comp (Minv_ij.comp BPj)‖ ≤ bound := by
  calc ‖PiA.comp (Minv_ij.comp BPj)‖
      ≤ ‖PiA‖ * ‖Minv_ij.comp BPj‖ := opNorm_comp_le PiA _
    _ ≤ ‖PiA‖ * (‖Minv_ij‖ * ‖BPj‖) := by gcongr; exact opNorm_comp_le _ _
    _ ≤ 1 * (bound * 1) := by
        apply mul_le_mul hPiA _ (by positivity) (by linarith)
        exact mul_le_mul hMinv hBPj (norm_nonneg _) hbound
    _ = bound := by ring

end TransferLocality

/-! ### Quadratic Form Bounds -/
section QuadraticFormBounds
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Two-sided quadratic-form bound.** -/
theorem quadratic_form_sandwich
    (M Proj : E →ₗ[ℝ] E) (u : E) (ν_lo ν_hi : ℝ)
    (hProju : Proj u = u)
    (hlow : ∀ x : E, ν_lo * ⟪x, Proj x⟫_ℝ ≤ ⟪x, M x⟫_ℝ)
    (hhigh : ∀ x : E, ⟪x, M x⟫_ℝ ≤ ν_hi * ⟪x, Proj x⟫_ℝ) :
    ν_lo * ‖u‖ ^ 2 ≤ ⟪u, M u⟫_ℝ ∧ ⟪u, M u⟫_ℝ ≤ ν_hi * ‖u‖ ^ 2 := by
  have hProj_inner : ⟪u, Proj u⟫_ℝ = ‖u‖ ^ 2 := by
    rw [hProju, real_inner_self_eq_norm_sq]
  constructor
  · calc ν_lo * ‖u‖ ^ 2 = ν_lo * ⟪u, Proj u⟫_ℝ := by rw [hProj_inner]
      _ ≤ ⟪u, M u⟫_ℝ := hlow u
  · calc ⟪u, M u⟫_ℝ ≤ ν_hi * ⟪u, Proj u⟫_ℝ := hhigh u
      _ = ν_hi * ‖u‖ ^ 2 := by rw [hProj_inner]

/-- **Scaled two-sided quadratic-form bound.** -/
theorem quadratic_form_sandwich_scaled
    (M Proj : E →ₗ[ℝ] E) (u : E) (ν_lo ν_hi c : ℝ)
    (hc : 0 ≤ c)
    (hProju : Proj u = u)
    (hlow : ∀ x : E, ν_lo * ⟪x, Proj x⟫_ℝ ≤ ⟪x, M x⟫_ℝ)
    (hhigh : ∀ x : E, ⟪x, M x⟫_ℝ ≤ ν_hi * ⟪x, Proj x⟫_ℝ) :
    c * ν_lo * ‖u‖ ^ 2 ≤ c * ⟪u, M u⟫_ℝ ∧
    c * ⟪u, M u⟫_ℝ ≤ c * ν_hi * ‖u‖ ^ 2 := by
  obtain ⟨hlo, hhi⟩ := quadratic_form_sandwich M Proj u ν_lo ν_hi hProju hlow hhigh
  constructor
  · calc c * ν_lo * ‖u‖ ^ 2
        = c * (ν_lo * ‖u‖ ^ 2) := by ring
      _ ≤ c * ⟪u, M u⟫_ℝ := by gcongr
  · calc c * ⟪u, M u⟫_ℝ
        ≤ c * (ν_hi * ‖u‖ ^ 2) := by gcongr
      _ = c * ν_hi * ‖u‖ ^ 2 := by ring

open Filter in
/-- **Sequence decay from square domination.** -/
theorem tendsto_zero_of_le_const_mul_sq
    (Γ : ℕ → ℝ) (ratio : ℕ → ℝ) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2)
    (h_ratio : Tendsto ratio atTop (nhds 0)) :
    Tendsto Γ atTop (nhds 0) := by
  apply squeeze_zero hΓ_nn hΓ_le
  have h_sq : Tendsto (fun N => ratio N ^ 2) atTop (nhds 0) := by
    have : Tendsto (fun N => ratio N * ratio N) atTop (nhds (0 * 0)) :=
      h_ratio.mul h_ratio
    simp only [mul_zero] at this
    convert this using 1; ext; ring
  have : Tendsto (fun N => C * ratio N ^ 2) atTop (nhds (C * 0)) :=
    h_sq.const_mul C
  simp only [mul_zero] at this
  exact this

end QuadraticFormBounds

end OperatorEstimates

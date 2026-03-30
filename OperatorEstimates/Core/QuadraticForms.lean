/-
  **Core / quadratic forms.** Bounds on `⟪u, M u⟫` from transfer-controlled quantities;
  headline API includes `QuadraticFormControl` and sandwich lemmas.
-/
import OperatorEstimates.Core.Transfer
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OperatorEstimates

section Helpers
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `re ⟪x, x⟫ = ‖x‖²` for any `RCLike` scalar field. -/
lemma re_inner_self_eq_norm_sq (x : E) :
    RCLike.re ⟪x, x⟫_𝕜 = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := 𝕜)]
  norm_cast

end Helpers

/-! ### Observable Bounds -/
section ObservableBounds
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Upper quadratic-form bound from transfer control.** -/
theorem observable_upper_bound
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃) (ψ : E₁) (ν_hi Δ : ℝ)
    (hψ : ‖ψ‖ = 1) (hΔ : 0 < Δ) (hR : ‖R‖ ≤ Δ⁻¹) (hν : 0 ≤ ν_hi)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜) :
    RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≤
      ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 := by
  set u := A (R (B ψ))
  have hProj_inner : RCLike.re ⟪u, Proj u⟫_𝕜 = ‖u‖ ^ 2 := by
    rw [hProj]
    exact re_inner_self_eq_norm_sq u
  have hsandwich : RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * ‖u‖ ^ 2 := by
    calc RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * RCLike.re ⟪u, Proj u⟫_𝕜 := hhigh u
      _ = ν_hi * ‖u‖ ^ 2 := by rw [hProj_inner]
  have hu : ‖u‖ ≤ ‖A‖ * ‖B‖ / Δ := by
    calc ‖u‖ ≤ ‖A‖ * ‖R (B ψ)‖ := le_opNorm A _
      _ ≤ ‖A‖ * (‖R‖ * ‖B ψ‖) := by gcongr; exact le_opNorm R _
      _ ≤ ‖A‖ * (‖R‖ * (‖B‖ * ‖ψ‖)) := by gcongr; exact le_opNorm B _
      _ = ‖A‖ * ‖R‖ * ‖B‖ := by rw [hψ, mul_one]; ring
      _ ≤ ‖A‖ * Δ⁻¹ * ‖B‖ := by gcongr
      _ = ‖A‖ * ‖B‖ / Δ := by field_simp
  have hu_sq : ‖u‖ ^ 2 ≤ (‖A‖ * ‖B‖ / Δ) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg u]) hu
  calc RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * ‖u‖ ^ 2 := hsandwich
    _ ≤ ν_hi * (‖A‖ * ‖B‖ / Δ) ^ 2 := by gcongr
    _ = ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 := by field_simp

/-- **Abstract upper quadratic-form bound.** -/
theorem observable_upper_bound_abstract
    (M Proj : E₃ →ₗ[𝕜] E₃) (u : E₃) (ν_hi : ℝ)
    (hProj : Proj u = u)
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜) :
    RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * ‖u‖ ^ 2 := by
  have hProj_inner : RCLike.re ⟪u, Proj u⟫_𝕜 = ‖u‖ ^ 2 := by
    rw [hProj]
    exact re_inner_self_eq_norm_sq u
  calc RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * RCLike.re ⟪u, Proj u⟫_𝕜 := hhigh u
    _ = ν_hi * ‖u‖ ^ 2 := by rw [hProj_inner]

/-- **Lower quadratic-form bound from a localized lower estimate.** -/
theorem observable_lower_bound
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃)
    (ψ : E₁) (φ : E₂)
    (r a b ε_B ν_lo : ℝ)
    (hRφ : R φ = (r : 𝕜) • φ) (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_B)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo)
    (hL : a * b * r - ‖A‖ * ‖R‖ * ε_B ≥ 0) :
    RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≥
      ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_B) ^ 2 := by
  set u := A (R (B ψ))
  set L := a * b * r - ‖A‖ * ‖R‖ * ε_B
  have hProj_inner : RCLike.re ⟪u, Proj u⟫_𝕜 = ‖u‖ ^ 2 := by
    rw [hProj]
    exact re_inner_self_eq_norm_sq u
  have hsandwich : ν_lo * ‖u‖ ^ 2 ≤ RCLike.re ⟪u, M u⟫_𝕜 := by
    calc ν_lo * ‖u‖ ^ 2 = ν_lo * RCLike.re ⟪u, Proj u⟫_𝕜 := by rw [hProj_inner]
      _ ≤ RCLike.re ⟪u, M u⟫_𝕜 := hlow u
  have hu : ‖u‖ ≥ L :=
    transfer_lower_exact A R B ψ φ r a b ε_B hRφ hr ha hb hb_nn hη
  have hu_sq : L ^ 2 ≤ ‖u‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg u]) hu
  linarith [mul_le_mul_of_nonneg_left hu_sq hν]

/-- **Abstract lower quadratic-form bound.** -/
theorem observable_lower_bound_abstract
    (M Proj : E₃ →ₗ[𝕜] E₃) (u : E₃) (ν_lo L : ℝ)
    (hProj : Proj u = u)
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo) (hL : 0 ≤ L) (hu : ‖u‖ ≥ L) :
    RCLike.re ⟪u, M u⟫_𝕜 ≥ ν_lo * L ^ 2 := by
  have hProj_inner : RCLike.re ⟪u, Proj u⟫_𝕜 = ‖u‖ ^ 2 := by
    rw [hProj]
    exact re_inner_self_eq_norm_sq u
  have hsandwich : ν_lo * ‖u‖ ^ 2 ≤ RCLike.re ⟪u, M u⟫_𝕜 := by
    calc ν_lo * ‖u‖ ^ 2 = ν_lo * RCLike.re ⟪u, Proj u⟫_𝕜 := by rw [hProj_inner]
      _ ≤ RCLike.re ⟪u, M u⟫_𝕜 := hlow u
  have hu_sq : L ^ 2 ≤ ‖u‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg u]) hu
  linarith [mul_le_mul_of_nonneg_left hu_sq hν]

/-- **Abstract two-sided quadratic-form bound.** -/
theorem observable_two_sided_bound_abstract
    (M Proj : E₃ →ₗ[𝕜] E₃) (u : E₃) (ν_lo ν_hi L : ℝ)
    (hProj : Proj u = u)
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜)
    (hν : 0 ≤ ν_lo) (hL : 0 ≤ L) (hu : ‖u‖ ≥ L) :
    ν_lo * L ^ 2 ≤ RCLike.re ⟪u, M u⟫_𝕜 ∧
      RCLike.re ⟪u, M u⟫_𝕜 ≤ ν_hi * ‖u‖ ^ 2 := by
  exact ⟨observable_lower_bound_abstract M Proj u ν_lo L hProj hlow hν hL hu,
    observable_upper_bound_abstract M Proj u ν_hi hProj hhigh⟩

/-- **Lower bound with an effective localization error term.** -/
theorem observable_lower_bound_effective
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃)
    (ψ : E₁) (φ : E₂)
    (r a b ε_eff ν_lo : ℝ)
    (hRφ : R φ = (r : 𝕜) • φ) (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_eff)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo)
    (hL : a * b * r - ‖A‖ * ‖R‖ * ε_eff ≥ 0) :
    RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≥
      ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_eff) ^ 2 :=
  observable_lower_bound A R B M Proj ψ φ r a b ε_eff ν_lo
    hRφ hr ha hb hb_nn hη hProj hlow hν hL

/-- **Scaled upper quadratic-form bound.** -/
theorem observable_upper_bound_scaled
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃) (ψ : E₁) (ν_hi Δ c : ℝ)
    (hψ : ‖ψ‖ = 1) (hΔ : 0 < Δ) (hR : ‖R‖ ≤ Δ⁻¹) (hν : 0 ≤ ν_hi) (hc : 0 ≤ c)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜) :
    c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≤
      c * ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 := by
  have h := observable_upper_bound A R B M Proj ψ ν_hi Δ hψ hΔ hR hν hProj hhigh
  calc c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜
      ≤ c * (ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2) := mul_le_mul_of_nonneg_left h hc
    _ = c * ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 := by ring

/-- **Scaled lower quadratic-form bound.** -/
theorem observable_lower_bound_scaled
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃)
    (ψ : E₁) (φ : E₂)
    (r a b ε_B ν_lo c : ℝ)
    (hRφ : R φ = (r : 𝕜) • φ) (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_B)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo) (hc : 0 ≤ c)
    (hL : a * b * r - ‖A‖ * ‖R‖ * ε_B ≥ 0) :
    c * ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_B) ^ 2 ≤
      c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 := by
  have h := observable_lower_bound A R B M Proj ψ φ r a b ε_B ν_lo
    hRφ hr ha hb hb_nn hη hProj hlow hν hL
  calc c * ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_B) ^ 2
      = c * (ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_B) ^ 2) := by ring
    _ ≤ c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 :=
        mul_le_mul_of_nonneg_left (by linarith) hc

/-- **Two-sided quadratic-form bound.** -/
theorem observable_two_sided_bound
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃)
    (ψ : E₁) (φ : E₂)
    (r a b ε_B ν_lo ν_hi Δ c : ℝ)
    (hψ : ‖ψ‖ = 1)
    (hΔ : 0 < Δ) (hR : ‖R‖ ≤ Δ⁻¹)
    (hν_hi : 0 ≤ ν_hi) (hν_lo : 0 ≤ ν_lo) (hc : 0 ≤ c)
    (hRφ : R φ = (r : 𝕜) • φ) (hr : 0 ≤ r)
    (ha : ‖A φ‖ ≥ a)
    (hb : ‖⟪φ, B ψ⟫_𝕜‖ ≥ b) (hb_nn : 0 ≤ b)
    (hη : ‖B ψ - ⟪φ, B ψ⟫_𝕜 • φ‖ ≤ ε_B)
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜)
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hL : a * b * r - ‖A‖ * ‖R‖ * ε_B ≥ 0) :
    c * ν_lo * (a * b * r - ‖A‖ * ‖R‖ * ε_B) ^ 2 ≤
      c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ∧
    c * RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≤
      c * ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 :=
  ⟨observable_lower_bound_scaled A R B M Proj ψ φ r a b ε_B ν_lo c
     hRφ hr ha hb hb_nn hη hProj hlow hν_lo hc hL,
   observable_upper_bound_scaled A R B M Proj ψ ν_hi Δ c
     hψ hΔ hR hν_hi hc hProj hhigh⟩

end ObservableBounds

/-! ### Agmon Bounds -/
section AgmonBounds
open ContinuousLinearMap Real
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Agmon-weighted upper quadratic-form bound.** -/
theorem agmon_observable_upper_bound
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃) (ψ : E₁) (ν_hi Δ C₁ C₂ d₁ d₂ : ℝ)
    (hψ : ‖ψ‖ = 1) (hΔ : 0 < Δ) (hR : ‖R‖ ≤ Δ⁻¹) (hν : 0 ≤ ν_hi)
    (hA : ‖A‖ ≤ C₁ * exp (-d₁))
    (hB : ‖B‖ ≤ C₂ * exp (-d₂))
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜) :
    RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≤
      ν_hi * C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂)) / Δ ^ 2 := by
  have hbase := observable_upper_bound A R B M Proj ψ ν_hi Δ hψ hΔ hR hν hProj hhigh
  have hA_sq : ‖A‖ ^ 2 ≤ (C₁ * exp (-d₁)) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg A]) hA
  have hB_sq : ‖B‖ ^ 2 ≤ (C₂ * exp (-d₂)) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg B]) hB
  have hexp : exp (-d₁) ^ 2 * exp (-d₂) ^ 2 = exp (-2 * (d₁ + d₂)) := by
    simp only [sq, ← exp_add]
    congr 1
    ring
  have hprod : ‖A‖ ^ 2 * ‖B‖ ^ 2 ≤ C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂)) := by
    calc ‖A‖ ^ 2 * ‖B‖ ^ 2
        ≤ (C₁ * exp (-d₁)) ^ 2 * (C₂ * exp (-d₂)) ^ 2 := by
          exact mul_le_mul hA_sq hB_sq (sq_nonneg _) (sq_nonneg _)
      _ = C₁ ^ 2 * C₂ ^ 2 * (exp (-d₁) ^ 2 * exp (-d₂) ^ 2) := by ring
      _ = C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂)) := by rw [hexp]
  calc RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜
      ≤ ν_hi * ‖A‖ ^ 2 * ‖B‖ ^ 2 / Δ ^ 2 := hbase
    _ = ν_hi * (‖A‖ ^ 2 * ‖B‖ ^ 2) / Δ ^ 2 := by ring
    _ ≤ ν_hi * (C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂))) / Δ ^ 2 := by gcongr
    _ = ν_hi * C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂)) / Δ ^ 2 := by ring

end AgmonBounds

/-! ### Localized Bounds -/
section LocalizedBounds
open ContinuousLinearMap Real
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Agmon-weighted lower quadratic-form bound.** -/
theorem agmon_observable_lower_bound
    (M Proj : E₃ →ₗ[𝕜] E₃) (u : E₃) (ν_lo c_lo d : ℝ)
    (hProj : Proj u = u)
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo) (hc : 0 ≤ c_lo)
    (hu : ‖u‖ ≥ c_lo * exp (-d)) :
    RCLike.re ⟪u, M u⟫_𝕜 ≥ ν_lo * (c_lo * exp (-d)) ^ 2 := by
  have hL_nn : 0 ≤ c_lo * exp (-d) := mul_nonneg hc (exp_pos _).le
  exact observable_lower_bound_abstract M Proj u ν_lo (c_lo * exp (-d))
    hProj hlow hν hL_nn hu

/-- **Two-sided Agmon-weighted quadratic-form bound.** -/
theorem agmon_observable_two_sided_bound
    (A : E₂ →L[𝕜] E₃) (R : E₂ →L[𝕜] E₂) (B : E₁ →L[𝕜] E₂)
    (M Proj : E₃ →ₗ[𝕜] E₃) (ψ : E₁) (ν_lo ν_hi Δ C₁ C₂ d₁ d₂ c_lo d : ℝ)
    (hψ : ‖ψ‖ = 1) (hΔ : 0 < Δ) (hR : ‖R‖ ≤ Δ⁻¹)
    (hν_lo : 0 ≤ ν_lo) (hν_hi : 0 ≤ ν_hi)
    (hc_lo : 0 ≤ c_lo)
    (hA : ‖A‖ ≤ C₁ * exp (-d₁))
    (hB : ‖B‖ ≤ C₂ * exp (-d₂))
    (hProj : Proj (A (R (B ψ))) = A (R (B ψ)))
    (hhigh : ∀ x : E₃, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜)
    (hlow : ∀ x : E₃, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hu_lower : ‖A (R (B ψ))‖ ≥ c_lo * exp (-d)) :
    ν_lo * (c_lo * exp (-d)) ^ 2 ≤ RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ∧
    RCLike.re ⟪A (R (B ψ)), M (A (R (B ψ)))⟫_𝕜 ≤
      ν_hi * C₁ ^ 2 * C₂ ^ 2 * exp (-2 * (d₁ + d₂)) / Δ ^ 2 :=
  ⟨agmon_observable_lower_bound M Proj (A (R (B ψ))) ν_lo c_lo d
     hProj hlow hν_lo hc_lo hu_lower,
   agmon_observable_upper_bound A R B M Proj ψ ν_hi Δ C₁ C₂ d₁ d₂
     hψ hΔ hR hν_hi hA hB hProj hhigh⟩

end LocalizedBounds

/-! ### Uniform Lower Bounds -/
section UniformLowerBounds
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]

/-- **Uniform lower bound from a persistent norm threshold.** -/
theorem uniform_lower_bound
    (Γ : ℕ → ℝ) (L : ℕ → ℝ) (ν_lo c_min : ℝ)
    (hν : 0 ≤ ν_lo) (hc : 0 < c_min)
    (hL : ∀ N, c_min ≤ L N)
    (hΓ_ge : ∀ N, ν_lo * L N ^ 2 ≤ Γ N) :
    ∀ N, ν_lo * c_min ^ 2 ≤ Γ N := by
  intro N
  have hsq : c_min ^ 2 ≤ L N ^ 2 :=
    sq_le_sq' (by linarith [hL N]) (hL N)
  have h1 := mul_le_mul_of_nonneg_left hsq hν
  linarith [hΓ_ge N]

/-- **Scaled uniform lower bound from a persistent norm threshold.** -/
theorem uniform_lower_bound_scaled
    (Γ : ℕ → ℝ) (L : ℕ → ℝ) (ν_lo c_min c : ℝ)
    (hν : 0 ≤ ν_lo) (hc_min : 0 < c_min) (hc : 0 ≤ c)
    (hL : ∀ N, c_min ≤ L N)
    (hΓ_ge : ∀ N, c * ν_lo * L N ^ 2 ≤ Γ N) :
    ∀ N, c * ν_lo * c_min ^ 2 ≤ Γ N := by
  intro N
  have hsq : c_min ^ 2 ≤ L N ^ 2 :=
    sq_le_sq' (by linarith [hL N]) (hL N)
  have h1 := mul_le_mul_of_nonneg_left hsq (mul_nonneg hc hν)
  linarith [hΓ_ge N]

/-- **Uniform lower bound from abstract quadratic-form control.** -/
theorem uniform_lower_bound_from_vectors
    (M Proj : ℕ → (E₃ →ₗ[𝕜] E₃)) (u : ℕ → E₃)
    (L : ℕ → ℝ) (ν_lo c_min : ℝ)
    (hν : 0 ≤ ν_lo) (hc : 0 < c_min)
    (hProj : ∀ N, Proj N (u N) = u N)
    (hlow : ∀ N x, ν_lo * RCLike.re ⟪x, Proj N x⟫_𝕜 ≤ RCLike.re ⟪x, M N x⟫_𝕜)
    (hL_nn : ∀ N, 0 ≤ L N)
    (hL_ge : ∀ N, c_min ≤ L N)
    (hu : ∀ N, ‖u N‖ ≥ L N) :
    ∀ N, ν_lo * c_min ^ 2 ≤ RCLike.re ⟪u N, M N (u N)⟫_𝕜 := by
  have hΓ_ge : ∀ N, ν_lo * L N ^ 2 ≤ RCLike.re ⟪u N, M N (u N)⟫_𝕜 := by
    intro N
    exact observable_lower_bound_abstract (M N) (Proj N) (u N) ν_lo (L N)
      (hProj N) (hlow N) hν (hL_nn N) (hu N)
  exact uniform_lower_bound (fun N => RCLike.re ⟪u N, M N (u N)⟫_𝕜) L ν_lo c_min hν hc hL_ge hΓ_ge

end UniformLowerBounds

section BundledControl
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Bundled two-sided quadratic-form control relative to a projection. -/
structure QuadraticFormControl (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  M : E →ₗ[𝕜] E
  Proj : E →ₗ[𝕜] E
  ν_lo : ℝ
  ν_hi : ℝ
  lower : ∀ x : E, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜
  upper : ∀ x : E, RCLike.re ⟪x, M x⟫_𝕜 ≤ ν_hi * RCLike.re ⟪x, Proj x⟫_𝕜
  ν_lo_nonneg : 0 ≤ ν_lo
  ν_hi_nonneg : 0 ≤ ν_hi

namespace QuadraticFormControl

/-- Lower quadratic-form bound at a projected vector. -/
theorem lower_at (ctrl : QuadraticFormControl 𝕜 E) (u : E) (L : ℝ)
    (hProj : ctrl.Proj u = u) (hL : 0 ≤ L) (hu : ‖u‖ ≥ L) :
    ctrl.ν_lo * L ^ 2 ≤ RCLike.re ⟪u, ctrl.M u⟫_𝕜 :=
  observable_lower_bound_abstract ctrl.M ctrl.Proj u ctrl.ν_lo L
    hProj ctrl.lower ctrl.ν_lo_nonneg hL hu

/-- Upper quadratic-form bound at a projected vector. -/
theorem upper_at (ctrl : QuadraticFormControl 𝕜 E) (u : E)
    (hProj : ctrl.Proj u = u) :
    RCLike.re ⟪u, ctrl.M u⟫_𝕜 ≤ ctrl.ν_hi * ‖u‖ ^ 2 :=
  observable_upper_bound_abstract ctrl.M ctrl.Proj u ctrl.ν_hi hProj ctrl.upper

/-- Two-sided quadratic-form bound at a projected vector. -/
theorem two_sided_at (ctrl : QuadraticFormControl 𝕜 E) (u : E) (L : ℝ)
    (hProj : ctrl.Proj u = u) (hL : 0 ≤ L) (hu : ‖u‖ ≥ L) :
    ctrl.ν_lo * L ^ 2 ≤ RCLike.re ⟪u, ctrl.M u⟫_𝕜 ∧
      RCLike.re ⟪u, ctrl.M u⟫_𝕜 ≤ ctrl.ν_hi * ‖u‖ ^ 2 :=
  observable_two_sided_bound_abstract ctrl.M ctrl.Proj u ctrl.ν_lo ctrl.ν_hi L
    hProj ctrl.lower ctrl.upper ctrl.ν_lo_nonneg hL hu

end QuadraticFormControl
end BundledControl

end OperatorEstimates

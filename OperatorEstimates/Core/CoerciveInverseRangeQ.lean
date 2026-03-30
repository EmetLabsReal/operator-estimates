/-
  **Core / coercive inverse on `range Q`.** Complement-sector coercivity and a right inverse on the
  subspace `range Q`, lifted to an ambient `Rinv : E →L E` with `‖Rinv‖ ≤ γ⁻¹` when `‖Q‖ ≤ 1`, plus
  sector identities `Q ∘ Rinv = Rinv` and `Q * H * Q ∘ Rinv = Q`.

  All norm estimates on the ambient lift are proved via pointwise bounds, avoiding the need for
  `opNorm` on `ContinuousLinearMap` between submodule subtypes (which Lean's instance synthesizer
  cannot resolve automatically when the scalar field is `RCLike`).
-/
import OperatorEstimates.Core.Transfer
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace OperatorEstimates

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Range of an idempotent bounded projection as a submodule. -/
def rangeSubmodule (Q : E →L[𝕜] E) : Submodule 𝕜 E :=
  LinearMap.range (Q : E →ₗ[𝕜] E)

lemma mem_rangeSubmodule_iff {Q : E →L[𝕜] E} {x : E} :
    x ∈ rangeSubmodule Q ↔ ∃ y : E, Q y = x := by
  simp [rangeSubmodule, LinearMap.mem_range]

lemma Q_mem_rangeSubmodule (Q : E →L[𝕜] E) (h : Q.comp Q = Q) (x : E) :
    Q x ∈ rangeSubmodule Q := by
  rw [mem_rangeSubmodule_iff]
  refine ⟨Q x, ?_⟩
  simp [← comp_apply, h]

lemma Q_eq_self_of_mem_rangeSubmodule {Q : E →L[𝕜] E} (h : Q.comp Q = Q) {x : E}
    (hx : x ∈ rangeSubmodule Q) : Q x = x := by
  rcases mem_rangeSubmodule_iff.mp hx with ⟨y, hy⟩
  rw [← hy, ← comp_apply, h]

lemma QHQ_maps_to_rangeSubmodule (Q : E →L[𝕜] E) (hQQ : Q.comp Q = Q) (H : E →L[𝕜] E)
    (u : rangeSubmodule Q) : (Q * H * Q) u.val ∈ rangeSubmodule Q :=
  Q_mem_rangeSubmodule Q hQQ _

/-- Restriction of `Q * H * Q` to an endomorphism of `rangeSubmodule Q`. -/
noncomputable def M_U (Q : E →L[𝕜] E) (hQQ : Q.comp Q = Q) (H : E →L[𝕜] E) :
    rangeSubmodule Q →L[𝕜] rangeSubmodule Q :=
  ((Q * H * Q).comp (rangeSubmodule Q).subtypeL).codRestrict (rangeSubmodule Q)
    (fun u => QHQ_maps_to_rangeSubmodule Q hQQ H u)

@[simp]
lemma M_U_apply_coe (Q : E →L[𝕜] E) (hQQ : Q.comp Q = Q) (H : E →L[𝕜] E)
    (u : rangeSubmodule Q) : (M_U Q hQQ H u : E) = (Q * H * Q) u.val :=
  rfl

lemma inner_M_U (Q : E →L[𝕜] E) (hQQ : Q.comp Q = Q) (H : E →L[𝕜] E) (u : rangeSubmodule Q) :
    RCLike.re (inner 𝕜 u (M_U Q hQQ H u)) =
      RCLike.re (inner 𝕜 u.val ((Q * H * Q) u.val)) := by
  simp [Submodule.coe_inner, M_U_apply_coe]

/-- Coercive right inverse on `range Q`. -/
structure CoerciveRightInverseOnRangeQ (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  Q : E →L[𝕜] E
  H : E →L[𝕜] E
  hQQ : Q.comp Q = Q
  Minv_U : rangeSubmodule Q →L[𝕜] rangeSubmodule Q
  γ : ℝ
  gamma_pos : 0 < γ
  coercive_on_range :
    ∀ u : rangeSubmodule Q,
      γ * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 u (M_U Q hQQ H u))
  rightInvOnRange : (M_U Q hQQ H).comp Minv_U = ContinuousLinearMap.id 𝕜 (rangeSubmodule Q)

namespace CoerciveRightInverseOnRangeQ

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- Pointwise bound on the inverse: `‖Minv_U u‖ ≤ γ⁻¹ * ‖u‖` for all `u` in `range Q`.
This is the core coercivity estimate, proved without needing `opNorm` on submodule-typed maps. -/
theorem Minv_U_pointwise_bound (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (u : rangeSubmodule c.Q) : ‖c.Minv_U u‖ ≤ c.γ⁻¹ * ‖u‖ := by
  set v := c.Minv_U u with hv_def
  by_cases hv : (v : E) = 0
  · -- v = 0 ⟹ ‖v‖ = 0
    have hvn : ‖(v : E)‖ = 0 := by rw [hv, norm_zero]
    show ‖(v : E)‖ ≤ c.γ⁻¹ * ‖(u : E)‖
    rw [hvn]
    exact mul_nonneg (inv_nonneg.mpr c.gamma_pos.le) (norm_nonneg _)
  · have hvnorm : 0 < ‖(v : E)‖ := norm_pos_iff.mpr hv
    have hMv_eq_u : M_U c.Q c.hQQ c.H v = u := by
      have := congrFun (congrArg DFunLike.coe c.rightInvOnRange) u
      simpa [comp_apply] using this
    have hcoer : c.γ * ‖(v : E)‖ ^ 2 ≤ RCLike.re (inner 𝕜 v (M_U c.Q c.hQQ c.H v)) :=
      c.coercive_on_range v
    have hCS : RCLike.re (inner 𝕜 v (M_U c.Q c.hQQ c.H v)) ≤ ‖(v : E)‖ * ‖(u : E)‖ := by
      rw [hMv_eq_u]
      calc RCLike.re (inner 𝕜 v u)
          ≤ |RCLike.re (inner 𝕜 v u)| := le_abs_self _
        _ ≤ ‖inner 𝕜 v u‖ := RCLike.abs_re_le_norm _
        _ ≤ ‖(v : E)‖ * ‖(u : E)‖ := norm_inner_le_norm (v : E) (u : E)
    have key : c.γ * ‖(v : E)‖ ≤ ‖(u : E)‖ := by
      have h1 : c.γ * (‖(v : E)‖ * ‖(v : E)‖) ≤ ‖(v : E)‖ * ‖(u : E)‖ := by
        calc c.γ * (‖(v : E)‖ * ‖(v : E)‖) = c.γ * ‖(v : E)‖ ^ 2 := by ring
          _ ≤ RCLike.re (inner 𝕜 v (M_U c.Q c.hQQ c.H v)) := hcoer
          _ ≤ ‖(v : E)‖ * ‖(u : E)‖ := hCS
      exact le_of_mul_le_mul_left (by linarith) hvnorm
    show ‖(v : E)‖ ≤ c.γ⁻¹ * ‖(u : E)‖
    calc ‖(v : E)‖ = c.γ⁻¹ * (c.γ * ‖(v : E)‖) := by
          rw [inv_mul_cancel_left₀ c.gamma_pos.ne']
      _ ≤ c.γ⁻¹ * ‖(u : E)‖ := by
          apply mul_le_mul_of_nonneg_left key (inv_nonneg.mpr c.gamma_pos.le)

/-- `Q` with codomain restricted to `range Q`. -/
noncomputable def Q_to_range (c : CoerciveRightInverseOnRangeQ 𝕜 E) :
    E →L[𝕜] rangeSubmodule c.Q :=
  c.Q.codRestrict (rangeSubmodule c.Q) (Q_mem_rangeSubmodule c.Q c.hQQ)

/-- Ambient lift: apply `Q`, invert on `range Q`, embed back into `E`. -/
noncomputable def RinvAmbient (c : CoerciveRightInverseOnRangeQ 𝕜 E) : E →L[𝕜] E :=
  (rangeSubmodule c.Q).subtypeL.comp (c.Minv_U.comp c.Q_to_range)

theorem RinvAmbient_opNorm_bound (c : CoerciveRightInverseOnRangeQ 𝕜 E) (hQn : ‖c.Q‖ ≤ 1) :
    ‖c.RinvAmbient‖ ≤ c.γ⁻¹ := by
  rw [opNorm_le_iff (inv_nonneg.mpr c.gamma_pos.le)]
  intro x
  -- RinvAmbient x = ι(Minv_U(Q_to_range x)); subtype embedding preserves norms
  show ‖(rangeSubmodule c.Q).subtypeL (c.Minv_U (c.Q_to_range x))‖ ≤ c.γ⁻¹ * ‖x‖
  -- ‖ι(v)‖ = ‖v‖ (subtype norm = ambient norm, definitional)
  change ‖(c.Minv_U (c.Q_to_range x) : E)‖ ≤ c.γ⁻¹ * ‖x‖
  set u := c.Q_to_range x
  -- ‖(Minv_U u : E)‖ = ‖Minv_U u‖ (definitional)
  have hγinv_nn : 0 ≤ c.γ⁻¹ := inv_nonneg.mpr c.gamma_pos.le
  calc ‖(c.Minv_U u : E)‖
      = ‖c.Minv_U u‖ := rfl
    _ ≤ c.γ⁻¹ * ‖u‖ := c.Minv_U_pointwise_bound u
    _ = c.γ⁻¹ * ‖c.Q x‖ := rfl -- ‖Q_to_range x‖ = ‖Q x‖ (definitional)
    _ ≤ c.γ⁻¹ * (‖c.Q‖ * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left (le_opNorm c.Q x) hγinv_nn
    _ ≤ c.γ⁻¹ * (1 * ‖x‖) := by
        apply mul_le_mul_of_nonneg_left _ hγinv_nn
        exact mul_le_mul_of_nonneg_right hQn (norm_nonneg _)
    _ = c.γ⁻¹ * ‖x‖ := by ring

theorem Q_comp_RinvAmbient (c : CoerciveRightInverseOnRangeQ 𝕜 E) :
    c.Q.comp c.RinvAmbient = c.RinvAmbient := by
  ext x
  simp only [RinvAmbient, comp_apply, Submodule.subtypeL_apply]
  set u : rangeSubmodule c.Q := c.Minv_U (c.Q_to_range x)
  have hu : (u : E) ∈ rangeSubmodule c.Q := u.property
  exact Q_eq_self_of_mem_rangeSubmodule c.hQQ hu

theorem QHQ_comp_RinvAmbient (c : CoerciveRightInverseOnRangeQ 𝕜 E) :
    (c.Q * c.H * c.Q).comp c.RinvAmbient = c.Q := by
  ext x
  simp only [comp_apply, RinvAmbient, mul_apply, Submodule.subtypeL_apply]
  set v : rangeSubmodule c.Q := c.Q_to_range x
  have hvQ : (v : E) = c.Q x := rfl
  set w : rangeSubmodule c.Q := c.Minv_U v
  have hM : M_U c.Q c.hQQ c.H w = v := by
    simpa [w, comp_apply] using congrFun (congrArg DFunLike.coe c.rightInvOnRange) v
  have hwQ : c.Q (w : E) = (w : E) :=
    Q_eq_self_of_mem_rangeSubmodule c.hQQ w.property
  have hM' : (M_U c.Q c.hQQ c.H w : E) = c.Q (c.H (w : E)) := by
    rw [M_U_apply_coe]
    simp only [mul_apply, hwQ]
  calc
    (c.Q * c.H * c.Q) (w : E) = c.Q (c.H (c.Q (w : E))) := rfl
    _ = c.Q (c.H (w : E)) := by rw [hwQ]
    _ = (M_U c.Q c.hQQ c.H w : E) := hM'.symm
    _ = (v : E) := by rw [hM]
    _ = c.Q x := hvQ.symm

end CoerciveRightInverseOnRangeQ

/-! ### Finite-dimensional constructor

In finite dimensions, coercivity of `Q * H * Q` on `range Q` automatically gives invertibility.
This closes the gap between a spectral gap hypothesis and a full `CoerciveRightInverseOnRangeQ`
bundle. -/

section FiniteDimensionalInverse

open scoped InnerProductSpace

variable [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
private theorem M_U_injective_of_coercive
    (Q : E →L[𝕜] E) (hQQ : Q.comp Q = Q) (H : E →L[𝕜] E)
    (γ : ℝ) (hγ : 0 < γ)
    (hcoercive : ∀ u : rangeSubmodule Q,
      γ * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 u (M_U Q hQQ H u))) :
    Function.Injective (M_U Q hQQ H) := by
  intro u v huv
  have h : M_U Q hQQ H (u - v) = 0 := by rw [map_sub, sub_eq_zero.mpr huv]
  have hle : γ * ‖(u - v : ↥(rangeSubmodule Q))‖ ^ 2 ≤ 0 := by
    calc γ * ‖(u - v : ↥(rangeSubmodule Q))‖ ^ 2
        ≤ RCLike.re (inner 𝕜 (u - v) (M_U Q hQQ H (u - v))) := hcoercive (u - v)
      _ = 0 := by rw [h, inner_zero_right, map_zero]
  have h_sq_nonpos : ‖(u - v : ↥(rangeSubmodule Q))‖ ^ 2 ≤ 0 := by
    by_contra h_neg
    push_neg at h_neg
    linarith [mul_pos hγ h_neg]
  have h_sq_eq : ‖(u - v : ↥(rangeSubmodule Q))‖ ^ 2 = 0 :=
    le_antisymm h_sq_nonpos (sq_nonneg _)
  have : ‖(u - v : ↥(rangeSubmodule Q))‖ = 0 := by
    rwa [sq_eq_zero_iff] at h_sq_eq
  rwa [norm_eq_zero, sub_eq_zero] at this

/-- In finite dimensions, a coercive operator `Q * H * Q` restricted to `range Q` is automatically
invertible. This constructs the full `CoerciveRightInverseOnRangeQ` bundle — including the right
inverse and its norm bound — from just the coercivity hypothesis.

This is the theorem that closes the pipeline from "complement block has a spectral gap" to
the full reduction API. -/
noncomputable def CoerciveRightInverseOnRangeQ.fromCoercivity
    (Q : E →L[𝕜] E) (H : E →L[𝕜] E) (hQQ : Q.comp Q = Q)
    (γ : ℝ) (hγ : 0 < γ)
    (hcoercive : ∀ u : rangeSubmodule Q,
      γ * ‖u‖ ^ 2 ≤ RCLike.re (inner 𝕜 u (M_U Q hQQ H u))) :
    CoerciveRightInverseOnRangeQ 𝕜 E :=
  let hinj := M_U_injective_of_coercive Q hQQ H γ hγ hcoercive
  let hsurj : Function.Surjective (M_U Q hQQ H) :=
    LinearMap.injective_iff_surjective.mp hinj
  let linEquiv := LinearEquiv.ofBijective (M_U Q hQQ H).toLinearMap ⟨hinj, hsurj⟩
  let contEquiv := linEquiv.toContinuousLinearEquiv
  { Q := Q
    H := H
    hQQ := hQQ
    Minv_U := contEquiv.symm.toContinuousLinearMap
    γ := γ
    gamma_pos := hγ
    coercive_on_range := hcoercive
    rightInvOnRange := by
      ext1 u
      exact contEquiv.apply_symm_apply u }

end FiniteDimensionalInverse

end OperatorEstimates

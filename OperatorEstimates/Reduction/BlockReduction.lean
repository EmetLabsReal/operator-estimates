/-
  **Reduction / block reduction.** Effective Schur-style operator, explicit error and
  locality bounds, integrated reduction principle, and bundled
  `ComplementaryProjections` / `EffectiveReductionSetup`.

  Convenience constructors: `ComplementaryProjections.ofIdempotent` (from `P² = P`),
  `ComplementaryProjections.swap` (exchange P ↔ Q).

  Derived quantities on `EffectiveReductionSetup`: `delta` (`λ²/γ`), `chi` (`λ²/γ²`),
  `ratio` (`λ/γ`), with `gap_survives_iff_chi` and `delta_eq_chi_mul_gamma`.

  Algebraic block splitting is in `OperatorEstimates.Core.Splitting`.
  All sections are over `RCLike 𝕜` unless noted.
-/
import OperatorEstimates.Core.Perturbation
import OperatorEstimates.Core.QuadraticForms
import OperatorEstimates.Core.Splitting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OperatorEstimates

/-! ### Effective Operator -/
section EffectiveOperator
open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Effective operator definition.**

`P * H * Q` and `Q * H * P` are the cross-sector transfer terms. The correction term removes
their leading effect, leaving an operator confined to the retained `P`-sector up to the
quantitative error controlled below. -/
def effectiveOperator (P H Q Rinv : E →L[𝕜] E) : E →L[𝕜] E :=
  P * H * P - P * H * Q * Rinv * Q * H * P

/-- **Pointwise evaluation of the effective operator.** -/
theorem effectiveOperator_apply (P H Q Rinv : E →L[𝕜] E) (x : E) :
    effectiveOperator P H Q Rinv x = P (H (P x)) - P (H (Q (Rinv (Q (H (P x)))))) := by
  rfl

/-- **Effective operator error bound.** -/
theorem effective_operator_error
    (P H Q Rinv : E →L[𝕜] E) (lam Δ : ℝ)
    (hΔ : 0 < Δ) (hlam : 0 ≤ lam)
    (hPHQ : ‖P * H * Q‖ ≤ lam)
    (hQHP : ‖Q * H * P‖ ≤ lam)
    (hRinv : ‖Rinv‖ ≤ Δ⁻¹) :
    ‖effectiveOperator P H Q Rinv - P * H * P‖ ≤ lam ^ 2 / Δ := by
  set X := (P * H * Q) * (Rinv * (Q * H * P))
  have h_diff : effectiveOperator P H Q Rinv - P * H * P = - X := by
    dsimp [effectiveOperator]
    have h_assoc : P * H * Q * Rinv * Q * H * P = X := by simp only [X, mul_assoc]
    rw [h_assoc]
    abel
  rw [h_diff, norm_neg]
  have h_bound : ‖X‖ ≤ ‖P * H * Q‖ * (‖Rinv‖ * ‖Q * H * P‖) := by
    calc ‖X‖ = ‖(P * H * Q) * (Rinv * (Q * H * P))‖ := rfl
      _ ≤ ‖P * H * Q‖ * ‖Rinv * (Q * H * P)‖ := norm_mul_le _ _
      _ ≤ ‖P * H * Q‖ * (‖Rinv‖ * ‖Q * H * P‖) := by gcongr; exact norm_mul_le _ _
  calc ‖X‖ ≤ ‖P * H * Q‖ * (‖Rinv‖ * ‖Q * H * P‖) := h_bound
    _ ≤ lam * (Δ⁻¹ * lam) := by gcongr
    _ = lam ^ 2 * Δ⁻¹ := by ring
    _ = lam ^ 2 / Δ := by rw [div_eq_mul_inv]

open scoped InnerProductSpace in
/-- **Rayleigh control for the effective operator.** -/
theorem effective_operator_rayleigh
    (P H Q Rinv : E →L[𝕜] E) (lam Δ : ℝ)
    (hΔ : 0 < Δ) (hlam : 0 ≤ lam)
    (hPHQ : ‖P * H * Q‖ ≤ lam)
    (hQHP : ‖Q * H * P‖ ≤ lam)
    (hRinv : ‖Rinv‖ ≤ Δ⁻¹)
    (x : E) (hx : ‖x‖ = 1) :
    |RCLike.re ⟪x, effectiveOperator P H Q Rinv x⟫_𝕜 -
      RCLike.re ⟪x, P (H (P x))⟫_𝕜| ≤ lam ^ 2 / Δ := by
  have h_err := effective_operator_error P H Q Rinv lam Δ hΔ hlam hPHQ hQHP hRinv
  have h_ray := rayleigh_perturbation (effectiveOperator P H Q Rinv) (P * H * P) x
    (lam ^ 2 / Δ) hx h_err
  have h_eval : RCLike.re ⟪x, (P * H * P) x⟫_𝕜 = RCLike.re ⟪x, P (H (P x))⟫_𝕜 := rfl
  rwa [h_eval] at h_ray

end EffectiveOperator

/-! ### Stability Estimates -/
section StabilityEstimates
open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Effective gap remains positive under small coupling.** -/
theorem effective_gap_positive_of_small_coupling
    (γ lam : ℝ)
    (hγ : 0 < γ)
    (h_pert : lam ^ 2 < γ ^ 2) :
    0 < γ - lam ^ 2 / γ := by
  have h_sq_lt : lam ^ 2 < γ * γ := by linarith [h_pert]
  have h_div_lt : lam ^ 2 / γ < γ := (div_lt_iff₀ hγ).mpr h_sq_lt
  linarith

/-- **Coercivity survives under perturbation.** -/
theorem coercivity_survives_under_perturbation
    (H H' : E →L[𝕜] E) (γ ε : ℝ)
    (hcoercive : ∀ x : E, γ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H x⟫_𝕜)
    (hpert : ‖H' - H‖ ≤ ε) :
    ∀ x : E, (γ - ε) * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H' x⟫_𝕜 :=
  coercivity_perturbation H' H γ ε hcoercive hpert

/-- **Lower norm bounds produce a transfer-scale lower bound.** -/
theorem transfer_scale_lower_bound
    (A R B : E →L[𝕜] E) (a b r_low : ℝ)
    (hb : 0 ≤ b)
    (hr : 0 ≤ r_low)
    (hA : a ≤ ‖A‖)
    (hR : r_low ≤ ‖R‖)
    (hB : b ≤ ‖B‖) :
    a * r_low * b ≤ ‖A‖ * ‖R‖ * ‖B‖ := by
  have h1 : a * r_low ≤ ‖A‖ * ‖R‖ := mul_le_mul hA hR hr (norm_nonneg A)
  exact mul_le_mul h1 hB hb (mul_nonneg (norm_nonneg A) (norm_nonneg R))

/-- **Quadratic-form lower bound from a norm threshold.** -/
theorem observable_lower_bound_from_scale
    (M Proj : E →ₗ[𝕜] E) (u : E) (ν_lo L_coup : ℝ)
    (hProj : Proj u = u)
    (hlow : ∀ x : E, ν_lo * RCLike.re ⟪x, Proj x⟫_𝕜 ≤ RCLike.re ⟪x, M x⟫_𝕜)
    (hν : 0 ≤ ν_lo)
    (hL_nn : 0 ≤ L_coup)
    (hu : L_coup ≤ ‖u‖) :
    ν_lo * L_coup ^ 2 ≤ RCLike.re ⟪u, M u⟫_𝕜 := by
  have hProj_inner : RCLike.re ⟪u, Proj u⟫_𝕜 = ‖u‖ ^ 2 := by
    rw [hProj]
    exact re_inner_self_eq_norm_sq u
  have hsandwich : ν_lo * ‖u‖ ^ 2 ≤ RCLike.re ⟪u, M u⟫_𝕜 := by
    calc ν_lo * ‖u‖ ^ 2 = ν_lo * RCLike.re ⟪u, Proj u⟫_𝕜 := by rw [hProj_inner]
      _ ≤ RCLike.re ⟪u, M u⟫_𝕜 := hlow u
  have hu_sq : L_coup ^ 2 ≤ ‖u‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg u]) hu
  linarith [mul_le_mul_of_nonneg_left hu_sq hν]

end StabilityEstimates

/-! ### Locality Bounds -/
section LocalityBounds
open ContinuousLinearMap Real

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Transfer locality with exponential resolvent decay.** -/
theorem transfer_locality_with_exponential_resolvent_decay
    (PHQ_i Rinv_ij QHP_j : E →L[𝕜] E) (lam_i lam_j C_r α d : ℝ)
    (hlam_i : 0 ≤ lam_i) (hC_r : 0 ≤ C_r)
    (h_PHQ : ‖PHQ_i‖ ≤ lam_i)
    (h_QHP : ‖QHP_j‖ ≤ lam_j)
    (h_Rinv : ‖Rinv_ij‖ ≤ C_r * exp (-α * d)) :
    ‖PHQ_i * Rinv_ij * QHP_j‖ ≤ lam_i * lam_j * C_r * exp (-α * d) := by
  have h_assoc : PHQ_i * Rinv_ij * QHP_j = PHQ_i * (Rinv_ij * QHP_j) := by
    rw [mul_assoc]
  calc ‖PHQ_i * Rinv_ij * QHP_j‖
      = ‖PHQ_i * (Rinv_ij * QHP_j)‖ := by rw [h_assoc]
    _ ≤ ‖PHQ_i‖ * ‖Rinv_ij * QHP_j‖ := norm_mul_le _ _
    _ ≤ ‖PHQ_i‖ * (‖Rinv_ij‖ * ‖QHP_j‖) := by gcongr; exact norm_mul_le _ _
    _ ≤ lam_i * (C_r * exp (-α * d) * lam_j) := by gcongr
    _ = lam_i * lam_j * C_r * exp (-α * d) := by ring

/-- **Effective operator locality.** -/
theorem effective_operator_locality
    (PHQ_ij Rinv_ij QHP_ji : E →L[𝕜] E) (lam C_r α d : ℝ)
    (hlam : 0 ≤ lam) (hC_r : 0 ≤ C_r)
    (h_PHQ : ‖PHQ_ij‖ ≤ lam)
    (h_QHP : ‖QHP_ji‖ ≤ lam)
    (h_Rinv : ‖Rinv_ij‖ ≤ C_r * exp (-α * d)) :
    ‖PHQ_ij * Rinv_ij * QHP_ji‖ ≤ lam ^ 2 * C_r * exp (-α * d) := by
  have h := transfer_locality_with_exponential_resolvent_decay PHQ_ij Rinv_ij QHP_ji
    lam lam C_r α d hlam hC_r h_PHQ h_QHP h_Rinv
  calc ‖PHQ_ij * Rinv_ij * QHP_ji‖
      ≤ lam * lam * C_r * exp (-α * d) := h
    _ = lam ^ 2 * C_r * exp (-α * d) := by ring

end LocalityBounds

/-! ### Effective Reduction -/
section EffectiveReduction
open ContinuousLinearMap Real

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Integrated Reduction Principle.** -/
theorem effective_reduction_principle
    (H P Q Rinv : E →L[𝕜] E) (γ lam : ℝ)
    (hγ : 0 < γ)
    (hlam : 0 ≤ lam)
    (hPHQ : ‖P * H * Q‖ ≤ lam)
    (hQHP : ‖Q * H * P‖ ≤ lam)
    (hRinv : ‖Rinv‖ ≤ γ⁻¹) :
    ‖effectiveOperator P H Q Rinv - P * H * P‖ ≤ lam ^ 2 / γ ∧
    (lam ^ 2 < γ ^ 2 → 0 < γ - lam ^ 2 / γ) ∧
    (∀ (C_r α d : ℝ), 0 ≤ C_r → ‖Rinv‖ ≤ C_r * exp (-α * d) →
      ‖P * H * Q * Rinv * Q * H * P‖ ≤ lam ^ 2 * C_r * exp (-α * d)) := by
  constructor
  · exact effective_operator_error P H Q Rinv lam γ hγ hlam hPHQ hQHP hRinv
  constructor
  · intro h_pert
    exact effective_gap_positive_of_small_coupling γ lam hγ h_pert
  · intro C_r α d hC_r h_decay
    exact effective_operator_locality (P * H * Q) Rinv (Q * H * P) lam C_r α d hlam hC_r
      hPHQ hQHP h_decay

end EffectiveReduction

section BundledReduction
open ContinuousLinearMap Real
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Bundled complementary projections for block decomposition arguments. -/
structure ComplementaryProjections (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  P : E →L[𝕜] E
  Q : E →L[𝕜] E
  sum_eq : P + Q = 1
  P_idem : P * P = P
  Q_idem : Q * Q = Q
  PQ_zero : P * Q = 0
  QP_zero : Q * P = 0

/-- Build `ComplementaryProjections` from a single idempotent `P` and `Q := 1 - P`.
All five algebraic identities are derived from `P² = P`. -/
def ComplementaryProjections.ofIdempotent
    (P : E →L[𝕜] E) (hP : P * P = P) : ComplementaryProjections 𝕜 E where
  P := P
  Q := 1 - P
  sum_eq := by simp
  P_idem := hP
  Q_idem := by
    show (1 - P) * (1 - P) = 1 - P
    calc (1 - P) * (1 - P) = 1 - P - P + P * P := by
          simp [mul_sub, sub_mul, mul_one, one_mul]; abel
      _ = 1 - P - P + P := by rw [hP]
      _ = 1 - P := by abel
  PQ_zero := by
    show P * (1 - P) = 0
    calc P * (1 - P) = P - P * P := by simp [mul_sub, mul_one]
      _ = P - P := by rw [hP]
      _ = 0 := by simp
  QP_zero := by
    show (1 - P) * P = 0
    calc (1 - P) * P = P - P * P := by simp [sub_mul, one_mul]
      _ = P - P := by rw [hP]
      _ = 0 := by simp

/-- Swap the roles of `P` and `Q` in a complementary projection pair. -/
def ComplementaryProjections.swap
    (decomp : ComplementaryProjections 𝕜 E) : ComplementaryProjections 𝕜 E where
  P := decomp.Q
  Q := decomp.P
  sum_eq := by rw [add_comm]; exact decomp.sum_eq
  P_idem := decomp.Q_idem
  Q_idem := decomp.P_idem
  PQ_zero := decomp.QP_zero
  QP_zero := decomp.PQ_zero

namespace ComplementaryProjections

/-- `Q = 1 - P`. -/
theorem Q_eq (decomp : ComplementaryProjections 𝕜 E) : decomp.Q = 1 - decomp.P := by
  have h := decomp.sum_eq
  have : decomp.Q = decomp.P + decomp.Q - decomp.P := by abel
  rw [this, h]

/-- `P = 1 - Q`. -/
theorem P_eq (decomp : ComplementaryProjections 𝕜 E) : decomp.P = 1 - decomp.Q := by
  have h := decomp.sum_eq
  have : decomp.P = decomp.P + decomp.Q - decomp.Q := by abel
  rw [this, h]

/-- `P * P` as a `comp` for interoperability. -/
theorem P_comp_P (decomp : ComplementaryProjections 𝕜 E) : decomp.P.comp decomp.P = decomp.P :=
  decomp.P_idem

/-- `Q * Q` as a `comp` for interoperability. -/
theorem Q_comp_Q (decomp : ComplementaryProjections 𝕜 E) : decomp.Q.comp decomp.Q = decomp.Q :=
  decomp.Q_idem

theorem block_expansion (decomp : ComplementaryProjections 𝕜 E) (H : E →L[𝕜] E) :
    H = decomp.P * H * decomp.P + decomp.P * H * decomp.Q +
      decomp.Q * H * decomp.P + decomp.Q * H * decomp.Q :=
  OperatorEstimates.block_expansion H decomp.P decomp.Q decomp.sum_eq

theorem block_expansion_apply (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E) (x : E) :
    H x = decomp.P (H (decomp.P x)) + decomp.P (H (decomp.Q x)) +
      decomp.Q (H (decomp.P x)) + decomp.Q (H (decomp.Q x)) :=
  OperatorEstimates.block_expansion_apply H decomp.P decomp.Q decomp.sum_eq x

theorem block_diagonal_of_vanishing_offdiag (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (hPHQ : decomp.P * H * decomp.Q = 0)
    (hQHP : decomp.Q * H * decomp.P = 0) :
    H = decomp.P * H * decomp.P + decomp.Q * H * decomp.Q :=
  OperatorEstimates.block_decomposition_of_vanishing_offdiag
    H decomp.P decomp.Q decomp.sum_eq hPHQ hQHP

theorem invariant_subspaces (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E) (x : E)
    (hPHQ : decomp.P * H * decomp.Q = 0)
    (hQHP : decomp.Q * H * decomp.P = 0) :
    (decomp.P x = x → H x = decomp.P (H x)) ∧
      (decomp.Q x = x → H x = decomp.Q (H x)) :=
  OperatorEstimates.invariant_subspace_of_block_diagonal
    H decomp.P decomp.Q decomp.sum_eq hPHQ hQHP x

end ComplementaryProjections

/-- Bundled data for effective block-reduction estimates.

This structure packages the data needed to define and control the effective operator
`P H P - P H Q Rinv Q H P`. -/
structure EffectiveReductionSetup (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  decomp : ComplementaryProjections 𝕜 E
  H : E →L[𝕜] E
  Rinv : E →L[𝕜] E
  γ : ℝ
  lam : ℝ
  gamma_pos : 0 < γ
  lam_nonneg : 0 ≤ lam
  PHQ_bound : ‖decomp.P * H * decomp.Q‖ ≤ lam
  QHP_bound : ‖decomp.Q * H * decomp.P‖ ≤ lam
  Rinv_bound : ‖Rinv‖ ≤ γ⁻¹

namespace EffectiveReductionSetup

/-- The Schur error budget `δ = λ² / γ`. -/
noncomputable def delta (cfg : EffectiveReductionSetup 𝕜 E) : ℝ :=
  cfg.lam ^ 2 / cfg.γ

/-- The control parameter `χ = λ² / γ²`. When `χ ≪ 1`, the reduction is perturbative. -/
noncomputable def chi (cfg : EffectiveReductionSetup 𝕜 E) : ℝ :=
  cfg.lam ^ 2 / cfg.γ ^ 2

/-- The ratio `λ / γ`. -/
noncomputable def ratio (cfg : EffectiveReductionSetup 𝕜 E) : ℝ :=
  cfg.lam / cfg.γ

/-- `δ = χ * γ`. -/
theorem delta_eq_chi_mul_gamma (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.delta = cfg.chi * cfg.γ := by
  simp only [delta, chi]
  field_simp [cfg.gamma_pos.ne']

/-- The control parameter is nonneg. -/
theorem chi_nonneg (cfg : EffectiveReductionSetup 𝕜 E) : 0 ≤ cfg.chi :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Near-singular rate theorem.** The security margin decomposes as `γ - δ = γ * (1 - χ)`.
The margin degrades linearly in `χ` with rate `γ`. -/
theorem security_margin_eq (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.γ - cfg.delta = cfg.γ * (1 - cfg.chi) := by
  rw [cfg.delta_eq_chi_mul_gamma]; ring

/-- The security margin is nonneg iff `χ ≤ 1`. -/
theorem security_margin_nonneg_iff (cfg : EffectiveReductionSetup 𝕜 E) :
    0 ≤ cfg.γ - cfg.delta ↔ cfg.chi ≤ 1 := by
  rw [cfg.security_margin_eq]
  constructor
  · intro h; nlinarith [cfg.gamma_pos]
  · intro h; nlinarith [cfg.gamma_pos]

/-- Quantitative gap: the security margin is bounded below by `γ * (1 - χ)` and above by `γ`. -/
theorem security_margin_bounds (cfg : EffectiveReductionSetup 𝕜 E)
    (hchi : cfg.chi ≤ 1) :
    0 ≤ cfg.γ - cfg.delta ∧ cfg.γ - cfg.delta ≤ cfg.γ := by
  rw [cfg.security_margin_eq]
  constructor
  · nlinarith [cfg.gamma_pos]
  · nlinarith [cfg.gamma_pos, cfg.chi_nonneg]

/-- `chi < 1` iff the gap survives. -/
theorem gap_survives_iff_chi (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.chi < 1 ↔ cfg.lam ^ 2 < cfg.γ ^ 2 := by
  rw [chi, div_lt_one (sq_pos_of_pos cfg.gamma_pos)]

/-- The error budget is nonneg. -/
theorem delta_nonneg (cfg : EffectiveReductionSetup 𝕜 E) : 0 ≤ cfg.delta :=
  div_nonneg (sq_nonneg _) cfg.gamma_pos.le

/-- The ratio is nonneg. -/
theorem ratio_nonneg (cfg : EffectiveReductionSetup 𝕜 E) : 0 ≤ cfg.ratio :=
  div_nonneg cfg.lam_nonneg cfg.gamma_pos.le

/-- `χ = (λ / γ)²`. -/
theorem chi_eq_ratio_sq (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.chi = cfg.ratio ^ 2 := by
  simp only [chi, ratio, div_pow]

/-- `δ = ratio * λ`. -/
theorem delta_eq_ratio_mul_lam (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.delta = cfg.ratio * cfg.lam := by
  simp only [delta, ratio]
  field_simp [cfg.gamma_pos.ne']

def effectiveOperator (cfg : EffectiveReductionSetup 𝕜 E) : E →L[𝕜] E :=
  OperatorEstimates.effectiveOperator cfg.decomp.P cfg.H cfg.decomp.Q cfg.Rinv

theorem error_bound (cfg : EffectiveReductionSetup 𝕜 E) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤
      cfg.lam ^ 2 / cfg.γ :=
  OperatorEstimates.effective_operator_error
    cfg.decomp.P cfg.H cfg.decomp.Q cfg.Rinv cfg.lam cfg.γ
    cfg.gamma_pos cfg.lam_nonneg cfg.PHQ_bound cfg.QHP_bound cfg.Rinv_bound

/-- Small cross-sector coupling places the retained block in an effective localization regime:
the reduced dynamics are quantitatively close to the projected `P H P` dynamics. -/
theorem effective_localization_regime (cfg : EffectiveReductionSetup 𝕜 E) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤
      cfg.lam ^ 2 / cfg.γ :=
  cfg.error_bound

theorem gap_survives (cfg : EffectiveReductionSetup 𝕜 E)
    (hsmall : cfg.lam ^ 2 < cfg.γ ^ 2) :
    0 < cfg.γ - cfg.lam ^ 2 / cfg.γ :=
  OperatorEstimates.effective_gap_positive_of_small_coupling
    cfg.γ cfg.lam cfg.gamma_pos hsmall

/-- Error bound stated in terms of `delta`. -/
theorem error_bound_delta (cfg : EffectiveReductionSetup 𝕜 E) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤ cfg.delta :=
  cfg.error_bound

/-- Gap survival stated in terms of `chi`. -/
theorem gap_survives_of_chi (cfg : EffectiveReductionSetup 𝕜 E)
    (hchi : cfg.chi < 1) :
    0 < cfg.γ - cfg.delta :=
  cfg.gap_survives (cfg.gap_survives_iff_chi.mp hchi)

theorem locality_bound (cfg : EffectiveReductionSetup 𝕜 E)
    (C_r α d : ℝ) (hC_r : 0 ≤ C_r)
    (hdecay : ‖cfg.Rinv‖ ≤ C_r * exp (-α * d)) :
    ‖cfg.decomp.P * cfg.H * cfg.decomp.Q * cfg.Rinv *
      cfg.decomp.Q * cfg.H * cfg.decomp.P‖ ≤
      cfg.lam ^ 2 * C_r * exp (-α * d) :=
  OperatorEstimates.effective_operator_locality
    (cfg.decomp.P * cfg.H * cfg.decomp.Q) cfg.Rinv
    (cfg.decomp.Q * cfg.H * cfg.decomp.P)
    cfg.lam C_r α d cfg.lam_nonneg hC_r cfg.PHQ_bound cfg.QHP_bound hdecay

theorem conclusion (cfg : EffectiveReductionSetup 𝕜 E) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤
      cfg.lam ^ 2 / cfg.γ ∧
    (cfg.lam ^ 2 < cfg.γ ^ 2 → 0 < cfg.γ - cfg.lam ^ 2 / cfg.γ) ∧
    (∀ (C_r α d : ℝ), 0 ≤ C_r → ‖cfg.Rinv‖ ≤ C_r * exp (-α * d) →
      ‖cfg.decomp.P * cfg.H * cfg.decomp.Q * cfg.Rinv *
        cfg.decomp.Q * cfg.H * cfg.decomp.P‖ ≤
        cfg.lam ^ 2 * C_r * exp (-α * d)) :=
  OperatorEstimates.effective_reduction_principle
    cfg.H cfg.decomp.P cfg.decomp.Q cfg.Rinv cfg.γ cfg.lam
    cfg.gamma_pos cfg.lam_nonneg cfg.PHQ_bound cfg.QHP_bound cfg.Rinv_bound

/-- The Schur error scale `ε = λ² / (γ (1 - χ)) = δ / (1 - χ)`.
This is the primary reduction-validity invariant: `ε → 0` is the acceptance criterion
for Mosco convergence of reduced forms to the effective retained-sector form. -/
noncomputable def schurErrorScale (cfg : EffectiveReductionSetup 𝕜 E) : ℝ :=
  cfg.delta / (1 - cfg.chi)

/-- `ε = δ / (1 - χ)` by definition. -/
theorem schurErrorScale_eq (cfg : EffectiveReductionSetup 𝕜 E) :
    cfg.schurErrorScale = cfg.delta / (1 - cfg.chi) :=
  rfl

/-- When `χ < 1`, `ε = λ² / (γ * (1 - χ))`. -/
theorem schurErrorScale_eq_lam_sq_div (cfg : EffectiveReductionSetup 𝕜 E)
    (_hchi : cfg.chi < 1) :
    cfg.schurErrorScale = cfg.lam ^ 2 / (cfg.γ * (1 - cfg.chi)) := by
  simp only [schurErrorScale, delta]
  rw [div_div]

/-- When `χ < 1`, `ε` is nonneg. -/
theorem schurErrorScale_nonneg (cfg : EffectiveReductionSetup 𝕜 E)
    (hchi : cfg.chi < 1) :
    0 ≤ cfg.schurErrorScale := by
  unfold schurErrorScale
  exact div_nonneg cfg.delta_nonneg (by linarith)

/-- `δ = ε * (1 - χ)`. The error budget factors through the Schur error scale. -/
theorem delta_eq_schurErrorScale_mul (cfg : EffectiveReductionSetup 𝕜 E)
    (hchi : cfg.chi < 1) :
    cfg.delta = cfg.schurErrorScale * (1 - cfg.chi) := by
  simp only [schurErrorScale]
  rw [div_mul_cancel₀]
  exact ne_of_gt (by linarith)

/-- The Schur error bound in terms of `ε`:
`‖H_eff - PHP‖ ≤ ε * (1 - χ)`. -/
theorem error_bound_schurErrorScale (cfg : EffectiveReductionSetup 𝕜 E)
    (hchi : cfg.chi < 1) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤
      cfg.schurErrorScale * (1 - cfg.chi) := by
  rw [← cfg.delta_eq_schurErrorScale_mul hchi]
  exact cfg.error_bound_delta

end EffectiveReductionSetup
end BundledReduction

end OperatorEstimates

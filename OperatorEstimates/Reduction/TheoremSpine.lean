import OperatorEstimates.Constitutive.ThresholdDomain
import OperatorEstimates.Reduction.EffectiveFromCoercivity
import OperatorEstimates.Reduction.NoGo

/-!
  **Reduction / theorem spine.** Compressed public theorem interface for the bounded engine,
  the constitutive threshold bridge, and the endpoint boundary pair.

  This module does not add new mathematics. It packages the existing reduction and endpoint
  layers into the small set of statements that define the repo's public theorem spine.
-/

namespace OperatorEstimates

open Filter
open Real
open scoped Topology

section RegimeGeometry

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! A public admissibility witness fixes the proposed sectorization and records the lifted
right-inverse identities that tie `Rinv` back to the omitted block `Q * H * Q`. -/
structure AdmittedReductionSetup (𝕜 : Type*) (E : Type*)
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    extends EffectiveReductionSetup 𝕜 E where
  Q_comp_Rinv :
    toEffectiveReductionSetup.decomp.Q.comp toEffectiveReductionSetup.Rinv =
      toEffectiveReductionSetup.Rinv
  QHQ_comp_Rinv :
    (toEffectiveReductionSetup.decomp.Q * toEffectiveReductionSetup.H *
        toEffectiveReductionSetup.decomp.Q).comp
        toEffectiveReductionSetup.Rinv =
      toEffectiveReductionSetup.decomp.Q

namespace AdmittedReductionSetup

noncomputable def fromCoerciveRightInverseOnRangeQ
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (hQ : c.Q = decomp.Q)
    (hH : c.H = H)
    (hQn : ‖c.Q‖ ≤ 1) :
    AdmittedReductionSetup 𝕜 E where
  toEffectiveReductionSetup :=
    EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ
      decomp H lam hlam hPHQ hQHP c hQ hH hQn
  Q_comp_Rinv :=
    EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ_Q_comp_Rinv
      decomp H lam hlam hPHQ hQHP c hQ hH hQn
  QHQ_comp_Rinv :=
    EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ_QHQ_comp_Rinv
      decomp H lam hlam hPHQ hQHP c hQ hH hQn

end AdmittedReductionSetup

/-- Static admissibility means that the bounded reduction setup has been constructed for the
candidate operator on a fixed proposed sectorization. -/
def StaticAdmissible
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E) : Prop :=
  ∃ cfg : AdmittedReductionSetup 𝕜 E, cfg.decomp = decomp ∧ cfg.H = H

/-- Pre-admissible systems do not carry a valid reduction setup, so no `χ` regime is evaluated. -/
def PreAdmissible
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E) : Prop :=
  ¬ StaticAdmissible decomp H

/-- Subcriticality is a regime condition on an already-constructed setup. -/
def Subcritical (cfg : AdmittedReductionSetup 𝕜 E) : Prop :=
  cfg.chi < 1

/-- Supercriticality is the complementary regime condition on an already-constructed setup. -/
def Supercritical (cfg : AdmittedReductionSetup 𝕜 E) : Prop :=
  1 ≤ cfg.chi

/-- Any constructed setup witnesses static admissibility of its underlying operator. -/
theorem static_admissible_of_setup (cfg : AdmittedReductionSetup 𝕜 E) :
    StaticAdmissible cfg.decomp cfg.H :=
  ⟨cfg, rfl, rfl⟩

theorem preAdmissible_iff_not_staticAdmissible
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E) :
    PreAdmissible decomp H ↔ ¬ StaticAdmissible decomp H :=
  Iff.rfl

namespace AdmittedReductionSetup

/-- On a valid setup, subcriticality is exactly the strict inequality `λ < γ`. -/
theorem subcritical_iff_lam_lt_gamma (cfg : AdmittedReductionSetup 𝕜 E) :
    Subcritical cfg ↔ cfg.lam < cfg.γ := by
  unfold Subcritical
  rw [cfg.gap_survives_iff_chi]
  constructor <;> intro h <;> nlinarith [cfg.lam_nonneg, cfg.gamma_pos, h]

/-- On a valid setup, subcriticality is exactly the strict inequality `δ < γ`. -/
theorem subcritical_iff_delta_lt_gamma (cfg : AdmittedReductionSetup 𝕜 E) :
    Subcritical cfg ↔ cfg.delta < cfg.γ := by
  unfold Subcritical
  rw [cfg.delta_eq_chi_mul_gamma]
  constructor <;> intro h
  · have hγ := cfg.gamma_pos
    nlinarith
  · have hγ := cfg.gamma_pos
    nlinarith

/-- On a valid setup, supercriticality is exactly the weak inequality `γ ≤ δ`. -/
theorem supercritical_iff_gamma_le_delta (cfg : AdmittedReductionSetup 𝕜 E) :
    Supercritical cfg ↔ cfg.γ ≤ cfg.delta := by
  unfold Supercritical
  rw [cfg.delta_eq_chi_mul_gamma]
  constructor <;> intro h
  · have hγ := cfg.gamma_pos
    nlinarith
  · have hγ := cfg.gamma_pos
    nlinarith

/-- On a valid setup, the subcritical regime implies residual gap survival. -/
theorem subcritical_implies_gap_survival (cfg : AdmittedReductionSetup 𝕜 E)
    (hsub : Subcritical cfg) :
    0 < cfg.γ - cfg.delta :=
  cfg.gap_survives_of_chi hsub

end AdmittedReductionSetup

end RegimeGeometry

namespace EffectiveReductionSetup

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Canonical bounded reduction theorem: Schur-scale error, residual gap survival under
`chi < 1`, and locality once complement decay is supplied. -/
theorem bounded_reduction_theorem (cfg : EffectiveReductionSetup 𝕜 E) :
    ‖cfg.effectiveOperator - cfg.decomp.P * cfg.H * cfg.decomp.P‖ ≤ cfg.delta ∧
    (cfg.chi < 1 → 0 < cfg.γ - cfg.delta) ∧
    (∀ (C_r α d : ℝ), 0 ≤ C_r → ‖cfg.Rinv‖ ≤ C_r * exp (-α * d) →
      ‖cfg.decomp.P * cfg.H * cfg.decomp.Q * cfg.Rinv *
        cfg.decomp.Q * cfg.H * cfg.decomp.P‖ ≤
        cfg.lam ^ 2 * C_r * exp (-α * d)) :=
  ⟨cfg.error_bound_delta, cfg.gap_survives_of_chi, cfg.locality_bound⟩

end EffectiveReductionSetup

namespace Constitutive.ThresholdDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Canonical constitutive bridge theorem: once the controlled regime is proved, the threshold
layer activates the bounded engine and returns the first reduction conclusions. -/
theorem threshold_to_reduction_theorem
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    ‖td.effectiveOperator h_control - td.decomp.P * td.H * td.decomp.P‖ ≤
      (td.toEffectiveReductionSetup h_control).delta ∧
    ((td.toEffectiveReductionSetup h_control).chi < 1 →
      0 < (td.toEffectiveReductionSetup h_control).γ -
        (td.toEffectiveReductionSetup h_control).delta) :=
  ⟨td.toEffectiveReductionSetup_error_bound_delta h_control,
    td.toEffectiveReductionSetup_gap_survives_of_chi h_control⟩

end Constitutive.ThresholdDomain

section Boundary

/-- Canonical positive endpoint theorem. The closure mechanism is exactly the rigidity
implication supplied by the application. -/
theorem boundary_closure_theorem
    (Γ ratio : ℕ → ℝ) (C : ℝ)
    (hΓ_nn : ∀ N, 0 ≤ Γ N)
    (hΓ_le : ∀ N, Γ N ≤ C * ratio N ^ 2)
    (h_rigidity : ¬ Tendsto ratio atTop (nhds 0) →
      Tendsto Γ atTop (nhds 0)) :
    Tendsto Γ atTop (nhds 0) :=
  Cascade.conditional_regularity_from_rigidity Γ ratio C hΓ_nn hΓ_le h_rigidity

/-- Canonical negative endpoint theorem. Deterministic saturation data alone do not justify the
closure implication. -/
theorem boundary_obstruction_theorem
    (lam gamma Gamma : ℕ → ℝ) (a c γ0 : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hγ0 : 0 < γ0)
    (h_ratio_lower : ∀ᶠ n in atTop, c ≤ lam n / gamma n)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_Gamma_lower : ∀ᶠ n in atTop, a * (lam n) ^ 2 / gamma n ≤ Gamma n) :
    ¬ (¬ Tendsto (fun n => lam n / gamma n) atTop (𝓝 0) →
        Tendsto Gamma atTop (𝓝 0)) :=
  NoGo.no_go_saturation lam gamma Gamma a c γ0 ha hc hγ0
    h_ratio_lower h_gamma_lower h_Gamma_lower

end Boundary

end OperatorEstimates

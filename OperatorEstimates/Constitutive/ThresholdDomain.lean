import OperatorEstimates.Reduction.EffectiveFromCoercivity

/-!
  **Constitutive / threshold domain.** Structural bounded-operator bridge for constitutive
  admissibility data.

  The point of this layer is to make threshold-dependent control explicit:
  - before the threshold is crossed, the omitted-sector control data are unavailable;
  - after the threshold is crossed, the omitted-sector coercive bundle is supplied;
  - the existing reduction engine then applies without modification.

  This module is intentionally structural in v1:
  - no unbounded operator or closed-form formalization,
  - no Dirichlet-form or full Feller boundary semantics,
  - no positivity or sub-Markov layer.
-/

namespace OperatorEstimates.Constitutive

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

/-- Threshold-dependent constitutive admissibility data for a bounded operator.

`threshold < theta` is the controlled regime in v1. Once that theorem-level condition is
available, the bundle `controlData` provides the omitted-sector coercive inverse data needed by
the reduction engine. -/
structure ThresholdDomain (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  H : E →L[ℝ] E
  decomp : ComplementaryProjections ℝ E
  theta : ℝ
  threshold : ℝ
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  PHQ_bound : ‖decomp.P * H * decomp.Q‖ ≤ lam
  QHP_bound : ‖decomp.Q * H * decomp.P‖ ≤ lam
  q_norm_le_one : ‖decomp.Q‖ ≤ 1
  controlData : threshold < theta → CoerciveRightInverseOnRangeQ ℝ E
  control_Q : ∀ h_control : threshold < theta, (controlData h_control).Q = decomp.Q
  control_H : ∀ h_control : threshold < theta, (controlData h_control).H = H

namespace ThresholdDomain

/-- The omitted sector is controlled exactly when the threshold has been crossed. -/
def controlledRegime (td : ThresholdDomain E) : Prop :=
  td.threshold < td.theta

/-- Post-threshold bridge into the existing effective reduction engine. -/
noncomputable def toEffectiveReductionSetup
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    EffectiveReductionSetup ℝ E :=
  EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ
    td.decomp td.H td.lam td.lam_nonneg td.PHQ_bound td.QHP_bound
    (td.controlData h_control) (td.control_Q h_control) (td.control_H h_control)
    (by simpa [td.control_Q h_control] using td.q_norm_le_one)

/-- The threshold bridge is definitionally the direct coercive range-`Q` constructor. -/
theorem toEffectiveReductionSetup_eq_fromCoerciveRightInverseOnRangeQ
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    td.toEffectiveReductionSetup h_control =
      EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ
        td.decomp td.H td.lam td.lam_nonneg td.PHQ_bound td.QHP_bound
        (td.controlData h_control) (td.control_Q h_control) (td.control_H h_control)
        (by simpa [td.control_Q h_control] using td.q_norm_le_one) :=
  rfl

/-- The effective operator available after threshold crossing. -/
noncomputable def effectiveOperator
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    E →L[ℝ] E :=
  (td.toEffectiveReductionSetup h_control).effectiveOperator

/-- Quantitative Schur error bound available after threshold crossing. -/
theorem toEffectiveReductionSetup_error_bound
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    ‖td.effectiveOperator h_control - td.decomp.P * td.H * td.decomp.P‖ ≤
      td.lam ^ 2 / (td.toEffectiveReductionSetup h_control).γ := by
  simpa [effectiveOperator, toEffectiveReductionSetup] using
    (td.toEffectiveReductionSetup h_control).error_bound

/-- The same post-threshold error bound stated using `delta`. -/
theorem toEffectiveReductionSetup_error_bound_delta
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime) :
    ‖td.effectiveOperator h_control - td.decomp.P * td.H * td.decomp.P‖ ≤
      (td.toEffectiveReductionSetup h_control).delta := by
  simpa [effectiveOperator, toEffectiveReductionSetup] using
    (td.toEffectiveReductionSetup h_control).error_bound_delta

/-- Gap survival in the post-threshold regime. -/
theorem toEffectiveReductionSetup_gap_survives_of_chi
    (td : ThresholdDomain E)
    (h_control : td.controlledRegime)
    (hchi : (td.toEffectiveReductionSetup h_control).chi < 1) :
    0 < (td.toEffectiveReductionSetup h_control).γ -
      (td.toEffectiveReductionSetup h_control).delta :=
  (td.toEffectiveReductionSetup h_control).gap_survives_of_chi hchi

end ThresholdDomain

end

end OperatorEstimates.Constitutive

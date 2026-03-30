import OperatorEstimates.Constitutive.ThresholdDomain
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
  **Examples / threshold crossing.** Synthetic bounded-operator example showing:

  - a threshold-dependent constitutive bridge,
  - pre-threshold absence of omitted-sector control,
  - post-threshold activation of the reduction engine,
  - explicit `delta` and `chi` consequences after threshold crossing.

  This file is intentionally synthetic. Its role is to demonstrate the API shape of
  `Constitutive.ThresholdDomain`, not to model a full PDE or boundary-classification problem.
-/

namespace OperatorEstimates.ThresholdCrossing

open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

abbrev State := EuclideanSpace ℝ (Fin 2)

abbrev retain : Fin 2 := 0
abbrev fast : Fin 2 := 1

/-- Rank-one coordinate transfer. -/
abbrev entry (i j : Fin 2) : State →L[ℝ] State :=
  (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i (1 : ℝ))

@[simp]
theorem entry_apply (i j k : Fin 2) (x : State) :
    entry i j x k = if k = i then x j else 0 := by
  simp [entry, EuclideanSpace.single]

private theorem coord_norm_le (x : State) (i : Fin 2) : ‖x i‖ ≤ ‖x‖ := by
  simpa [State] using (PiLp.norm_apply_le (p := (2 : ENNReal)) (x := x) i)

private theorem proj_norm_le_one (i : Fin 2) :
    ‖(EuclideanSpace.proj i : State →L[ℝ] ℝ)‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff]
  · intro x
    simpa using coord_norm_le x i
  · norm_num

private theorem single_norm_one (i : Fin 2) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  calc
    ‖EuclideanSpace.single i (1 : ℝ)‖ = ‖(1 : ℝ)‖ := by
      exact PiLp.norm_single (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) i (1 : ℝ)
    _ = 1 := by norm_num

private theorem entry_norm_le_one (i j : Fin 2) :
    ‖entry i j‖ ≤ 1 := by
  calc
    ‖entry i j‖
        = ‖(EuclideanSpace.proj j : State →L[ℝ] ℝ)‖ *
            ‖EuclideanSpace.single i (1 : ℝ)‖ := by
              rw [entry]
              exact ContinuousLinearMap.norm_smulRight_apply
                (EuclideanSpace.proj j : State →L[ℝ] ℝ)
                (EuclideanSpace.single i (1 : ℝ))
    _ ≤ 1 * 1 := by
          have hproj := proj_norm_le_one j
          have hsingle : ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 := by
            rw [single_norm_one]
          have hmul :
              ‖(EuclideanSpace.proj j : State →L[ℝ] ℝ)‖ *
                  ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 * 1 :=
            mul_le_mul hproj hsingle (norm_nonneg _) (by norm_num)
          simpa using hmul
    _ = 1 := by norm_num

abbrev pProjection : State →L[ℝ] State := entry retain retain
abbrev qProjection : State →L[ℝ] State := entry fast fast

private theorem pProjection_idem :
    pProjection.comp pProjection = pProjection := by
  ext x k
  fin_cases k <;> simp [pProjection, entry, retain]

private theorem qProjection_idem :
    qProjection.comp qProjection = qProjection := by
  ext x k
  fin_cases k <;> simp [qProjection, entry, fast]

private theorem p_add_q :
    pProjection + qProjection = (1 : State →L[ℝ] State) := by
  ext x k
  fin_cases k <;> simp [pProjection, qProjection, entry, retain, fast]

private theorem pq_zero :
    pProjection * qProjection = 0 := by
  ext x k
  fin_cases k <;> simp [pProjection, qProjection, entry, retain, fast]

private theorem qp_zero :
    qProjection * pProjection = 0 := by
  ext x k
  fin_cases k <;> simp [pProjection, qProjection, entry, retain, fast]

/-- One-way transfer from the omitted sector into the retained sector. -/
abbrev jumpOp : State →L[ℝ] State := ((1 : ℝ) / 4) • entry retain fast

/-- Synthetic threshold-dependent operator. The omitted sector is controlled only once `theta > 0`.
-/
abbrev H (theta : ℝ) : State →L[ℝ] State :=
  pProjection + theta • qProjection + jumpOp

abbrev decomp : ComplementaryProjections ℝ State where
  P := pProjection
  Q := qProjection
  sum_eq := p_add_q
  P_idem := pProjection_idem
  Q_idem := qProjection_idem
  PQ_zero := pq_zero
  QP_zero := qp_zero

private theorem q_norm_le_one : ‖qProjection‖ ≤ 1 :=
  entry_norm_le_one fast fast

private theorem jump_norm_le_quarter : ‖jumpOp‖ ≤ (1 : ℝ) / 4 := by
  calc
    ‖jumpOp‖ = ‖((1 : ℝ) / 4 : ℝ)‖ * ‖entry retain fast‖ := by
      rw [jumpOp, norm_smul]
    _ ≤ ((1 : ℝ) / 4) * 1 := by
      have hentry := entry_norm_le_one retain fast
      have hq : 0 ≤ (1 : ℝ) / 4 := by norm_num
      have habs : ‖((1 : ℝ) / 4 : ℝ)‖ = (1 : ℝ) / 4 := by
        rw [Real.norm_of_nonneg hq]
      rw [habs]
      exact mul_le_mul_of_nonneg_left hentry hq
    _ = (1 : ℝ) / 4 := by norm_num

private theorem pHq_eq_jump (theta : ℝ) :
    pProjection * H theta * qProjection = jumpOp := by
  ext x k
  fin_cases k <;>
    simp [H, jumpOp, pProjection, qProjection, entry, retain, fast,
      mul_comm, mul_assoc]

private theorem qHp_eq_zero (theta : ℝ) :
    qProjection * H theta * pProjection = 0 := by
  ext x k
  fin_cases k <;> simp [H, jumpOp, pProjection, qProjection, entry, retain, fast]

private theorem qHq_eq_thetaQ (theta : ℝ) :
    qProjection * H theta * qProjection = theta • qProjection := by
  ext x k
  fin_cases k <;>
    simp [H, jumpOp, pProjection, qProjection, entry, retain, fast,
      mul_comm, mul_assoc]

private theorem retain_coord_zero_of_rangeQ (u : rangeSubmodule qProjection) :
    (u : State) retain = 0 := by
  have hQ : qProjection (u : State) = (u : State) :=
    Q_eq_self_of_mem_rangeSubmodule qProjection_idem u.property
  have := congrArg (fun y : State => y retain) hQ
  simpa [qProjection, entry, fast, retain] using this.symm

private theorem M_U_theta_apply (theta : ℝ) (u : rangeSubmodule qProjection) :
    M_U qProjection qProjection_idem (H theta) u = theta • u := by
  ext k
  fin_cases k <;>
    simp [M_U_apply_coe, qHq_eq_thetaQ, qProjection, entry, fast,
      retain_coord_zero_of_rangeQ u]

private theorem coercive_on_range (theta : ℝ)
    (u : rangeSubmodule qProjection) :
    theta * ‖u‖ ^ 2 ≤ RCLike.re (inner ℝ u (M_U qProjection qProjection_idem (H theta) u)) := by
  rw [M_U_theta_apply theta u]
  have hinner :
      RCLike.re (inner ℝ u (theta • u)) = theta * ‖u‖ ^ 2 := by
    calc
      RCLike.re (inner ℝ u (theta • u))
          = RCLike.re ((theta : ℝ) * inner ℝ u u) := by
              simpa using congrArg RCLike.re (inner_smul_right (𝕜 := ℝ) u u theta)
      _ = theta * RCLike.re (inner ℝ u u) := by simp
      _ = theta * ‖u‖ ^ 2 := by
            have hself : RCLike.re (inner ℝ u u) = ‖u‖ ^ 2 := by
              exact inner_self_eq_norm_sq (𝕜 := ℝ) u
            rw [hself]
  have hinner' : inner ℝ u (theta • u) = theta * ‖u‖ ^ 2 := by
    simpa using hinner
  simp [hinner']

/-- Threshold-dependent constitutive data. The controlled regime is exactly `0 < theta`. -/
noncomputable def thresholdDomain (theta : ℝ) :
    OperatorEstimates.Constitutive.ThresholdDomain State where
  H := H theta
  decomp := decomp
  theta := theta
  threshold := 0
  lam := (1 : ℝ) / 4
  lam_nonneg := by norm_num
  PHQ_bound := by
    rw [pHq_eq_jump theta]
    exact jump_norm_le_quarter
  QHP_bound := by
    rw [qHp_eq_zero theta]
    simp
  q_norm_le_one := q_norm_le_one
  controlData h_control :=
    CoerciveRightInverseOnRangeQ.fromCoercivity
      qProjection (H theta) qProjection_idem theta h_control
      (coercive_on_range theta)
  control_Q _ := rfl
  control_H _ := rfl

/-- The threshold regime is exactly positivity of the threshold parameter. -/
theorem controlledRegime_iff (theta : ℝ) :
    (thresholdDomain theta).controlledRegime ↔ 0 < theta :=
  Iff.rfl

/-- Post-threshold the reduction setup becomes available. -/
noncomputable def postThresholdSetup (theta : ℝ) (h_control : 0 < theta) :
    EffectiveReductionSetup ℝ State :=
  (thresholdDomain theta).toEffectiveReductionSetup h_control

/-- Synthetic post-threshold Schur error bound. -/
theorem postThreshold_error_bound_delta (theta : ℝ) (h_control : 0 < theta) :
    ‖(thresholdDomain theta).effectiveOperator h_control
        - decomp.P * H theta * decomp.P‖ ≤
      (postThresholdSetup theta h_control).delta :=
  (thresholdDomain theta).toEffectiveReductionSetup_error_bound_delta h_control

/-- Post-threshold gap survival phrased using the derived parameter `chi`. -/
theorem postThreshold_gap_survives_of_chi (theta : ℝ) (h_control : 0 < theta)
    (hchi : (postThresholdSetup theta h_control).chi < 1) :
    0 < (postThresholdSetup theta h_control).γ - (postThresholdSetup theta h_control).delta :=
  (thresholdDomain theta).toEffectiveReductionSetup_gap_survives_of_chi h_control hchi

end

end OperatorEstimates.ThresholdCrossing

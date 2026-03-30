import OperatorEstimates.Reduction.TheoremSpine
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
  **Examples / regimes.** Small public finite-dimensional witnesses for the three
  regime branches attached to a fixed proposed sectorization:

  - `quarterTurn_preAdmissible` — the omitted block is identically zero, so no admitted setup
    exists for the chosen split.
  - `stable_subcritical` — small cross-sector coupling with positive omitted-block control.
  - `unstable_supercritical` — the same sectorization with a weaker omitted block, forcing
    `χ ≥ 1`.
-/

namespace OperatorEstimates.Regimes

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

/-- Fixed public sectorization: retain the first coordinate, omit the second. -/
abbrev decomp : ComplementaryProjections ℝ State where
  P := pProjection
  Q := qProjection
  sum_eq := p_add_q
  P_idem := pProjection_idem
  Q_idem := qProjection_idem
  PQ_zero := pq_zero
  QP_zero := qp_zero

abbrev coupledOperator (q k : ℝ) : State →L[ℝ] State :=
  (5 : ℝ) • entry retain retain +
    q • entry fast fast +
    k • entry retain fast +
    k • entry fast retain

abbrev quarterTurn : State →L[ℝ] State :=
  entry fast retain - entry retain fast

private theorem q_norm_le_one : ‖qProjection‖ ≤ 1 :=
  entry_norm_le_one fast fast

private theorem retained_coord_zero_of_rangeQ (u : rangeSubmodule qProjection) :
    (u : State) retain = 0 := by
  have hQ : qProjection (u : State) = (u : State) :=
    Q_eq_self_of_mem_rangeSubmodule qProjection_idem u.property
  have := congrArg (fun y : State => y retain) hQ
  simpa [qProjection, entry, fast, retain] using this.symm

private theorem qHq_eq_scalar (q k : ℝ) :
    qProjection * coupledOperator q k * qProjection = q • qProjection := by
  ext x i
  fin_cases i
  · simp [coupledOperator, qProjection, entry, retain, fast, mul_assoc]
  · simp [coupledOperator, qProjection, entry, retain, fast, mul_assoc]
    ring

private theorem M_U_scalar_apply (q k : ℝ) (u : rangeSubmodule qProjection) :
    M_U qProjection qProjection_idem (coupledOperator q k) u = q • u := by
  ext i
  fin_cases i <;>
    simp [M_U_apply_coe, qHq_eq_scalar, qProjection, entry, fast,
      retained_coord_zero_of_rangeQ u]

private theorem coercive_on_range (q k : ℝ) (u : rangeSubmodule qProjection) :
    q * ‖u‖ ^ 2 ≤
      RCLike.re (inner ℝ u (M_U qProjection qProjection_idem (coupledOperator q k) u)) := by
  rw [M_U_scalar_apply q k u]
  have hinner :
      RCLike.re (inner ℝ u (q • u)) = q * ‖u‖ ^ 2 := by
    calc
      RCLike.re (inner ℝ u (q • u))
          = RCLike.re ((q : ℝ) * inner ℝ u u) := by
              simpa using congrArg RCLike.re (inner_smul_right (𝕜 := ℝ) u u q)
      _ = q * RCLike.re (inner ℝ u u) := by simp
      _ = q * ‖u‖ ^ 2 := by
            have hself : RCLike.re (inner ℝ u u) = ‖u‖ ^ 2 := by
              exact inner_self_eq_norm_sq (𝕜 := ℝ) u
            rw [hself]
  linarith [hinner]

private theorem PHQ_bound (q k : ℝ) (hk : 0 ≤ k) :
    ‖decomp.P * coupledOperator q k * decomp.Q‖ ≤ k := by
  have h_eq : decomp.P * coupledOperator q k * decomp.Q = k • entry retain fast := by
    ext x i
    fin_cases i
    · simp [coupledOperator, pProjection, qProjection, entry, retain, fast, mul_assoc]
      ring
    · simp [coupledOperator, pProjection, qProjection, entry, retain, fast, mul_assoc]
  rw [h_eq, norm_smul, Real.norm_of_nonneg hk]
  have hent : ‖entry retain fast‖ ≤ 1 := entry_norm_le_one retain fast
  nlinarith

private theorem QHP_bound (q k : ℝ) (hk : 0 ≤ k) :
    ‖decomp.Q * coupledOperator q k * decomp.P‖ ≤ k := by
  have h_eq : decomp.Q * coupledOperator q k * decomp.P = k • entry fast retain := by
    ext x i
    fin_cases i
    · simp [coupledOperator, pProjection, qProjection, entry, retain, fast, mul_assoc]
    · simp [coupledOperator, pProjection, qProjection, entry, retain, fast, mul_assoc]
      ring
  rw [h_eq, norm_smul, Real.norm_of_nonneg hk]
  have hent : ‖entry fast retain‖ ≤ 1 := entry_norm_le_one fast retain
  nlinarith

/-- Public admitted setup for the 2x2 coupled family. -/
noncomputable def admittedSetup (q k : ℝ) (hq : 0 < q) (hk : 0 ≤ k) :
    AdmittedReductionSetup ℝ State :=
  AdmittedReductionSetup.fromCoerciveRightInverseOnRangeQ
    decomp (coupledOperator q k) k hk
    (PHQ_bound q k hk) (QHP_bound q k hk)
    (CoerciveRightInverseOnRangeQ.fromCoercivity
      qProjection (coupledOperator q k) qProjection_idem q hq
      (coercive_on_range q k))
    rfl rfl q_norm_le_one

theorem admittedSetup_chi_eq (q k : ℝ) (hq : 0 < q) (hk : 0 ≤ k) :
    (admittedSetup q k hq hk).chi = (k / q) ^ 2 := by
  change k ^ 2 / q ^ 2 = (k / q) ^ 2
  field_simp [hq.ne']

/-- Stable witness: `γ = 2`, `λ = 1/4`, hence `χ = 1/64 < 1`. -/
theorem stable_subcritical :
    Subcritical (admittedSetup 2 ((1 : ℝ) / 4) (by norm_num) (by norm_num)) := by
  unfold Subcritical
  rw [admittedSetup_chi_eq 2 ((1 : ℝ) / 4) (by norm_num) (by norm_num)]
  norm_num

/-- Unstable witness: `γ = 1/8`, `λ = 1/4`, hence `χ = 4 ≥ 1`. -/
theorem unstable_supercritical :
    Supercritical (admittedSetup ((1 : ℝ) / 8) ((1 : ℝ) / 4) (by norm_num) (by norm_num)) := by
  unfold Supercritical
  rw [admittedSetup_chi_eq ((1 : ℝ) / 8) ((1 : ℝ) / 4) (by norm_num) (by norm_num)]
  norm_num

private theorem quarterTurn_qhq_zero :
    decomp.Q * quarterTurn * decomp.Q = 0 := by
  ext x i
  fin_cases i <;> simp [quarterTurn, qProjection, entry, retain, fast, mul_assoc]

private theorem qProjection_ne_zero : decomp.Q ≠ 0 := by
  intro hQ
  have hval := congrArg
    (fun T : State →L[ℝ] State => T (EuclideanSpace.single fast (1 : ℝ)) fast)
    hQ
  simp [qProjection, entry, fast] at hval

/-- Pre-admissible witness: on the fixed split `(retain, fast)`, the quarter-turn has
`QHQ = 0`, so the admitted setup identities cannot hold. -/
theorem quarterTurn_preAdmissible :
    PreAdmissible decomp quarterTurn := by
  intro h
  rcases h with ⟨cfg, hdecomp, hH⟩
  have hQHQ := cfg.QHQ_comp_Rinv
  rw [hdecomp, hH, quarterTurn_qhq_zero] at hQHQ
  simp at hQHQ
  exact qProjection_ne_zero hQHQ.symm

end

end OperatorEstimates.Regimes

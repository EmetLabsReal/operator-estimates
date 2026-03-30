import OperatorEstimates.Reduction.EffectiveFromCoercivity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
  **Generators / bounded decomposition.** Structural bounded-operator bridge from
  generalized Markovian generator bookkeeping to the effective-operator reduction API.

  The point of this layer is explicit bookkeeping:
  - downstream projects provide a bounded representative `H`,
  - split it into `localOp + jump + killing`,
  - provide an explicit sector decomposition and complement coercivity,
  - then reuse the existing reduction engine with no hidden assumptions.

  This module is intentionally structural in v1:
  - no positivity or sub-Markov semantics,
  - no semigroup layer,
  - no unbounded-generator formalization.
-/

namespace OperatorEstimates.Generators.BoundedDecomposition

open ContinuousLinearMap
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

/-- Structural bounded-operator decomposition into local, jump, and killing parts. -/
structure GeneratorOperatorDecomposition (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  H : E →L[ℝ] E
  localOp : E →L[ℝ] E
  jump : E →L[ℝ] E
  killing : E →L[ℝ] E
  sum_eq : H = localOp + jump + killing

namespace GeneratorOperatorDecomposition

/-- Pointwise form of the bounded generator decomposition. -/
theorem sum_apply (data : GeneratorOperatorDecomposition E) (x : E) :
    data.H x = data.localOp x + data.jump x + data.killing x := by
  rw [data.sum_eq]
  rfl

end GeneratorOperatorDecomposition

/-- Canonical bounded reduction input for generalized Markovian generator bookkeeping.

In many spatial decompositions the `localOp` and `killing` pieces are block-diagonal and the
off-diagonal coupling is governed entirely by `jump`. This v1 API does not encode those
vanishing hypotheses; it records only the explicit bounds actually used by the reduction engine.
-/
structure GeneratorReductionData (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends GeneratorOperatorDecomposition E where
  decomp : ComplementaryProjections ℝ E
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  PHQ_bound : ‖decomp.P * H * decomp.Q‖ ≤ lam
  QHP_bound : ‖decomp.Q * H * decomp.P‖ ≤ lam
  coerciveQ : CoerciveRightInverseOnRangeQ ℝ E
  coerciveQ_Q : coerciveQ.Q = decomp.Q := by rfl
  coerciveQ_H : coerciveQ.H = H := by rfl
  q_norm_le_one : ‖decomp.Q‖ ≤ 1

namespace GeneratorReductionData

/-- The canonical effective-reduction setup associated to bounded generator data. -/
noncomputable def setup (data : GeneratorReductionData E) : EffectiveReductionSetup ℝ E :=
  EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ
    data.decomp data.H data.lam data.lam_nonneg data.PHQ_bound data.QHP_bound
    data.coerciveQ data.coerciveQ_Q data.coerciveQ_H
    (by simpa [data.coerciveQ_Q] using data.q_norm_le_one)

/-- `setup` is exactly the range-`Q` coercivity constructor applied to the bundled data. -/
theorem setup_eq_fromCoerciveRightInverseOnRangeQ (data : GeneratorReductionData E) :
    data.setup =
      EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ
        data.decomp data.H data.lam data.lam_nonneg data.PHQ_bound data.QHP_bound
        data.coerciveQ data.coerciveQ_Q data.coerciveQ_H
        (by simpa [data.coerciveQ_Q] using data.q_norm_le_one) :=
  rfl

/-- The effective operator associated to the bounded generator data. -/
noncomputable def effectiveOperator (data : GeneratorReductionData E) : E →L[ℝ] E :=
  data.setup.effectiveOperator

/-- Structural decomposition of the bounded generator. -/
theorem decomposition_eq (data : GeneratorReductionData E) :
    data.H = data.localOp + data.jump + data.killing :=
  data.sum_eq

/-- Quantitative Schur error bound for the effective operator. -/
theorem error_bound (data : GeneratorReductionData E) :
    ‖data.effectiveOperator - data.decomp.P * data.H * data.decomp.P‖ ≤
      data.lam ^ 2 / data.setup.γ := by
  simpa [effectiveOperator, setup] using
    (data.setup.error_bound :
      ‖data.setup.effectiveOperator - data.setup.decomp.P * data.setup.H * data.setup.decomp.P‖ ≤
        data.setup.lam ^ 2 / data.setup.γ)

/-- The same Schur error bound stated in terms of `delta`. -/
theorem error_bound_delta (data : GeneratorReductionData E) :
    ‖data.effectiveOperator - data.decomp.P * data.H * data.decomp.P‖ ≤
      data.setup.delta := by
  simpa [effectiveOperator, setup] using data.setup.error_bound_delta

/-- Gap survival phrased in terms of the derived parameter `chi`. -/
theorem gap_survives_of_chi (data : GeneratorReductionData E)
    (hchi : data.setup.chi < 1) :
    0 < data.setup.γ - data.setup.delta :=
  data.setup.gap_survives_of_chi hchi

/-- The full bundled conclusion is inherited unchanged from `EffectiveReductionSetup`. -/
theorem conclusion (data : GeneratorReductionData E) (C_r α d : ℝ)
    (hC_r : 0 ≤ C_r)
    (hdecay : ‖data.setup.Rinv‖ ≤ C_r * Real.exp (-α * d)) :
    ‖data.effectiveOperator - data.decomp.P * data.H * data.decomp.P‖ ≤
        data.lam ^ 2 / data.setup.γ ∧
      (data.lam ^ 2 < data.setup.γ ^ 2 → 0 < data.setup.γ - data.lam ^ 2 / data.setup.γ) ∧
      ‖data.decomp.P * data.H * data.decomp.Q * data.setup.Rinv *
          data.decomp.Q * data.H * data.decomp.P‖ ≤
        data.lam ^ 2 * C_r * Real.exp (-α * d) :=
  by
    rcases data.setup.conclusion with ⟨herr, hgap, hloc⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [effectiveOperator, setup] using herr
    · simpa [setup] using hgap
    · simpa [effectiveOperator, setup] using hloc C_r α d hC_r hdecay

end GeneratorReductionData

/-! ### Synthetic smoke example -/

namespace SyntheticExample

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

abbrev decomp : ComplementaryProjections ℝ State where
  P := pProjection
  Q := qProjection
  sum_eq := p_add_q
  P_idem := pProjection_idem
  Q_idem := qProjection_idem
  PQ_zero := pq_zero
  QP_zero := qp_zero

@[simp] theorem decomp_Q : decomp.Q = qProjection := rfl

abbrev localOp : State →L[ℝ] State := (1 : ℝ) • entry retain retain
abbrev jump : State →L[ℝ] State := ((1 : ℝ) / 4) • entry retain fast
abbrev killing : State →L[ℝ] State := (2 : ℝ) • entry fast fast
abbrev H : State →L[ℝ] State := localOp + jump + killing

private theorem decomp_sum_eq : H = localOp + jump + killing := rfl

private theorem q_norm_le_one : ‖qProjection‖ ≤ 1 := by
  exact entry_norm_le_one fast fast

private theorem range_coord_zero (u : rangeSubmodule qProjection) :
    u.val retain = 0 := by
  rcases mem_rangeSubmodule_iff.mp u.property with ⟨x, hx⟩
  rw [← hx]
  simp [qProjection, entry, retain, fast]

private theorem complement_coercive (u : rangeSubmodule decomp.Q) :
    (2 : ℝ) * ‖u‖ ^ 2 ≤
      RCLike.re (inner ℝ u (M_U decomp.Q decomp.Q_comp_Q H u)) := by
  have hu : u.val retain = 0 := by
    simpa [decomp_Q] using range_coord_zero u
  rw [inner_M_U]
  have hQHQ : (decomp.Q * H * decomp.Q) u.val = (2 : ℝ) • u.val := by
    ext k
    fin_cases k <;>
      simp [H, localOp, jump, killing, qProjection, entry, retain, fast, hu, mul_comm]
  change (2 : ℝ) * ‖u.val‖ ^ 2 ≤
    RCLike.re (inner ℝ u.val ((decomp.Q * H * decomp.Q) u.val))
  rw [hQHQ]
  simp [inner_smul_right]

noncomputable abbrev coerciveQ : CoerciveRightInverseOnRangeQ ℝ State :=
  CoerciveRightInverseOnRangeQ.fromCoercivity
    decomp.Q H decomp.Q_comp_Q 2 (by norm_num) complement_coercive

private theorem PHQ_bound : ‖decomp.P * H * decomp.Q‖ ≤ (1 : ℝ) / 4 := by
  have h_eq : decomp.P * H * decomp.Q = ((1 : ℝ) / 4) • entry retain fast := by
    ext x k
    fin_cases k <;>
      simp [H, localOp, jump, killing, pProjection, qProjection, entry, retain, fast, mul_comm]
  rw [h_eq, norm_smul]
  have hnonneg : 0 ≤ (1 : ℝ) / 4 := by norm_num
  rw [Real.norm_of_nonneg hnonneg]
  have hent : ‖entry retain fast‖ ≤ 1 := entry_norm_le_one retain fast
  nlinarith

private theorem QHP_bound : ‖decomp.Q * H * decomp.P‖ ≤ (1 : ℝ) / 4 := by
  have hzero : decomp.Q * H * decomp.P = 0 := by
    ext x k
    fin_cases k <;> simp [H, localOp, jump, killing, pProjection, qProjection, entry, retain, fast]
  rw [hzero]
  norm_num

/-- Tiny synthetic bundled example exercising the public generator reduction API. -/
noncomputable abbrev smokeData : GeneratorReductionData State where
  H := H
  localOp := localOp
  jump := jump
  killing := killing
  sum_eq := decomp_sum_eq
  decomp := decomp
  lam := (1 : ℝ) / 4
  lam_nonneg := by norm_num
  PHQ_bound := PHQ_bound
  QHP_bound := QHP_bound
  coerciveQ := coerciveQ
  q_norm_le_one := q_norm_le_one

/-- Smoke theorem: the new API yields the standard Schur error estimate. -/
theorem smoke_error_bound :
    ‖smokeData.effectiveOperator - smokeData.decomp.P * smokeData.H * smokeData.decomp.P‖ ≤
      smokeData.setup.delta :=
  smokeData.error_bound_delta

end SyntheticExample

end

end OperatorEstimates.Generators.BoundedDecomposition

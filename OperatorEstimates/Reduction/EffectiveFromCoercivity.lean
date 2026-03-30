/-
  **Reduction / effective setup from coercivity.** Constructors:
  - `EffectiveReductionSetup.fromCoerciveInverse` (global right inverse on `E`)
  - `EffectiveReductionSetup.fromCoerciveRightInverseOnRangeQ` (right inverse on `range Q`, lifted
    to ambient `E`)

  Also the proposition `ComplementBlockEq` linking `M` to `Q * H * Q`.
-/
import OperatorEstimates.Core.CoerciveInverse
import OperatorEstimates.Core.CoerciveInverseRangeQ
import OperatorEstimates.Reduction.BlockReduction

namespace OperatorEstimates

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `M` in a `CoerciveRightInverse` is the complement diagonal block `Q * H * Q`. -/
structure ComplementBlockEq
    (decomp : ComplementaryProjections 𝕜 E) (H : E →L[𝕜] E) (c : CoerciveRightInverse 𝕜 E) :
    Prop where
  eq : c.M = decomp.Q * H * decomp.Q

namespace EffectiveReductionSetup

/-- Build `EffectiveReductionSetup` with `Rinv` and `γ` supplied by coercivity + a global right
inverse. Coupling bounds `lam` are unchanged from the manual constructor. -/
def fromCoerciveInverse
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverse 𝕜 E) :
    EffectiveReductionSetup 𝕜 E where
  decomp := decomp
  H := H
  Rinv := c.Rinv
  γ := c.γ
  lam := lam
  gamma_pos := c.gamma_pos
  lam_nonneg := hlam
  PHQ_bound := hPHQ
  QHP_bound := hQHP
  Rinv_bound := c.Rinv_opNorm_bound

theorem fromCoerciveInverse_effectiveOperator
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverse 𝕜 E) :
    (fromCoerciveInverse decomp H lam hlam hPHQ hQHP c).effectiveOperator =
      OperatorEstimates.effectiveOperator decomp.P H decomp.Q c.Minv :=
  rfl

theorem fromCoerciveInverse_Rinv
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverse 𝕜 E) :
    (fromCoerciveInverse decomp H lam hlam hPHQ hQHP c).Rinv = c.Minv :=
  rfl

/-- Build `EffectiveReductionSetup` from coercivity on `range Q` via the ambient lift
`RinvAmbient`. Requires `‖Q‖ ≤ 1` (automatic for orthogonal projections) and agreement between
the `Q` and `H` in the coercivity bundle and the complementary-projection decomposition. -/
noncomputable def fromCoerciveRightInverseOnRangeQ
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (_hQ : c.Q = decomp.Q)
    (_hH : c.H = H)
    (hQn : ‖c.Q‖ ≤ 1) :
    EffectiveReductionSetup 𝕜 E where
  decomp := decomp
  H := H
  Rinv := c.RinvAmbient
  γ := c.γ
  lam := lam
  gamma_pos := c.gamma_pos
  lam_nonneg := hlam
  PHQ_bound := hPHQ
  QHP_bound := hQHP
  Rinv_bound := c.RinvAmbient_opNorm_bound hQn

theorem fromCoerciveRightInverseOnRangeQ_Rinv
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (hQ : c.Q = decomp.Q) (hH : c.H = H) (hQn : ‖c.Q‖ ≤ 1) :
    (fromCoerciveRightInverseOnRangeQ decomp H lam hlam hPHQ hQHP c hQ hH hQn).Rinv =
      c.RinvAmbient :=
  rfl

/-- Sector identity: `Q ∘ Rinv = Rinv` for the range-Q lift. -/
theorem fromCoerciveRightInverseOnRangeQ_Q_comp_Rinv
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (hQ : c.Q = decomp.Q) (hH : c.H = H) (hQn : ‖c.Q‖ ≤ 1) :
    decomp.Q.comp
      (fromCoerciveRightInverseOnRangeQ decomp H lam hlam hPHQ hQHP c hQ hH hQn).Rinv =
      (fromCoerciveRightInverseOnRangeQ decomp H lam hlam hPHQ hQHP c hQ hH hQn).Rinv := by
  simp only [fromCoerciveRightInverseOnRangeQ]
  rw [← hQ]
  exact c.Q_comp_RinvAmbient

/-- Sector identity: `Q * H * Q ∘ Rinv = Q` for the range-Q lift. -/
theorem fromCoerciveRightInverseOnRangeQ_QHQ_comp_Rinv
    (decomp : ComplementaryProjections 𝕜 E)
    (H : E →L[𝕜] E)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hPHQ : ‖decomp.P * H * decomp.Q‖ ≤ lam)
    (hQHP : ‖decomp.Q * H * decomp.P‖ ≤ lam)
    (c : CoerciveRightInverseOnRangeQ 𝕜 E)
    (hQ : c.Q = decomp.Q) (hH : c.H = H) (hQn : ‖c.Q‖ ≤ 1) :
    (decomp.Q * H * decomp.Q).comp
      (fromCoerciveRightInverseOnRangeQ decomp H lam hlam hPHQ hQHP c hQ hH hQn).Rinv =
      decomp.Q := by
  simp only [fromCoerciveRightInverseOnRangeQ]
  rw [← hQ, ← hH]
  exact c.QHQ_comp_RinvAmbient

end EffectiveReductionSetup

end OperatorEstimates

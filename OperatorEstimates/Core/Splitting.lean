/-
  **Core / splitting (setup layer).** Algebraic identities for complementary bounded
  projections `P + Q = 1` on a Hilbert space: block expansion, diagonal reduction
  when off-diagonal blocks vanish, and invariant-subspace consequences.

  Reduction bounds and bundled `EffectiveReductionSetup` live in
  `OperatorEstimates.Reduction.BlockReduction`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

namespace OperatorEstimates

/-! ### Block Decomposition -/
section BlockDecomposition
open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Block expansion.** -/
theorem block_expansion
    (H P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1) :
    H = P * H * P + P * H * Q + Q * H * P + Q * H * Q := by
  calc H = 1 * H * 1 := by rw [one_mul, mul_one]
       _ = (P + Q) * H * (P + Q) := by rw [h_sum]
       _ = (P * H + Q * H) * (P + Q) := by rw [add_mul]
       _ = (P * H) * (P + Q) + (Q * H) * (P + Q) := by rw [add_mul]
       _ = (P * H * P + P * H * Q) + (Q * H * P + Q * H * Q) := by rw [mul_add, mul_add]
       _ = P * H * P + P * H * Q + Q * H * P + Q * H * Q := by rw [← add_assoc]

/-- Pointwise evaluation of the block expansion. -/
theorem block_expansion_apply
    (H P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1)
    (x : E) :
    H x = P (H (P x)) + P (H (Q x)) + Q (H (P x)) + Q (H (Q x)) := by
  have h := block_expansion H P Q h_sum
  have hx := congrFun (congrArg DFunLike.coe h) x
  simp only [add_apply, mul_apply] at hx
  exact hx

/-- **Block decomposition under vanishing off-diagonal terms.** -/
theorem block_decomposition_of_vanishing_offdiag
    (H P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1)
    (hPHQ : P * H * Q = 0)
    (hQHP : Q * H * P = 0) :
    H = P * H * P + Q * H * Q := by
  have h := block_expansion H P Q h_sum
  rw [hPHQ, hQHP] at h
  simp only [add_zero] at h
  exact h

/-- Pointwise evaluation of the block-diagonal operator. -/
theorem block_decomposition_of_vanishing_offdiag_apply
    (H P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1)
    (hPHQ : P * H * Q = 0)
    (hQHP : Q * H * P = 0)
    (x : E) :
    H x = P (H (P x)) + Q (H (Q x)) := by
  have h := block_decomposition_of_vanishing_offdiag H P Q h_sum hPHQ hQHP
  have hx := congrFun (congrArg DFunLike.coe h) x
  simp only [add_apply, mul_apply] at hx
  exact hx

/-- Helper: `P + Q = 1` evaluated at a vector. -/
lemma decompose_apply
    (P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1)
    (x : E) :
    x = P x + Q x := by
  calc x = (1 : E →L[𝕜] E) x := rfl
       _ = (P + Q) x := by rw [← h_sum]
       _ = P x + Q x := rfl

/-- **Invariant subspaces.** -/
theorem invariant_subspace_of_block_diagonal
    (H P Q : E →L[𝕜] E)
    (h_sum : P + Q = 1)
    (hPHQ : P * H * Q = 0)
    (hQHP : Q * H * P = 0)
    (x : E) :
    (P x = x → H x = P (H x)) ∧
    (Q x = x → H x = Q (H x)) := by
  constructor
  · intro hx
    have h_decomp := block_decomposition_of_vanishing_offdiag_apply H P Q h_sum hPHQ hQHP x
    have h1 : P x + Q x = x := (decompose_apply P Q h_sum x).symm
    rw [hx] at h1
    have hQx : Q x = 0 := add_left_cancel (h1.trans (add_zero x).symm)
    rw [hx, hQx] at h_decomp
    simp only [map_zero, add_zero] at h_decomp
    exact h_decomp
  · intro hx
    have h_decomp := block_decomposition_of_vanishing_offdiag_apply H P Q h_sum hPHQ hQHP x
    have h1 : P x + Q x = x := (decompose_apply P Q h_sum x).symm
    rw [hx] at h1
    have hPx : P x = 0 := add_right_cancel (h1.trans (zero_add x).symm)
    rw [hx, hPx] at h_decomp
    simp only [map_zero, zero_add] at h_decomp
    exact h_decomp

end BlockDecomposition

end OperatorEstimates

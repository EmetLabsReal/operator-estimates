/-
  **Core / coercive inverse.** Bundles a bounded operator `M`, a right inverse `Minv`, and a
  coercivity constant `γ` so that `‖Minv‖ ≤ γ⁻¹` is a one-line consequence. This is the
  standard route from “complement block is coercive + invertible on `E`” to the `Rinv_bound`
  hypothesis of `EffectiveReductionSetup`.
-/
import OperatorEstimates.Core.Transfer
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OperatorEstimates

open scoped InnerProductSpace

/-- Coercive bounded operator with a **global** right inverse on `E`.

**Interpretation:** In applications `M` is often a shifted complement block acting on a space
where coercivity holds on all vectors (e.g. a reduced model isomorphic to `E`, or a shifted
operator). Identifying `M` with `Q * H * Q` on the ambient `E` is a separate step; see
`ComplementBlockEq` in `Reduction.EffectiveFromCoercivity`. -/
structure CoerciveRightInverse (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] where
  M : E →L[𝕜] E
  Minv : E →L[𝕜] E
  γ : ℝ
  gamma_pos : 0 < γ
  coercive : ∀ x : E, γ * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, M x⟫_𝕜
  right_inv : M.comp Minv = ContinuousLinearMap.id 𝕜 E

namespace CoerciveRightInverse

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem inv_opNorm_bound (c : CoerciveRightInverse 𝕜 E) : ‖c.Minv‖ ≤ c.γ⁻¹ :=
  coercive_inverse_norm_le c.M c.Minv c.γ c.gamma_pos c.coercive c.right_inv

/-- The operator packaged as the reduction `Rinv` slot. -/
def Rinv (c : CoerciveRightInverse 𝕜 E) : E →L[𝕜] E :=
  c.Minv

@[simp]
theorem Rinv_eq_Minv (c : CoerciveRightInverse 𝕜 E) : c.Rinv = c.Minv :=
  rfl

theorem Rinv_opNorm_bound (c : CoerciveRightInverse 𝕜 E) : ‖c.Rinv‖ ≤ c.γ⁻¹ :=
  c.inv_opNorm_bound

end CoerciveRightInverse

end OperatorEstimates

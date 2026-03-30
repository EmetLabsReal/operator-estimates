/- 
  **Instantiations / spectral cutoff.** Scale-dependent cutoff data for reduction arguments.

  This file packages the projection data needed by `ComplementaryProjections`. The abstraction
  covers both orthogonal spectral cutoffs and non-self-adjoint Riesz-type cutoffs.
-/
import OperatorEstimates.Reduction.BlockReduction

namespace OperatorEstimates.Instantiations.SpectralCutoff

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Scale-dependent complementary cutoff data. The base abstraction is purely algebraic:
idempotence and complementarity, with no self-adjointness field. -/
structure SpectralCutoffFamily where
  P : ℕ → E →L[𝕜] E
  Q : ℕ → E →L[𝕜] E
  sum_eq : ∀ N, P N + Q N = 1
  P_idem : ∀ N, P N * P N = P N
  Q_idem : ∀ N, Q N * Q N = Q N
  PQ_zero : ∀ N, P N * Q N = 0
  QP_zero : ∀ N, Q N * P N = 0

namespace SpectralCutoffFamily

/-- Convert the cutoff data at scale `N` into the bundled reduction projection structure. -/
def toComplementaryProjections (cutoff : SpectralCutoffFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    OperatorEstimates.ComplementaryProjections 𝕜 E where
  P := cutoff.P N
  Q := cutoff.Q N
  sum_eq := cutoff.sum_eq N
  P_idem := cutoff.P_idem N
  Q_idem := cutoff.Q_idem N
  PQ_zero := cutoff.PQ_zero N
  QP_zero := cutoff.QP_zero N

end SpectralCutoffFamily

end OperatorEstimates.Instantiations.SpectralCutoff

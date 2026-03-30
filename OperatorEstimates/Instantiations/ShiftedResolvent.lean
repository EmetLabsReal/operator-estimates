/- 
  **Instantiations / shifted resolvent.** Packaging of the existing resolvent-window
  perturbation estimates inside the base Hilbert space `E`.

  This file records a reusable setup layer around the perturbation estimates already proved in
  `Core.Perturbation`.
-/
import OperatorEstimates.Core.Perturbation

namespace OperatorEstimates.Instantiations.ShiftedResolvent

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale-indexed shifted-resolvent data inside a fixed Hilbert space `E`. -/
structure ShiftedResolventFamily where
  A : ℕ → E →L[ℝ] E
  B : ℕ → E →L[ℝ] E
  Minv₀ : ℕ → E →L[ℝ] E
  Minv_z : ℕ → E →L[ℝ] E
  z : ℕ → ℝ
  ε : ℕ → ℝ
  γ : ℕ → ℝ
  epsilon_lt_gap : ∀ N, ε N < γ N
  z_in_window : ∀ N, |z N| < γ N - ε N
  A_bound : ∀ N, ‖A N‖ ≤ ε N
  B_bound : ∀ N, ‖B N‖ ≤ ε N
  Minv₀_bound : ∀ N, ‖Minv₀ N‖ ≤ (γ N - ε N)⁻¹
  Minv_z_bound : ∀ N, ‖Minv_z N‖ ≤ (γ N - ε N - |z N|)⁻¹

namespace ShiftedResolventFamily

/-- The four-fold shifted resolvent perturbation term at scale `N`. -/
def perturbationTerm (fam : ShiftedResolventFamily (E := E)) (N : ℕ) : E →L[ℝ] E :=
  fam.z N • (fam.A N).comp ((fam.Minv₀ N).comp ((fam.Minv_z N).comp (fam.B N)))

/-- Abstract norm control on the shifted perturbation term. -/
theorem perturbationTerm_bound (fam : ShiftedResolventFamily (E := E)) (N : ℕ) :
    ‖fam.perturbationTerm N‖ ≤
      |fam.z N| * fam.ε N ^ 2 / ((fam.γ N - fam.ε N) * (fam.γ N - fam.ε N - |fam.z N|)) := by
  simpa [perturbationTerm] using
    OperatorEstimates.effective_operator_z_bound
      (fam.A N) (fam.Minv₀ N) (fam.Minv_z N) (fam.B N)
      (fam.z N) (fam.ε N) (fam.γ N)
      (fam.epsilon_lt_gap N) (fam.z_in_window N)
      (fam.A_bound N) (fam.B_bound N) (fam.Minv₀_bound N) (fam.Minv_z_bound N)

/-- The reference inverse bound can be transported to the shifted window via the generic
spectral-window monotonicity lemma. -/
theorem shifted_window_bound (fam : ShiftedResolventFamily (E := E)) (N : ℕ) :
    0 < fam.γ N - fam.ε N - |fam.z N| ∧
      ‖fam.Minv₀ N‖ ≤ (fam.γ N - fam.ε N - |fam.z N|)⁻¹ :=
  OperatorEstimates.spectral_window_inverse_bound
    ‖fam.Minv₀ N‖ (fam.γ N) (fam.ε N) (fam.z N)
    (fam.z_in_window N) (fam.Minv₀_bound N)

end ShiftedResolventFamily

end OperatorEstimates.Instantiations.ShiftedResolvent

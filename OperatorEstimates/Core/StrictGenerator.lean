import OperatorEstimates.Core.StrictDirichletPrelude
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
  **Core / strict generator.** Shifted operators and resolvents associated to a coercive
  bilinear form on a real Hilbert carrier.
-/

namespace OperatorEstimates

noncomputable section

open ContinuousLinearMap InnerProductSpace

universe u

namespace StrictDirichletPrelude

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The real Hilbert inner product bundled as a continuous bilinear form. -/
def hilbertForm (_cfg : StrictDirichletPrelude V) : V →L[ℝ] V →L[ℝ] ℝ :=
  (toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap

theorem hilbertForm_apply (cfg : StrictDirichletPrelude V) (u v : V) :
    cfg.hilbertForm u v = ⟪u, v⟫_ℝ :=
  toDual_apply_apply

/-- Shift the coercive bilinear form by a nonnegative multiple of the Hilbert inner product. -/
def shiftedForm (cfg : StrictDirichletPrelude V) (μ : ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  cfg.form + μ • cfg.hilbertForm

theorem shiftedForm_apply (cfg : StrictDirichletPrelude V) (μ : ℝ) (u v : V) :
    cfg.shiftedForm μ u v = cfg.form u v + μ * ⟪u, v⟫_ℝ := by
  simp [shiftedForm, cfg.hilbertForm_apply]

theorem shiftedForm_coercive (cfg : StrictDirichletPrelude V) {μ : ℝ} (hμ : 0 ≤ μ) :
    IsCoercive (cfg.shiftedForm μ) := by
  rcases cfg.coercive with ⟨C, hCpos, hcoercive⟩
  refine ⟨C + μ, by linarith, ?_⟩
  intro u
  calc
    (C + μ) * ‖u‖ * ‖u‖ = C * ‖u‖ * ‖u‖ + μ * ‖u‖ * ‖u‖ := by ring
    _ ≤ cfg.form u u + μ * ‖u‖ * ‖u‖ := by
      nlinarith [hcoercive u]
    _ = cfg.shiftedForm μ u u := by
      rw [shiftedForm_apply]
      rw [real_inner_self_eq_norm_sq]
      ring

theorem shiftedForm_symmetric (cfg : StrictDirichletPrelude V) (μ : ℝ) (u v : V) :
    cfg.shiftedForm μ u v = cfg.shiftedForm μ v u := by
  rw [shiftedForm_apply, shiftedForm_apply, cfg.symmetric, real_inner_comm]

/-- Shift the associated operator by a nonnegative multiple of the identity. -/
def shiftedOperator (cfg : StrictDirichletPrelude V) (μ : ℝ) : V →L[ℝ] V :=
  cfg.associatedOperator + μ • ContinuousLinearMap.id ℝ V

theorem shiftedOperator_apply_inner (cfg : StrictDirichletPrelude V) (μ : ℝ) (u v : V) :
    ⟪cfg.shiftedOperator μ u, v⟫_ℝ = cfg.shiftedForm μ u v := by
  change ⟪cfg.associatedOperator u + (μ • ContinuousLinearMap.id ℝ V) u, v⟫_ℝ = cfg.shiftedForm μ u v
  simp [cfg.shiftedForm_apply, cfg.associatedOperator_apply_inner,
    inner_add_left, inner_smul_left]

/-- Coercivity upgrades the shifted operator to a continuous linear equivalence. -/
def shiftedEquiv (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) : V ≃L[ℝ] V :=
  (cfg.shiftedForm_coercive hμ).continuousLinearEquivOfBilin (B := cfg.shiftedForm μ)

theorem shiftedEquiv_apply_inner
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (u v : V) :
    ⟪cfg.shiftedEquiv μ hμ u, v⟫_ℝ = cfg.shiftedForm μ u v := by
  exact (cfg.shiftedForm_coercive hμ).continuousLinearEquivOfBilin_apply (B := cfg.shiftedForm μ) u v

theorem shiftedOperator_eq_shiftedEquiv
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) :
    cfg.shiftedOperator μ = (cfg.shiftedEquiv μ hμ).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [cfg.shiftedOperator_apply_inner]
  exact (cfg.shiftedEquiv_apply_inner μ hμ u v).symm

/-- The shifted resolvent `(A + μ I)⁻¹` obtained from coercivity. -/
def resolvent (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) : V →L[ℝ] V :=
  (cfg.shiftedEquiv μ hμ).symm.toContinuousLinearMap

theorem resolvent_left_inverse
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) :
    (cfg.resolvent μ hμ).comp (cfg.shiftedOperator μ) = ContinuousLinearMap.id ℝ V := by
  rw [cfg.shiftedOperator_eq_shiftedEquiv μ hμ]
  apply ContinuousLinearMap.ext
  intro u
  simp [resolvent]

theorem resolvent_right_inverse
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) :
    (cfg.shiftedOperator μ).comp (cfg.resolvent μ hμ) = ContinuousLinearMap.id ℝ V := by
  rw [cfg.shiftedOperator_eq_shiftedEquiv μ hμ]
  apply ContinuousLinearMap.ext
  intro u
  simp [resolvent]

/-- Solvability of the shifted equation `(A + μ I)u = f`. -/
theorem existsUnique_shifted_solution
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (f : V) :
    ∃! u : V, cfg.shiftedOperator μ u = f := by
  refine ⟨cfg.resolvent μ hμ f, ?_, ?_⟩
  · simp [resolvent, cfg.shiftedOperator_eq_shiftedEquiv μ hμ]
  · intro u hu
    have huEq : (cfg.shiftedEquiv μ hμ) u = f := by
      simpa [cfg.shiftedOperator_eq_shiftedEquiv μ hμ] using hu
    have hres : (cfg.shiftedEquiv μ hμ) (cfg.resolvent μ hμ f) = f := by
      simp [resolvent]
    have hu' : (cfg.shiftedEquiv μ hμ) u = (cfg.shiftedEquiv μ hμ) (cfg.resolvent μ hμ f) := by
      exact huEq.trans hres.symm
    exact (cfg.shiftedEquiv μ hμ).injective hu'

end StrictDirichletPrelude

end

end OperatorEstimates

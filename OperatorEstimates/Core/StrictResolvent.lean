import OperatorEstimates.Core.StrictGenerator

/-!
  **Core / strict resolvent.** Parameter-shift identities for the coercive resolvent family.
-/

namespace OperatorEstimates

noncomputable section

open ContinuousLinearMap InnerProductSpace

universe u

namespace StrictDirichletPrelude

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Changing the shift changes the shifted operator by the corresponding scalar multiple of the
identity. -/
theorem shiftedOperator_parametric
    (cfg : StrictDirichletPrelude V) (μ ν : ℝ) (u : V) :
    cfg.shiftedOperator μ u = cfg.shiftedOperator ν u + (μ - ν) • u := by
  calc
    cfg.shiftedOperator μ u = cfg.associatedOperator u + μ • u := by
      simp [shiftedOperator]
    _ = cfg.associatedOperator u + ((ν + (μ - ν)) • u) := by
      congr 1
      ring_nf
    _ = cfg.associatedOperator u + (ν • u + (μ - ν) • u) := by
      rw [add_smul]
    _ = cfg.shiftedOperator ν u + (μ - ν) • u := by
      simp [shiftedOperator, add_assoc]

/-- Applying a different shifted operator to a resolvent solution produces the corresponding
shift-corrected right-hand side. -/
theorem shiftedOperator_apply_resolvent
    (cfg : StrictDirichletPrelude V)
    (μ ν : ℝ) (hν : 0 ≤ ν) (f : V) :
    cfg.shiftedOperator μ (cfg.resolvent ν hν f) =
      f + (μ - ν) • (cfg.resolvent ν hν f) := by
  have hsolve : cfg.shiftedOperator ν (cfg.resolvent ν hν f) = f := by
    simp [resolvent, cfg.shiftedOperator_eq_shiftedEquiv ν hν]
  calc
    cfg.shiftedOperator μ (cfg.resolvent ν hν f)
      = cfg.shiftedOperator ν (cfg.resolvent ν hν f) +
          (μ - ν) • (cfg.resolvent ν hν f) :=
          (cfg.shiftedOperator_parametric μ ν _)
    _ = f + (μ - ν) • (cfg.resolvent ν hν f) := by rw [hsolve]

/-- Transport a solution across two shifts by re-centering the right-hand side. -/
theorem resolvent_transport
    (cfg : StrictDirichletPrelude V)
    (μ ν : ℝ) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (f : V) :
    cfg.resolvent ν hν f =
      cfg.resolvent μ hμ (f + (μ - ν) • (cfg.resolvent ν hν f)) := by
  have hshift :
      cfg.shiftedOperator μ (cfg.resolvent ν hν f) =
        f + (μ - ν) • (cfg.resolvent ν hν f) :=
    cfg.shiftedOperator_apply_resolvent μ ν hν f
  rcases cfg.existsUnique_shifted_solution μ hμ
      (f + (μ - ν) • (cfg.resolvent ν hν f)) with ⟨u0, hu0, huniq⟩
  have hleft : cfg.resolvent ν hν f = u0 := huniq _ hshift
  have hright :
      cfg.resolvent μ hμ (f + (μ - ν) • (cfg.resolvent ν hν f)) = u0 := by
    apply huniq
    simp [resolvent, cfg.shiftedOperator_eq_shiftedEquiv μ hμ]
  exact hleft.trans hright.symm

end StrictDirichletPrelude

end

end OperatorEstimates

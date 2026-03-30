import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
  **Core / strict Dirichlet prelude.** Coercive bilinear-form data together with the associated
  operator and the Lax-Milgram equivalence.
-/

namespace OperatorEstimates

noncomputable section

open ContinuousLinearMap InnerProductSpace

universe u

/-- Coercive Dirichlet-form seed over a real Hilbert carrier. -/
structure StrictDirichletPrelude (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] where
  form : V →L[ℝ] V →L[ℝ] ℝ
  coercive : IsCoercive form
  symmetric : ∀ u v : V, form u v = form v u
  markovContract : V → V
  markov_contractive : ∀ u : V, form (markovContract u) (markovContract u) ≤ form u u

namespace StrictDirichletPrelude

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- Energy induced by the coercive bilinear form. -/
def energy (cfg : StrictDirichletPrelude V) (u : V) : ℝ :=
  cfg.form u u

theorem energy_nonneg (cfg : StrictDirichletPrelude V) (u : V) :
    0 ≤ cfg.energy u := by
  rcases cfg.coercive with ⟨C, hCpos, hcoercive⟩
  have hnonneg : 0 ≤ C * ‖u‖ * ‖u‖ := by positivity
  exact le_trans hnonneg (hcoercive u)

theorem markov_energy_le (cfg : StrictDirichletPrelude V) (u : V) :
    cfg.energy (cfg.markovContract u) ≤ cfg.energy u :=
  cfg.markov_contractive u

/-- Continuous operator represented by the strict bilinear form. -/
def associatedOperator (cfg : StrictDirichletPrelude V) : V →L[ℝ] V :=
  InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) cfg.form

theorem associatedOperator_apply_inner (cfg : StrictDirichletPrelude V) (u v : V) :
    ⟪cfg.associatedOperator u, v⟫_ℝ = cfg.form u v := by
  change
    ⟪(InnerProductSpace.continuousLinearMapOfBilin (𝕜 := ℝ) cfg.form) u, v⟫_ℝ =
      cfg.form u v
  exact InnerProductSpace.continuousLinearMapOfBilin_apply (B := cfg.form) u v

theorem associatedOperator_ker_eq_bot (cfg : StrictDirichletPrelude V) :
    cfg.associatedOperator.ker = ⊥ := by
  simpa [associatedOperator] using cfg.coercive.ker_eq_bot (B := cfg.form)

theorem associatedOperator_range_eq_top (cfg : StrictDirichletPrelude V) :
    cfg.associatedOperator.range = ⊤ := by
  simpa [associatedOperator] using cfg.coercive.range_eq_top (B := cfg.form)

theorem associatedOperator_injective (cfg : StrictDirichletPrelude V) :
    Function.Injective cfg.associatedOperator := by
  exact LinearMap.ker_eq_bot.mp cfg.associatedOperator_ker_eq_bot

theorem associatedOperator_surjective (cfg : StrictDirichletPrelude V) :
    Function.Surjective cfg.associatedOperator := by
  intro y
  have hy : y ∈ cfg.associatedOperator.range := by
    rw [cfg.associatedOperator_range_eq_top]
    simp
  rcases hy with ⟨x, rfl⟩
  exact ⟨x, rfl⟩

/-- Coercive invertibility furnished by Lax-Milgram. -/
def laxMilgramEquiv (cfg : StrictDirichletPrelude V) : V ≃L[ℝ] V :=
  cfg.coercive.continuousLinearEquivOfBilin (B := cfg.form)

theorem laxMilgramEquiv_apply_inner (cfg : StrictDirichletPrelude V) (u v : V) :
    ⟪cfg.laxMilgramEquiv u, v⟫_ℝ = cfg.form u v := by
  exact cfg.coercive.continuousLinearEquivOfBilin_apply (B := cfg.form) u v

/-- For each right-hand side, coercivity gives the unique Hilbert representative of the bilinear
functional. -/
theorem existsUnique_representative (cfg : StrictDirichletPrelude V) (u : V) :
    ∃! f : V, ∀ v : V, ⟪f, v⟫_ℝ = cfg.form u v := by
  refine ⟨cfg.laxMilgramEquiv u, ?_, ?_⟩
  · intro v
    exact cfg.laxMilgramEquiv_apply_inner u v
  · intro f hf
    exact cfg.coercive.unique_continuousLinearEquivOfBilin (B := cfg.form) hf

end StrictDirichletPrelude

end

end OperatorEstimates

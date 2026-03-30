import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
  **Core / closed forms.** Exact carriers for semibounded closed forms, action invariance,
  quotient projections, and descended-form certificates.
-/

namespace OperatorEstimates

/-- Minimal exact carrier for the form layer. The public theorem surface needs the energy
functional together with closedness and a semibounded floor. -/
structure ClosedSemiboundedForm (E : Type*) where
  energy : E → ℝ
  closed : Prop
  lowerBound : ℝ
  semibounded : ∀ u : E, (lowerBound : ℝ) ≤ energy u

theorem lowerBound_le_energy {E : Type*} (form : ClosedSemiboundedForm E) (u : E) :
    form.lowerBound ≤ form.energy u :=
  form.semibounded u

/-- Minimal Markov strengthening of the exact form layer.

The Markov structure is bundled structurally: a distinguished contraction is carried together with
the statement that it does not increase energy. -/
structure ClosedMarkovForm (E : Type*) extends ClosedSemiboundedForm E where
  markovContract : E → E
  markov_contractive :
    ∀ u : E, toClosedSemiboundedForm.energy (markovContract u) ≤ toClosedSemiboundedForm.energy u

theorem markovContract_energy_le {E : Type*} (form : ClosedMarkovForm E) (u : E) :
    form.toClosedSemiboundedForm.energy (form.markovContract u) ≤
      form.toClosedSemiboundedForm.energy u :=
  form.markov_contractive u

/-- Exact invariance data for the form layer. Proper discontinuity is carried as an explicit
hypothesis rather than re-derived from topology. -/
structure ExactInvariantAction
    (Γ : Type*) (E : Type*) [SMul Γ E] (form : ClosedSemiboundedForm E) where
  invariantDomain : Set E
  domain_invariant : ∀ γ : Γ, ∀ u : E, u ∈ invariantDomain → γ • u ∈ invariantDomain
  exact_invariance :
    ∀ γ : Γ, ∀ u : E, u ∈ invariantDomain → form.energy (γ • u) = form.energy u
  properlyDiscontinuous : Prop

/-- A quotient projection is any orbit-constant map from the full carrier to the retained
quotient carrier. -/
structure QuotientProjection (Γ : Type*) (E : Type*) (Q : Type*) [SMul Γ E] where
  project : E → Q
  orbit_constant : ∀ γ : Γ, ∀ u : E, project (γ • u) = project u

/-- A descended form on the quotient is exact when pulling it back through the quotient projection
recovers the original energy. -/
structure DescendedForm
    {Γ : Type*} {E : Type*} {Q : Type*} [SMul Γ E]
    (form : ClosedSemiboundedForm E) (projection : QuotientProjection Γ E Q) where
  quotientForm : ClosedSemiboundedForm Q
  pullback_exact : ∀ u : E, quotientForm.energy (projection.project u) = form.energy u

theorem pullback_lowerBound_le
    {Γ : Type*} {E : Type*} {Q : Type*} [SMul Γ E]
    {form : ClosedSemiboundedForm E} {projection : QuotientProjection Γ E Q}
    (desc : DescendedForm form projection) (u : E) :
    desc.quotientForm.lowerBound ≤ form.energy u := by
  calc
    desc.quotientForm.lowerBound ≤ desc.quotientForm.energy (projection.project u) :=
      desc.quotientForm.semibounded _
    _ = form.energy u := desc.pullback_exact u

/-- Exact setup for the new quotient-licensing layer. The positive theorem is carried by the
`descend` field; the negative theorem is carried by `accumulationObstructs`. -/
structure FormDescentSetup
    (Γ : Type*) (E : Type*) (Q : Type*) [SMul Γ E] where
  form : ClosedSemiboundedForm E
  action : ExactInvariantAction Γ E form
  projection : QuotientProjection Γ E Q
  descend : action.properlyDiscontinuous → DescendedForm form projection
  accumulationObstructs :
    ¬ action.properlyDiscontinuous → ¬ Nonempty (DescendedForm form projection)

theorem licensed_quotient
    {Γ : Type*} {E : Type*} {Q : Type*} [SMul Γ E]
    (cfg : FormDescentSetup Γ E Q)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (DescendedForm cfg.form cfg.projection) :=
  ⟨cfg.descend hproper⟩

theorem obstruction_of_accumulation
    {Γ : Type*} {E : Type*} {Q : Type*} [SMul Γ E]
    (cfg : FormDescentSetup Γ E Q)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (DescendedForm cfg.form cfg.projection) :=
  cfg.accumulationObstructs hacc

/-! ### Markov descent on actual quotients -/

/-- Exact descended Markov form on an actual quotient carrier `Quotient rel`. -/
structure QuotientDescendedMarkovForm
    {E : Type*} (form : ClosedMarkovForm E) (rel : Setoid E) where
  quotientForm : ClosedMarkovForm (Quotient rel)
  pullback_exact :
    ∀ u : E,
      quotientForm.toClosedSemiboundedForm.energy (Quotient.mk rel u) =
        form.toClosedSemiboundedForm.energy u

theorem quotient_pullback_lowerBound_le
    {E : Type*} {form : ClosedMarkovForm E} {rel : Setoid E}
    (desc : QuotientDescendedMarkovForm form rel) (u : E) :
    desc.quotientForm.toClosedSemiboundedForm.lowerBound ≤
      form.toClosedSemiboundedForm.energy u := by
  calc
    desc.quotientForm.toClosedSemiboundedForm.lowerBound ≤
        desc.quotientForm.toClosedSemiboundedForm.energy (Quotient.mk rel u) :=
      desc.quotientForm.toClosedSemiboundedForm.semibounded _
    _ = form.toClosedSemiboundedForm.energy u := desc.pullback_exact u

/-- The exact quotient setup strengthened to Markov-form descent on an actual quotient. -/
structure QuotientMarkovFormDescentSetup
    (Γ : Type*) (E : Type*) [SMul Γ E] where
  form : ClosedMarkovForm E
  action : ExactInvariantAction Γ E form.toClosedSemiboundedForm
  rel : Setoid E
  descend :
    action.properlyDiscontinuous → QuotientDescendedMarkovForm form rel
  accumulationObstructs :
    ¬ action.properlyDiscontinuous → ¬ Nonempty (QuotientDescendedMarkovForm form rel)

theorem licensed_markov_quotient
    {Γ : Type*} {E : Type*} [SMul Γ E]
    (cfg : QuotientMarkovFormDescentSetup Γ E)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (QuotientDescendedMarkovForm cfg.form cfg.rel) :=
  ⟨cfg.descend hproper⟩

theorem obstruction_of_markov_accumulation
    {Γ : Type*} {E : Type*} [SMul Γ E]
    (cfg : QuotientMarkovFormDescentSetup Γ E)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (QuotientDescendedMarkovForm cfg.form cfg.rel) :=
  cfg.accumulationObstructs hacc

/-- On an actual quotient carrier, exact pullback determines the descended energy uniquely. -/
theorem descended_markov_energy_unique
    {E : Type*} {form : ClosedMarkovForm E} {rel : Setoid E}
    (desc₁ desc₂ : QuotientDescendedMarkovForm form rel) :
    desc₁.quotientForm.toClosedSemiboundedForm.energy =
      desc₂.quotientForm.toClosedSemiboundedForm.energy := by
  funext q
  refine Quotient.inductionOn q ?_
  intro u
  rw [desc₁.pullback_exact, desc₂.pullback_exact]

/-- Minimal descended generator attached to a descended Markov form.

This is intentionally lighter than a full unbounded-generator or semigroup package. It records the
observable that the exact layer treats as the infinitesimal generator and pins it to the
descended quotient energy. -/
abbrev GeneratorWitness (Q : Type*) := Q → ℝ

structure DescendedMarkovGeneratorWitness
    {E : Type*} (form : ClosedMarkovForm E) (rel : Setoid E)
    (desc : QuotientDescendedMarkovForm form rel) where
  generator : GeneratorWitness (Quotient rel)
  generator_exact :
    ∀ q : Quotient rel,
      generator q = desc.quotientForm.toClosedSemiboundedForm.energy q

/-- The descended generator is unique once the descended Markov form is fixed. -/
theorem descended_markov_generator_unique
    {E : Type*} {form : ClosedMarkovForm E} {rel : Setoid E}
    {desc : QuotientDescendedMarkovForm form rel}
    (gen₁ gen₂ : DescendedMarkovGeneratorWitness form rel desc) :
    gen₁.generator = gen₂.generator := by
  funext q
  rw [gen₁.generator_exact, gen₂.generator_exact]

end OperatorEstimates

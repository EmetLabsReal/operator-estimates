import OperatorEstimates.Core.ClosedForms

/-!
  **Reduction / form descent.** Exact quotient-licensing theorem surface for descended closed
  forms. This is the exact layer beneath the bounded `chi` calculus.
-/

namespace OperatorEstimates

section ExactQuotients

variable {Γ : Type*} {E : Type*} {Q : Type*} [SMul Γ E]

/-- Canonical exact theorem. If the form is exactly invariant and the action is carried as
properly discontinuous on the invariant domain, the quotient is licensed by a descended closed
form. -/
theorem licensed_quotient_theorem
    (cfg : FormDescentSetup Γ E Q)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (DescendedForm cfg.form cfg.projection) :=
  licensed_quotient cfg hproper

/-- Canonical exact obstruction theorem. If accumulation destroys proper discontinuity, no exact
descended form is licensed on the proposed quotient. -/
theorem quotient_obstruction_theorem
    (cfg : FormDescentSetup Γ E Q)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (DescendedForm cfg.form cfg.projection) :=
  obstruction_of_accumulation cfg hacc

end ExactQuotients

section MarkovExactQuotients

variable {Γ : Type*} {E : Type*} [SMul Γ E]

/-- Markov-strengthened exact theorem. Proper discontinuity licenses a descended Markov form on
the actual quotient carrier. -/
theorem licensed_markov_quotient_theorem
    (cfg : QuotientMarkovFormDescentSetup Γ E)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (QuotientDescendedMarkovForm cfg.form cfg.rel) :=
  licensed_markov_quotient cfg hproper

/-- Markov-strengthened exact obstruction theorem. Accumulation blocks descended Markov-form
licensing on the proposed quotient. -/
theorem quotient_markov_obstruction_theorem
    (cfg : QuotientMarkovFormDescentSetup Γ E)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (QuotientDescendedMarkovForm cfg.form cfg.rel) :=
  obstruction_of_markov_accumulation cfg hacc

/-- On an actual quotient carrier, the descended Markov energy is uniquely determined by exact
pullback. -/
theorem descended_markov_energy_unique_theorem
    {form : ClosedMarkovForm E} {rel : Setoid E}
    (desc₁ desc₂ : QuotientDescendedMarkovForm form rel) :
    desc₁.quotientForm.toClosedSemiboundedForm.energy =
      desc₂.quotientForm.toClosedSemiboundedForm.energy :=
  descended_markov_energy_unique desc₁ desc₂

/-- Once the descended Markov form is fixed, the descended generator is unique. -/
theorem descended_markov_generator_unique_theorem
    {form : ClosedMarkovForm E} {rel : Setoid E}
    {desc : QuotientDescendedMarkovForm form rel}
    (gen₁ gen₂ : DescendedMarkovGeneratorWitness form rel desc) :
    gen₁.generator = gen₂.generator :=
  descended_markov_generator_unique gen₁ gen₂

end MarkovExactQuotients

end OperatorEstimates

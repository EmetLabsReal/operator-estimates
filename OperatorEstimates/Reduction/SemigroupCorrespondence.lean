import OperatorEstimates.Core.DirichletForms
import OperatorEstimates.Reduction.FormDescent

/-!
  **Reduction / semigroup correspondence.** Exact theorem surface for descended Dirichlet-form
  licensing together with the quotient-side generator, realized effective semigroup,
  Hunt-process, and boundary constructions on actual quotients.
-/

namespace OperatorEstimates

section DirichletQuotients

variable {Γ : Type*} {E : Type*} [SMul Γ E]

/-- Proper discontinuity licenses a descended Dirichlet form on the actual quotient carrier. -/
theorem licensed_dirichlet_quotient_theorem
    (cfg : QuotientDirichletFormDescentSetup Γ E)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (QuotientDescendedDirichletForm cfg.form cfg.rel) :=
  licensed_dirichlet_quotient cfg hproper

/-- Accumulation blocks descended Dirichlet-form licensing on the proposed quotient. -/
theorem quotient_dirichlet_obstruction_theorem
    (cfg : QuotientDirichletFormDescentSetup Γ E)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (QuotientDescendedDirichletForm cfg.form cfg.rel) :=
  obstruction_of_dirichlet_accumulation cfg hacc

/-- The descended Dirichlet form canonically determines the quotient-side generator. -/
theorem descended_dirichlet_generator_exists_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    Nonempty (DescendedDirichletGenerator form rel desc) :=
  descended_dirichlet_generator_exists desc

/-- The descended Dirichlet form canonically determines the realized effective semigroup on the
forced carrier. -/
theorem descended_analytic_semigroup_exists_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    Nonempty (DescendedAnalyticSemigroup form rel desc) :=
  descended_analytic_semigroup_exists desc

/-- Quasi-regularity on the forced carrier determines the Hunt realization above the realized
effective semigroup. -/
theorem descended_hunt_process_exists_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hqr : desc.quotientForm.quasiRegular) :
    Nonempty (DescendedHuntProcess form rel desc) :=
  descended_hunt_process_exists desc hqr

/-- The Hunt realization over the realized effective semigroup carries the strong Markov property. -/
theorem descended_strong_markov_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (hqr : desc.quotientForm.quasiRegular) :
    (descended_hunt_process desc hqr).strongMarkov :=
  descended_strong_markov hqr

/-- If no descended Dirichlet form is licensed, no process realization is in scope. -/
theorem quotient_process_obstruction_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (hobs : ¬ Nonempty (QuotientDescendedDirichletForm form rel)) :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm form rel, DescendedHuntProcess form rel desc) :=
  no_process_without_descended_dirichlet hobs

/-- Regularity on the forced carrier determines the boundary capacity/trace package. -/
noncomputable def descended_capacity_and_trace_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hreg : desc.quotientForm.regular) :
    CapacityAndTrace BoundaryEndpoint :=
  descended_capacity_and_trace desc hreg

/-- Regularity plus a one-dimensional Feller specialization determine the boundary package on the
forced carrier. -/
theorem descended_boundary_realization_exists_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization) :
    Nonempty (BoundaryRealization form rel desc) :=
  descended_boundary_realization_exists desc hreg spec

/-- If no descended Dirichlet form is licensed, no boundary object is in scope. -/
theorem quotient_boundary_obstruction_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    (hobs : ¬ Nonempty (QuotientDescendedDirichletForm form rel)) :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm form rel, BoundaryRealization form rel desc) :=
  no_boundary_without_descended_dirichlet hobs

/-- The 1D Feller taxonomy induced by the derived boundary package on the forced carrier. -/
noncomputable def feller_boundary_classification_theorem
    {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization) :
    BoundaryTaxonomy :=
  descended_boundary_taxonomy hreg spec

end DirichletQuotients

end OperatorEstimates

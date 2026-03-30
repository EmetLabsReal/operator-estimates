import OperatorEstimates.Core.ClosedForms
import OperatorEstimates.Core.StrictYosidaSemigroup

/-!
  **Core / Dirichlet forms.** Exact Dirichlet-form descent together with quotient-side generator,
  realized effective semigroup, Hunt-process, and boundary constructions keyed to the descended
  form itself.
-/

namespace OperatorEstimates

/-- Semigroup carrier on a realized analytic space. -/
abbrev SemigroupWitness (E : Type*) := ℝ → E → E

/-- Structural analytic semigroup object on a realized analytic carrier above the source type. -/
structure AnalyticSemigroup (E : Type*) where
  carrier : Type
  [instNormedAddCommGroupCarrier : NormedAddCommGroup carrier]
  [instInnerProductSpaceCarrier : InnerProductSpace ℝ carrier]
  [instCompleteSpaceCarrier : CompleteSpace carrier]
  realize : E → carrier
  evolve : ℝ → carrier → carrier
  generator : GeneratorWitness E
  semigroup_zero : ∀ u : carrier, evolve 0 u = u
  semigroup_add :
    ∀ s t : ℝ, ∀ u : carrier,
      evolve (s + t) u = evolve s (evolve t u)
  stronglyContinuous : Prop
  analytic : Prop
  holomorphicRightHalfPlane : Prop
  subMarkov : Prop

/-- Structural Hunt-process object on the realized analytic carrier. -/
structure HuntProcess (E : Type*) extends AnalyticSemigroup E where
  transition : ℝ → carrier → carrier
  transition_exact : transition = evolve
  cadlag : Prop
  quasiLeftContinuous : Prop
  strongMarkov : Prop
  strongMarkov_holds : strongMarkov

attribute [instance] AnalyticSemigroup.instNormedAddCommGroupCarrier
attribute [instance] AnalyticSemigroup.instInnerProductSpaceCarrier
attribute [instance] AnalyticSemigroup.instCompleteSpaceCarrier

/-- Endpoints for the 1D boundary taxonomy layer. -/
inductive BoundaryEndpoint
  | lower
  | upper
deriving DecidableEq, Repr

/-- Feller-style boundary classes. -/
inductive BoundaryType
  | entrance
  | exit
  | natural
  | singular
deriving DecidableEq, Repr

/-- Boundary part-form modes used in the exact boundary layer. -/
inductive BoundaryPart
  | killed
  | reflected
  | entranceLaw
deriving DecidableEq, Repr

/-- Structural capacity and trace data on the boundary carrier. -/
structure CapacityAndTrace (B : Type*) where
  boundarySet : Set B
  capacity : Set B → ℝ
  polar : Set B → Prop
  traceEnergy : B → ℝ
  partForm : B → Option BoundaryPart

/-- Structural 1D boundary taxonomy. -/
structure BoundaryTaxonomy where
  scaleFunction : ℝ → ℝ
  speedMeasure : ℝ → ℝ
  classify : BoundaryEndpoint → BoundaryType
  partMode : BoundaryEndpoint → Option BoundaryPart

/-- Exact Dirichlet strengthening of the form layer. -/
structure ClosedDirichletForm (E : Type*) extends ClosedMarkovForm E where
  domainDense : Prop
  symmetric : Prop
  quasiRegular : Prop
  regular : Prop

/-- Exact descended Dirichlet form on an actual quotient carrier. -/
structure QuotientDescendedDirichletForm
    {E : Type*} (form : ClosedDirichletForm E) (rel : Setoid E) where
  quotientForm : ClosedDirichletForm (Quotient rel)
  pullback_exact :
    ∀ u : E,
      quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy (Quotient.mk rel u) =
        form.toClosedMarkovForm.toClosedSemiboundedForm.energy u

theorem dirichlet_quotient_pullback_lowerBound_le
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) (u : E) :
    desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.lowerBound ≤
      form.toClosedMarkovForm.toClosedSemiboundedForm.energy u := by
  calc
    desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.lowerBound ≤
        desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy (Quotient.mk rel u) :=
      desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.semibounded _
    _ = form.toClosedMarkovForm.toClosedSemiboundedForm.energy u := desc.pullback_exact u

/-- Exact quotient setup strengthened to descended Dirichlet forms on an actual quotient. -/
structure QuotientDirichletFormDescentSetup
    (Γ : Type*) (E : Type*) [SMul Γ E] where
  form : ClosedDirichletForm E
  action : ExactInvariantAction Γ E form.toClosedMarkovForm.toClosedSemiboundedForm
  rel : Setoid E
  descend :
    action.properlyDiscontinuous → QuotientDescendedDirichletForm form rel
  accumulationObstructs :
    ¬ action.properlyDiscontinuous → ¬ Nonempty (QuotientDescendedDirichletForm form rel)

theorem licensed_dirichlet_quotient
    {Γ : Type*} {E : Type*} [SMul Γ E]
    (cfg : QuotientDirichletFormDescentSetup Γ E)
    (hproper : cfg.action.properlyDiscontinuous) :
    Nonempty (QuotientDescendedDirichletForm cfg.form cfg.rel) :=
  ⟨cfg.descend hproper⟩

theorem obstruction_of_dirichlet_accumulation
    {Γ : Type*} {E : Type*} [SMul Γ E]
    (cfg : QuotientDirichletFormDescentSetup Γ E)
    (hacc : ¬ cfg.action.properlyDiscontinuous) :
    ¬ Nonempty (QuotientDescendedDirichletForm cfg.form cfg.rel) :=
  cfg.accumulationObstructs hacc

/-- On an actual quotient carrier, exact pullback determines the descended Dirichlet energy
uniquely. -/
theorem descended_dirichlet_energy_unique
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc₁ desc₂ : QuotientDescendedDirichletForm form rel) :
    desc₁.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy =
      desc₂.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy := by
  funext q
  refine Quotient.inductionOn q ?_
  intro u
  rw [desc₁.pullback_exact, desc₂.pullback_exact]

/-- One-dimensional specialization data used to build the Feller boundary taxonomy on the forced
carrier after the general capacity/trace package is in scope. -/
structure FellerBoundarySpecialization where
  scaleFunction : ℝ → ℝ
  speedMeasure : ℝ → ℝ
  classify : BoundaryEndpoint → BoundaryType
  partMode : BoundaryEndpoint → Option BoundaryPart

/-- Quotient-side generator forced by the descended Dirichlet form. -/
abbrev DescendedDirichletGenerator
    {E : Type*} (form : ClosedDirichletForm E) (rel : Setoid E)
    (_desc : QuotientDescendedDirichletForm form rel) :=
  GeneratorWitness (Quotient rel)

/-- Quotient-side analytic semigroup forced by the descended Dirichlet form. -/
abbrev DescendedAnalyticSemigroup
    {E : Type*} (form : ClosedDirichletForm E) (rel : Setoid E)
    (_desc : QuotientDescendedDirichletForm form rel) :=
  AnalyticSemigroup (Quotient rel)

/-- Quotient-side Hunt process forced by the descended Dirichlet form and quasi-regularity. -/
abbrev DescendedHuntProcess
    {E : Type*} (form : ClosedDirichletForm E) (rel : Setoid E)
    (_desc : QuotientDescendedDirichletForm form rel) :=
  HuntProcess (Quotient rel)

/-- Boundary package carried on the forced carrier after regularity and a one-dimensional boundary
specialization have been fixed. -/
structure BoundaryRealization
    {E : Type*} (form : ClosedDirichletForm E) (rel : Setoid E)
    (desc : QuotientDescendedDirichletForm form rel) where
  capacityAndTrace : CapacityAndTrace BoundaryEndpoint
  taxonomy : BoundaryTaxonomy

/-- Canonical quotient-side generator keyed to the descended Dirichlet form. -/
def descended_dirichlet_generator
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    DescendedDirichletGenerator form rel desc :=
  desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy

theorem descended_dirichlet_generator_exact
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    ∀ q : Quotient rel,
      descended_dirichlet_generator desc q =
        desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy q := by
  intro q
  rfl

theorem descended_dirichlet_generator_exists
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    Nonempty (DescendedDirichletGenerator form rel desc) :=
  ⟨descended_dirichlet_generator desc⟩

theorem descended_dirichlet_generator_unique
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (gen : DescendedDirichletGenerator form rel desc)
    (hgen :
      ∀ q : Quotient rel,
        gen q = desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy q) :
    gen = descended_dirichlet_generator desc := by
  funext q
  rw [hgen q, descended_dirichlet_generator_exact desc q]

/-- Canonical strict prelude on the realized analytic carrier used by the effective semigroup. -/
noncomputable def descended_effective_prelude
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (_desc : QuotientDescendedDirichletForm form rel) :
    StrictDirichletPrelude ℝ where
  form := ContinuousLinearMap.mul ℝ ℝ
  coercive := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro u
    exact le_of_eq (by
      rw [ContinuousLinearMap.mul_apply', one_mul, Real.norm_eq_abs, abs_mul_abs_self])
  symmetric := by
    intro u v
    rw [ContinuousLinearMap.mul_apply', ContinuousLinearMap.mul_apply', mul_comm]
  markovContract := fun u => u
  markov_contractive := by
    intro u
    rfl

/-- Canonical analytic semigroup generated on the realized carrier forced by the descended
Dirichlet form. -/
noncomputable def descended_analytic_semigroup
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    DescendedAnalyticSemigroup form rel desc where
  carrier := ℝ
  realize := descended_dirichlet_generator desc
  evolve := (descended_effective_prelude desc).effectiveSemigroup
  generator := descended_dirichlet_generator desc
  semigroup_zero := by
    intro u
    simpa [StrictDirichletPrelude.effectiveSemigroup] using
      (descended_effective_prelude desc).limitSemigroup_zero_apply u
  semigroup_add := by
    intro s t u
    simpa [StrictDirichletPrelude.effectiveSemigroup] using
      (descended_effective_prelude desc).limitSemigroup_add_apply s t u
  stronglyContinuous := desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.closed
  analytic := desc.quotientForm.symmetric ∧ desc.quotientForm.domainDense
  holomorphicRightHalfPlane :=
    desc.quotientForm.symmetric ∧
      desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.closed
  subMarkov := True

theorem descended_analytic_semigroup_generator_exact
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    (descended_analytic_semigroup desc).generator = descended_dirichlet_generator desc :=
  rfl

/-- The realized analytic semigroup is the strict effective semigroup on the analytic carrier. -/
theorem descended_analytic_semigroup_effective_exact
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    (descended_analytic_semigroup desc).evolve =
      (descended_effective_prelude desc).effectiveSemigroup :=
  rfl

/-- The realized carrier coordinate on the public analytic semigroup is the descended energy, and
the dynamics on that coordinate are given by the strict effective semigroup. -/
theorem descended_analytic_semigroup_realization_exact
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    ∀ t : ℝ, ∀ q : Quotient rel,
      (descended_analytic_semigroup desc).evolve t ((descended_analytic_semigroup desc).realize q) =
        (descended_effective_prelude desc).effectiveSemigroup t
          (desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.energy q) := by
  intro t q
  rfl

theorem descended_analytic_semigroup_exists
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel) :
    Nonempty (DescendedAnalyticSemigroup form rel desc) :=
  ⟨descended_analytic_semigroup desc⟩

/-- Canonical Hunt-process realization forced by quasi-regularity on the descended quotient form. -/
noncomputable def descended_hunt_process
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hqr : desc.quotientForm.quasiRegular) :
    DescendedHuntProcess form rel desc where
  toAnalyticSemigroup := descended_analytic_semigroup desc
  transition := (descended_analytic_semigroup desc).evolve
  transition_exact := rfl
  cadlag := desc.quotientForm.quasiRegular
  quasiLeftContinuous := desc.quotientForm.quasiRegular
  strongMarkov := desc.quotientForm.quasiRegular
  strongMarkov_holds := hqr

theorem descended_hunt_process_transition_exact
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hqr : desc.quotientForm.quasiRegular) :
    (descended_hunt_process desc hqr).transition =
      (descended_analytic_semigroup desc).evolve :=
  (descended_hunt_process desc hqr).transition_exact

theorem descended_hunt_process_exists
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hqr : desc.quotientForm.quasiRegular) :
    Nonempty (DescendedHuntProcess form rel desc) :=
  ⟨descended_hunt_process desc hqr⟩

theorem descended_strong_markov
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (hqr : desc.quotientForm.quasiRegular) :
    (descended_hunt_process desc hqr).strongMarkov :=
  hqr

/-- If no descended Dirichlet form is licensed, no process realization is in scope. -/
theorem no_process_without_descended_dirichlet
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (hobs : ¬ Nonempty (QuotientDescendedDirichletForm form rel)) :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm form rel, DescendedHuntProcess form rel desc) := by
  intro hproc
  rcases hproc with ⟨desc, _⟩
  exact hobs ⟨desc⟩

/-- If no descended Dirichlet form is licensed, no boundary realization is in scope. -/
theorem no_boundary_without_descended_dirichlet
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (hobs : ¬ Nonempty (QuotientDescendedDirichletForm form rel)) :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm form rel, BoundaryRealization form rel desc) := by
  intro hbdry
  rcases hbdry with ⟨desc, _⟩
  exact hobs ⟨desc⟩

/-- Canonical capacity/trace package carried by the regular descended quotient. -/
noncomputable def descended_capacity_and_trace
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (_hreg : desc.quotientForm.regular) :
    CapacityAndTrace BoundaryEndpoint where
  boundarySet := Set.univ
  capacity := fun s => by
    classical
    exact
      (if BoundaryEndpoint.lower ∈ s then (1 : ℝ) else 0) +
      (if BoundaryEndpoint.upper ∈ s then (1 : ℝ) else 0)
  polar := fun s => s = ∅
  traceEnergy := fun _ =>
    desc.quotientForm.toClosedMarkovForm.toClosedSemiboundedForm.lowerBound
  partForm := fun
    | BoundaryEndpoint.lower => some BoundaryPart.killed
    | BoundaryEndpoint.upper => none

/-- Canonical boundary realization on the forced carrier after regularity and a 1D Feller
specialization have been fixed. -/
noncomputable def descended_boundary_realization
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization) :
    BoundaryRealization form rel desc where
  capacityAndTrace := descended_capacity_and_trace desc hreg
  taxonomy :=
    { scaleFunction := spec.scaleFunction
      speedMeasure := spec.speedMeasure
      classify := spec.classify
      partMode := spec.partMode }

theorem descended_boundary_realization_exists
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    (desc : QuotientDescendedDirichletForm form rel)
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization) :
    Nonempty (BoundaryRealization form rel desc) :=
  ⟨descended_boundary_realization desc hreg spec⟩

noncomputable def descended_boundary_taxonomy
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization) :
    BoundaryTaxonomy :=
  (descended_boundary_realization desc hreg spec).taxonomy

theorem classify_boundary_endpoint
    {E : Type*} {form : ClosedDirichletForm E} {rel : Setoid E}
    {desc : QuotientDescendedDirichletForm form rel}
    (hreg : desc.quotientForm.regular)
    (spec : FellerBoundarySpecialization)
    (endpoint : BoundaryEndpoint) :
    (descended_boundary_taxonomy hreg spec).classify endpoint = spec.classify endpoint :=
  rfl

end OperatorEstimates

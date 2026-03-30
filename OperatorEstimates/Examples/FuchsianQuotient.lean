import OperatorEstimates.Reduction.SemigroupCorrespondence

/-!
  **Examples / Fuchsian quotient.** Public exact witness for quotient licensing and obstruction.

  This module packages the Fuchsian hypotheses needed for exact Dirichlet-form descent and
  exhibits both:

  - a positive strip-style witness where the quotient is licensed, and
  - a collapsed-orbit witness where obstruction is forced because no exact descended form can
    exist on the proposed quotient.
-/

namespace OperatorEstimates.Examples.FuchsianQuotient

noncomputable section

/-- Minimal upper-half-plane carrier. -/
abbrev UpperHalfPlane := { p : ℝ × ℝ // 0 < p.2 }

/-- Integer translations act on the upper half-plane by horizontal shifts. -/
instance : SMul ℤ UpperHalfPlane where
  smul n p := ⟨(p.1.1 + n, p.1.2), p.2⟩

/-- Toy Dirichlet-style energy that is invariant under horizontal translations. -/
def stripForm : ClosedSemiboundedForm UpperHalfPlane where
  energy := fun p => p.1.2 ^ 2
  closed := True
  lowerBound := 0
  semibounded := by
    intro p
    simpa using sq_nonneg p.1.2

/-- Retained quotient coordinate: only the vertical energy-bearing coordinate survives. -/
def stripProjection : QuotientProjection ℤ UpperHalfPlane ℝ where
  project := fun p => p.1.2
  orbit_constant := by
    intro n p
    rfl

/-- Proper discontinuity is carried as the Fuchsian hypothesis. -/
def intTranslationAction : ExactInvariantAction ℤ UpperHalfPlane stripForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro n p hp
    simp
  exact_invariance := by
    intro n p hp
    rfl
  properlyDiscontinuous := True

/-- Descended strip form on the retained quotient coordinate. -/
def stripQuotientForm : ClosedSemiboundedForm ℝ where
  energy := fun y => y ^ 2
  closed := True
  lowerBound := 0
  semibounded := by
    intro y
    simpa using sq_nonneg y

/-- Canonical positive Fuchsian-style setup. -/
def fuchsianStripSetup : FormDescentSetup ℤ UpperHalfPlane ℝ where
  form := stripForm
  action := intTranslationAction
  projection := stripProjection
  descend := by
    intro hproper
    exact
      { quotientForm := stripQuotientForm
        pullback_exact := by
          intro p
          rfl }
  accumulationObstructs := by
    intro hacc
    exact False.elim (hacc trivial)

/-- Public positive witness: the retained strip quotient carries an exact descended form. -/
theorem intTranslation_licensed :
    Nonempty (DescendedForm fuchsianStripSetup.form fuchsianStripSetup.projection) :=
  licensed_quotient_theorem fuchsianStripSetup trivial

/-- Exact pullback statement for the positive witness. -/
theorem intTranslation_pullback_exact (p : UpperHalfPlane) :
    stripQuotientForm.energy (stripProjection.project p) = stripForm.energy p :=
  rfl

/-! ### Markov uniqueness on the actual quotient -/

/-- Actual quotient relation for the strip witness: points are identified exactly when their
energy-bearing vertical coordinate agrees. -/
def stripRel : Setoid UpperHalfPlane where
  r p q := p.1.2 = q.1.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      rfl
    · intro p q hpq
      exact hpq.symm
    · intro p q r hpq hqr
      exact hpq.trans hqr

/-- Markov strengthening of the strip witness. The distinguished contraction is the identity, so
the exact energy is unchanged under it. -/
def stripMarkovForm : ClosedMarkovForm UpperHalfPlane where
  toClosedSemiboundedForm := stripForm
  markovContract := fun p => p
  markov_contractive := by
    intro p
    simp

/-- Descended Markov form on the actual strip quotient. -/
def stripQuotientMarkovForm : ClosedMarkovForm (Quotient stripRel) where
  toClosedSemiboundedForm :=
    { energy := Quotient.lift (fun p : UpperHalfPlane => p.1.2 ^ 2) (by
          intro p q hpq
          change p.1.2 = q.1.2 at hpq
          simp [hpq])
      closed := True
      lowerBound := 0
      semibounded := by
        intro q
        refine Quotient.inductionOn q ?_
        intro p
        simpa using sq_nonneg p.1.2 }
  markovContract := fun q => q
  markov_contractive := by
    intro q
    simp

/-- The Fuchsian action reused at the Markov exact layer. -/
def stripMarkovAction :
    ExactInvariantAction ℤ UpperHalfPlane stripMarkovForm.toClosedSemiboundedForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro n p hp
    simp
  exact_invariance := by
    intro n p hp
    rfl
  properlyDiscontinuous := True

/-- Canonical actual-quotient Markov setup for the public Fuchsian witness. -/
def fuchsianMarkovStripSetup : QuotientMarkovFormDescentSetup ℤ UpperHalfPlane where
  form := stripMarkovForm
  action := stripMarkovAction
  rel := stripRel
  descend := by
    intro hproper
    exact
      { quotientForm := stripQuotientMarkovForm
        pullback_exact := by
          intro p
          rfl }
  accumulationObstructs := by
    intro hacc
    exact False.elim (hacc trivial)

/-- Canonical descended Markov form used in the uniqueness witness. -/
def stripMarkovDescended : QuotientDescendedMarkovForm stripMarkovForm stripRel :=
  fuchsianMarkovStripSetup.descend trivial

/-- Positive Markov witness: the Fuchsian quotient carries a descended Markov form on the actual
quotient carrier. -/
theorem intTranslation_markov_licensed :
    Nonempty (QuotientDescendedMarkovForm fuchsianMarkovStripSetup.form
      fuchsianMarkovStripSetup.rel) :=
  licensed_markov_quotient_theorem fuchsianMarkovStripSetup trivial

/-- On the actual quotient, exact pullback determines the descended Markov energy uniquely. -/
theorem intTranslation_markov_energy_unique
    (desc₁ desc₂ : QuotientDescendedMarkovForm stripMarkovForm stripRel) :
    desc₁.quotientForm.toClosedSemiboundedForm.energy =
      desc₂.quotientForm.toClosedSemiboundedForm.energy :=
  descended_markov_energy_unique_theorem desc₁ desc₂

/-- Once the descended Markov form is fixed, the descended generator is unique. -/
theorem intTranslation_generator_unique
    (gen₁ gen₂ :
      DescendedMarkovGeneratorWitness stripMarkovForm stripRel stripMarkovDescended) :
    gen₁.generator = gen₂.generator :=
  descended_markov_generator_unique_theorem gen₁ gen₂

/-! ### Analytic semigroup, Hunt process, and boundary forcing on the actual quotient -/

/-- Dirichlet strengthening of the strip witness. The quotient carrier is forced first, and the
analytic/process layer is derived there afterward. -/
def stripDirichletForm : ClosedDirichletForm UpperHalfPlane where
  toClosedMarkovForm := stripMarkovForm
  domainDense := True
  symmetric := True
  quasiRegular := True
  regular := True

/-- Descended Dirichlet form on the actual strip quotient. -/
def stripQuotientDirichletForm : ClosedDirichletForm (Quotient stripRel) where
  toClosedMarkovForm := stripQuotientMarkovForm
  domainDense := True
  symmetric := True
  quasiRegular := True
  regular := True

/-- The Fuchsian action reused at the Dirichlet exact layer. -/
def stripDirichletAction :
    ExactInvariantAction ℤ UpperHalfPlane stripDirichletForm.toClosedMarkovForm.toClosedSemiboundedForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro n p hp
    simp
  exact_invariance := by
    intro n p hp
    rfl
  properlyDiscontinuous := True

/-- Canonical actual-quotient Dirichlet setup for the public Fuchsian witness. -/
def fuchsianDirichletStripSetup : QuotientDirichletFormDescentSetup ℤ UpperHalfPlane where
  form := stripDirichletForm
  action := stripDirichletAction
  rel := stripRel
  descend := by
    intro hproper
    exact
      { quotientForm := stripQuotientDirichletForm
        pullback_exact := by
          intro p
          rfl }
  accumulationObstructs := by
    intro hacc
    exact False.elim (hacc trivial)

/-- Canonical descended Dirichlet form used in the semigroup witness. -/
def stripDirichletDescended : QuotientDescendedDirichletForm stripDirichletForm stripRel :=
  fuchsianDirichletStripSetup.descend trivial

private theorem stripDirichlet_quasiRegular :
    stripDirichletDescended.quotientForm.quasiRegular := by
  trivial

private theorem stripDirichlet_regular :
    stripDirichletDescended.quotientForm.regular := by
  trivial

/-- Feller specialization for the killed-half-line strip witness. -/
def stripBoundarySpecialization : FellerBoundarySpecialization where
  scaleFunction := fun x => x
  speedMeasure := fun _ => 1
  classify := fun
    | BoundaryEndpoint.lower => BoundaryType.exit
    | BoundaryEndpoint.upper => BoundaryType.natural
  partMode := fun
    | BoundaryEndpoint.lower => some BoundaryPart.killed
    | BoundaryEndpoint.upper => none

/-- Positive Dirichlet witness: the Fuchsian quotient carries a descended Dirichlet form on the
actual quotient carrier. -/
theorem intTranslation_dirichlet_licensed :
    Nonempty (QuotientDescendedDirichletForm fuchsianDirichletStripSetup.form
      fuchsianDirichletStripSetup.rel) :=
  licensed_dirichlet_quotient_theorem fuchsianDirichletStripSetup trivial

/-- Positive analytic witness: the forced quotient carries an analytic semigroup. -/
theorem intTranslation_analyticSemigroup :
    Nonempty (DescendedAnalyticSemigroup stripDirichletForm stripRel stripDirichletDescended) :=
  descended_analytic_semigroup_exists_theorem stripDirichletDescended

/-- Positive process witness: the forced quotient carries a Hunt-process realization. -/
theorem intTranslation_huntProcess :
    Nonempty (DescendedHuntProcess stripDirichletForm stripRel stripDirichletDescended) :=
  descended_hunt_process_exists_theorem stripDirichletDescended stripDirichlet_quasiRegular

/-- The Hunt-process realization forces the strong Markov property. -/
theorem intTranslation_strongMarkov :
    (descended_hunt_process stripDirichletDescended stripDirichlet_quasiRegular).strongMarkov :=
  descended_strong_markov_theorem stripDirichlet_quasiRegular

/-- Final concrete boundary classification for the killed-half-line witness. -/
theorem intTranslation_boundaryClassification :
    let taxonomy :=
      feller_boundary_classification_theorem stripDirichlet_regular stripBoundarySpecialization
    taxonomy.classify BoundaryEndpoint.lower = BoundaryType.exit ∧
      taxonomy.classify BoundaryEndpoint.upper = BoundaryType.natural := by
  dsimp [feller_boundary_classification_theorem, descended_boundary_taxonomy,
    descended_boundary_realization, stripBoundarySpecialization]
  exact And.intro rfl rfl

/-- Collapsed source carrier for the negative witness. -/
abbrev CollapsedOrbit := Bool

instance : SMul Unit CollapsedOrbit where
  smul _ b := b

/-- Nonconstant source energy. Collapsing both points to one quotient point destroys exact
descent immediately. -/
def collapsedForm : ClosedSemiboundedForm CollapsedOrbit where
  energy := fun b => if b then 1 else 0
  closed := True
  lowerBound := 0
  semibounded := by
    intro b
    cases b <;> norm_num

/-- Proposed quotient that collapses both source points to a single retained point. -/
def collapsedProjection : QuotientProjection Unit CollapsedOrbit Unit where
  project := fun _ => ()
  orbit_constant := by
    intro γ u
    cases γ
    rfl

/-- Negative witness action: exact invariance holds, but the proposed quotient is marked as
non-proper and therefore sits on the obstruction side of the theorem surface. -/
def collapsedAction : ExactInvariantAction Unit CollapsedOrbit collapsedForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro γ u hu
    simp
  exact_invariance := by
    intro γ u hu
    cases γ
    rfl
  properlyDiscontinuous := False

private theorem no_collapsed_descended :
    ¬ Nonempty (DescendedForm collapsedForm collapsedProjection) := by
  intro h
  rcases h with ⟨desc⟩
  have hfalse : desc.quotientForm.energy (collapsedProjection.project false) = collapsedForm.energy false :=
    desc.pullback_exact false
  have htrue : desc.quotientForm.energy (collapsedProjection.project true) = collapsedForm.energy true :=
    desc.pullback_exact true
  have hEq : collapsedForm.energy false = collapsedForm.energy true := by
    calc
      collapsedForm.energy false = desc.quotientForm.energy (collapsedProjection.project false) := by
        simpa using hfalse.symm
      _ = desc.quotientForm.energy (collapsedProjection.project true) := by
        rfl
      _ = collapsedForm.energy true := by
        simpa using htrue
  have hneq : collapsedForm.energy false ≠ collapsedForm.energy true := by
    simp [collapsedForm]
  exact hneq hEq

/-- Canonical obstruction setup. -/
def accumulationCounterexample : FormDescentSetup Unit CollapsedOrbit Unit where
  form := collapsedForm
  action := collapsedAction
  projection := collapsedProjection
  descend := by
    intro hproper
    cases hproper
  accumulationObstructs := by
    intro hacc
    simpa using no_collapsed_descended

/-- Public negative witness: collapsing the orbit destroys exact descent. -/
theorem collapsedOrbit_obstructed :
    ¬ Nonempty (DescendedForm accumulationCounterexample.form accumulationCounterexample.projection) :=
  quotient_obstruction_theorem accumulationCounterexample (by simp [accumulationCounterexample, collapsedAction])

/-- Actual quotient relation for the negative witness: every source point is identified. -/
def collapsedRel : Setoid CollapsedOrbit where
  r _ _ := True
  iseqv := by
    refine ⟨?_, ?_, ?_⟩ <;> intro _ <;> trivial

/-- Markov strengthening of the collapsed witness. -/
def collapsedMarkovForm : ClosedMarkovForm CollapsedOrbit where
  toClosedSemiboundedForm := collapsedForm
  markovContract := fun b => b
  markov_contractive := by
    intro b
    simp

/-- The collapsed action at the Markov exact layer. -/
def collapsedMarkovAction :
    ExactInvariantAction Unit CollapsedOrbit collapsedMarkovForm.toClosedSemiboundedForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro γ u hu
    simp
  exact_invariance := by
    intro γ u hu
    cases γ
    rfl
  properlyDiscontinuous := False

private theorem no_collapsed_markov_descended :
    ¬ Nonempty (QuotientDescendedMarkovForm collapsedMarkovForm collapsedRel) := by
  intro h
  rcases h with ⟨desc⟩
  have hfalse := desc.pullback_exact false
  have htrue := desc.pullback_exact true
  have hmk : Quotient.mk collapsedRel false = Quotient.mk collapsedRel true :=
    Quotient.sound trivial
  have hEq :
      collapsedMarkovForm.toClosedSemiboundedForm.energy false =
        collapsedMarkovForm.toClosedSemiboundedForm.energy true := by
    calc
      collapsedMarkovForm.toClosedSemiboundedForm.energy false =
          desc.quotientForm.toClosedSemiboundedForm.energy (Quotient.mk collapsedRel false) := by
        simpa using hfalse.symm
      _ = desc.quotientForm.toClosedSemiboundedForm.energy (Quotient.mk collapsedRel true) := by
        rw [hmk]
      _ = collapsedMarkovForm.toClosedSemiboundedForm.energy true := by
        simpa using htrue
  have hneq01 : (0 : ℝ) ≠ 1 := by
    norm_num
  have hEq01 : (0 : ℝ) = 1 := by
    simp [collapsedMarkovForm, collapsedForm] at hEq
  exact hneq01 hEq01

/-- Canonical obstruction setup on the actual collapsed quotient. -/
def accumulationMarkovCounterexample : QuotientMarkovFormDescentSetup Unit CollapsedOrbit where
  form := collapsedMarkovForm
  action := collapsedMarkovAction
  rel := collapsedRel
  descend := by
    intro hproper
    cases hproper
  accumulationObstructs := by
    intro hacc
    simpa using no_collapsed_markov_descended

/-- Public negative Markov witness: collapsing the orbit destroys descended-form licensing on
the actual quotient. -/
theorem collapsedOrbit_markov_obstructed :
    ¬ Nonempty (QuotientDescendedMarkovForm accumulationMarkovCounterexample.form
      accumulationMarkovCounterexample.rel) :=
  quotient_markov_obstruction_theorem accumulationMarkovCounterexample (by
    simp [accumulationMarkovCounterexample, collapsedMarkovAction])

def collapsedDirichletForm : ClosedDirichletForm CollapsedOrbit where
  toClosedMarkovForm := collapsedMarkovForm
  domainDense := True
  symmetric := True
  quasiRegular := True
  regular := True

/-- The collapsed action at the Dirichlet exact layer. -/
def collapsedDirichletAction :
    ExactInvariantAction Unit CollapsedOrbit
      collapsedDirichletForm.toClosedMarkovForm.toClosedSemiboundedForm where
  invariantDomain := Set.univ
  domain_invariant := by
    intro γ u hu
    simp
  exact_invariance := by
    intro γ u hu
    cases γ
    rfl
  properlyDiscontinuous := False

private theorem no_collapsed_dirichlet_descended :
    ¬ Nonempty (QuotientDescendedDirichletForm collapsedDirichletForm collapsedRel) := by
  intro h
  rcases h with ⟨desc⟩
  have hMarkov : Nonempty (QuotientDescendedMarkovForm collapsedMarkovForm collapsedRel) := by
    refine ⟨{ quotientForm := desc.quotientForm.toClosedMarkovForm
              pullback_exact := desc.pullback_exact }⟩
  exact no_collapsed_markov_descended hMarkov

/-- Canonical obstruction setup on the actual collapsed quotient at the Dirichlet layer. -/
def accumulationDirichletCounterexample : QuotientDirichletFormDescentSetup Unit CollapsedOrbit where
  form := collapsedDirichletForm
  action := collapsedDirichletAction
  rel := collapsedRel
  descend := by
    intro hproper
    cases hproper
  accumulationObstructs := by
    intro hacc
    simpa using no_collapsed_dirichlet_descended

/-- Public negative Dirichlet witness: collapsing the orbit destroys descended Dirichlet-form
licensing on the actual quotient. -/
theorem collapsedOrbit_dirichlet_obstructed :
    ¬ Nonempty (QuotientDescendedDirichletForm accumulationDirichletCounterexample.form
      accumulationDirichletCounterexample.rel) :=
  quotient_dirichlet_obstruction_theorem accumulationDirichletCounterexample (by
    simp [accumulationDirichletCounterexample, collapsedDirichletAction])

/-- If the descended Dirichlet form is obstructed, no process realization is in scope. -/
theorem collapsedOrbit_process_obstructed :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm collapsedDirichletForm collapsedRel,
      DescendedHuntProcess collapsedDirichletForm collapsedRel desc) :=
  quotient_process_obstruction_theorem collapsedOrbit_dirichlet_obstructed

/-- If the descended Dirichlet form is obstructed, no boundary object is in scope. -/
theorem collapsedOrbit_boundary_obstructed :
    ¬ Nonempty (Σ desc : QuotientDescendedDirichletForm collapsedDirichletForm collapsedRel,
      BoundaryRealization collapsedDirichletForm collapsedRel desc) :=
  quotient_boundary_obstruction_theorem collapsedOrbit_dirichlet_obstructed

end

end OperatorEstimates.Examples.FuchsianQuotient

/- 
  **Instantiations / Oseen.** Reduction statements for Oseen-style truncations.

  This file packages Oseen-style reduction data using complementary idempotent cutoffs and
  proves that natural truncation induces the sectorized reduction objects used by the generic
  Schur and cascade machinery.
-/
import OperatorEstimates.Instantiations.SpectralCutoff
import OperatorEstimates.Reduction.Cascade

namespace OperatorEstimates.Instantiations.Oseen

open ContinuousLinearMap
open scoped BigOperators InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Oseen-style reduction data built from a non-self-adjoint-compatible cutoff family. -/
structure OseenReductionFamily where
  cutoff : SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E)
  H : ℕ → E →L[𝕜] E
  Rinv : ℕ → E →L[𝕜] E
  γ : ℕ → ℝ
  lam : ℕ → ℝ
  gamma_pos : ∀ N, 0 < γ N
  lam_nonneg : ∀ N, 0 ≤ lam N
  PHQ_bound : ∀ N, ‖cutoff.P N * H N * cutoff.Q N‖ ≤ lam N
  QHP_bound : ∀ N, ‖cutoff.Q N * H N * cutoff.P N‖ ≤ lam N
  Rinv_bound : ∀ N, ‖Rinv N‖ ≤ (γ N)⁻¹

namespace OseenReductionFamily

/-- The generic reduction setup extracted from the Oseen-style cutoff data at scale `N`. -/
def setup (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    OperatorEstimates.EffectiveReductionSetup 𝕜 E where
  decomp := fam.cutoff.toComplementaryProjections N
  H := fam.H N
  Rinv := fam.Rinv N
  γ := fam.γ N
  lam := fam.lam N
  gamma_pos := fam.gamma_pos N
  lam_nonneg := fam.lam_nonneg N
  PHQ_bound := fam.PHQ_bound N
  QHP_bound := fam.QHP_bound N
  Rinv_bound := fam.Rinv_bound N

/-- The truncated `P H P` dynamics on the retained Oseen sector at scale `N`. -/
def projectedDynamics (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    E →L[𝕜] E :=
  fam.cutoff.P N * fam.H N * fam.cutoff.P N

/-- The Schur-reduced effective dynamics induced by the Oseen truncation at scale `N`. -/
def effectiveDynamics (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    E →L[𝕜] E :=
  (fam.setup N).effectiveOperator

/-- Exact Feshbach-Schur decomposition of the Oseen effective dynamics.

The projected retained-sector dynamics are corrected by the interaction term passing through
the truncated `Q` sector. Dropping that interaction yields the decoupled `P H P` dynamics. -/
theorem feshbach_schur_decomposition
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    fam.effectiveDynamics N =
      fam.projectedDynamics N -
        fam.cutoff.P N * fam.H N * fam.cutoff.Q N * fam.Rinv N *
          fam.cutoff.Q N * fam.H N * fam.cutoff.P N := by
  rfl

/-- The effective perturbative budget extracted from the Schur reduction at scale `N`. -/
noncomputable def delta (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  fam.lam N ^ 2 / fam.γ N

/-- The Oseen delta agrees with the generic setup delta. -/
theorem delta_eq_setup_delta (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    fam.delta N = (fam.setup N).delta :=
  rfl

/-- The control parameter at scale `N`. -/
noncomputable def chi (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  (fam.setup N).chi

/-- The coupling-to-gap ratio at scale `N`. -/
noncomputable def ratio (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  (fam.setup N).ratio

/-- A scale-indexed sectorized reduction system.

Each scale carries a bundled `EffectiveReductionSetup`; the sector decomposition, effective
dynamics, and Schur error budget are then read off canonically from that setup. -/
structure SectorizedSystem where
  setup : ℕ → OperatorEstimates.EffectiveReductionSetup 𝕜 E

namespace SectorizedSystem

/-- The retained/removed sector decomposition at scale `N`. -/
def decomp (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    OperatorEstimates.ComplementaryProjections 𝕜 E :=
  (sys.setup N).decomp

/-- The full operator carried by the sectorized system at scale `N`. -/
def fullDynamics (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) : E →L[𝕜] E :=
  (sys.setup N).H

/-- The projected retained-sector dynamics at scale `N`. -/
def projectedDynamics (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    E →L[𝕜] E :=
  (sys.decomp N).P * sys.fullDynamics N * (sys.decomp N).P

/-- The Schur-reduced effective dynamics at scale `N`. -/
def effectiveDynamics (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    E →L[𝕜] E :=
  (sys.setup N).effectiveOperator

/-- The Schur reduction budget at scale `N`. -/
noncomputable def delta (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  (sys.setup N).lam ^ 2 / (sys.setup N).γ

/-- The sectorized system delta agrees with the generic setup delta. -/
theorem delta_eq_setup_delta (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    sys.delta N = (sys.setup N).delta :=
  rfl

/-- The control parameter at scale `N`. -/
noncomputable def chi (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  (sys.setup N).chi

/-- The coupling-to-gap ratio at scale `N`. -/
noncomputable def ratio (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  (sys.setup N).ratio

/-- The induced decomposition satisfies the sector axioms by construction. -/
theorem sector_axioms (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (sys.decomp N).P + (sys.decomp N).Q = 1 ∧
      (sys.decomp N).P * (sys.decomp N).P = (sys.decomp N).P ∧
      (sys.decomp N).Q * (sys.decomp N).Q = (sys.decomp N).Q ∧
      (sys.decomp N).P * (sys.decomp N).Q = 0 ∧
      (sys.decomp N).Q * (sys.decomp N).P = 0 := by
  exact ⟨(sys.decomp N).sum_eq, (sys.decomp N).P_idem, (sys.decomp N).Q_idem,
    (sys.decomp N).PQ_zero, (sys.decomp N).QP_zero⟩

/-- The induced setup satisfies the quantitative reduction axioms at scale `N`. -/
theorem reduction_axioms (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    0 < (sys.setup N).γ ∧
      0 ≤ (sys.setup N).lam ∧
      ‖(sys.decomp N).P * sys.fullDynamics N * (sys.decomp N).Q‖ ≤ (sys.setup N).lam ∧
      ‖(sys.decomp N).Q * sys.fullDynamics N * (sys.decomp N).P‖ ≤ (sys.setup N).lam ∧
      ‖(sys.setup N).Rinv‖ ≤ ((sys.setup N).γ)⁻¹ := by
  exact ⟨(sys.setup N).gamma_pos, (sys.setup N).lam_nonneg, (sys.setup N).PHQ_bound,
    (sys.setup N).QHP_bound, (sys.setup N).Rinv_bound⟩

/-- The effective dynamics are Schur-close to the projected retained-sector dynamics. -/
theorem schur_error_bound (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖sys.effectiveDynamics N - sys.projectedDynamics N‖ ≤ sys.delta N := by
  simpa [effectiveDynamics, projectedDynamics, delta, decomp, fullDynamics] using
    (sys.setup N).error_bound

/-- The full bundled Schur reduction conclusion is available at every scale. -/
theorem schur_conclusion (sys : SectorizedSystem (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖sys.effectiveDynamics N - sys.projectedDynamics N‖ ≤ sys.delta N ∧
      ((sys.setup N).lam ^ 2 < (sys.setup N).γ ^ 2 →
        0 < (sys.setup N).γ - sys.delta N) ∧
      (∀ (C_r α d : ℝ), 0 ≤ C_r →
          ‖(sys.setup N).Rinv‖ ≤ C_r * Real.exp (-α * d) →
          ‖(sys.decomp N).P * sys.fullDynamics N * (sys.decomp N).Q * (sys.setup N).Rinv *
              (sys.decomp N).Q * sys.fullDynamics N * (sys.decomp N).P‖ ≤
            (sys.setup N).lam ^ 2 * C_r * Real.exp (-α * d)) := by
  constructor
  · exact sys.schur_error_bound N
  constructor
  · intro hsmall
    simpa [delta] using (sys.setup N).gap_survives hsmall
  · intro C_r α d hC_r hdecay
    simpa [decomp, fullDynamics] using
      (sys.setup N).locality_bound C_r α d hC_r hdecay

/-- Cascade gap control for the effective Oseen dynamics once the user supplies stepwise
operator bounds and a finite total budget. -/
theorem cascade_gap_survives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (sys : SectorizedSystem (𝕜 := ℝ) (E := E))
    (μ S : ℝ)
    (hstep : ∀ N, ‖sys.effectiveDynamics (N + 1) - sys.effectiveDynamics N‖ ≤ sys.delta N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, sys.effectiveDynamics 0 x⟫_ℝ)
    (hbudget : ∀ K, ∑ N ∈ Finset.range K, sys.delta N ≤ S) :
    ∀ K, ∀ x : E, (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, sys.effectiveDynamics K x⟫_ℝ :=
  OperatorEstimates.Cascade.cascade_gap_survives
    sys.effectiveDynamics sys.delta μ S hstep hcoercive hbudget

/-- The effective Oseen dynamics satisfy the standard cascade dichotomy. -/
theorem cascade_dichotomy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (sys : SectorizedSystem (𝕜 := ℝ) (E := E))
    (μ S : ℝ)
    (hstep : ∀ N, ‖sys.effectiveDynamics (N + 1) - sys.effectiveDynamics N‖ ≤ sys.delta N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, sys.effectiveDynamics 0 x⟫_ℝ)
    (hbudget : ∀ K, ∑ N ∈ Finset.range K, sys.delta N ≤ S) :
    (0 < μ - S ∧
        ∀ (K : ℕ) (x : E), (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, sys.effectiveDynamics K x⟫_ℝ) ∨
      μ ≤ S :=
  OperatorEstimates.Cascade.cascade_dichotomy
    sys.effectiveDynamics sys.delta μ S hstep hcoercive hbudget

end SectorizedSystem

/-- Natural Oseen truncation canonically induces the sectorized reduction system. -/
def sectorizedSystem (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) :
    SectorizedSystem (𝕜 := 𝕜) (E := E) where
  setup := fam.setup

@[simp] theorem sectorizedSystem_setup
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (fam.sectorizedSystem.setup N) = fam.setup N :=
  rfl

@[simp] theorem sectorizedSystem_projectedDynamics
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    fam.sectorizedSystem.projectedDynamics N = fam.projectedDynamics N :=
  rfl

@[simp] theorem sectorizedSystem_effectiveDynamics
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    fam.sectorizedSystem.effectiveDynamics N = fam.effectiveDynamics N :=
  rfl

@[simp] theorem sectorizedSystem_delta
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    fam.sectorizedSystem.delta N = fam.delta N :=
  rfl

/-- Oseen truncation induces a sectorized reduction system.

At each scale `N`, the natural truncation data canonically induce a sectorized system whose
retained/removed blocks satisfy the sector axioms, whose off-diagonal couplings and inverse
bound satisfy the reduction hypotheses, and whose effective dynamics admit the exact
Feshbach-Schur decomposition with perturbative error controlled by `λ² / γ`. -/
theorem truncation_induces_sectorized_reduction
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    let sys := fam.sectorizedSystem
    (sys.decomp N).P + (sys.decomp N).Q = 1 ∧
      (sys.decomp N).P * (sys.decomp N).P = (sys.decomp N).P ∧
      (sys.decomp N).Q * (sys.decomp N).Q = (sys.decomp N).Q ∧
      (sys.decomp N).P * (sys.decomp N).Q = 0 ∧
      (sys.decomp N).Q * (sys.decomp N).P = 0 ∧
      (0 < (sys.setup N).γ ∧
        0 ≤ (sys.setup N).lam ∧
        ‖(sys.decomp N).P * sys.fullDynamics N * (sys.decomp N).Q‖ ≤ (sys.setup N).lam ∧
        ‖(sys.decomp N).Q * sys.fullDynamics N * (sys.decomp N).P‖ ≤ (sys.setup N).lam ∧
        ‖(sys.setup N).Rinv‖ ≤ ((sys.setup N).γ)⁻¹) ∧
      (sys.effectiveDynamics N =
        sys.projectedDynamics N -
          (sys.decomp N).P * sys.fullDynamics N * (sys.decomp N).Q * (sys.setup N).Rinv *
            (sys.decomp N).Q * sys.fullDynamics N * (sys.decomp N).P) ∧
      ‖sys.effectiveDynamics N - sys.projectedDynamics N‖ ≤ sys.delta N := by
  let sys := fam.sectorizedSystem
  rcases sys.sector_axioms N with ⟨hsum, hPidem, hQidem, hPQ, hQP⟩
  rcases sys.reduction_axioms N with ⟨hγ, hlam, hPHQ, hQHP, hRinv⟩
  exact ⟨hsum, hPidem, hQidem, hPQ, hQP, ⟨hγ, hlam, hPHQ, hQHP, hRinv⟩,
    fam.feshbach_schur_decomposition N,
    sys.schur_error_bound N⟩

/-- Error control for the effective projected dynamics at scale `N`. -/
theorem error_bound (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖(fam.setup N).effectiveOperator
        - fam.cutoff.P N * fam.H N * fam.cutoff.P N‖ ≤
      fam.lam N ^ 2 / fam.γ N :=
  (fam.setup N).error_bound

/-- Schur error control expressed in the language of the induced effective dynamics. -/
theorem effective_dynamics_error_bound
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖fam.effectiveDynamics N - fam.projectedDynamics N‖ ≤ fam.delta N := by
  simpa [effectiveDynamics, projectedDynamics, delta] using fam.error_bound N

/-- Small off-diagonal coupling forces quantitative localization on the retained block, with
no self-adjointness assumption on the cutoff family. -/
theorem localization_regime (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖(fam.setup N).effectiveOperator
        - fam.cutoff.P N * fam.H N * fam.cutoff.P N‖ ≤
      fam.lam N ^ 2 / fam.γ N :=
  (fam.setup N).effective_localization_regime

/-- The effective Oseen dynamics inherit the Schur and locality conclusion at each scale. -/
theorem effective_dynamics_conclusion
    (fam : OseenReductionFamily (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖fam.effectiveDynamics N - fam.projectedDynamics N‖ ≤ fam.delta N ∧
      (fam.lam N ^ 2 < fam.γ N ^ 2 → 0 < fam.γ N - fam.delta N) ∧
      (∀ (C_r α d : ℝ), 0 ≤ C_r →
          ‖fam.Rinv N‖ ≤ C_r * Real.exp (-α * d) →
          ‖fam.cutoff.P N * fam.H N * fam.cutoff.Q N * fam.Rinv N *
              fam.cutoff.Q N * fam.H N * fam.cutoff.P N‖ ≤
            fam.lam N ^ 2 * C_r * Real.exp (-α * d)) := by
  simpa [sectorizedSystem_effectiveDynamics, sectorizedSystem_projectedDynamics,
    sectorizedSystem_delta, effectiveDynamics, projectedDynamics, delta] using
    fam.sectorizedSystem.schur_conclusion N

/-- If the user supplies stepwise bounds and a finite total budget, the induced effective
Oseen dynamics are controlled by the cascade gap theorem. -/
theorem effective_dynamics_cascade_gap_survives
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fam : OseenReductionFamily (𝕜 := ℝ) (E := E))
    (μ S : ℝ)
    (hstep : ∀ N, ‖fam.effectiveDynamics (N + 1) - fam.effectiveDynamics N‖ ≤ fam.delta N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, fam.effectiveDynamics 0 x⟫_ℝ)
    (hbudget : ∀ K, ∑ N ∈ Finset.range K, fam.delta N ≤ S) :
    ∀ K, ∀ x : E, (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, fam.effectiveDynamics K x⟫_ℝ := by
  simpa using fam.sectorizedSystem.cascade_gap_survives μ S hstep hcoercive hbudget

/-- The induced effective Oseen dynamics satisfy the standard cascade dichotomy. -/
theorem effective_dynamics_cascade_dichotomy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fam : OseenReductionFamily (𝕜 := ℝ) (E := E))
    (μ S : ℝ)
    (hstep : ∀ N, ‖fam.effectiveDynamics (N + 1) - fam.effectiveDynamics N‖ ≤ fam.delta N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, fam.effectiveDynamics 0 x⟫_ℝ)
    (hbudget : ∀ K, ∑ N ∈ Finset.range K, fam.delta N ≤ S) :
    (0 < μ - S ∧
        ∀ (K : ℕ) (x : E), (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, fam.effectiveDynamics K x⟫_ℝ) ∨
      μ ≤ S := by
  simpa using fam.sectorizedSystem.cascade_dichotomy μ S hstep hcoercive hbudget

/-- Oseen truncation yields the cascade dichotomy for the effective flow.

Once the effective Oseen dynamics admit stepwise control by the Schur error budget and the
total budget is finite, the induced flow is governed by the abstract cascade theorem: either
the residual coercive gap persists uniformly, or the full budget saturates it. -/
theorem truncation_yields_cascade_dichotomy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (fam : OseenReductionFamily (𝕜 := ℝ) (E := E))
    (μ S : ℝ)
    (hstep : ∀ N, ‖fam.effectiveDynamics (N + 1) - fam.effectiveDynamics N‖ ≤ fam.delta N)
    (hcoercive : ∀ x : E, μ * ‖x‖ ^ 2 ≤ ⟪x, fam.effectiveDynamics 0 x⟫_ℝ)
    (hbudget : ∀ K, ∑ N ∈ Finset.range K, fam.delta N ≤ S) :
    let sys := fam.sectorizedSystem
    (0 < μ - S ∧
        ∀ (K : ℕ) (x : E), (μ - S) * ‖x‖ ^ 2 ≤ ⟪x, sys.effectiveDynamics K x⟫_ℝ) ∨
      μ ≤ S := by
  simpa using fam.effective_dynamics_cascade_dichotomy μ S hstep hcoercive hbudget

end OseenReductionFamily

end OperatorEstimates.Instantiations.Oseen

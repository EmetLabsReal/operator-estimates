import OperatorEstimates.Core.StrictResolvent
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.Ring.Basic

/-!
  **Core / strict Yosida semigroup.** Bounded Yosida approximants and their exponential
  semigroup on a real Hilbert carrier.
-/

namespace OperatorEstimates

noncomputable section

open ContinuousLinearMap InnerProductSpace Filter

universe u

namespace StrictDirichletPrelude

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

local instance : NormedAlgebra ℚ (V →L[ℝ] V) :=
  .restrictScalars ℚ ℝ (V →L[ℝ] V)

/-- Bounded Yosida approximation built from the resolvent family. -/
def yosidaApprox (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) : V →L[ℝ] V :=
  μ • (ContinuousLinearMap.id ℝ V - cfg.resolvent μ hμ)

theorem yosidaApprox_apply (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (u : V) :
    cfg.yosidaApprox μ hμ u = μ • (u - cfg.resolvent μ hμ u) := by
  simp [yosidaApprox]

theorem yosidaApprox_scaled_commute
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (s t : ℝ) :
    Commute (s • cfg.yosidaApprox μ hμ) (t • cfg.yosidaApprox μ hμ) :=
  ((Commute.refl (cfg.yosidaApprox μ hμ)).smul_left s).smul_right t

/-- Exponential semigroup of the bounded Yosida approximation. -/
def yosidaSemigroupOp
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (t : ℝ) : V →L[ℝ] V :=
  NormedSpace.exp (t • cfg.yosidaApprox μ hμ)

def yosidaSemigroup
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) : ℝ → V → V :=
  fun t u => cfg.yosidaSemigroupOp μ hμ t u

theorem yosidaSemigroup_zero
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) :
    cfg.yosidaSemigroupOp μ hμ 0 = ContinuousLinearMap.id ℝ V := by
  ext u
  simp [yosidaSemigroupOp]

theorem yosidaSemigroup_add
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (s t : ℝ) :
    cfg.yosidaSemigroupOp μ hμ (s + t) =
      cfg.yosidaSemigroupOp μ hμ s * cfg.yosidaSemigroupOp μ hμ t := by
  simpa [yosidaSemigroupOp, add_smul] using
    (NormedSpace.exp_add_of_commute (cfg.yosidaApprox_scaled_commute μ hμ s t))

theorem yosidaSemigroup_zero_apply
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (u : V) :
    cfg.yosidaSemigroup μ hμ 0 u = u := by
  simp [yosidaSemigroup, yosidaSemigroup_zero]

theorem yosidaSemigroup_add_apply
    (cfg : StrictDirichletPrelude V) (μ : ℝ) (hμ : 0 ≤ μ) (s t : ℝ) (u : V) :
    cfg.yosidaSemigroup μ hμ (s + t) u =
      cfg.yosidaSemigroup μ hμ s (cfg.yosidaSemigroup μ hμ t u) := by
  change (cfg.yosidaSemigroupOp μ hμ (s + t)) u =
      (cfg.yosidaSemigroupOp μ hμ s * cfg.yosidaSemigroupOp μ hμ t) u
  rw [cfg.yosidaSemigroup_add μ hμ s t]

/-- Exponential semigroup of the bounded associated operator. -/
def limitSemigroupOp (cfg : StrictDirichletPrelude V) (t : ℝ) : V →L[ℝ] V :=
  NormedSpace.exp (t • cfg.associatedOperator)

def limitSemigroup (cfg : StrictDirichletPrelude V) : ℝ → V → V :=
  fun t u => cfg.limitSemigroupOp t u

/-- The effective semigroup on the strict Hilbert carrier. -/
abbrev effectiveSemigroupOp (cfg : StrictDirichletPrelude V) (t : ℝ) : V →L[ℝ] V :=
  cfg.limitSemigroupOp t

abbrev effectiveSemigroup (cfg : StrictDirichletPrelude V) : ℝ → V → V :=
  cfg.limitSemigroup

theorem limitSemigroup_zero (cfg : StrictDirichletPrelude V) :
    cfg.limitSemigroupOp 0 = ContinuousLinearMap.id ℝ V := by
  ext u
  simp [limitSemigroupOp]

theorem limitSemigroup_add (cfg : StrictDirichletPrelude V) (s t : ℝ) :
    cfg.limitSemigroupOp (s + t) = cfg.limitSemigroupOp s * cfg.limitSemigroupOp t := by
  have hcomm :
      Commute (s • cfg.associatedOperator) (t • cfg.associatedOperator) :=
    ((Commute.refl cfg.associatedOperator).smul_left s).smul_right t
  simpa [limitSemigroupOp, add_smul] using NormedSpace.exp_add_of_commute hcomm

theorem limitSemigroup_zero_apply (cfg : StrictDirichletPrelude V) (u : V) :
    cfg.limitSemigroup 0 u = u := by
  simp [limitSemigroup, cfg.limitSemigroup_zero]

theorem limitSemigroup_add_apply (cfg : StrictDirichletPrelude V) (s t : ℝ) (u : V) :
    cfg.limitSemigroup (s + t) u =
      cfg.limitSemigroup s (cfg.limitSemigroup t u) := by
  change (cfg.limitSemigroupOp (s + t)) u =
      (cfg.limitSemigroupOp s * cfg.limitSemigroupOp t) u
  rw [cfg.limitSemigroup_add s t]

/-- Operator-norm convergence of approximants transfers to operator-norm convergence of their
exponential semigroups at each fixed time. -/
theorem tendsto_exp_smul_of_tendsto
    {α : Type*} {l : Filter α} {Aε : α → V →L[ℝ] V}
    (cfg : StrictDirichletPrelude V)
    (hA : Tendsto Aε l (nhds cfg.associatedOperator))
    (t : ℝ) :
    Tendsto (fun a => NormedSpace.exp (t • Aε a)) l (nhds (cfg.limitSemigroupOp t)) := by
  have hsmul : Tendsto (fun a => t • Aε a) l (nhds (t • cfg.associatedOperator)) :=
    hA.const_smul t
  simpa [limitSemigroupOp] using Filter.Tendsto.exp hsmul

/-- If an operator-valued family has two limits, the semigroup limit is unique. -/
theorem semigroup_limit_unique
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {α : Type*} {l : Filter α} [NeBot l] {S T : W →L[ℝ] W} {F : α → W →L[ℝ] W}
    (hS : Tendsto F l (nhds S))
    (hT : Tendsto F l (nhds T)) :
    S = T :=
  tendsto_nhds_unique hS hT

/-- Uniqueness of the semigroup obtained as a pointwise limit of the same approximating operator
family. -/
theorem limitSemigroup_unique_of_tendsto
    {α : Type*} {l : Filter α} [NeBot l] {Aε : α → V →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (cfg : StrictDirichletPrelude V)
    (hS : ∀ t : ℝ, Tendsto (fun a => NormedSpace.exp (t • Aε a)) l (nhds (S t)))
    (hLimit :
      ∀ t : ℝ,
        Tendsto (fun a => NormedSpace.exp (t • Aε a)) l (nhds (cfg.limitSemigroupOp t))) :
    S = cfg.limitSemigroupOp := by
  funext t
  exact semigroup_limit_unique (hS t) (hLimit t)

/-- The effective semigroup is the operator-norm Yosida limit once the approximants converge to
the associated operator. -/
theorem effectiveSemigroup_is_yosida_limit
    {α : Type*} {l : Filter α} {Aε : α → V →L[ℝ] V}
    (cfg : StrictDirichletPrelude V)
    (hA : Tendsto Aε l (nhds cfg.associatedOperator))
    (t : ℝ) :
    Tendsto (fun a => NormedSpace.exp (t • Aε a)) l (nhds (cfg.effectiveSemigroupOp t)) := by
  simpa [effectiveSemigroupOp] using cfg.tendsto_exp_smul_of_tendsto hA t

/-- Any semigroup obtained as the same Yosida limit coincides with the effective semigroup. -/
theorem effectiveSemigroup_unique_as_yosida_limit
    {α : Type*} {l : Filter α} [NeBot l] {Aε : α → V →L[ℝ] V} {S : ℝ → V →L[ℝ] V}
    (cfg : StrictDirichletPrelude V)
    (hS : ∀ t : ℝ, Tendsto (fun a => NormedSpace.exp (t • Aε a)) l (nhds (S t)))
    (hA : Tendsto Aε l (nhds cfg.associatedOperator)) :
    S = cfg.effectiveSemigroupOp := by
  apply cfg.limitSemigroup_unique_of_tendsto hS
  intro t
  simpa [effectiveSemigroupOp] using cfg.tendsto_exp_smul_of_tendsto hA t

end StrictDirichletPrelude

end

end OperatorEstimates

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.Basic

/-!
  **Hierarchy / scale structure.**

  This file provides the structural vocabulary for scale-indexed arguments:

  - rooted parent-child hierarchies of scales;
  - coarse-graining maps along parent edges;
  - scale-indexed observables such as `Γ`, `Γ_local`, `Γ_jump`, `ratio`, and `δ`;
  - regime predicates for cascade, suppression, strong locality, and balance.

  It is intentionally definitional. The actual theorem content remains in
  `Reduction.Cascade`, `Reduction.BlockReduction`, and `Reduction.NoGo`.
-/

namespace OperatorEstimates.Hierarchy

open Filter ContinuousLinearMap
open scoped Topology

/-- A rooted parent-child hierarchy of scales. -/
structure ScaleHierarchy (ι : Type*) where
  root : ι
  parent : ι → Option ι
  level : ι → ℕ
  level_root : level root = 0
  parent_none_iff : ∀ i, parent i = none ↔ i = root
  parent_level : ∀ {i p : ι}, parent i = some p → level p + 1 = level i

namespace ScaleHierarchy

variable {ι : Type*} (H : ScaleHierarchy ι)

/-- The root has no parent. -/
theorem root_parent : H.parent H.root = none :=
  (H.parent_none_iff H.root).2 rfl

/-- Parent edges strictly lower the level. -/
theorem parent_level_lt {i p : ι} (h : H.parent i = some p) :
    H.level p < H.level i := by
  exact (H.parent_level h) ▸ Nat.lt_succ_self (H.level p)

/-- Any node with a parent is not the root. -/
theorem ne_root_of_parent_eq_some {i p : ι} (h : H.parent i = some p) :
    i ≠ H.root := by
  intro hi
  have hnone : H.parent i = none := by simpa [hi] using H.root_parent
  rw [h] at hnone
  cases hnone

end ScaleHierarchy

/-- A rooted chain through a scale hierarchy. -/
structure ScaleChain {ι : Type*} (H : ScaleHierarchy ι) where
  node : ℕ → ι
  root_node : node 0 = H.root
  parent_step : ∀ n, H.parent (node (n + 1)) = some (node n)

/-- Parent-child coarse-graining maps with quantitative edge bounds. -/
structure CoarseMapFamily {ι : Type*} (H : ScaleHierarchy ι)
    (𝕜 : Type*) [RCLike 𝕜]
    (E : ι → Type*) [∀ N, NormedAddCommGroup (E N)] [∀ N, InnerProductSpace 𝕜 (E N)] where
  toParent : ∀ {N M : ι}, H.parent N = some M → E N →L[𝕜] E M
  edgeBound : ∀ {N M : ι}, H.parent N = some M → ℝ
  edgeBound_nonneg : ∀ {N M : ι} (h : H.parent N = some M), 0 ≤ edgeBound h
  norm_toParent_le : ∀ {N M : ι} (h : H.parent N = some M), ‖toParent h‖ ≤ edgeBound h

/-- Scale-indexed observables carried by the cascade layer. -/
structure ScaleFamily where
  Γ : ℕ → ℝ
  Γ_local : ℕ → ℝ
  Γ_jump : ℕ → ℝ
  ratio : ℕ → ℝ
  δ : ℕ → ℝ
  L_eff : ℕ → ℝ := fun _ => 0
  decomp : ∀ N, Γ N = Γ_local N + Γ_jump N

/-- The cascade regime: transfer does not collapse along the scale axis. -/
def cascade_regime (S : ScaleFamily) : Prop :=
  ¬ Tendsto S.Γ atTop (nhds 0)

/-- The suppression regime: transfer collapses along the scale axis. -/
def suppression_regime (S : ScaleFamily) : Prop :=
  Tendsto S.Γ atTop (nhds 0)

/-- The strongly local regime: the jump contribution collapses along the scale axis. -/
def strongly_local_regime (S : ScaleFamily) : Prop :=
  Tendsto S.Γ_jump atTop (nhds 0)

/-- The balanced regime: the transfer ratio stays uniformly bounded and nonvanishing. -/
def balanced_regime (S : ScaleFamily) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ N in atTop, c ≤ S.ratio N ∧ S.ratio N ≤ C

end OperatorEstimates.Hierarchy

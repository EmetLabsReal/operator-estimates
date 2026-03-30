import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
  **Examples / Fischer projection.** Exact finite-dimensional witness that a Fischer-style
  symbolic encoding preserves stereochemical orientation because the relevant invariant is the
  sign of an oriented volume.

  The witness is intentionally minimal:

  - a canonical three-bond frame with the fourth bond fixed as the implicit away direction,
  - explicit determinant formula for the orientation sign,
  - singular failure boundary at zero oriented volume,
  - standard Fischer move parity: 180-degree rotation is even, quarter-turn is odd.
-/

namespace OperatorEstimates.Examples.FischerProjection

open Equiv
open Equiv.Perm

abbrev BondFrame := Matrix (Fin 3) (Fin 3) ℝ
abbrev FischerPosition := Fin 4

/-- Canonical Fischer-compatible frame.

Columns correspond to left / right / top bonds, with the lowest-priority bond taken as the
implicit away direction. Horizontal bonds are encoded as forward (`z = 1`), the vertical top bond
as backward (`z = -1`).
-/
def frameMatrix (a b c : ℝ) : BondFrame :=
  !![-a, b, 0;
     0,  0, c;
     1,  1, -1]

/-- Oriented volume of the retained stereochemical frame. -/
def orientedVolume (a b c : ℝ) : ℝ :=
  (frameMatrix a b c).det

/-- Nondegeneracy of the retained stereochemical frame. -/
def Nondegenerate (a b c : ℝ) : Prop :=
  orientedVolume a b c ≠ 0

/-- Determinant formula for the canonical Fischer-compatible frame. -/
theorem orientedVolume_eq (a b c : ℝ) :
    orientedVolume a b c = c * (a + b) := by
  simp [orientedVolume, frameMatrix, Matrix.det_fin_three]
  ring

/-- Positive horizontal and vertical scales force positive orientation. -/
theorem orientedVolume_pos {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < orientedVolume a b c := by
  rw [orientedVolume_eq]
  have hab : 0 < a + b := add_pos ha hb
  nlinarith

/-- A positively scaled Fischer-compatible frame is nondegenerate. -/
theorem nondegenerate_of_positive_scales {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Nondegenerate a b c := by
  have hvol : 0 < orientedVolume a b c := orientedVolume_pos ha hb hc
  exact ne_of_gt hvol

/-- Planarity is the singular boundary where the stereochemical sign disappears. -/
theorem planarBoundary_degenerate (a b : ℝ) :
    orientedVolume a b 0 = 0 := by
  rw [orientedVolume_eq]
  ring

/-- Permuting the visible bonds changes orientation exactly by permutation sign. -/
theorem orientedVolume_permute_columns (σ : Perm (Fin 3)) (a b c : ℝ) :
    ((frameMatrix a b c).submatrix id σ).det = σ.sign * orientedVolume a b c := by
  simpa [orientedVolume] using Matrix.det_permute' σ (frameMatrix a b c)

/-- Swapping the two horizontal bonds flips stereochemical orientation. -/
theorem swap_horizontal_flips (a b c : ℝ) :
    ((frameMatrix a b c).submatrix id (swap (0 : Fin 3) 1)).det = -orientedVolume a b c := by
  have hσ : (0 : Fin 3) ≠ 1 := by decide
  rw [orientedVolume_permute_columns (swap (0 : Fin 3) 1) a b c, sign_swap hσ]
  simp

/-- Cyclically relabeling the visible bonds is an even move and preserves orientation. -/
theorem threeCycle_preserves (a b c : ℝ) :
    ((frameMatrix a b c).submatrix id
      (((swap (0 : Fin 3) 2) * (swap (0 : Fin 3) 1) : Perm (Fin 3)))).det =
      orientedVolume a b c := by
  let σ : Perm (Fin 3) := (swap (0 : Fin 3) 2) * (swap (0 : Fin 3) 1)
  have hσ : σ.sign = 1 := by
    native_decide
  change ((frameMatrix a b c).submatrix id σ).det = orientedVolume a b c
  rw [orientedVolume_permute_columns σ a b c, hσ]
  simp

/-- Standard 180-degree Fischer rotation: swap left/right and top/bottom. -/
def rot180 : Perm FischerPosition :=
  (swap 0 1) * (swap 2 3)

/-- Standard quarter-turn Fischer rotation, modeled as a 4-cycle on the projection positions. -/
def rot90 : Perm FischerPosition :=
  (swap 0 3) * (swap 0 1) * (swap 0 2)

/-- A Fischer 180-degree rotation is even, so it preserves configuration. -/
theorem sign_rot180 : rot180.sign = 1 := by
  native_decide

/-- A Fischer quarter-turn is odd, so it reverses configuration. -/
theorem sign_rot90 : rot90.sign = -1 := by
  native_decide

/-- Explicit position action for the 180-degree Fischer rule. -/
theorem rot180_apply :
    rot180 0 = 1 ∧ rot180 1 = 0 ∧ rot180 2 = 3 ∧ rot180 3 = 2 := by
  decide

/-- Explicit position action for the quarter-turn Fischer rule. -/
theorem rot90_apply :
    rot90 0 = 2 ∧ rot90 2 = 1 ∧ rot90 1 = 3 ∧ rot90 3 = 0 := by
  decide

end OperatorEstimates.Examples.FischerProjection

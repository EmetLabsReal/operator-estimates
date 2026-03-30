/-
  **Reduction / no-go.** Deterministic obstruction theorems for the endpoint rigidity
  implication.

  The obstruction applies when the effective scale `λ² / γ` stays bounded below because
  both `λ / γ` and `γ` stay bounded below. In that regime, any observable `Γ` bounded
  below by a positive multiple of `λ² / γ` cannot converge to zero. In scale language,
  this is the obstruction to closing the endpoint rigidity implication from deterministic
  saturation data alone. Any stronger application-level interpretation of that implication
  must be supplied separately.
-/
import OperatorEstimates.Hierarchy.ScaleHierarchy
import OperatorEstimates.Reduction.Cascade

namespace OperatorEstimates.NoGo

open Filter
open scoped Topology

/-! ### Auxiliary lemmas -/
section AuxLemmas

/-- An eventual positive lower bound prevents convergence to zero. -/
lemma not_tendsto_zero_of_eventually_ge
    (f : ℕ → ℝ) (c : ℝ)
    (hc : 0 < c)
    (h : ∀ᶠ n in atTop, c ≤ f n) :
    ¬ Tendsto f atTop (𝓝 0) := by
  intro hf
  have hlt : ∀ᶠ n in atTop, f n < c := by
    simpa using hf (Iio_mem_nhds hc)
  rcases (h.and hlt).exists with ⟨n, hge, hltc⟩
  linarith

end AuxLemmas

/-! ### Saturation bounds -/
section SaturationBounds

/-- Saturation of `λ / γ`, together with a nondegenerate gap and a lower bound by
the effective scale `λ² / γ`, forces an eventual positive lower bound on `Γ`. -/
lemma eventually_lower_bound_Gamma_of_saturation
    (lam gamma Gamma : ℕ → ℝ) (a c γ0 : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hγ0 : 0 < γ0)
    (h_ratio_lower : ∀ᶠ n in atTop, c ≤ lam n / gamma n)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_Gamma_lower : ∀ᶠ n in atTop, a * (lam n) ^ 2 / gamma n ≤ Gamma n) :
    ∀ᶠ n in atTop, a * c ^ 2 * γ0 ≤ Gamma n := by
  filter_upwards [h_ratio_lower, h_gamma_lower, h_Gamma_lower] with n hratio hgamma hGamma
  have hgamma_pos : 0 < gamma n := lt_of_lt_of_le hγ0 hgamma
  have hratio_sq : c ^ 2 ≤ (lam n / gamma n) ^ 2 := by
    nlinarith [hc, hratio]
  have hscale : c ^ 2 * γ0 ≤ (lam n / gamma n) ^ 2 * gamma n := by
    nlinarith [hratio_sq, hgamma, hγ0]
  have hcancel : (lam n / gamma n) * gamma n = lam n := by
    field_simp [hgamma_pos.ne']
  have hrewrite : (lam n / gamma n) ^ 2 * gamma n = (lam n) ^ 2 / gamma n := by
    calc
      (lam n / gamma n) ^ 2 * gamma n = (lam n / gamma n) * ((lam n / gamma n) * gamma n) := by ring
      _ = (lam n / gamma n) * lam n := by rw [hcancel]
      _ = lam n * (lam n / gamma n) := by ring
      _ = (lam n) ^ 2 / gamma n := by
          rw [pow_two, div_eq_mul_inv]
          ring
  have hscale' : c ^ 2 * γ0 ≤ (lam n) ^ 2 / gamma n := by
    simpa [hrewrite] using hscale
  have hmult : a * c ^ 2 * γ0 ≤ a * (lam n) ^ 2 / gamma n := by
    calc
      a * c ^ 2 * γ0 = a * (c ^ 2 * γ0) := by ring
      _ ≤ a * ((lam n) ^ 2 / gamma n) := mul_le_mul_of_nonneg_left hscale' ha.le
      _ = a * (lam n) ^ 2 / gamma n := by ring
  exact le_trans hmult hGamma

end SaturationBounds

/-! ### Endpoint obstruction -/
section NoGo

/-- Deterministic no-go theorem for the endpoint rigidity implication.

If `λ / γ` stays bounded below away from zero, `γ` stays bounded below away from zero,
and `Γ` stays bounded below by a positive multiple of `λ² / γ`, then the implication
`¬(λ / γ → 0) → Γ → 0` is false. If an application interprets `Γ → 0` as a further
regularity or smoothness closure statement, that interpretation is external to this theorem
and must be formalized separately. -/
theorem no_go_saturation
    (lam gamma Gamma : ℕ → ℝ) (a c γ0 : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hγ0 : 0 < γ0)
    (h_ratio_lower : ∀ᶠ n in atTop, c ≤ lam n / gamma n)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_Gamma_lower : ∀ᶠ n in atTop, a * (lam n) ^ 2 / gamma n ≤ Gamma n) :
    ¬ (¬ Tendsto (fun n => lam n / gamma n) atTop (𝓝 0) →
        Tendsto Gamma atTop (𝓝 0)) := by
  intro h_rigidity
  have hratio_not : ¬ Tendsto (fun n => lam n / gamma n) atTop (𝓝 0) :=
    not_tendsto_zero_of_eventually_ge (fun n => lam n / gamma n) c hc h_ratio_lower
  have hGamma_lower' :
      ∀ᶠ n in atTop, a * c ^ 2 * γ0 ≤ Gamma n :=
    eventually_lower_bound_Gamma_of_saturation lam gamma Gamma a c γ0
      ha hc hγ0 h_ratio_lower h_gamma_lower h_Gamma_lower
  have hGamma_pos : 0 < a * c ^ 2 * γ0 := by
    positivity
  have hGamma_not : ¬ Tendsto Gamma atTop (𝓝 0) :=
    not_tendsto_zero_of_eventually_ge Gamma (a * c ^ 2 * γ0) hGamma_pos hGamma_lower'
  exact hGamma_not (h_rigidity hratio_not)

/-- User-facing corollary for the common saturation language "`λ` is eventually comparable
to `γ`". The upper bound is not needed for the obstruction itself, but it matches the
way applications are often phrased. -/
theorem no_go_of_eventually_comparable
    (lam gamma Gamma : ℕ → ℝ) (a c C γ0 : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hC : c ≤ C) (hγ0 : 0 < γ0)
    (h_ratio_lower : ∀ᶠ n in atTop, c ≤ lam n / gamma n)
    (h_ratio_upper : ∀ᶠ n in atTop, lam n / gamma n ≤ C)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_Gamma_lower : ∀ᶠ n in atTop, a * (lam n) ^ 2 / gamma n ≤ Gamma n) :
    ¬ (¬ Tendsto (fun n => lam n / gamma n) atTop (𝓝 0) →
        Tendsto Gamma atTop (𝓝 0)) := by
  have h_window : ∀ᶠ n in atTop, c ≤ C :=
    Eventually.of_forall (fun (_ : ℕ) => hC)
  have h_comparable : ∀ᶠ n in atTop, c ≤ lam n / gamma n ∧ lam n / gamma n ≤ C := by
    filter_upwards [h_ratio_lower, h_ratio_upper, h_window] with n hlow hupp _
    exact ⟨hlow, hupp⟩
  exact no_go_saturation lam gamma Gamma a c γ0 ha hc hγ0
    (h_comparable.mono fun _ h => h.1) h_gamma_lower h_Gamma_lower

/-- Scale-family wrapper for the deterministic obstruction theorem. In suppression language,
deterministic saturation data cannot justify closing the implication from nonvanishing ratio
to transfer collapse. Any stronger application-level reading of that collapse remains external
to this theorem. -/
theorem no_go_for_scale_family
    (S : Hierarchy.ScaleFamily) (gamma : ℕ → ℝ) (a c γ0 : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hγ0 : 0 < γ0)
    (h_ratio_lower : ∀ᶠ n in atTop, c ≤ S.ratio n / gamma n)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_Gamma_lower : ∀ᶠ n in atTop, a * (S.ratio n) ^ 2 / gamma n ≤ S.Γ n) :
    ¬ (¬ Tendsto (fun n => S.ratio n / gamma n) atTop (𝓝 0) →
        Hierarchy.suppression_regime S) := by
  simpa [Hierarchy.suppression_regime] using
    no_go_saturation S.ratio gamma S.Γ a c γ0 ha hc hγ0
      h_ratio_lower h_gamma_lower h_Gamma_lower

/-- If the scale ratio stays balanced away from zero and the jump observable stays above the
effective scale `ratio² * γ`, then the jump contribution cannot collapse. This is the direct
strong-locality obstruction used by the hierarchy endpoint theorem. -/
theorem not_strongly_local_of_balanced_jump_family
    (S : Hierarchy.ScaleFamily) (gamma : ℕ → ℝ) (a γ0 : ℝ)
    (ha : 0 < a) (hγ0 : 0 < γ0)
    (hbal : Hierarchy.balanced_regime S)
    (h_gamma_lower : ∀ᶠ n in atTop, γ0 ≤ gamma n)
    (h_jump_lower : ∀ᶠ n in atTop, a * S.ratio n ^ 2 * gamma n ≤ S.Γ_jump n) :
    ¬ Hierarchy.strongly_local_regime S := by
  rcases hbal with ⟨c, _, hc, _, hwindow⟩
  have h_ratio_lower :
      ∀ᶠ n in atTop, c ≤ (S.ratio n * gamma n) / gamma n := by
    filter_upwards [hwindow, h_gamma_lower] with n hratio hgamma
    have hgamma_pos : 0 < gamma n := lt_of_lt_of_le hγ0 hgamma
    have hcancel : (S.ratio n * gamma n) / gamma n = S.ratio n := by
      field_simp [hgamma_pos.ne']
    simpa [hcancel] using hratio.1
  have h_Gamma_lower :
      ∀ᶠ n in atTop, a * (S.ratio n * gamma n) ^ 2 / gamma n ≤ S.Γ_jump n := by
    filter_upwards [h_jump_lower, h_gamma_lower] with n hjump hgamma
    have hgamma_pos : 0 < gamma n := lt_of_lt_of_le hγ0 hgamma
    have hrewrite :
        a * (S.ratio n * gamma n) ^ 2 / gamma n = a * S.ratio n ^ 2 * gamma n := by
      field_simp [pow_two, hgamma_pos.ne']
    simpa [hrewrite] using hjump
  have h_nogo :
      ¬ (¬ Tendsto (fun n => (S.ratio n * gamma n) / gamma n) atTop (𝓝 0) →
          Tendsto S.Γ_jump atTop (𝓝 0)) :=
    no_go_saturation (fun n => S.ratio n * gamma n) gamma S.Γ_jump a c γ0
      ha hc hγ0 h_ratio_lower h_gamma_lower h_Gamma_lower
  intro hlocal
  apply h_nogo
  intro _
  simpa [Hierarchy.strongly_local_regime] using hlocal

end NoGo

end OperatorEstimates.NoGo

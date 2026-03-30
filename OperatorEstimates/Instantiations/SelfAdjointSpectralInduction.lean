/- 
  **Instantiations / self-adjoint spectral induction.** Canonical induction from a
  finite-dimensional self-adjoint spectral core into the existing reduction API.

  This file is intentionally narrow. It does not add a new reduction theorem and it does not
  strengthen `BlockReduction`. Instead it shows that a natural operator class already induces the
  public setup objects:

  - a scale-indexed cutoff family built from spectral subspaces of the self-adjoint core;
  - the corresponding complementary projections;
  - an `EffectiveReductionSetup` for the perturbed operator `T + B`.

  The induced coupling scale is chosen canonically as the maximum of the two off-diagonal
  perturbation blocks, so the reduction bounds are automatic once the resolvent data are supplied.
-/
import OperatorEstimates.Instantiations.SpectralCutoff
import OperatorEstimates.Core.CoerciveInverseRangeQ
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic

namespace OperatorEstimates.Instantiations.SelfAdjointSpectralInduction

open ContinuousLinearMap Module End

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-! ### Canonical spectral cores -/

/-- A finite-dimensional self-adjoint spectral core plus perturbation and complementary-block
inverse data. The retained spectral slices are specified by scale-indexed finite sets of
eigenvalues of the self-adjoint core. -/
structure SelfAdjointSpectralCore where
  T : E →L[𝕜] E
  B : E →L[𝕜] E
  retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E))
  Rinv : ℕ → E →L[𝕜] E
  γ : ℕ → ℝ
  hT_symm : (T : End 𝕜 E).IsSymmetric
  gamma_pos : ∀ N, 0 < γ N
  Rinv_bound : ∀ N, ‖Rinv N‖ ≤ (γ N)⁻¹

namespace SelfAdjointSpectralCore

/-- The retained spectral subspace at scale `N`, canonically induced from the eigenspaces of the
self-adjoint core. -/
noncomputable def retainedSubspace
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) : Submodule 𝕜 E :=
  (core.retain N).sup fun μ => eigenspace (core.T : End 𝕜 E) (μ : 𝕜)

omit [FiniteDimensional 𝕜 E] in
private theorem retainedSubspace_mem_invtSubmodule_aux
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E))
    (s : Finset (Eigenvalues (core.T : End 𝕜 E))) :
    s.sup (fun μ => eigenspace (core.T : End 𝕜 E) (μ : 𝕜)) ∈
      Module.End.invtSubmodule (core.T : End 𝕜 E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact Module.End.invtSubmodule.bot_mem (f := (core.T : End 𝕜 E))
  | insert μ s hμ ih =>
      simpa [Finset.sup_insert, hμ] using
        Module.End.invtSubmodule.sup_mem
          (eigenspace_mem_invtSubmodule (core.T : End 𝕜 E) (μ : 𝕜)) ih

omit [FiniteDimensional 𝕜 E] in
/-- The retained spectral subspace is invariant under the self-adjoint core. -/
theorem retainedSubspace_mem_invtSubmodule
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    core.retainedSubspace N ∈ Module.End.invtSubmodule (core.T : End 𝕜 E) := by
  simpa [retainedSubspace] using
    core.retainedSubspace_mem_invtSubmodule_aux (core.retain N)

omit [FiniteDimensional 𝕜 E] in
/-- The orthogonal complement of the retained spectral subspace is also invariant. -/
theorem orthogonal_retained_mem_invtSubmodule
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.retainedSubspace N)ᗮ ∈ Module.End.invtSubmodule (core.T : End 𝕜 E) :=
  LinearMap.IsSymmetric.orthogonalComplement_mem_invtSubmodule core.hT_symm
    (core.retainedSubspace_mem_invtSubmodule N)

omit [FiniteDimensional 𝕜 E] in
private theorem map_retainedSubspace
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ)
    {x : E} (hx : x ∈ core.retainedSubspace N) :
    core.T x ∈ core.retainedSubspace N := by
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := core.T)).1
    (core.retainedSubspace_mem_invtSubmodule N) x hx

omit [FiniteDimensional 𝕜 E] in
private theorem map_orthogonal_retained
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ)
    {x : E} (hx : x ∈ (core.retainedSubspace N)ᗮ) :
    core.T x ∈ (core.retainedSubspace N)ᗮ := by
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (f := core.T)).1
    (core.orthogonal_retained_mem_invtSubmodule N) x hx

/-- The canonical spectral cutoff family induced by the retained eigenspace selections. -/
noncomputable def cutoff
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) :
    SpectralCutoff.SpectralCutoffFamily (𝕜 := 𝕜) (E := E) where
  P N := (core.retainedSubspace N).starProjection
  Q N := ((core.retainedSubspace N)ᗮ).starProjection
  sum_eq N := by
    simpa [ContinuousLinearMap.one_def] using
      (Submodule.id_eq_sum_starProjection_self_orthogonalComplement
        (K := core.retainedSubspace N)).symm
  P_idem N := by
    simpa using (core.retainedSubspace N).isIdempotentElem_starProjection.eq
  Q_idem N := by
    simpa using ((core.retainedSubspace N)ᗮ).isIdempotentElem_starProjection.eq
  PQ_zero N := by
    simpa using
      (Submodule.isOrtho_orthogonal_right (core.retainedSubspace N)).starProjection_comp_starProjection
  QP_zero N := by
    simpa using
      (Submodule.isOrtho_orthogonal_left (core.retainedSubspace N)).starProjection_comp_starProjection

private lemma phq_T_zero
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.cutoff.P N) * core.T * (core.cutoff.Q N) = 0 := by
  ext x
  have hxQ : core.cutoff.Q N x ∈ (core.retainedSubspace N)ᗮ := by
    simp [cutoff]
  have hTx : core.T (core.cutoff.Q N x) ∈ (core.retainedSubspace N)ᗮ :=
    core.map_orthogonal_retained N hxQ
  have hzero :
      (core.retainedSubspace N).starProjection (core.T (core.cutoff.Q N x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := core.retainedSubspace N)).2 hTx
  simpa [cutoff, ContinuousLinearMap.mul_apply] using hzero

private lemma qhp_T_zero
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.cutoff.Q N) * core.T * (core.cutoff.P N) = 0 := by
  ext x
  have hxP : core.cutoff.P N x ∈ core.retainedSubspace N := by
    simp [cutoff, Submodule.starProjection_apply_mem]
  have hTx : core.T (core.cutoff.P N x) ∈ core.retainedSubspace N :=
    core.map_retainedSubspace N hxP
  have hzero :
      ((core.retainedSubspace N)ᗮ).starProjection (core.T (core.cutoff.P N x)) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (K := core.retainedSubspace N) hTx
  simpa [cutoff, ContinuousLinearMap.mul_apply] using hzero

/-- Canonical off-diagonal size for the perturbation block. -/
noncomputable def coupling
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) : ℝ :=
  max ‖core.cutoff.P N * core.B * core.cutoff.Q N‖
    ‖core.cutoff.Q N * core.B * core.cutoff.P N‖

private lemma phq_T_add_B
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    core.cutoff.P N * (core.T + core.B) * core.cutoff.Q N =
      core.cutoff.P N * core.B * core.cutoff.Q N := by
  have spl :
      core.cutoff.P N * (core.T + core.B) * core.cutoff.Q N =
        core.cutoff.P N * core.T * core.cutoff.Q N +
          core.cutoff.P N * core.B * core.cutoff.Q N := by
    ext x
    simp [ContinuousLinearMap.mul_apply, map_add]
  rw [spl, core.phq_T_zero N, zero_add]

private lemma qhp_T_add_B
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    core.cutoff.Q N * (core.T + core.B) * core.cutoff.P N =
      core.cutoff.Q N * core.B * core.cutoff.P N := by
  have spl :
      core.cutoff.Q N * (core.T + core.B) * core.cutoff.P N =
        core.cutoff.Q N * core.T * core.cutoff.P N +
          core.cutoff.Q N * core.B * core.cutoff.P N := by
    ext x
    simp [ContinuousLinearMap.mul_apply, map_add]
  rw [spl, core.qhp_T_zero N, zero_add]

/-- The canonical reduction setup induced from the self-adjoint spectral core at scale `N`. -/
noncomputable def inducedSetup
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    OperatorEstimates.EffectiveReductionSetup 𝕜 E where
  decomp := (core.cutoff).toComplementaryProjections N
  H := core.T + core.B
  Rinv := core.Rinv N
  γ := core.γ N
  lam := core.coupling N
  gamma_pos := core.gamma_pos N
  lam_nonneg := by
    dsimp [coupling]
    exact le_max_iff.mpr (Or.inl (norm_nonneg _))
  PHQ_bound := by
    have hP : (core.cutoff.toComplementaryProjections N).P = core.cutoff.P N := rfl
    have hQ : (core.cutoff.toComplementaryProjections N).Q = core.cutoff.Q N := rfl
    rw [hP, hQ, core.phq_T_add_B N]
    exact le_max_left _ _
  QHP_bound := by
    have hP : (core.cutoff.toComplementaryProjections N).P = core.cutoff.P N := rfl
    have hQ : (core.cutoff.toComplementaryProjections N).Q = core.cutoff.Q N := rfl
    rw [hP, hQ, core.qhp_T_add_B N]
    exact le_max_right _ _
  Rinv_bound := core.Rinv_bound N

/-- The delta of the induced setup equals `coupling² / γ`. -/
theorem inducedSetup_delta
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.inducedSetup N).delta = core.coupling N ^ 2 / core.γ N :=
  rfl

/-- The control parameter of the induced setup equals `coupling² / γ²`. -/
theorem inducedSetup_chi
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.inducedSetup N).chi = core.coupling N ^ 2 / core.γ N ^ 2 :=
  rfl

/-- The ratio of the induced setup equals `coupling / γ`. -/
theorem inducedSetup_ratio
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    (core.inducedSetup N).ratio = core.coupling N / core.γ N :=
  rfl

/-- The induced setup is immediately consumable by the generic reduction error theorem. -/
theorem induced_error_bound
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖(core.inducedSetup N).effectiveOperator
        - core.cutoff.P N * (core.T + core.B) * core.cutoff.P N‖ ≤
      core.coupling N ^ 2 / core.γ N :=
  (core.inducedSetup N).error_bound

/-- The induced setup inherits the full bundled reduction conclusion unchanged. -/
theorem induced_conclusion
    (core : SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    ‖(core.inducedSetup N).effectiveOperator
        - core.cutoff.P N * (core.T + core.B) * core.cutoff.P N‖ ≤
        core.coupling N ^ 2 / core.γ N ∧
      (core.coupling N ^ 2 < core.γ N ^ 2 → 0 < core.γ N - core.coupling N ^ 2 / core.γ N) ∧
      (∀ (C_r α d : ℝ), 0 ≤ C_r →
          ‖core.Rinv N‖ ≤ C_r * Real.exp (-α * d) →
          ‖core.cutoff.P N * (core.T + core.B) * core.cutoff.Q N * core.Rinv N *
              core.cutoff.Q N * (core.T + core.B) * core.cutoff.P N‖ ≤
            core.coupling N ^ 2 * C_r * Real.exp (-α * d)) :=
  (core.inducedSetup N).conclusion

end SelfAdjointSpectralCore

/-! ### Coercivity-derived spectral cores -/

/-- The retained spectral subspace, defined independently of `SelfAdjointSpectralCore` so it can be
referenced in constructors that *build* a core. -/
noncomputable def retainedSubspaceOf (T : E →L[𝕜] E)
    (retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E))) (N : ℕ) : Submodule 𝕜 E :=
  (retain N).sup fun μ => eigenspace (T : End 𝕜 E) (μ : 𝕜)

/-- Self-adjoint spectral core where complement-sector inverse data is *derived* from coercivity on
`range Q` at each scale, rather than supplied as a raw ambient `Rinv`. The conversion
`toSelfAdjointSpectralCore` manufactures `Rinv` via `RinvAmbient`. -/
structure SelfAdjointSpectralCoreFromCoercivity where
  T : E →L[𝕜] E
  B : E →L[𝕜] E
  retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E))
  hT_symm : (T : End 𝕜 E).IsSymmetric
  coercData : ℕ → CoerciveRightInverseOnRangeQ 𝕜 E
  hQ_eq : ∀ N, (coercData N).Q = ((retainedSubspaceOf T retain N)ᗮ).starProjection
  hH_eq : ∀ N, (coercData N).H = T + B

namespace SelfAdjointSpectralCoreFromCoercivity

/-- The complement projection at scale `N` is an orthogonal projection and therefore has `‖Q‖ ≤ 1`. -/
private theorem Q_norm_le_one (core : SelfAdjointSpectralCoreFromCoercivity (𝕜 := 𝕜) (E := E))
    (N : ℕ) : ‖(core.coercData N).Q‖ ≤ 1 := by
  rw [core.hQ_eq N]
  exact Submodule.starProjection_norm_le _

/-- Convert a coercivity-derived core into a `SelfAdjointSpectralCore` by lifting each
`CoerciveRightInverseOnRangeQ` to an ambient `Rinv` via `RinvAmbient`. -/
noncomputable def toSelfAdjointSpectralCore
    (core : SelfAdjointSpectralCoreFromCoercivity (𝕜 := 𝕜) (E := E)) :
    SelfAdjointSpectralCore (𝕜 := 𝕜) (E := E) where
  T := core.T
  B := core.B
  retain := core.retain
  Rinv N := (core.coercData N).RinvAmbient
  γ N := (core.coercData N).γ
  hT_symm := core.hT_symm
  gamma_pos N := (core.coercData N).gamma_pos
  Rinv_bound N := (core.coercData N).RinvAmbient_opNorm_bound (core.Q_norm_le_one N)

/-- The retained subspace of the converted core agrees with the standalone definition. -/
theorem toSelfAdjointSpectralCore_retainedSubspace
    (core : SelfAdjointSpectralCoreFromCoercivity (𝕜 := 𝕜) (E := E)) (N : ℕ) :
    core.toSelfAdjointSpectralCore.retainedSubspace N = retainedSubspaceOf core.T core.retain N :=
  rfl

end SelfAdjointSpectralCoreFromCoercivity

/-! ### Direct construction from complement spectral gap

The standard use case: `T` self-adjoint, `B` perturbation, eigenvalue selections `retain`, and at each
scale the complement block `Q(T+B)Q` is coercive on `range Q` with gap `γ N`. The right inverse is
manufactured automatically via `CoerciveRightInverseOnRangeQ.fromCoercivity`. -/

/-- The complement projection for the retained eigenspace at scale `N`, as a standalone definition. -/
noncomputable def complementProjectionOf (T : E →L[𝕜] E)
    (retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E))) (N : ℕ) : E →L[𝕜] E :=
  ((retainedSubspaceOf T retain N)ᗮ).starProjection

private theorem complementProjectionOf_idem (T : E →L[𝕜] E)
    (retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E))) (N : ℕ) :
    (complementProjectionOf T retain N).comp (complementProjectionOf T retain N) =
      complementProjectionOf T retain N :=
  ((retainedSubspaceOf T retain N)ᗮ).isIdempotentElem_starProjection.eq

/-- Build a `SelfAdjointSpectralCoreFromCoercivity` — and through it the full reduction API —
from just spectral gap data. The right inverse is derived automatically in finite dimensions.

**Input contract:** at each scale `N`, the complement block `Q(T+B)Q` restricted to `range Q` is
coercive with gap `γ N`. That is:
```
∀ u ∈ range Q, γ N * ‖u‖² ≤ Re⟨u, Q(T+B)Q u⟩
```
where `Q N` is the orthogonal complement projection of the retained spectral subspace.

**Output:** a `SelfAdjointSpectralCoreFromCoercivity` whose `.toSelfAdjointSpectralCore.inducedSetup`
gives the full `EffectiveReductionSetup` at each scale. -/
noncomputable def SelfAdjointSpectralCoreFromCoercivity.fromGap
    (T B : E →L[𝕜] E)
    (retain : ℕ → Finset (Eigenvalues (T : End 𝕜 E)))
    (hT_symm : (T : End 𝕜 E).IsSymmetric)
    (γ : ℕ → ℝ) (hγ : ∀ N, 0 < γ N)
    (hcoercive : ∀ N, ∀ u : rangeSubmodule (complementProjectionOf T retain N),
      γ N * ‖u‖ ^ 2 ≤
        RCLike.re (inner 𝕜 u
          (M_U (complementProjectionOf T retain N)
            (complementProjectionOf_idem T retain N) (T + B) u))) :
    SelfAdjointSpectralCoreFromCoercivity (𝕜 := 𝕜) (E := E) where
  T := T
  B := B
  retain := retain
  hT_symm := hT_symm
  coercData N :=
    CoerciveRightInverseOnRangeQ.fromCoercivity
      (complementProjectionOf T retain N) (T + B)
      (complementProjectionOf_idem T retain N)
      (γ N) (hγ N) (hcoercive N)
  hQ_eq _ := rfl
  hH_eq _ := rfl

end OperatorEstimates.Instantiations.SelfAdjointSpectralInduction

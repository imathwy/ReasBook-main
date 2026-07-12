import Mathlib

-- `lean_leansearch` was unavailable in this session, so this file uses mathlib's canonical
-- open-subset inclusion `Subtype.val : U → M` and manifold derivative `mfderiv`.

noncomputable section

open scoped Manifold

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Proposition 3.9: if `U` is an open subset of `M`, then for every `p : U` the differential of
the inclusion `Subtype.val : U → M` at `p` is an isomorphism of tangent spaces. -/
theorem mfderiv_open_subset_inclusion_isInvertible (U : TopologicalSpace.Opens M) (p : U) :
    (mfderiv I I (Subtype.val : U → M) p).IsInvertible := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have hsymm : ContMDiffOn I I 1 e.symm (U : Set M) := by
    intro x hx
    have hcomp : ContMDiffWithinAt I I 1 (Subtype.val ∘ e.symm) (U : Set M) x := by
      refine contMDiffWithinAt_id.congr_of_mem ?_ hx
      intro y hy
      simpa [e] using e.right_inv (by simpa [e] using hy)
    have hiff :
        ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) (Subtype.val ∘ e.symm)
            (U : Set M) x ↔
          ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) e.symm (U : Set M) x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff e.symm (U : Set M) x
    simpa [ContMDiffWithinAt] using
      hiff.mp (by simpa [ContMDiffWithinAt] using hcomp)
  let Φ : PartialDiffeomorph I I U M 1 := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      simpa [e] using
        ((contMDiff_subtype_val : ContMDiff I I 1 (Subtype.val : U → M)).contMDiffOn :
          ContMDiffOn I I 1 (Subtype.val : U → M) Set.univ)
    contMDiffOn_invFun := by
      simpa [e] using hsymm }
  have hp : p ∈ Φ.source := by
    simp [Φ, e]
  have hlocal : IsLocalDiffeomorphAt I I 1 (Φ : U → M) p := by
    exact ⟨Φ, hp, fun x _ ↦ rfl⟩
  have hinv : (mfderiv I I (Φ : U → M) p).IsInvertible := by
    rw [← hlocal.mfderivToContinuousLinearEquiv_coe one_ne_zero]
    exact ContinuousLinearMap.isInvertible_equiv
  simpa [Φ, e] using hinv

import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Exercise_4_10
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Definition_4_25_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_25.Theorem_4_26
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Definition_4_26_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uM'

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']

namespace IsLocalDiffeomorph

/-- Exercise 4.37: every continuous local section of a smooth local diffeomorphism is a smooth
local section on its open domain. -/
theorem isSmoothLocalSection {π : M → M'} (hπ : IsLocalDiffeomorph I I' ∞ π)
    {U : TopologicalSpace.Opens M'} {σ : C(U, M)}
    (hσ : (⟨π, hπ.isLocalHomeomorph.continuous⟩ : C(M, M')).IsLocalSection U σ) :
    Manifold.IsSmoothLocalSection I I' π U σ := by
  refine ⟨?_, hσ.apply_eq⟩
  have hcomp : π ∘ σ = Subtype.val := by
    funext x
    exact hσ.apply_eq x
  refine (smooth_iff_comp_left_of_isLocalDiffeomorph hπ σ.continuous).mpr ?_
  simpa [hcomp] using
    (contMDiff_subtype_val : ContMDiff I' I' ∞ (Subtype.val : U → M'))

/-- Exercise 4.37: bridge form on a raw open subset. Every continuous local section of a smooth
local diffeomorphism is smooth on its open domain. -/
theorem localSection_contMDiffOn {π : M → M'} (hπ : IsLocalDiffeomorph I I' ∞ π) {U : Set M'}
    (hU : IsOpen U) {σ : M' → M} (hσ : ContinuousOn σ U) (hsec : Set.RightInvOn σ π U) :
    ContMDiffOn I' I ∞ σ U := by
  let U' : TopologicalSpace.Opens M' := ⟨U, hU⟩
  let σ' : C(U', M) := ⟨U.restrict σ, hσ.restrict⟩
  have hσ' : (⟨π, hπ.isLocalHomeomorph.continuous⟩ : C(M, M')).IsLocalSection U' σ' := by
    intro x
    exact hsec x.2
  have hsmooth : Manifold.IsSmoothLocalSection I I' π U' σ' := hπ.isSmoothLocalSection hσ'
  intro x hx
  have hsub : ContMDiffAt I' I ∞ (fun y : U' ↦ σ y) ⟨x, hx⟩ := by
    simpa [σ'] using hsmooth.1 ⟨x, hx⟩
  exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt

end IsLocalDiffeomorph

namespace Manifold.IsSmoothCoveringMap

/-- Exercise 4.37: every continuous local section of a smooth covering map is a smooth local
section on its open domain. -/
theorem isSmoothLocalSection {π : M → M'} (hπ : Manifold.IsSmoothCoveringMap I I' π)
    {U : TopologicalSpace.Opens M'} {σ : C(U, M)}
    (hσ : (⟨π, hπ.isCoveringMap.continuous⟩ : C(M, M')).IsLocalSection U σ) :
    Manifold.IsSmoothLocalSection I I' π U σ :=
  hπ.isLocalDiffeomorph.isSmoothLocalSection hσ

/-- Exercise 4.37: bridge form on a raw open subset. Every continuous local section of a smooth
covering map is smooth on its open domain. -/
theorem localSection_contMDiffOn {π : M → M'} (hπ : Manifold.IsSmoothCoveringMap I I' π)
    {U : Set M'} (hU : IsOpen U) {σ : M' → M} (hσ : ContinuousOn σ U)
    (hsec : Set.RightInvOn σ π U) : ContMDiffOn I' I ∞ σ U :=
  hπ.isLocalDiffeomorph.localSection_contMDiffOn hU hσ hsec

end Manifold.IsSmoothCoveringMap

end

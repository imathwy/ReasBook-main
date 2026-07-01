import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_14_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) (v : D ⥤ C)

/- Domain-style sampling for Lemma 7.22.4:
- primary domain: adjunctions between Grothendieck sites and the continuity/cocontinuity owner
  abstractions;
- sampled owner API:
  `Functor.IsContinuous`,
  `Functor.IsCocontinuous`,
  `IsMorphismOfSites`,
  `Adjunction.isCocontinuous_iff_coverPreserving`,
  `RepresentablyFlat.of_isRightAdjoint`,
  `isMorphismOfSites_of_isContinuous_representablyFlat`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma for a continuous right adjoint `v`;
  `core/canonical`: the owner predicates `Functor.IsContinuous`, `Functor.IsCocontinuous`, and
    `IsMorphismOfSites`;
  `bridge/view`: the adjunction equivalence
    `Adjunction.isCocontinuous_iff_coverPreserving`.

Primitive data are the adjunction `u ⊣ v` and continuity of the right adjoint `v`. The
cover-preserving owner on `v` and the representable flatness of `v` are derived API: the former
is used only internally to recover cocontinuity of `u`, while the latter, together with
continuity, yields that `v` defines a morphism of sites.
-/
/-- Lemma 7.22.4: if the right adjoint `v : (\mathcal D, K) ⥤ (\mathcal C, J)` is continuous,
then its left adjoint `u : (\mathcal C, J) ⥤ (\mathcal D, K)` is cocontinuous. This is the
source-facing owner needed to apply Lemmas `7.22.1` and `7.22.2`. -/
theorem leftAdjoint_isCocontinuous_of_continuous_rightAdjoint
    (adj : u ⊣ v) [v.IsContinuous K J] : u.IsCocontinuous J K := by
  have hcover : CoverPreserving K J v := by
    sorry
  exact (Adjunction.isCocontinuous_iff_coverPreserving J K adj).2 hcover

/-- A continuous right adjoint defines the morphism of sites occurring in Lemma `7.22.4`. -/
theorem rightAdjoint_isMorphismOfSites_of_continuous
    (adj : u ⊣ v) [v.IsContinuous K J] : IsMorphismOfSites K J v := by
  let _ : v.IsRightAdjoint := Adjunction.isRightAdjoint adj
  let _ : RepresentablyFlat v := inferInstance
  exact isMorphismOfSites_of_isContinuous_representablyFlat K J v

/- Owner recall: this is exactly the canonical adjunction equivalence between cocontinuity of the
left adjoint and cover preservation of the right adjoint. -/
recall Adjunction.isCocontinuous_iff_coverPreserving

end CategoryTheory

import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small
import stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Lemma 18.32.5:
- primary domain: categorical smallness of invertible `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `ObjectProperty.EssentiallySmall`,
  `ObjectProperty.EssentiallySmall.exists_small`,
  `AlgebraicGeometry.RingedSpace.exists_set_of_invertible_module_representatives`;
- best owner abstraction:
  the object property `(IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))`;
- primitive data:
  only the invertibility predicate on objects of `ringedSiteModuleCategory J 𝒪`;
- derived API:
  essential smallness of that owner property and the source-facing representative set obtained
  from the skeleton of a small full subcategory produced by the canonical `exists_small` API.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claim that invertible modules admit a set of
  representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.EssentiallySmall
    ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)))`;
- `bridge/view`: the internal small object property whose iso-closure is the invertible-module
  owner property, and the skeleton-based representative set extracted from it.
-/

/-- Invertible modules on a ringed site are closed under isomorphisms. -/
instance isInvertible_isClosedUnderIsomorphisms
    {𝒪 : Sheaf J CommRingCat.{max u v}} :
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] →
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)) := by
  sorry

section

variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]

-- Proof sketch: invertible modules are produced from set-sized local free rank-one data and
-- gluing data over coverings, so the owner object property `IsInvertible` is essentially small.
/-- Core/canonical companion to Lemma 18.32.5: invertible `\mathcal O`-modules on a ringed site
form an essentially small object property. -/
instance invertibleModuleProperty_essentiallySmall
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ObjectProperty.EssentiallySmall.{max u v}
      ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪))) := by
  sorry

-- Proof sketch: apply the canonical `ObjectProperty.EssentiallySmall.exists_small` API to the
-- invertible-module owner property to get a small full subcategory whose iso-closure recovers it,
-- then choose one object from each isomorphism class via the skeleton of that small full
-- subcategory.
omit [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Lemma 18.32.5: on a ringed site `(\mathcal C, \mathcal O)`, there is a set of representatives
for the isomorphism classes of invertible `\mathcal O`-modules. Equivalently, every invertible
module is isomorphic to a unique chosen representative. -/
theorem exists_set_of_invertible_module_representatives
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [MonoidalCategory (ringedSiteModuleCategory J 𝒪)] :
    ∃ S : Set (ringedSiteModuleCategory J 𝒪),
      ∀ (ℒ : ringedSiteModuleCategory J 𝒪) [IsInvertible ℒ],
        ∃! 𝒩 : ringedSiteModuleCategory J 𝒪, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℒ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{max u v}
      ((IsInvertible : ObjectProperty (ringedSiteModuleCategory J 𝒪)))
  let F : Skeleton P.FullSubcategory ⥤ ringedSiteModuleCategory J 𝒪 :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set (ringedSiteModuleCategory J 𝒪) := Set.range F.obj
  refine ⟨S, ?_⟩
  intro ℒ hℒ'
  letI : IsInvertible ℒ := hℒ'
  have hℒ : P.isoClosure ℒ := by
    rw [← hP]
    infer_instance
  rw [ObjectProperty.prop_isoClosure_iff] at hℒ
  rcases hℒ with ⟨M, hM, ⟨e⟩⟩
  let Y : P.FullSubcategory := ⟨M, hM⟩
  refine ⟨F.obj (toSkeleton Y), ?_, ?_⟩
  · constructor
    · exact ⟨toSkeleton Y, rfl⟩
    · exact ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)) ≪≫ e.symm⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨⟨q, rfl⟩, ⟨e'⟩⟩
    have hq : q = toSkeleton Y := by
      rw [← toSkeleton_fromSkeleton_obj q]
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk (e' ≪≫ e)⟩
    simpa using congrArg F.obj hq

end

end SheafOfModules.RingedSite

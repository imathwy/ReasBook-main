import Mathlib
import stacks_project.Chap06.Extension_by_zero_by_the_initial_object
import stacks_project.Chap06.Lemma_6_31_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe v u

/-
Domain-style sampling for Lemma 6.31.11:
- primary domain: extension by the initial object for sheaves of algebraic structures along an
  open immersion;
- sampled owner API:
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem`,
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`;
- owner abstraction: the Chapter 6 owner is the open-subset extension-by-initial-object adjunction
  and its stalk description, not a new local wrapper;
- primitive data: the open subset `U`, the sheaf `𝒢`, and the canonical map `initial.to` on the
  stalks;
- derived API: the fully faithful instance and the essential-image criterion.

Source/core/bridge triage:
- `source-facing`: the Stacks-project statements that `j_!` is fully faithful and that its
  essential image is detected by initial stalks outside `U`;
- `core/canonical`: `OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction` together with
  the owner-side stalk theorem outside `U`;
- `bridge/view`: this file’s algebraic-structure specialization of those owner declarations.

The public API here should therefore keep only the source-facing fully-faithful and essential-image
statements, while reusing the owner adjunction and stalk theorem directly rather than keeping a
parallel local stalk-initial wrapper.
-/

section

variable {X : TopCat.{v}}

variable {C : Type u} [Category.{v} C] [HasInitial C] [HasColimits C] [HasLimits C]
variable {FC : C → C → Type v} {CC : C → Type v}
variable [hFunLike : ∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [hConcrete : ConcreteCategory.{v} C FC]
variable [hPreservesLimits : PreservesLimits (CategoryTheory.forget C)]
variable [hPreservesFilteredColimits : PreservesFilteredColimits (CategoryTheory.forget C)]
variable [hReflectsIsomorphisms : (CategoryTheory.forget C).ReflectsIsomorphisms]
variable [hWeakSheafify : CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

include FC CC hFunLike hConcrete hPreservesLimits hPreservesFilteredColimits
  hReflectsIsomorphisms

-- Proof sketch: the restriction functor to the open subspace is the sheaf pushforward along the
-- inclusion-of-opens functor, and `j_!` is its left adjoint. As in the set-valued case, the unit
-- is an isomorphism because on opens lying in `U` the construction agrees with the original sheaf.
/-- Lemma 6.31.11 (1): for a type of algebraic structures with an initial object, extension by the
initial object along the inclusion `j : U ↪ X` is a fully faithful functor on sheaves. -/
instance openSubsetSheafExtensionByInitialObject_fullyFaithful
    (U : Opens X) :
    (((j! U) :
      (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  letI : IsIso h.unit := by
    change IsIso
      ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom)
    infer_instance
  simpa using h.fullyFaithfulLOfIsIsoUnit

-- Proof sketch: if a sheaf is of the form `j_! ℱ`, then its stalks outside `U` are initial by the
-- extension-by-initial-object construction. Conversely, if the stalks of `𝒢` outside `U` are
-- initial, then the counit map `j_! j^{-1} 𝒢 ⟶ 𝒢` is an isomorphism on every stalk, hence an
-- isomorphism of sheaves, which places `𝒢` in the essential image of `j_!`.
/-- Lemma 6.31.11 (2): a sheaf of algebraic structures on `X` lies in the essential image of
extension by the initial object from `U` if and only if, at every point of `X \ U`, the canonical
map from the initial object of `C` to the stalk is an isomorphism. -/
theorem openSubsetSheafExtensionByInitialObject_essImage_iff_isIso_initial_to_stalk_of_not_mem
    (U : Opens X) (𝒢 : X.Sheaf C) :
    (j! U).essImage 𝒢 ↔
      ∀ x : X, x ∉ (U : Set X) →
        IsIso (initial.to (𝒢.presheaf.stalk x)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let hFF :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).FullyFaithful :=
    openSubsetSheafExtensionByInitialObject_fullyFaithful U
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Full :=
    hFF.full
  letI :
      (((j! U) :
        (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C)).Faithful :=
    hFF.faithful
  have hess : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢 := by
    simpa using
      (h.isIso_counit_app_iff_mem_essImage : IsIso (h.counit.app 𝒢) ↔ (j! U).essImage 𝒢)
  constructor
  · intro h𝒢 x hx
    letI : IsIso (h.counit.app 𝒢) := hess.mpr h𝒢
    have hε : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := by
      infer_instance
    letI : IsIso ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢)) := hε
    have hMap :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      Functor.map_isIso (TopCat.Presheaf.stalkFunctor C x)
        ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))
    letI :
        IsIso
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) :=
      hMap
    have hSource :
        IsInitial
          (((j! U).obj
              ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
        ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
    have hTarget : IsInitial (𝒢.presheaf.stalk x) :=
      IsInitial.ofIso hSource
        (@asIso _ _ _ _
          ((TopCat.Presheaf.stalkFunctor C x).map
            ((TopCat.Sheaf.forget C X).map (h.counit.app 𝒢))) hMap)
    exact isIso_of_isInitial initialIsInitial hTarget (initial.to (𝒢.presheaf.stalk x))
  · intro h𝒢
    let ε := h.counit.app 𝒢
    have : IsIso ε := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      by_cases hx : x ∈ (U : Set X)
      · let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
        let e :=
          (show (((j! U).obj
                ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) ≅
              ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢).presheaf.stalk xU
            from by
            simpa [hx] using
              OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription U
                ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) x)
        have heq :
            ((TopCat.Presheaf.stalkFunctor C x).map ε.hom) ≫
                (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom =
              e.hom := by
          sorry
        have hComp :
            IsIso
              (((TopCat.Presheaf.stalkFunctor C x).map ε.hom) ≫
                (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
          rw [heq]
          infer_instance
        have :
            IsIso
              ((((TopCat.Presheaf.stalkFunctor C x).map ε.hom) ≫
                  (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) ≫
                inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) 𝒢 xU).hom) := by
          exact inferInstance
        simpa [Category.assoc] using this
      · let hSource :
            IsInitial
              (((j! U).obj
                  ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢)).presheaf.stalk x) :=
          OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem U
            ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj 𝒢) hx
        letI : IsIso (initial.to (𝒢.presheaf.stalk x)) := h𝒢 x hx
        let hTarget : IsInitial (𝒢.presheaf.stalk x) :=
          IsInitial.ofIso initialIsInitial (asIso (initial.to (𝒢.presheaf.stalk x)))
        exact isIso_of_isInitial hSource hTarget ((TopCat.Presheaf.stalkFunctor C x).map ε.hom)
    exact hess.mp this

end

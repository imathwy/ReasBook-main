import StacksProject_2024.stacks_project.Chap21.Lemma_21_43_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty

universe u v w w'

namespace CategoryTheory.ModulesOnCategory

section

variable {C : Type u}
variable {D : C → Type w} [∀ U : C, Category (D U)]
variable {Dτ : C → Type w'} [∀ U : C, Category (Dτ U)]
variable {DU : C → Type w} [∀ U : C, Category (DU U)]

variable (QC : ∀ U : C, ObjectProperty (D U))
variable (RGamma : ∀ U : C, D U ⥤ DU U)
variable (Lf : ∀ U : C, DU U ⥤ D U)
variable (sectionsAdj : ∀ U : C, Lf U ⊣ RGamma U)
variable (sectionsCounitProperty :
  ∀ U : C, QC U ≤ counitIsomorphismProperty (Lf U) (RGamma U) (sectionsAdj U))
variable (epsilonPullback : ∀ U : C, D U ⥤ Dτ U)
variable (rEpsilonPushforward : ∀ U : C, Dτ U ⥤ D U)
variable (epsilonAdj : ∀ U : C, epsilonPullback U ⊣ rEpsilonPushforward U)
variable (RGammaTau : ∀ U : C, Dτ U ⥤ DU U)
variable (leray : ∀ U : C, RGammaTau U ≅ rEpsilonPushforward U ⋙ RGamma U)

/-
Domain-style sampling for Lemma 21.43.13:
- primary domain: Hom-set equivalences built by composing adjunction equivalences with the Chapter
  21 quasi-coherent sections equivalence and transport along a comparison isomorphism;
- sampled owner declarations:
  `Adjunction.homEquiv`,
  `CategoryTheory.ModulesOnCategory.sections_homEquiv`,
  `Iso.homCongr`,
  `Equiv.trans`;
- best owner abstraction:
  `source-facing`: the local Hom equivalence of Lemma 21.43.13;
  `core/canonical`: the upstream counit-isomorphism bridge `sections_homEquiv`;
  `bridge/view`: `Adjunction.homEquiv`, `Iso.homCongr`, and their composite with the Leray
    identification `RGammaTau U ≅ rEpsilonPushforward U ⋙ RGamma U`.
- primitive vs. derived split:
  primitive data: the two adjunctions, the quasi-coherent full subcategory objects `K`, the target
  object `M`, the canonical counit-isomorphism property inclusion for quasi-coherent objects, and
  the Leray
    isomorphism;
  derived API: the resulting composite Hom-set equivalence below.

This file therefore stays at the `bridge/view` layer and keeps only the composite equivalence
itself, using the canonical counit-isomorphism bridge from Lemma `21.43.5` rather than replacing
that bridge by another local wrapper specialized to `QC`.
-/

/-- Lemma 21.43.13: with the notation and assumptions of Lemma `21.43.12`, if `K` is
quasi-coherent and `M` is arbitrary, then for every object `U : C` the local adjunction
`epsilonPullback U ⊣ rEpsilonPushforward U`, the quasi-coherent sections comparison from
Lemma `21.43.5`, and the Leray isomorphism `leray U` combine to give an equivalence
`((epsilonPullback U).obj K.obj ⟶ M) ≃ ((RGamma U).obj K.obj ⟶ (RGammaTau U).obj M)`. -/
@[stacks 0H0T]
noncomputable abbrev epsilonPullback_homEquiv_sections
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U) :
    ((epsilonPullback U).obj K.obj ⟶ M) ≃
      ((RGamma U).obj K.obj ⟶ (RGammaTau U).obj M) :=
    ((epsilonAdj U).homEquiv K.obj M).trans
    ((sections_homEquivOfFullSubcategory
        (RGamma U) (Lf U) (sectionsAdj U) (QC U) (sectionsCounitProperty U) K
        ((rEpsilonPushforward U).obj M)).trans
      (Iso.homCongr (Iso.refl ((RGamma U).obj K.obj)) ((leray U).app M).symm))

local notation "epsilonPullbackHomEquivSections" =>
  epsilonPullback_homEquiv_sections QC RGamma Lf sectionsAdj sectionsCounitProperty
    epsilonPullback rEpsilonPushforward epsilonAdj RGammaTau leray

/-- The forward map of `epsilonPullback_homEquiv_sections` is obtained by applying the local
adjunction bijection `ε^* ⊣ Rε_*`, then the quasi-coherent sections equivalence of
Lemma `21.43.5`, and finally transporting along the Leray comparison isomorphism. -/
@[simp] theorem epsilonPullback_homEquiv_sections_apply
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    (f : (epsilonPullback U).obj K.obj ⟶ M) :
    epsilonPullbackHomEquivSections U K M f =
      (sectionsAdj U).homEquiv ((RGamma U).obj K.obj) ((rEpsilonPushforward U).obj M)
          ((sectionsAdj U).counit.app K.obj ≫ ((epsilonAdj U).homEquiv K.obj M f)) ≫
        ((leray U).app M).inv := by
  simp [epsilonPullback_homEquiv_sections]

/-- The inverse map of `epsilonPullback_homEquiv_sections` first transports a morphism
`(RGamma U).obj K.obj ⟶ (RGammaTau U).obj M` across the Leray comparison, then applies the
inverse of the quasi-coherent sections equivalence from Lemma `21.43.5`, and finally uses the
inverse adjunction bijection for `ε^* ⊣ Rε_*`. -/
@[simp] theorem epsilonPullback_homEquiv_sections_symm_apply
    (U : C)
    (K : (QC U).FullSubcategory)
    (M : Dτ U)
    (g : (RGamma U).obj K.obj ⟶ (RGammaTau U).obj M) :
    (epsilonPullbackHomEquivSections U K M).symm g =
      ((epsilonAdj U).homEquiv K.obj M).symm
        ((sections_homEquivOfFullSubcategory
            (RGamma U) (Lf U) (sectionsAdj U) (QC U) (sectionsCounitProperty U) K
            ((rEpsilonPushforward U).obj M)).symm
          (g ≫ ((leray U).app M).hom)) := by
  simp [epsilonPullback_homEquiv_sections, sections_homEquivOfFullSubcategory]

end

end CategoryTheory.ModulesOnCategory

import StacksProject_2024.stacks_project.Chap07.LocalizationProjection

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite CategoryOfElements
open CategoryTheory.OverPresheafAux

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type v))

noncomputable section

/- Domain-style sampling for Lemma 7.30.3:
- primary domain: localization of a sheaf topos at an object, presented by the site on the
  category of elements of a set-valued sheaf;
- sampled owner declarations:
  `localizationProjection`,
  `localizationTopology`,
  `CategoryOfElements.costructuredArrowYonedaEquivalence`,
  `overEquivPresheafCostructuredArrow`,
  `forgetAdjToOver`,
  `Over.forgetAdjStar`;
- best owner abstraction: the source-facing localization projection/topology and their
  continuity/cocontinuity instances are reusable support owners imported from
  `Chap07.LocalizationProjection`; this file then builds the slice-topos equivalence
  `sheafCategoryOfElementsEquivOver ℱ` and the inverse-image comparison with `Over.star ℱ`;
- primitive data: only the sheaf `ℱ`;
- derived API: `sheafCategoryOfElementsEquivOver ℱ` and the comparison between the induced inverse
  image and `Over.star ℱ`.

Source/core/bridge triage:
- `source-facing`: `sheafCategoryOfElementsEquivOver ℱ`;
- `core/canonical`: the imported localization owners `localizationProjection`,
  `localizationTopology`, together with the costructured-arrow/presheaf-over owners
  `CategoryOfElements.costructuredArrowYonedaEquivalence` and
  `overEquivPresheafCostructuredArrow`, plus the slice right-adjoint owners `toOver ℱ` and
  `Over.forgetAdjStar ℱ`;
- `bridge/view`: the internal transport from sheaves on the induced topology to slice objects over
  `ℱ`, and the induced inverse-image comparison isomorphisms.
-/

local notation "Elt" => ℱ.obj.Elementsᵒᵖ
local notation "j" => localizationProjection ℱ

local notation "Jₑ" => localizationTopology ℱ

-- Proof sketch: identify the opposite of the category of elements with the corresponding
-- costructured-arrow category via Yoneda, and then use the canonical equivalence between
-- presheaves on that costructured-arrow category and presheaves over `ℱ.obj`.
private noncomputable abbrev sheafCategoryOfElementsPresheafEquivOverPresheaf :
    Eltᵒᵖ ⥤ Type v ≌ Over ℱ.obj :=
  ((costructuredArrowYonedaEquivalence ℱ.obj).op.congrLeft).trans
    (overEquivPresheafCostructuredArrow ℱ.obj).symm

private noncomputable def yonedaCollectionProjIsoToOverLeft
    (P G : Cᵒᵖ ⥤ Type v) :
    yonedaCollectionPresheaf P ((CostructuredArrow.proj yoneda P).op ⋙ G) ≅
      ((toOver P).obj G).left :=
  NatIso.ofComponents
    (fun X ↦ by
      change YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop ≅
        (G.obj X × P.obj X)
      let homX : YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop →
          G.obj X × P.obj X := fun p ↦ ⟨p.snd, p.yonedaEquivFst⟩
      let invX : G.obj X × P.obj X →
          YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop :=
        fun p ↦ YonedaCollection.mk (yonedaEquiv.symm p.2) p.1
      refine { hom := homX, inv := invX, hom_inv_id := ?_, inv_hom_id := ?_ }
      · funext p
        change invX (homX p) = p
        let q : YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop :=
          invX (homX p)
        have h : q.fst = p.fst := by
          simp [q, homX, invX, YonedaCollection.yonedaEquivFst_eq]
        refine YonedaCollection.ext h ?_
        simp [homX, invX]
      · funext p
        change homX (invX p) = p
        rcases p with ⟨g, s⟩
        apply Prod.ext
        · simp [homX, invX]
        · simp [homX, invX, YonedaCollection.yonedaEquivFst_eq])
    (by
      intro X Y f
      ext p
      apply Prod.ext
      · simp
      · simp [YonedaCollection.map₂_yonedaEquivFst])

private instance presheafIsSheaf_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (Presheaf.IsSheaf J : ObjectProperty (Cᵒᵖ ⥤ Type v)) where
  of_iso e hP := (Presheaf.isSheaf_of_iso_iff e).1 hP

private abbrev overPresheafHasSheafDomain : ObjectProperty (Over ℱ.obj) :=
  ObjectProperty.inverseImage (Presheaf.IsSheaf J) (Over.forget ℱ.obj)

private noncomputable def overPresheafHasSheafDomainEquivOver :
    (overPresheafHasSheafDomain ℱ).FullSubcategory ≌ Over ℱ where
  functor :=
    { obj := fun T ↦
        Over.mk (⟨T.obj.hom⟩ : ⟨T.obj.left, show Presheaf.IsSheaf J T.obj.left from T.property⟩ ⟶ ℱ)
      map := fun f ↦ Over.homMk ⟨f.hom.left⟩ (Sheaf.hom_ext f.hom.w) }
  inverse :=
    { obj := fun η ↦ ⟨Over.mk η.hom.hom, show overPresheafHasSheafDomain ℱ (Over.mk η.hom.hom) from η.left.property⟩
      map := fun f ↦
        ObjectProperty.homMk
          (Over.homMk f.left.hom (congrArg (fun g ↦ g.hom) (Over.w f))) }
  unitIso := NatIso.ofComponents
    (fun T ↦
      ObjectProperty.isoMk (overPresheafHasSheafDomain ℱ)
        (Over.isoMk (Iso.refl _) (by simp)))
    (by
      intro T T' f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      simp)
  counitIso := NatIso.ofComponents
    (fun η ↦ Over.isoMk (Iso.refl _) (by ext X x; rfl))
    (by
      intro η η' f
      apply Over.OverMorphism.ext
      apply Sheaf.hom_ext
      rfl)
  functor_unitIso_comp T := by
    apply Over.OverMorphism.ext
    apply Sheaf.hom_ext
    rfl

-- Proof sketch: under the canonical equivalence between the opposite category of elements of `ℱ`
-- and the Yoneda costructured-arrow category, the inverse object is the usual restricted-Yoneda
-- fiber construction attached to `T.hom`; hence the sheaf condition is exactly the one coming from
-- the sheaf domain `T.left`.
private theorem sheafCategoryOfElementsInverseObj_isSheaf
    (T : Over ℱ.obj)
    (hT : Presheaf.IsSheaf J T.left) :
    Presheaf.IsSheaf Jₑ
      ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).inverse.obj T) := by
  sorry

private theorem sheafCategoryOfElementsFunctorObj_isSheaf
    (P : Eltᵒᵖ ⥤ Type v)
    (hP : Presheaf.IsSheaf Jₑ P) :
    Presheaf.IsSheaf J
      ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P).left := by
  sorry

private theorem sheafCategoryOfElementsPresheafEquivOverPresheaf_obj_isSheaf_iff
    (P : Eltᵒᵖ ⥤ Type v) :
    Presheaf.IsSheaf J
        ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P).left ↔
      Presheaf.IsSheaf Jₑ P := by
  constructor
  · intro hP
    let e := (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).unitIso.app P
    exact
      (Presheaf.isSheaf_of_iso_iff e).2
        (sheafCategoryOfElementsInverseObj_isSheaf ℱ
          ((sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor.obj P) hP)
  · intro hP
    exact sheafCategoryOfElementsFunctorObj_isSheaf ℱ P hP

private theorem sheafCategoryOfElementsPresheafEquivOverPresheaf_inverseImage :
    (overPresheafHasSheafDomain ℱ).inverseImage
        (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ).functor =
      Presheaf.IsSheaf Jₑ := by
  ext P
  simpa [overPresheafHasSheafDomain, ObjectProperty.prop_inverseImage_iff] using
    sheafCategoryOfElementsPresheafEquivOverPresheaf_obj_isSheaf_iff ℱ P

/-- Lemma 7.30.3 (3): there is an equivalence between sheaves on the site of elements of `ℱ` and
objects of `Sh(C, J)` over `ℱ`. -/
noncomputable def sheafCategoryOfElementsEquivOver :
    Sheaf Jₑ (Type v) ≌ Over ℱ :=
  (Equivalence.congrFullSubcategory
      (sheafCategoryOfElementsPresheafEquivOverPresheaf ℱ)
      (sheafCategoryOfElementsPresheafEquivOverPresheaf_inverseImage ℱ)).trans
    (overPresheafHasSheafDomainEquivOver ℱ)

-- Internal comparison with the abstract slice inverse-image `toOver ℱ`; the public compatibility
-- statement below composes this with the canonical identification `toOver ℱ ≅ Over.star ℱ`.
private noncomputable def sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoToOver :
    ((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
        (sheafCategoryOfElementsEquivOver ℱ).functor) ≅
      toOver ℱ :=
  NatIso.ofComponents
    (fun G ↦ by
      simpa [Functor.sheafPushforwardContinuous, ObjectProperty.lift,
          sheafCategoryOfElementsEquivOver, overPresheafHasSheafDomainEquivOver,
          sheafCategoryOfElementsPresheafEquivOverPresheaf] using
        (by
          refine Over.isoMk
            (ObjectProperty.isoMk (Presheaf.IsSheaf J)
              (by
                simpa [toOver] using
                  (((yonedaCollectionFunctor ℱ.obj).mapIso
                      (Functor.isoWhiskerRight
                        (Iso.refl ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj)) ≪≫
                    yonedaCollectionProjIsoToOverLeft ℱ.obj G.obj)))
            (by
              apply Sheaf.hom_ext
              ext X x
              change SemiCartesianMonoidalCategory.snd (G.obj.obj X) (ℱ.obj.obj X)
                ((YonedaCollection.map₁
                      (Functor.whiskerRight
                        (𝟙 ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj) x).snd,
                    (YonedaCollection.map₁
                      (Functor.whiskerRight
                        (𝟙 ((CostructuredArrow.proj yoneda ℱ.obj).op))
                        G.obj) x).yonedaEquivFst) =
                ((yonedaCollectionPresheafToA
                    ((CostructuredArrow.proj yoneda ℱ.obj).op ⋙ G.obj)).app
                  X) x
              simp [yonedaCollectionPresheafToA, SemiCartesianMonoidalCategory.snd])))
    (by
      sorry)

/-- Lemma 7.30.3 (compatibility): under `sheafCategoryOfElementsEquivOver`, the sheaf functor
induced by the projection from the category of elements of `ℱ` is canonically isomorphic to the
localization inverse-image functor `Over.star ℱ`. Equivalently, this equivalence identifies the
morphism of topoi induced by `π_ℱ` with the localization morphism at `ℱ`. -/
noncomputable def sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar :
    ((localizationProjection ℱ).sheafPushforwardContinuous (Type v) Jₑ J ⋙
        (sheafCategoryOfElementsEquivOver ℱ).functor) ≅
      Over.star ℱ :=
  sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoToOver ℱ ≪≫
    ((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm

-- Proof sketch: the comparison is the application of the natural isomorphism
-- `sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ` to `G`.
/-- The comparison morphism from the image of `G` under
`(sheafCategoryOfElementsEquivOver ℱ).functor` to the slice inverse image `Over.star ℱ` is an
isomorphism. -/
theorem sheafCategoryOfElementsEquivOver_functor_obj_inverseImage_hom_isIso
    (G : Sheaf J (Type v)) :
    IsIso ((sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ).hom.app G) :=
  sorry

end

end CategoryTheory

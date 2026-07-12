import Mathlib
import StacksProject_2024.Chap07.Definition_7_29_2
import StacksProject_2024.Chap07.Lemma_7_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped CategoryTheory.GrothendieckTopology.SheafifiedRepresentable

noncomputable section

universe w u v u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace ObjectProperty

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable (P : ObjectProperty (Sheaf J (Type (max u v))))

/- Domain-style sampling for Lemma 7.29.4:
- primary domain: surjective-cover pretopologies on full subcategories of sheaf categories and the
  resulting dense-subsite comparison;
- sampled owner declarations:
  `Presieve.ofArrows`,
  `Sheaf.IsLocallySurjective`,
  `Sheaf.IsQuasiCompactObject.finite_subcoproduct`,
  `Functor.IsDenseSubsite`;
- best owner abstraction: the source-facing covering predicate should be built from a small family
  presentation `Presieve.ofArrows Y π` of the presieve together with the ambient owner
  `Sheaf.IsLocallySurjective` on the canonical coproduct map `Sigma.desc (fun i ↦ (π i).hom)`;
  the later comparison statements are then organized around the canonical dense-subsite owner
  `Functor.IsDenseSubsite`;
- primitive data: the full subcategory `P.FullSubcategory`, a small family of morphisms
  `π : ∀ i, Y i ⟶ X`, and its induced coproduct map in the ambient sheaf category;
- derived API: the induced pretopology/topology, the dense-subsite structure on
  `sheafSubcategoryRepresentableFunctor P hP`, and the inverse-image/direct-image identifications
  with representables.

Source/core/bridge triage:
- `source-facing`: the surjective covering condition on presieves and the six clauses of
  Lemma 7.29.4;
- `core/canonical`: `Presieve.ofArrows`, `Sheaf.IsLocallySurjective`,
  `Functor.IsDenseSubsite`, and `J.uliftSheafifiedRepresentableHomEquiv`;
- `bridge/view`: the small-family presentation of a presieve and the later comparison between
  inverse image of Yoneda and the underlying ambient sheaf.

The public coverage predicate should therefore expose only the locally surjective coproduct-map
condition for a family presenting the presieve, with coproduct existence supplied internally by
the ambient sheaf category rather than packaged as extra data.
-/

instance hasCoproductOfFullSubcategoryFamily
    {ι : Type (max u v)} (Y : ι → P.FullSubcategory) :
    HasCoproduct (fun i ↦ (Y i).obj) := by
  let _ : HasColimitsOfShape (Discrete ι) (Type (max u v)) := inferInstance
  let _ : HasColimitsOfShape (Discrete ι) (Sheaf J (Type (max u v))) :=
    Sheaf.instHasColimitsOfShape
  infer_instance

/-- A presieve on the full subcategory is covering when it admits a small family presentation whose
associated coproduct map is locally surjective as a morphism of ambient sheaves. -/
def sheafSubcategorySurjectiveCovering
    {X : P.FullSubcategory} (R : Presieve X) : Prop :=
  ∃ (ι : Type (max u v)) (Y : ι → P.FullSubcategory) (π : ∀ i, Y i ⟶ X),
    R = Presieve.ofArrows Y π ∧
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i ↦ (π i).hom))

-- Proof sketch: present the singleton presieve by its one-arrow family; the associated coproduct
-- map is an isomorphism in the ambient sheaf category, hence locally surjective.
/-- Singleton isomorphism families are covering for the surjective coverage on the full subcategory
of sheaves. -/
theorem sheafSubcategorySurjectiveCovering_hasIsos
    {X Y : P.FullSubcategory} (f : Y ⟶ X) [IsIso f] :
    sheafSubcategorySurjectiveCovering P (Presieve.singleton f) := sorry

-- Proof sketch: choose a family presentation of `R`, pull back the ambient locally surjective
-- coproduct map along the chosen morphism in the full subcategory, and identify the resulting
-- family with a presentation of the pullback presieve.
/-- Surjective covering families in the full subcategory of sheaves are stable under pullback. -/
theorem sheafSubcategorySurjectiveCovering_pullbacks
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {X Y : P.FullSubcategory} (f : Y ⟶ X) (R : Presieve X)
    (hR : sheafSubcategorySurjectiveCovering P R) :
    sheafSubcategorySurjectiveCovering P (Presieve.pullbackArrows f R) := sorry

-- Proof sketch: choose a family presentation of `R`, compose its ambient locally surjective
-- coproduct map with the ambient locally surjective coproduct maps for the chosen presentations of
-- the refining presieves, and identify the composite with a family presentation of `R.bind Ti`.
/-- Surjective covering families in the full subcategory of sheaves are closed under refinement by
surjective coverings on each domain. -/
theorem sheafSubcategorySurjectiveCovering_transitive
    {X : P.FullSubcategory} (R : Presieve X)
    (Ti : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ X), R f → Presieve Y)
    (hR : sheafSubcategorySurjectiveCovering P R)
    (hTi : ∀ ⦃Y : P.FullSubcategory⦄ (f : Y ⟶ X) (hf : R f),
      sheafSubcategorySurjectiveCovering P (Ti f hf)) :
    sheafSubcategorySurjectiveCovering P (R.bind Ti) := sorry

/-- The pretopology on a full subcategory of `Sh(J)` whose covering families are those admitting a
small family presentation with locally surjective ambient coproduct map. -/
def sheafSubcategorySurjectivePretopology
    [P.IsClosedUnderLimitsOfShape WalkingCospan] : Pretopology P.FullSubcategory where
  coverings _ R := sheafSubcategorySurjectiveCovering P R
  has_isos := fun {_ _} f _ ↦ sheafSubcategorySurjectiveCovering_hasIsos P f
  pullbacks := fun {_ _} f R hR ↦ sheafSubcategorySurjectiveCovering_pullbacks P f R hR
  transitive := fun {_} R Ti hR hTi ↦
    sheafSubcategorySurjectiveCovering_transitive P R Ti hR hTi

/-- The canonical functor `U ↦ h_U^#` lifted from `C` to the chosen full subcategory of sheaves.
-/
noncomputable abbrev sheafSubcategoryRepresentableFunctor
    [HasWeakSheafify J (Type (max u v))]
    (hP : ∀ U : C, P (h[U]^#[J])) :
    C ⥤ P.FullSubcategory :=
  P.lift J.sheafifiedRepresentableFunctor hP

/-- Lemma 7.29.4 (1): the surjective covering families on the full subcategory of sheaves define
the Grothendieck topology on `\mathcal C'`, so `\mathcal C'` becomes a site. -/
abbrev sheafSubcategorySurjectiveTopology
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    GrothendieckTopology P.FullSubcategory :=
  (sheafSubcategorySurjectivePretopology P).toGrothendieck

-- Proof sketch: this is the defining equality of the topology abbreviation obtained from the
-- pretopology of locally surjective family presentations.
/-- The surjective topology on the full subcategory is by definition the Grothendieck topology
generated by the surjective pretopology. -/
theorem sheafSubcategorySurjectiveTopology_def
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    sheafSubcategorySurjectiveTopology P =
      (sheafSubcategorySurjectivePretopology P).toGrothendieck := sorry

/-- Lemma 7.29.4 (2): the surjective topology on the full subcategory of sheaves is subcanonical,
so representable presheaves on `\mathcal C'` are sheaves. -/
-- Proof sketch: a morphism into an ambient sheaf is determined by its restrictions along a
-- locally surjective family, and the equalizer condition is exactly Lemma 7.11.3 applied in the
-- ambient sheaf category.
instance sheafSubcategorySurjectiveTopology_subcanonical
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    (sheafSubcategorySurjectiveTopology P).Subcanonical := sorry

section

variable [HasWeakSheafify J (Type (max u v))]
variable [P.IsClosedUnderLimitsOfShape WalkingCospan]
variable (hP : ∀ U : C, P (h[U]^#[J]))

/-- Lemma 7.29.4 (3): if every sheafified representable `h_U^#` belongs to the chosen full
subcategory, then the functor `v : \mathcal C \to \mathcal C'`, `U ↦ h_U^#`, is special
cocontinuous for the surjective topology on `\mathcal C'`. -/
-- Proof sketch: continuity and cocontinuity come from the description of coverings by locally
-- surjective maps of sheaves, the local fullness and faithfulness conditions are read off from the
-- sheafification adjunction on representables, and closure under pullbacks ensures the fibre
-- product conditions stay inside the full subcategory.
instance sheafSubcategoryRepresentableFunctor_isDenseSubsite :
    (sheafSubcategoryRepresentableFunctor P hP).IsDenseSubsite
      J (sheafSubcategorySurjectiveTopology P) := sorry

/- Bridge/view recall: once
`sheafSubcategoryRepresentableFunctor_isDenseSubsite` upgrades `U ↦ h_U^#` to the chapter's
canonical owner `Functor.IsDenseSubsite`, the induced cocontinuous direct image
on sheaves of sets is an equivalence after supplying the needed pointwise right Kan extensions, by
the bridge theorem from Definition `7.29.2`. -/
#check
  Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
    (sheafSubcategoryRepresentableFunctor P hP)

private noncomputable def inverseImageYonedaObjUnderlyingIso
    (ℱ : P.FullSubcategory) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      ((sheafSubcategorySurjectiveTopology P).yoneda.obj ℱ)).obj ≅
        (P.ι.obj ℱ).obj :=
  NatIso.ofComponents
    (fun U ↦
      let e := J.uliftSheafifiedRepresentableHomEquiv (P.ι.obj ℱ) U.unop
      Equiv.toIso
        { toFun := fun α ↦ e α.hom
          invFun := fun x ↦ ObjectProperty.homMk (e.symm x)
          left_inv := fun α ↦ ObjectProperty.hom_ext P (e.symm_apply_apply α.hom)
          right_inv := e.apply_symm_apply })
    (fun {U V} f ↦ by
      ext α
      simpa using
        J.uliftSheafifiedRepresentableHomEquiv_naturality f.unop (P.ι.obj ℱ) α.hom)

/-- Lemma 7.29.4 (4): for any object `\mathcal F` of the full subcategory, the inverse image of
the representable sheaf `h_\mathcal F` on `\mathcal C'` is canonically isomorphic to the
underlying sheaf `\mathcal F` on `\mathcal C`. -/
-- Proof sketch: evaluate the inverse image of the representable sheaf of `ℱ` on `U`; this gives
-- morphisms `h_U^# ⟶ ℱ`, which the sheafification adjunction identifies with sections of the
-- underlying ambient sheaf `ℱ.obj` over `U`.
noncomputable def sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso
    (ℱ : P.FullSubcategory) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      ((sheafSubcategorySurjectiveTopology P).yoneda.obj ℱ) ≅
        P.ι.obj ℱ) :=
  { hom := homMk (inverseImageYonedaObjUnderlyingIso P hP ℱ).hom
    inv := homMk (inverseImageYonedaObjUnderlyingIso P hP ℱ).inv
    hom_inv_id := by
      apply hom_ext
      exact (inverseImageYonedaObjUnderlyingIso P hP ℱ).hom_inv_id
    inv_hom_id := by
      apply hom_ext
      exact (inverseImageYonedaObjUnderlyingIso P hP ℱ).inv_hom_id }

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to the canonical inverse
-- image comparison isomorphism above.
/-- The inverse-image comparison isomorphism for representable sheaves has the expected left
inverse identity. -/
theorem sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso_hom_inv_id
    (ℱ : P.FullSubcategory) :
    (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP ℱ).hom ≫
        (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP ℱ).inv =
      𝟙 _ := sorry

/-- Lemma 7.29.4 (5): for any `U` in `\mathcal C`, the direct image of `h_U^#` along the induced
equivalence is canonically the representable sheaf of `v(U)` in the subcanonical site
`\mathcal C'`. -/
-- Proof sketch: combine the adjunction between inverse and direct image with clause (4); then use
-- the Yoneda identification in the subcanonical topology on `\mathcal C'`.
noncomputable def sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso
    (U : C) :
    (((sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardCocontinuous
      (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)).obj
      h[U]^#[J] ≅
        (sheafSubcategorySurjectiveTopology P).yoneda.obj
          ((sheafSubcategoryRepresentableFunctor P hP).obj U)) :=
  let g := (sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardCocontinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let q := (sheafSubcategoryRepresentableFunctor P hP).sheafPushforwardContinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let _ : q.IsEquivalence := inferInstance
  let e := q.asEquivalence
  let adj := (sheafSubcategoryRepresentableFunctor P hP).sheafAdjunctionCocontinuous
    (Type (max u v)) J (sheafSubcategorySurjectiveTopology P)
  let Y := (sheafSubcategorySurjectiveTopology P).yoneda.obj
    ((sheafSubcategoryRepresentableFunctor P hP).obj U)
  let h : g ≅ e.inverse := Adjunction.rightAdjointUniq adj e.toAdjunction
  h.app (h[U]^#[J]) ≪≫
    e.inverse.mapIso
      (sheafSubcategoryRepresentableFunctor_inverseImage_yoneda_obj_iso P hP
        ((sheafSubcategoryRepresentableFunctor P hP).obj U)).symm ≪≫
    (e.unitIso.app Y).symm

-- Proof sketch: any isomorphism satisfies `hom ≫ inv = 𝟙`; apply this to the canonical direct
-- image comparison isomorphism above.
/-- The direct-image comparison isomorphism for sheafified representables has the expected left
inverse identity. -/
theorem sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso_hom_inv_id
    (U : C) :
    (sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso P hP U).hom ≫
        (sheafSubcategoryRepresentableFunctor_pushforward_sheafifiedRepresentable_iso P hP U).inv =
      𝟙 _ := sorry

end

end ObjectProperty
end CategoryTheory

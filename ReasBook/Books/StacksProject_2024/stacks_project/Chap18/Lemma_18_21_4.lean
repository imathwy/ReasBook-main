import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap18.Definition_18_8_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_21_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite CategoryOfElements
open CategoryTheory.OverPresheafAux
open RingedSite.Hom

universe u v w

noncomputable section

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ)

/- Domain-style sampling for Lemma 18.21.4:
- primary domain: relocalization of localizations of a ringed topos, with the canonical slice-topos
  comparison on the underlying topoi and the induced comparison on localized structure sheaves;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.star`,
  `Over.pullback`,
  `Over.starPullbackIsoStar`,
  `RingedSite.Hom.underlyingStructureSheaf`,
  `sheafCompose`;
- best owner abstraction: the underlying relocalization comparison is already owned by the
  canonical slice base-change isomorphism `Over.starPullbackIsoStar`, and the ringed refinement is
  the specialization of that same owner to the forgotten structure sheaf;
- primitive data: a morphism of sheaves `s : 𝒢 ⟶ ℱ`;
- derived API: the localization inverse-image functors `Over.star ℱ`, `Over.star 𝒢`, the
  pullback functor `Over.pullback s`, the underlying structure-sheaf owner
  `underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪)`, and the induced comparison on
  localized structure sheaves after forgetting ring structure.

Source/core/bridge triage:
- `source-facing`: the commutative triangle of localization morphisms of ringed topoi attached to
  `s`, including compatibility of the structure-sheaf maps;
- `core/canonical`: `Over.starPullbackIsoStar`;
- `bridge/view`: the explicit source and target functors `Over.star ℱ ⋙ Over.pullback s` and
  `Over.star 𝒢`, and the specialization of their comparison to the forgotten structure sheaf.

Primitive data and derived API separate cleanly here: the owner only needs the sheaf map `s`,
while the ringed statement is obtained by applying that owner to the underlying structure sheaf.
This file should therefore reuse `Over.starPullbackIsoStar` directly as the main entry and expose
the structure-sheaf compatibility only as its thin derived companion.
-/
/- Lemma 18.21.4: for a morphism of sheaves `s : 𝒢 ⟶ ℱ` on a ringed topos
`(\mathit{Sh}(\mathcal C), \mathcal O)`, the natural commutative triangle of localization
morphisms of the underlying topoi is the canonical relocalization comparison
`Over.star ℱ ⋙ Over.pullback s ≅ Over.star 𝒢`. This is the topos-level part of the ringed-topos
diagram, and the ringed refinement is obtained by transporting the structure sheaf along this
localization square. -/
recall Over.starPullbackIsoStar

section

variable {C : Type w} [Category.{w} C] {J : GrothendieckTopology C}

private noncomputable def overLeftIso
    {ℱ : Sheaf J (Type w)} {X Y : Over ℱ} (e : X ≅ Y) :
    X.left ≅ Y.left :=
  { hom := e.hom.left
    inv := e.inv.left
    hom_inv_id := by simpa using Over.hom_left_inv_left e
    inv_hom_id := by simpa using Over.inv_left_hom_left e }

/-- Helper for Lemma 18.21.4: the Yoneda-collection model of `toOver` has the expected underlying
sheaf on the base site. -/
private noncomputable def yonedaCollection_projection_toOver_left
    (P G : Cᵒᵖ ⥤ Type w) :
    yonedaCollectionPresheaf P ((CostructuredArrow.proj yoneda P).op ⋙ G) ≅
      ((toOver P).obj G).left :=
  NatIso.ofComponents
    (fun X ↦ by
      change YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop ≅
        (G.obj X × P.obj X)
      let homX :
          YonedaCollection ((CostructuredArrow.proj yoneda P).op ⋙ G) X.unop →
            G.obj X × P.obj X := fun p ↦ ⟨p.snd, p.yonedaEquivFst⟩
      let invX :
          G.obj X × P.obj X →
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

/-- Helper for Lemma 18.21.4: the category-of-elements equivalence sends the inverse image of a
sheaf to the same slice object as `toOver`, after forgetting the map to `ℱ`. -/
private noncomputable def sheafCategoryOfElementsEquivOver_functor_obj_left_iso_toOver_left
    (ℱ : Sheaf J (Type w)) (A : Sheaf J (Type w)) :
    ((((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
            (localizationTopology ℱ) J) ⋙
          (sheafCategoryOfElementsEquivOver ℱ).functor).obj A).left ≅
      ((toOver ℱ).obj A).left := by
  -- First identify the explicit category-of-elements model with the Yoneda-collection model of
  -- `toOver`; the remaining comparison is the concrete `YonedaCollection` iso proved above.
  simpa [sheafCategoryOfElementsEquivOver, Functor.sheafPushforwardContinuous, ObjectProperty.lift,
    toOver] using
    (ObjectProperty.isoMk (Presheaf.IsSheaf J)
      ((((yonedaCollectionFunctor ℱ.obj).mapIso
          (Functor.isoWhiskerRight
            (Iso.refl ((CostructuredArrow.proj yoneda ℱ.obj).op))
            A.obj)) ≪≫
        yonedaCollection_projection_toOver_left ℱ.obj A.obj)))

/-- Helper for Lemma 18.21.4: rewrite the public Chapter 7 comparison
`localizationProjection⁻¹ ⋙ sheafCategoryOfElementsEquivOver ≅ Over.star` so that the codomain is
the equivalence inverse applied after `Over.star`. -/
private noncomputable def localizationProjection_continuous_iso_star_whisker_inverse
    (ℱ : Sheaf J (Type w)) :
    (localizationProjection ℱ).sheafPushforwardContinuous (Type w)
        (localizationTopology ℱ) J ≅
      Over.star ℱ ⋙ (sheafCategoryOfElementsEquivOver ℱ).inverse := by
  let comparison := sheafCategoryOfElementsEquivOver ℱ
  -- Whisker the Chapter 7 slice comparison by the equivalence unit so the localized inverse image
  -- is expressed directly as `Over.star` followed by the inverse equivalence.
  exact
    (Functor.rightUnitor
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J)).symm ≪≫
      Functor.isoWhiskerLeft
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J)
        comparison.unitIso ≪≫
      Functor.associator
        ((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J)
        comparison.functor comparison.inverse ≪≫
      Functor.isoWhiskerRight
        (sheafCategoryOfElementsEquivOver_inducedMorphismInverseImageIsoStar ℱ)
        comparison.inverse

/-- Helper for Lemma 18.21.4: the public Chapter 7 comparison `toOver ℱ ≅ Over.star ℱ` gives the
same underlying sheaf on the base site after forgetting the map to `ℱ`. -/
private noncomputable def toOver_left_iso_star_left
    (ℱ : Sheaf J (Type w)) (A : Sheaf J (Type w)) :
    ((toOver ℱ).obj A).left ≅ ((Over.star ℱ).obj A).left :=
  -- Apply the public right-adjoint uniqueness comparison objectwise and then forget the slice
  -- structure to its left component.
  overLeftIso ((((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm.app A))

/-- Helper for Lemma 18.21.4: on `Type`-valued sheaves, the localized inverse image followed by
the category-of-elements equivalence has underlying sheaf `((Over.star ℱ).obj A).left`. -/
private noncomputable def localizationProjection_inverseImage_obj_iso_star_left
    (ℱ : Sheaf J (Type w)) (A : Sheaf J (Type w)) :
    ((((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
            (localizationTopology ℱ) J) ⋙
          (sheafCategoryOfElementsEquivOver ℱ).functor).obj A).left ≅
      ((Over.star ℱ).obj A).left :=
  -- First identify the slice object with the concrete `toOver` model, then move from
  -- `toOver ℱ` to the canonical localization inverse image `Over.star ℱ`.
  sheafCategoryOfElementsEquivOver_functor_obj_left_iso_toOver_left ℱ A ≪≫
    toOver_left_iso_star_left ℱ A

/-- Helper for Lemma 18.21.4: the direct image from the localization site agrees objectwise with
the left object carried by the slice-equivalence functor. -/
private noncomputable def localizationProjection_cocontinuous_obj_iso_functor_left
    (ℱ : Sheaf J (Type w)) (G : Sheaf (localizationTopology ℱ) (Type w)) :
    ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
        (localizationTopology ℱ) J).obj G ≅
      (((sheafCategoryOfElementsEquivOver ℱ).functor.obj G).left) := by
  let comparison := sheafCategoryOfElementsEquivOver ℱ
  let comparisonAdj := comparison.toAdjunction
  let sliceAdj :
      comparison.functor ⋙ Over.forget ℱ ⊣ Over.star ℱ ⋙ comparison.inverse :=
    comparisonAdj.comp (Over.forgetAdjStar ℱ)
  let localizationAdj :
      (localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J ⊣
        (localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
          (localizationTopology ℱ) J :=
    (localizationProjection ℱ).sheafAdjunctionCocontinuous
      (Type w) (localizationTopology ℱ) J
  let sliceAdj' :
      (localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J ⊣
        comparison.functor ⋙ Over.forget ℱ :=
    (sliceAdj.ofNatIsoRight
        (localizationProjection_continuous_iso_star_whisker_inverse ℱ).symm).symm
  -- Proof comment: both base-sheaf presentations are right adjoints to the same inverse-image
  -- owner `localizationProjection ℱ ⋙ sheafPushforwardContinuous`.
  simpa [Functor.comp_obj] using
    (Adjunction.rightAdjointUniq localizationAdj sliceAdj').app G

/-- Helper for Lemma 18.21.4: after forgetting ring structure, the localized structure sheaf is
the inverse image of the original underlying structure sheaf along the localization projection. -/
private noncomputable def localizationAtSheaf_underlyingStructureSheaf_iso_inverseImage
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    underlyingStructureSheaf (RingedSite.localizationAtSheaf 𝒪 ℱ) ≅
      ((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
        (localizationTopology ℱ) J).obj
        (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪)) :=
  -- The localized ringed site was defined by pulling `𝒪` back along `localizationProjection ℱ`,
  -- so forgetting ring structure turns that pullback into the corresponding set-valued inverse
  -- image.
  (Functor.pushforwardUnderlyingIso (u := localizationProjection ℱ)
      (J₁ := localizationTopology ℱ) (J₂ := J) (e := Iso.refl _)).symm

/-- Helper for Lemma 18.21.4: forgetting the localized `RingCat` direct image lands in the
corresponding `Type`-valued direct image on the underlying localized structure sheaf. -/
private noncomputable def localizationAtSheaf_forget_pushforward_obj_iso
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    (sheafCompose J (forget RingCat.{w})).obj
        (((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
            (localizationTopology ℱ) J).obj
          (RingedSite.localizationAtSheaf 𝒪 ℱ).structureSheaf) ≅
      ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
        (localizationTopology ℱ) J).obj
        (underlyingStructureSheaf (RingedSite.localizationAtSheaf 𝒪 ℱ)) := by
  let X := (RingedSite.localizationAtSheaf 𝒪 ℱ).structureSheaf
  let Xunder := underlyingStructureSheaf (RingedSite.localizationAtSheaf 𝒪 ℱ)
  let presheafIso :
      (((((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
              (localizationTopology ℱ) J).obj X).1) ⋙ forget RingCat.{w}) ≅
        ((((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
              (localizationTopology ℱ) J).obj Xunder).1) := by
    calc
      (((((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
              (localizationTopology ℱ) J).obj X).1) ⋙ forget RingCat.{w}) ≅
          (((localizationProjection ℱ).op.ran.obj X.1) ⋙ forget RingCat.{w}) :=
        (((Functor.whiskeringRight _ RingCat.{w} (Type w)).obj (forget RingCat.{w})).mapIso
          (((localizationProjection ℱ).sheafPushforwardCocontinuousCompSheafToPresheafIso
            RingCat (localizationTopology ℱ) J).app X))
      _ ≅
          ((localizationProjection ℱ).op.ran.obj (X.1 ⋙ forget RingCat.{w})) :=
        ((forget RingCat.{w}).ranCompIsoOfPreserves
          (localizationProjection ℱ).op).app X.1
      _ ≅
          ((((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
                (localizationTopology ℱ) J).obj Xunder).1) :=
        (((localizationProjection ℱ).sheafPushforwardCocontinuousCompSheafToPresheafIso
          (Type w) (localizationTopology ℱ) J).app Xunder).symm
  -- Proof comment: on presheaves, cocontinuous direct image is right Kan extension, and
  -- forgetting rings commutes with that `ran`; rebuilding the sheaf gives the desired comparison.
  simpa [Functor.comp_obj, RingedSite.Hom.underlyingStructureSheaf, ObjectProperty.lift] using
    (ObjectProperty.isoMk (Presheaf.IsSheaf J) presheafIso)

/-- Helper for Lemma 18.21.4: the forgotten target of `j_ℱ^♯` identifies directly with the left
object of the slice localization `Over.star ℱ` applied to the underlying structure sheaf. -/
private noncomputable def localizationAtSheafStructureMap_target_star_left_iso
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    (sheafCompose J (forget RingCat.{w})).obj
        (((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
            (localizationTopology ℱ) J).obj
          (RingedSite.localizationAtSheaf 𝒪 ℱ).structureSheaf) ≅
      ((Over.star ℱ).obj
        (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪))).left := by
  -- Route correction: normalize the target in the source order. First forget the `RingCat`
  -- direct image, then rewrite `𝒪_ℱ` as `j⁻¹ A`, then apply the pure `Type`-valued
  -- `j_* j⁻¹ A ≅ A_ℱ` comparison.
  let A : Sheaf J (Type w) := underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪)
  calc
    (sheafCompose J (forget RingCat.{w})).obj
        (((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
            (localizationTopology ℱ) J).obj
          (RingedSite.localizationAtSheaf 𝒪 ℱ).structureSheaf)
        ≅
      ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
        (localizationTopology ℱ) J).obj
        (underlyingStructureSheaf (RingedSite.localizationAtSheaf 𝒪 ℱ)) :=
      -- First separate the RingCat-to-Type transport from the Chapter 7 localization comparison.
      localizationAtSheaf_forget_pushforward_obj_iso 𝒪 ℱ
    _ ≅
      ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
        (localizationTopology ℱ) J).obj
        (((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J).obj A) :=
      -- Then rewrite the localized structure sheaf as the inverse image `j⁻¹ A`.
      Functor.mapIso
        ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
          (localizationTopology ℱ) J)
        (localizationAtSheaf_underlyingStructureSheaf_iso_inverseImage 𝒪 ℱ)
    _ ≅
      ((((sheafCategoryOfElementsEquivOver ℱ).functor).obj
            (((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
              (localizationTopology ℱ) J).obj A)).left) :=
      -- The pure Type-side direct-image comparison is now isolated from the forgetful transport.
      localizationProjection_cocontinuous_obj_iso_functor_left ℱ
        (((localizationProjection ℱ).sheafPushforwardContinuous (Type w)
          (localizationTopology ℱ) J).obj A)
    _ ≅ ((Over.star ℱ).obj A).left :=
      -- Finally switch from the category-of-elements equivalence back to the canonical slice
      -- owner `Over.star ℱ`.
      localizationProjection_inverseImage_obj_iso_star_left ℱ A

private noncomputable def localizationAtSheafUnderlyingStructureMapTargetIso
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    (sheafCompose J (forget RingCat.{w})).obj
        (((localizationProjection ℱ).sheafPushforwardCocontinuous RingCat
            (localizationTopology ℱ) J).obj
          (RingedSite.localizationAtSheaf 𝒪 ℱ).structureSheaf) ≅
      ((Over.star ℱ).obj
        (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪))).left :=
  localizationAtSheafStructureMap_target_star_left_iso 𝒪 ℱ

/-- The forgotten pushforward-form structure map `j_ℱ^♯` transported to the canonical slice-topos
owner `Over.star ℱ`. -/
noncomputable abbrev localizationAtSheafUnderlyingStructureMap
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪) ⟶
      ((Over.star ℱ).obj
        (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪))).left :=
  (sheafCompose J (forget RingCat.{w})).map
      (RingedSite.localizationAtSheafStructureMap 𝒪 ℱ) ≫
    (localizationAtSheafUnderlyingStructureMapTargetIso 𝒪 ℱ).hom

/-- Helper for Lemma 18.21.4: removing the final target transport from the forgotten localized
structure map recovers the raw pushforward-form structure map. -/
private theorem localizationAtSheafUnderlyingStructureMap_comp_targetIso_inv
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    localizationAtSheafUnderlyingStructureMap 𝒪 ℱ ≫
        (localizationAtSheafUnderlyingStructureMapTargetIso 𝒪 ℱ).inv =
      (sheafCompose J (forget RingCat.{w})).map
        (RingedSite.localizationAtSheafStructureMap 𝒪 ℱ) := by
  -- Proof comment: this is only the abbreviation unfolded against the inverse of its final
  -- target identification.
  simp [localizationAtSheafUnderlyingStructureMap, Category.assoc]

/-- Helper for Lemma 18.21.4: after forgetting the `Over` packaging on the relocalization
comparison `Over.starPullbackIsoStar`, its left component already lands in the concrete pullback
object owned by `Over.pullback s`. This isolates the transport layer used in the main square. -/
private abbrev starPullbackIsoStar_inv_app_left_to_pullback
    {𝒢 ℱ : Sheaf J (Type w)} (s : 𝒢 ⟶ ℱ) (A : Sheaf J (Type w)) :
    ((Over.star 𝒢).obj A).left ⟶ pullback ((Over.star ℱ).obj A).hom s := by
  -- Route correction: normalize the codomain first so the remaining relocalization step is a
  -- concrete pullback map, not an opaque `Over`-level transport.
  simpa [Functor.comp_obj] using ((Over.starPullbackIsoStar s).inv.app A).left

/-- Helper for Lemma 18.21.4: the left component of the unit for `Over.forgetAdjStar` is the
standard product lift. This is the concrete slice-side map that the omitted relocalization check
must ultimately compare. -/
private theorem forgetAdjStar_unit_app_left_eq
    (ℱ : Sheaf J (Type w)) (Y : Over ℱ) :
    ((Over.forgetAdjStar ℱ).unit.app Y).left = prod.lift Y.hom (𝟙 _) := by
  -- This is the explicit owner formula for the slice-topos unit map.
  simpa using Over.forgetAdjStar_unit_app_left ℱ Y

/-- Helper for Lemma 18.21.4: before passing to the slice-topos presentation, the forgotten
localized structure map is exactly the unit of the `Type`-valued localization adjunction. -/
private theorem localizationAtSheafUnderlyingStructureMap_toLocalizationUnit
    (𝒪 : Sheaf J RingCat.{w}) (ℱ : Sheaf J (Type w)) :
    let A : Sheaf J (Type w) := underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪)
    localizationAtSheafUnderlyingStructureMap 𝒪 ℱ ≫
        (localizationAtSheafUnderlyingStructureMapTargetIso 𝒪 ℱ).inv ≫
        (localizationAtSheaf_forget_pushforward_obj_iso 𝒪 ℱ).hom ≫
        (Functor.mapIso
          ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
            (localizationTopology ℱ) J)
          (localizationAtSheaf_underlyingStructureSheaf_iso_inverseImage 𝒪 ℱ)).hom =
      ((localizationProjection ℱ).sheafAdjunctionCocontinuous (Type w)
        (localizationTopology ℱ) J).unit.app A := by
  -- Proof comment: the only nontrivial content here is that the ringed structure map was defined
  -- as the adjunction image of the identity on the localized structure sheaf, so after forgetting
  -- ring structure and rewriting that sheaf as `j⁻¹ A`, the map is literally the unit.
  dsimp
  have h :=
    congrArg
      (fun k ↦
        k ≫
          (localizationAtSheaf_forget_pushforward_obj_iso 𝒪 ℱ).hom ≫
            (Functor.mapIso
              ((localizationProjection ℱ).sheafPushforwardCocontinuous (Type w)
                (localizationTopology ℱ) J)
              (localizationAtSheaf_underlyingStructureSheaf_iso_inverseImage 𝒪 ℱ)).hom)
      (localizationAtSheafUnderlyingStructureMap_comp_targetIso_inv 𝒪 ℱ)
  simpa [RingedSite.localizationAtSheafStructureMap, Category.assoc, Adjunction.homEquiv_unit] using h

/-- Lemma 18.21.4, ringed layer: after transporting `j_ℱ^♯` and `j_𝒢^♯` to the slice-topos
owners, the structure map for `𝒢` is obtained from the structure map for `ℱ` by the canonical
relocalization comparison. -/
theorem localizationAtSheafUnderlyingStructureMap_relocalization
    {𝒢 ℱ : Sheaf J (Type w)} (𝒪 : Sheaf J RingCat.{w}) (s : 𝒢 ⟶ ℱ) :
    localizationAtSheafUnderlyingStructureMap 𝒪 𝒢 ≫
        (((Over.starPullbackIsoStar s).inv.app
              (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪))).left ≫
          pullback.fst
            ((Over.star ℱ).obj
              (underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪))).hom
            s) =
      localizationAtSheafUnderlyingStructureMap 𝒪 ℱ := by
  let A : Sheaf J (Type w) := underlyingStructureSheaf (RingedSite.ofRingSheaf J 𝒪)
  -- Proof comment: first remove the final `ℱ`-target transport so the remaining equality lives
  -- entirely before the last object-level identification.
  refine (cancel_mono (localizationAtSheafUnderlyingStructureMapTargetIso 𝒪 ℱ).inv).1 ?_
  -- Proof comment: after this normalization, the goal is the raw equality between the forgotten
  -- pushforward-form structure maps before the terminal target identification.
  simp [A, localizationAtSheafUnderlyingStructureMap, Category.assoc]
  -- Route correction: rewrite both structure maps as localization-adjunction units before
  -- comparing the remaining relocalization mate on the slice-topos side.
  rw [localizationAtSheafUnderlyingStructureMap_toLocalizationUnit (𝒪 := 𝒪) (ℱ := 𝒢)]
  rw [localizationAtSheafUnderlyingStructureMap_toLocalizationUnit (𝒪 := 𝒪) (ℱ := ℱ)]
  simp only [Category.assoc]

end

end

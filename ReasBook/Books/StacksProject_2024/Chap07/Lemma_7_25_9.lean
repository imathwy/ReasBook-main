import Mathlib
import StacksProject_2024.Chap07.Lemma_7_25_4
import StacksProject_2024.Chap07.Lemma_7_25_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [∀ F : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify (J.over V) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

/- Domain-style sampling for Lemma 7.25.9:
- primary domain: relocalization between localized sheaf topoi, compared through the slice
  equivalences over the sheafified representables;
- sampled owner declarations:
  `GrothendieckTopology.representableLocalizationComparison`,
  `CategoryTheory.Over.map`,
  `CategoryTheory.Over.pullback`,
  `CategoryTheory.Over.isoMk`;
- source-facing layer: the textbook identifications of relocalization lower shriek with
  postcomposition by `h_V^# ⟶ h_U^#` and relocalization inverse image with pullback along that
  morphism;
- core/canonical owner abstractions: the slice functors `Over.map (J.sheafifiedRepresentableMap f)`
  and `Over.pullback (J.sheafifiedRepresentableMap f)` on
  `Sh(C, J) / h_V^#` and `Sh(C, J) / h_U^#`, viewed through the equivalences
  `J.representableLocalizationComparison V` and `J.representableLocalizationComparison U`;
- bridge/view layer: this file is precisely the owner-level comparison between the localization
  functors on slice sites and those canonical slice-category functors on sheaves;
- primitive data: only the site `J`, the morphism `f`, and the sheaf argument;
- derived API: the comparison isomorphism and pullback description in `Over` are induced from the
  canonical localization comparison functors and the canonical slice functors, so the public
  surface should live in `Over`, not only in raw `CommSq`/`IsPullback` form.
-/

section LowerShriek

variable [∀ F : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasLeftKanExtension F]

/-- Helper for Lemma 7.25.9: the identity object in `Over U` has terminal representable presheaf.
-/
private noncomputable def localized_identity_representable_iso_terminal
    (U : C) :
    ((CategoryTheory.uliftYoneda.{max u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u v)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max u v)) :=
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max u v) :=
    CategoryTheory.uliftYoneda.{max u v}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u v)) :=
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  IsTerminal.uniqueUpToIso hRep <|
    Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit

/-- Helper for Lemma 7.25.9: the identity object in the localized site has terminal sheafified
representable. -/
private noncomputable def localized_identity_sheafifiedRepresentable_iso_terminal
    (U : C) :
    (J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (J.over U) Types.isTerminalPUnit := by
  -- Pass the terminal presheaf identification through sheafification.
  simpa [GrothendieckTopology.sheafifiedRepresentable,
    GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Functor.mapIso (presheafToSheaf (J.over U) (Type (max u v)))
      (localized_identity_representable_iso_terminal (U := U)) ≪≫
        (sheafificationIso (Sheaf.terminal (J.over U) Types.isTerminalPUnit)).symm)

/-- Helper for Lemma 7.25.9: the identity slice object remains terminal after sheafification. -/
private noncomputable def localized_identity_sheafifiedRepresentable_isTerminal
    (U : C) :
    IsTerminal ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) := by
  -- Transport the standard terminal sheaf along the explicit representable isomorphism.
  exact IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (J.over U) Types.isTerminalPUnit)
    (localized_identity_sheafifiedRepresentable_iso_terminal (J := J) U).symm

/-- Helper for Lemma 7.25.9: pulling `V/V` forward along `f` produces the slice object
classified by `f`. -/
private theorem over_map_obj_terminal_eq :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  -- Unfold the slice pullback on objects and simplify the identity composite.
  change Over.mk (((𝟙 V) ≫ f)) = Over.mk f
  simp

/-- Helper for Lemma 7.25.9: forgetting the slice arrow `Over.homMk a` recovers the original map
`a : W ⟶ U`. -/
private theorem over_forget_map_homMk
    {W : C} (a : W ⟶ U) :
    (Over.forget U).map (show Over.mk a ⟶ Over.mk (𝟙 U) from Over.homMk a) = a := by
  -- `Over.homMk a` is defined so that forgetting to `C` returns exactly `a`.
  rfl

/-- Helper for Lemma 7.25.9: forgetting the transport map from
`(Over.map f).obj (Over.mk (𝟙 V))` to `Over.mk f` yields the identity on `V`. -/
private theorem over_forget_map_terminal_identification :
    (Over.forget U).map
        (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
          eqToHom (over_map_obj_terminal_eq (f := f))) =
      𝟙 V := by
  -- The transport identifies two copies of the same object `V` over `U`, so its forgotten map is
  -- the identity.
  simpa using
    (CategoryTheory.eqToHom_map
      (Over.forget U)
      (over_map_obj_terminal_eq (f := f)))

/-- Helper for Lemma 7.25.9: the sheafified representable map induced by the terminal-object
rewrite is the functorial `eqToHom` on the corresponding sheafified representables. -/
private theorem sheafifiedRepresentableMap_eqToHom_over_map_obj_terminal :
    (J.over U).sheafifiedRepresentableMap
        (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
          eqToHom (over_map_obj_terminal_eq (f := f))) =
      eqToHom
        (congrArg (fun X ↦ (J.over U).sheafifiedRepresentable X)
          (over_map_obj_terminal_eq (f := f))) := by
  -- `sheafifiedRepresentableMap` is literally the functor map on sheafified representables.
  simpa [GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor] using
    (CategoryTheory.eqToHom_map ((J.over U).sheafifiedRepresentableFunctor)
      (over_map_obj_terminal_eq (f := f)))

/-- Helper for Lemma 7.25.9: after applying the global lower-shriek functor, the terminal-object
rewrite still acts by the corresponding functorial `eqToHom` on the relocalized representable
`h[f]^#`. -/
private theorem pullback_map_eqToHom_over_map_obj_terminal :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
            eqToHom (over_map_obj_terminal_eq (f := f)))) =
      eqToHom
        (congrArg
          (fun X ↦
            ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
              ((J.over U).sheafifiedRepresentable X))
          (over_map_obj_terminal_eq (f := f))) := by
  -- Apply the lower-shriek functor to the previous `eqToHom` computation.
  calc
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
            eqToHom (over_map_obj_terminal_eq (f := f)))) =
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        (eqToHom
          (congrArg (fun X ↦ (J.over U).sheafifiedRepresentable X)
            (over_map_obj_terminal_eq (f := f)))) := by
          exact congrArg
            (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map)
            (sheafifiedRepresentableMap_eqToHom_over_map_obj_terminal
              (J := J) (f := f))
    _ =
      eqToHom
        (congrArg
          (fun X ↦
            ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
              ((J.over U).sheafifiedRepresentable X))
          (over_map_obj_terminal_eq (f := f))) := by
            simpa using
              (CategoryTheory.eqToHom_map
                ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J)
                (congrArg (fun X ↦ (J.over U).sheafifiedRepresentable X)
                  (over_map_obj_terminal_eq (f := f))))

/-- Helper for Lemma 7.25.9: the construction-level pullback comparison `sheafPullbackIso.inv`
is natural after forgetting back to presheaves. -/
private theorem sheafPullbackIso_inv_underlying_naturality
    {X Y : Sheaf (J.over U) (Type (max u v))} (η : X ⟶ Y) :
    ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (Over.forget U) (Type (max u v)) (J.over U) J).inv.app X).hom ≫
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η).hom =
    ((presheafToSheaf J (Type (max u v))).map
        ((Over.forget U).op.lan.map
          ((sheafToPresheaf (J.over U) (Type (max u v))).map η))).hom ≫
      ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (Over.forget U) (Type (max u v)) (J.over U) J).inv.app Y).hom := by
  -- This is just the naturality of `sheafPullbackIso.inv`, expressed on underlying presheaves.
  exact congrArg (fun k ↦ k.hom)
    (((Functor.sheafPullbackConstruction.sheafPullbackIso
      (Over.forget U) (Type (max u v)) (J.over U) J).inv.naturality η).symm)

/-- Helper for Lemma 7.25.9: after applying left Kan extension along `Over.forget U`, the
`toSheafify` naturality square for `uliftYoneda.map g` stays unchanged. -/
private theorem over_forget_lan_toSheafify_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g)) ≫
        ((Over.forget U).op.lan.map
          (CategoryTheory.toSheafify (J.over U) (CategoryTheory.uliftYoneda.obj Y))) =
      ((Over.forget U).op.lan.map
          (CategoryTheory.toSheafify (J.over U) (CategoryTheory.uliftYoneda.obj X))) ≫
        ((Over.forget U).op.lan.map
          (CategoryTheory.sheafifyMap (J.over U) (CategoryTheory.uliftYoneda.map g))) := by
  -- Apply `lan.map` to the source-side `toSheafify` naturality for `uliftYoneda.map g`.
  simpa [Functor.map_comp] using
    congrArg ((Over.forget U).op.lan.map)
      (CategoryTheory.toSheafify_naturality (J := J.over U)
        (η := CategoryTheory.uliftYoneda.map g))

/-- Helper for Lemma 7.25.9: the inverse `plusPlusIsoSheafify` comparison turns the concrete
weak-sheafify map on `lan.map (uliftYoneda.map g)` into the abstract `presheafToSheaf` map. -/
private theorem lan_plusPlusIsoSheafify_inv_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    let A := Type (max u v)
    let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.obj X
    let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.obj Y
    let βX := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PX)
    let βY := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PY)
    βX.inv ≫ J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g)) =
      ((presheafToSheaf J A).map
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g))).hom ≫
        βY.inv := by
  -- Conjugate the concrete `J.sheafifyMap` by `plusPlusIsoSheafify` and cancel the right
  -- `plusPlus` factor.
  dsimp
  let A := Type (max u v)
  let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.obj X
  let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.obj Y
  let βX := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PX)
  let βY := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PY)
  have hnat :
      J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g)) ≫ βY.hom =
        βX.hom ≫
          ((presheafToSheaf J A).map
            ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g))).hom := by
    simpa [A, PX, PY, βX, βY, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J A).hom.naturality
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g))
  calc
    βX.inv ≫ J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g)) =
        (βX.inv ≫ J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g))) ≫
          βY.hom ≫ βY.inv := by
            simp
    _ =
      ((presheafToSheaf J A).map
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.map g))).hom ≫ βY.inv := by
          simpa [Category.assoc] using congrArg (fun k ↦ βX.inv ≫ k ≫ βY.inv) hnat

/-- Helper for Lemma 7.25.9: the `lan` image of `toSheafify` naturality for the
`uliftYoneda.{max u v}` model. -/
private theorem over_forget_lan_toSheafify_naturality_ulift
    {X Y : Over U} (g : X ⟶ Y) :
    ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g)) ≫
        ((Over.forget U).op.lan.map
          ((J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj Y))) =
      ((Over.forget U).op.lan.map
          ((J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj X))) ≫
        ((Over.forget U).op.lan.map
          ((J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g))) := by
  -- Apply `lan.map` directly to the exact `toSheafify` naturality square for the explicit
  -- `uliftYoneda.{max u v}` model used by Lemma 7.13.5.
  have h₀ :
      CategoryTheory.uliftYoneda.{max u v}.map g ≫
          (J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj Y) =
        (J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj X) ≫
          (J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g) := by
    simpa using
      (CategoryTheory.toSheafify_naturality (J := J.over U)
        (η := CategoryTheory.uliftYoneda.{max u v}.map g))
  have h :
      (Over.forget U).op.lan.map
          (CategoryTheory.uliftYoneda.{max u v}.map g ≫
            (J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj Y)) =
        (Over.forget U).op.lan.map
      ((J.over U).toSheafify (CategoryTheory.uliftYoneda.{max u v}.obj X) ≫
        (J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g)) := by
    exact congrArg ((Over.forget U).op.lan.map) h₀
  simpa only [Functor.map_comp] using h

/-- Helper for Lemma 7.25.9: the outer `plusPlusIsoSheafify` conjugation for the
`uliftYoneda.{max u v}` model. -/
private theorem lan_plusPlusIsoSheafify_inv_naturality_ulift
    {X Y : Over U} (g : X ⟶ Y) :
    let A := Type (max u v)
    let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
    let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
    let βX := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PX)
    let βY := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PY)
    βX.inv ≫ J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g)) =
      ((presheafToSheaf J A).map
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g))).hom ≫ βY.inv := by
  -- Conjugate the concrete sheafification map by `plusPlusIsoSheafify` with the same explicit
  -- universe choice used by the `compULiftYonedaIsoULiftYonedaCompLan` factor.
  dsimp
  let A := Type (max u v)
  let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
  let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
  let βX := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PX)
  let βY := plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj PY)
  have hnat :
      J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g)) ≫
          βY.hom =
        βX.hom ≫
          ((presheafToSheaf J A).map
            ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g))).hom := by
    simpa [A, PX, PY, βX, βY, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J A).hom.naturality
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g))
  calc
    βX.inv ≫ J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g)) =
        (βX.inv ≫
            J.sheafifyMap ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g))) ≫
          βY.hom ≫ βY.inv := by
            simp
    _ =
      ((presheafToSheaf J A).map
        ((Over.forget U).op.lan.map (CategoryTheory.uliftYoneda.{max u v}.map g))).hom ≫ βY.inv := by
          simpa [Category.assoc] using congrArg (fun k ↦ βX.inv ≫ k ≫ βY.inv) hnat

/-- Helper for Lemma 7.25.9: after applying left Kan extension, naturality of the inner
`plusPlusIsoSheafify` comparison in the localized site. -/
private theorem over_forget_lan_plusPlusIsoSheafify_hom_naturality_ulift
    {X Y : Over U} (g : X ⟶ Y) :
    let A := Type (max u v)
    let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
    let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
    ((Over.forget U).op.lan.map ((J.over U).sheafifyMap
      (CategoryTheory.uliftYoneda.{max u v}.map g))) ≫
      ((Over.forget U).op.lan.map (plusPlusIsoSheafify (J.over U) A PY).hom) =
    ((Over.forget U).op.lan.map (plusPlusIsoSheafify (J.over U) A PX).hom) ≫
      ((Over.forget U).op.lan.map
        ((sheafToPresheaf (J.over U) A).map
          ((presheafToSheaf (J.over U) A).map
            (CategoryTheory.uliftYoneda.{max u v}.map g)))) := by
  dsimp
  let A := Type (max u v)
  let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
  let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
  have h := (plusPlusFunctorIsoSheafification (J.over U) A).hom.naturality
    (CategoryTheory.uliftYoneda.{max u v}.map g)
  simpa [A, PX, PY, GrothendieckTopology.sheafification_map,
    sheafification_map, Functor.map_comp] using
    congrArg ((Over.forget U).op.lan.map) h

/-- Helper for Lemma 7.25.9: naturality of the outer `plusPlusIsoSheafify` comparison after the
localized sheafification map has been pushed forward to `C`. -/
private theorem lan_plusPlusIsoSheafify_target_hom_naturality_ulift
    {X Y : Over U} (g : X ⟶ Y) :
    let A := Type (max u v)
    let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
    let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
    J.sheafifyMap ((Over.forget U).op.lan.map
        ((J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g))) ≫
      (plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj ((J.over U).sheafify PY))).hom =
    (plusPlusIsoSheafify J A ((Over.forget U).op.lan.obj ((J.over U).sheafify PX))).hom ≫
      ((presheafToSheaf J A).map
        ((Over.forget U).op.lan.map
          ((J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g)))).hom := by
  dsimp
  let A := Type (max u v)
  let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
  let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
  simpa [A, PX, PY, GrothendieckTopology.sheafification_map, sheafification_map] using
    (plusPlusFunctorIsoSheafification J A).hom.naturality
      ((Over.forget U).op.lan.map
        ((J.over U).sheafifyMap (CategoryTheory.uliftYoneda.{max u v}.map g)))

/-- Helper for Lemma 7.25.9: after forgetting to presheaves, the continuous representable
comparison is exactly the explicit Lemma 7.13.5 whiskered chain. -/
private theorem continuous_sheafified_representable_underlying_whiskered_normal_form
    (X : Over U) :
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom) =
    (sheafToPresheaf J (Type (max u v))).map
        ((presheafToSheaf J (Type (max u v))).map
          ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan (Over.forget U)).app X).hom) ≫
      (plusPlusIsoSheafify J (Type (max u v))
          ((Over.forget U).op.lan.obj
            (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X))).inv ≫
      J.sheafifyMap
        ((Over.forget U).op.lan.map
          ((J.over U).toSheafify
            (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X))) ≫
      (plusPlusIsoSheafify J (Type (max u v))
          ((Over.forget U).op.lan.obj
            ((J.over U).sheafify
              (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X)))).hom ≫
      (sheafToPresheaf J (Type (max u v))).map
          ((presheafToSheaf J (Type (max u v))).map
            ((Over.forget U).op.lan.map
              (plusPlusIsoSheafify (J.over U) (Type (max u v))
                (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X)).hom)) ≫
      (sheafToPresheaf J (Type (max u v))).map
          ((Functor.sheafPullbackConstruction.sheafPullbackIso
            (Over.forget U) (Type (max u v)) (J.over U) J).symm.app
              ((J.over U).uliftSheafifiedRepresentable X)).hom := by
  -- Expose the unique sheafification-comparison isomorphism used by Lemma 7.13.5 so `asIso`
  -- unfolds to the concrete middle map in the whiskered chain.
  let _ : IsIso
      (J.sheafifyMap
        ((Over.forget U).op.lan.map
          ((J.over U).toSheafify
            (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X)))) :=
    continuous_pullback_sheafification_comparison_isIso
      (Over.forget U) (J.over U) J
      (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj X)
  -- After unfolding `continuous_sheafified_representable_iso`, the four factors are already
  -- definitionally the desired whiskered normal form.
  simp [continuous_sheafified_representable_iso, Iso.trans_hom]
  rfl

/-- A small reassociation lemma for the explicit five-factor tail naturality computation below. -/
private theorem comp_chain_of_tail_naturality
    {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ Y₂ Y₃ Y₄ Z : D}
    {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄}
    {e : X₄ ⟶ X₅} {p : X₅ ⟶ X₆} {r : X₄ ⟶ Y₄} {s : Y₄ ⟶ X₆}
    {m : X₃ ⟶ Y₃} {dy : Y₃ ⟶ Y₄} {j : X₂ ⟶ Y₂} {cy : Y₂ ⟶ Y₃}
    {k : X₁ ⟶ Y₁} {sy : Y₁ ⟶ Y₂} {fm : X₀ ⟶ Z} {bY : Z ⟶ Y₁}
    (hσ : e ≫ p = r ≫ s)
    (hδ : m ≫ dy = d ≫ r)
    (hγ : j ≫ cy = c ≫ m)
    (hto : k ≫ sy = b ≫ j)
    (hβ : a ≫ k = fm ≫ bY) :
    a ≫ b ≫ c ≫ d ≫ e ≫ p = fm ≫ bY ≫ sy ≫ cy ≫ dy ≫ s := by
  calc
    a ≫ b ≫ c ≫ d ≫ e ≫ p = a ≫ b ≫ c ≫ d ≫ (e ≫ p) := by
      simp
    _ = a ≫ b ≫ c ≫ d ≫ (r ≫ s) := by
      rw [hσ]
    _ = a ≫ b ≫ c ≫ (d ≫ r) ≫ s := by
      simp [Category.assoc]
    _ = a ≫ b ≫ c ≫ (m ≫ dy) ≫ s := by
      rw [← hδ]
    _ = a ≫ b ≫ c ≫ m ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = a ≫ b ≫ (c ≫ m) ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = a ≫ b ≫ (j ≫ cy) ≫ dy ≫ s := by
      rw [← hγ]
    _ = a ≫ b ≫ j ≫ cy ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = a ≫ (b ≫ j) ≫ cy ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = a ≫ (k ≫ sy) ≫ cy ≫ dy ≫ s := by
      rw [← hto]
    _ = a ≫ k ≫ sy ≫ cy ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = (a ≫ k) ≫ sy ≫ cy ≫ dy ≫ s := by
      simp [Category.assoc]
    _ = (fm ≫ bY) ≫ sy ≫ cy ≫ dy ≫ s := by
      rw [hβ]
    _ = fm ≫ bY ≫ sy ≫ cy ≫ dy ≫ s := by
      simp [Category.assoc]

/-- A small reassociation lemma for composing the first representable naturality square with the
tail naturality square. -/
private theorem comp_first_tail_naturality
    {D : Type*} [Category D]
    {A₀ A₁ A₂ B₀ B₁ B₂ : D}
    {firstX : A₀ ⟶ A₁} {tailX : A₁ ⟶ A₂} {pullm : A₂ ⟶ B₂}
    {fm : A₁ ⟶ B₁} {tailY : B₁ ⟶ B₂}
    {global : A₀ ⟶ B₀} {firstY : B₀ ⟶ B₁}
    (hfirst : firstX ≫ fm = global ≫ firstY)
    (htail : tailX ≫ pullm = fm ≫ tailY) :
    (firstX ≫ tailX) ≫ pullm = global ≫ (firstY ≫ tailY) := by
  calc
    (firstX ≫ tailX) ≫ pullm = firstX ≫ (tailX ≫ pullm) := by
      simp [Category.assoc]
    _ = firstX ≫ (fm ≫ tailY) := by
      rw [htail]
    _ = (firstX ≫ fm) ≫ tailY := by
      simp [Category.assoc]
    _ = (global ≫ firstY) ≫ tailY := by
      rw [hfirst]
    _ = global ≫ (firstY ≫ tailY) := by
      simp [Category.assoc]

/-- Helper for Lemma 7.25.9: the representable comparison is natural for any morphism in the
localized slice `Over U`. -/
private theorem continuous_sheafified_representable_whiskered_tail_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    let tail : (Z : Over U) →
        (sheafToPresheaf J (Type (max u v))).obj
          ((presheafToSheaf J (Type (max u v))).obj
            ((Over.forget U).op.lan.obj
              (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z))) ⟶
        (sheafToPresheaf J (Type (max u v))).obj
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable Z)) :=
      fun Z ↦
        (plusPlusIsoSheafify J (Type (max u v))
            ((Over.forget U).op.lan.obj
              (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z))).inv ≫
          (J.sheafifyMap
            ((Over.forget U).op.lan.map
              ((J.over U).toSheafify
                (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)))) ≫
          (plusPlusIsoSheafify J (Type (max u v))
              ((Over.forget U).op.lan.obj
                ((J.over U).sheafify
                  (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)))).hom ≫
          ((sheafToPresheaf J (Type (max u v))).map
              ((presheafToSheaf J (Type (max u v))).map
                ((Over.forget U).op.lan.map
                  (plusPlusIsoSheafify (J.over U) (Type (max u v))
                    (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)).hom))) ≫
          ((sheafToPresheaf J (Type (max u v))).map
              ((Functor.sheafPullbackConstruction.sheafPullbackIso
                (Over.forget U) (Type (max u v)) (J.over U) J).symm.app
                  ((J.over U).uliftSheafifiedRepresentable Z)).hom)
    tail X ≫
        (sheafToPresheaf J (Type (max u v))).map
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)) =
      ((presheafToSheaf J (Type (max u v))).map
          ((Over.forget U).op.lan.map
            (CategoryTheory.uliftYoneda.{max u v}.map g))).hom ≫
        tail Y := by
  -- Route correction: after the first `compULiftYoneda` factor is separated, only the explicit
  -- sheafification/pullback transport remains, so commute that tail on its own.
  dsimp only
  let A := Type (max u v)
  let PX : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj X
  let PY : (Over U)ᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max u v}.obj Y
  let m : PX ⟶ PY := CategoryTheory.uliftYoneda.{max u v}.map g
  let L : ((Over U)ᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) := (Over.forget U).op.lan
  let F := presheafToSheaf J A
  let G := presheafToSheaf (J.over U) A
  let βX := plusPlusIsoSheafify J A (L.obj PX)
  let βY := plusPlusIsoSheafify J A (L.obj PY)
  let sX := J.sheafifyMap (L.map ((J.over U).toSheafify PX))
  let sY := J.sheafifyMap (L.map ((J.over U).toSheafify PY))
  let sm := (J.over U).sheafifyMap m
  let jm := J.sheafifyMap (L.map m)
  let jsm := J.sheafifyMap (L.map sm)
  let γX := plusPlusIsoSheafify J A (L.obj ((J.over U).sheafify PX))
  let γY := plusPlusIsoSheafify J A (L.obj ((J.over U).sheafify PY))
  let δX := plusPlusIsoSheafify (J.over U) A PX
  let δY := plusPlusIsoSheafify (J.over U) A PY
  let dX := (sheafToPresheaf J A).map (F.map (L.map δX.hom))
  let dY := (sheafToPresheaf J A).map (F.map (L.map δY.hom))
  let η := (J.over U).sheafifiedRepresentableMap g
  let pullF := (Over.forget U).sheafPullback A (J.over U) J
  let σX := (sheafToPresheaf J A).map
    ((Functor.sheafPullbackConstruction.sheafPullbackIso
      (Over.forget U) A (J.over U) J).symm.app
        ((J.over U).uliftSheafifiedRepresentable X)).hom
  let σY := (sheafToPresheaf J A).map
    ((Functor.sheafPullbackConstruction.sheafPullbackIso
      (Over.forget U) A (J.over U) J).symm.app
        ((J.over U).uliftSheafifiedRepresentable Y)).hom
  let pullm := (sheafToPresheaf J A).map (pullF.map η)
  let fm := (F.map (L.map m)).hom
  let funder := (F.map (L.map ((sheafToPresheaf (J.over U) A).map η))).hom
  have hσ : σX ≫ pullm = funder ≫ σY := by
    simpa [A, F, G, L, η, pullF, σX, σY, pullm, funder,
      GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using
      (sheafPullbackIso_inv_underlying_naturality (J := J) (U := U) (η := η))
  have hδ :
      (F.map (L.map sm)).hom ≫ dY = dX ≫ funder := by
    have h := congrArg (fun k ↦ (F.map k).hom)
      (over_forget_lan_plusPlusIsoSheafify_hom_naturality_ulift
        (J := J) (U := U) (g := g))
    simpa [A, PX, PY, m, L, F, G, sm, δX, δY, dX, dY, η, funder,
      GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor,
      Functor.map_comp, Category.assoc] using h
  have hγ : jsm ≫ γY.hom = γX.hom ≫ (F.map (L.map sm)).hom := by
    simpa [A, PX, PY, m, L, F, sm, jsm, γX, γY] using
      (lan_plusPlusIsoSheafify_target_hom_naturality_ulift
        (J := J) (U := U) (g := g))
  have hto : jm ≫ sY = sX ≫ jsm := by
    have h := congrArg (J.sheafifyMap)
      (over_forget_lan_toSheafify_naturality_ulift
        (J := J) (U := U) (g := g))
    simpa [A, PX, PY, m, L, sX, sY, sm, jm, jsm,
      GrothendieckTopology.sheafification_map, sheafification_map,
      Functor.map_comp, Category.assoc] using h
  have hβ : βX.inv ≫ jm = fm ≫ βY.inv := by
    simpa [A, PX, PY, m, L, F, βX, βY, jm, fm] using
      (lan_plusPlusIsoSheafify_inv_naturality_ulift
        (J := J) (U := U) (g := g))
  change
    βX.inv ≫ sX ≫ γX.hom ≫ dX ≫ σX ≫ pullm =
      fm ≫ βY.inv ≫ sY ≫ γY.hom ≫ dY ≫ σY
  exact comp_chain_of_tail_naturality hσ hδ hγ hto hβ

/-- Helper for Lemma 7.25.9: the representable comparison is natural for any morphism in the
localized slice `Over U`. -/
private theorem continuous_sheafified_representable_middle_presheaf_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom ≫
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap g)) =
    (sheafToPresheaf J (Type (max u v))).map
      (J.sheafifiedRepresentableMap ((Over.forget U).map g) ≫
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J Y).hom) := by
  -- Route correction: normalize exactly as in the source proof after forgetting to presheaves,
  -- so only the middle `lan`/sheafification transport has to commute.
  -- Expose the forgotten comparison as the four-factor Lemma 7.13.5 composite before commuting
  -- its middle transport with the map induced by `g`.
  rw [Functor.map_comp, Functor.map_comp]
  simp only [GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor]
  rw [continuous_sheafified_representable_underlying_whiskered_normal_form
    (J := J) (X := X)]
  rw [continuous_sheafified_representable_underlying_whiskered_normal_form
    (J := J) (X := Y)]
  -- Peel off the initial `compULiftYoneda` factor by naturality, then commute only the explicit
  -- transport-heavy tail.
  let A := Type (max u v)
  let first : (Z : Over U) →
      (sheafToPresheaf J A).obj (J.uliftSheafifiedRepresentable ((Over.forget U).obj Z)) ⟶
        (sheafToPresheaf J A).obj
          ((presheafToSheaf J A).obj
            ((Over.forget U).op.lan.obj
              (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z))) :=
    fun Z ↦
      (sheafToPresheaf J A).map
        ((presheafToSheaf J A).map
          ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan (Over.forget U)).app Z).hom)
  let tail : (Z : Over U) →
      (sheafToPresheaf J A).obj
        ((presheafToSheaf J A).obj
          ((Over.forget U).op.lan.obj
            (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z))) ⟶
      (sheafToPresheaf J A).obj
        (((Over.forget U).sheafPullback A (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable Z)) :=
    fun Z ↦
      (plusPlusIsoSheafify J A
          ((Over.forget U).op.lan.obj
            (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z))).inv ≫
        (J.sheafifyMap
          ((Over.forget U).op.lan.map
            ((J.over U).toSheafify
              (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)))) ≫
        (plusPlusIsoSheafify J A
            ((Over.forget U).op.lan.obj
              ((J.over U).sheafify
                (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)))).hom ≫
        ((sheafToPresheaf J A).map
            ((presheafToSheaf J A).map
              ((Over.forget U).op.lan.map
                (plusPlusIsoSheafify (J.over U) A
                  (CategoryTheory.uliftYoneda.{max u v, v, max u v}.obj Z)).hom))) ≫
        ((sheafToPresheaf J A).map
            ((Functor.sheafPullbackConstruction.sheafPullbackIso
              (Over.forget U) A (J.over U) J).symm.app
                ((J.over U).uliftSheafifiedRepresentable Z)).hom)
  let fm :=
    ((presheafToSheaf J A).map
      ((Over.forget U).op.lan.map
        (CategoryTheory.uliftYoneda.{max u v}.map g))).hom
  let global :=
    (sheafToPresheaf J A).map
      (J.uliftSheafifiedRepresentableFunctor.map ((Over.forget U).map g))
  let pullm :=
    (sheafToPresheaf J A).map
      (((Over.forget U).sheafPullback A (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap g))
  have hfirst :
      first X ≫ fm = global ≫ first Y := by
    -- This is the naturality of the first Lemma 7.13.5 factor before the transport-heavy tail.
    have h := congrArg
      (fun k ↦ ((presheafToSheaf J (Type (max u v))).map k).hom)
      ((Presheaf.compULiftYonedaIsoULiftYonedaCompLan
        (Over.forget U)).hom.naturality g).symm
    simpa [A, first, fm, global, GrothendieckTopology.uliftSheafifiedRepresentableFunctor,
      GrothendieckTopology.sheafifiedRepresentableFunctor,
      GrothendieckTopology.sheafifiedRepresentableMap,
      Functor.map_comp, Category.assoc] using h
  have htail : tail X ≫ pullm = fm ≫ tail Y := by
    simpa [A, tail, fm, pullm, GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using
      (continuous_sheafified_representable_whiskered_tail_naturality
        (J := J) (U := U) (g := g))
  have hmain : (first X ≫ tail X) ≫ pullm = global ≫ (first Y ≫ tail Y) := by
    exact comp_first_tail_naturality hfirst htail
  simpa [A, first, tail, fm, global, pullm, Category.assoc] using hmain

/-- Helper for Lemma 7.25.9: forgetting sheaf morphisms to presheaves reflects equality. -/
private theorem sheafToPresheaf_map_eq_iff
    {X Y : Sheaf J (Type (max u v))} {α β : X ⟶ Y} :
    (sheafToPresheaf J (Type (max u v))).map α =
      (sheafToPresheaf J (Type (max u v))).map β ↔
        α = β := by
  constructor
  · -- The forgetful functor to presheaves is faithful, so equality can be checked downstairs.
    intro h
    exact (sheafToPresheaf J (Type (max u v))).map_injective h
  · -- Any owner-level equality stays equal after applying the forgetful functor.
    intro h
    simpa [h]

/-- Helper for Lemma 7.25.9: the representable comparison is natural for any morphism in the
localized slice `Over U`. -/
private theorem continuous_sheafified_representable_iso_over_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap g) =
    J.sheafifiedRepresentableMap ((Over.forget U).map g) ≫
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J Y).hom := by
  -- Reduce the owner-level naturality square to the presheaf-level transport statement above.
  apply (sheafToPresheaf J (Type (max u v))).map_injective
  exact continuous_sheafified_representable_middle_presheaf_naturality
    (J := J) (U := U) (g := g)

/-- Helper for Lemma 7.25.9: after forgetting to presheaves, the terminal representable component
of `Functor.sheafPullbackComp'` is the same owner-level comparison as the direct representable
comparison for `(Over.map f).obj (Over.mk (𝟙 V))`. -/
private theorem sheafPullbackComp_terminal_representable_component_characterization :
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
        (Functor.sheafPullbackComp'
            (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app
          ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv)) =
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        ((Over.map f).obj (Over.mk (𝟙 V)))).hom) := by
  -- Route correction: specialize immediately to the terminal slice representable, where the
  -- source comparison is definitionally the direct representable comparison.
  -- Forgetting to presheaves preserves this definitional identity unchanged.
  let X₀ : Over U := (Over.map f).obj (Over.mk (𝟙 V))
  change
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
        (Functor.sheafPullbackComp'
            (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app
          ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv)) =
    (sheafToPresheaf J (Type (max u v))).map
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X₀).hom)
  -- TODO: the remaining blocker is a terminal-only normalization of the hidden
  -- `ObjectProperty.homMk` and `Adjunction.leftAdjointUniq` factors after unfolding
  -- `Functor.sheafPullbackComp'` and `continuous_sheafified_representable_iso`.
  -- The source-faithful next step is to prove the owner-level equality first and then push it
  -- through `sheafToPresheaf`, using `sheafToPresheaf_map_eq_iff` to switch freely between the
  -- owner and presheaf views.
  sorry

/-- Helper for Lemma 7.25.9: the composed lower-shriek comparison agrees with the direct
comparison on the terminal representable of `Over V`. -/
private theorem continuous_sheafified_representable_iso_comp_terminal :
    (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
        (Over.mk (𝟙 V))).hom ≫
      (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app
        ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
            (Over.mk (𝟙 V))).inv) =
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
      ((Over.map f).obj (Over.mk (𝟙 V)))).hom := by
  -- Reduce the terminal owner-level comparison to the corresponding presheaf computation.
  apply (sheafToPresheaf J (Type (max u v))).map_injective
  exact sheafPullbackComp_terminal_representable_component_characterization
    (J := J) (U := U) (V := V) (f := f)

/-- Helper for Lemma 7.25.9: the owner-level representable comparison is stable under the
canonical transport `((Over.map f).obj (Over.mk (𝟙 V))) = Over.mk f`. -/
private theorem continuous_sheafified_representable_iso_over_map_terminal_transport :
    let X₀ : Over U := (Over.map f).obj (Over.mk (𝟙 V))
    let g₀ : X₀ ⟶ Over.mk f := eqToHom (over_map_obj_terminal_eq (f := f))
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X₀).hom ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap g₀) =
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
      (Over.mk f)).hom := by
  -- First use general naturality for the transport map, then identify its forgotten image with
  -- the identity on `V`.
  dsimp
  calc
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          ((Over.map f).obj (Over.mk (𝟙 V)))).hom ≫
        ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap
            (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
              eqToHom (over_map_obj_terminal_eq (f := f)))) =
      J.sheafifiedRepresentableMap
          ((Over.forget U).map
            (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
              eqToHom (over_map_obj_terminal_eq (f := f)))) ≫
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk f)).hom := by
            exact continuous_sheafified_representable_iso_over_naturality
              (J := J)
              (U := U)
              (g := (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                eqToHom (over_map_obj_terminal_eq (f := f))))
    _ = (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk f)).hom := by
            rw [over_forget_map_terminal_identification (f := f)]
            simp

/-- Helper for Lemma 7.25.9: after relocalizing along `f`, the terminal arrow to `U/U` factors
through the image of `V/V` via the canonical map `Over.mk f ⟶ Over.mk (𝟙 U)`. -/
private theorem relocalization_terminal_hom_factorization
    (𝒢 : Sheaf (J.over V) (Type (max u v))) :
    ((localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).from
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢)) =
      ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).map
          ((localized_identity_sheafifiedRepresentable_isTerminal (J := J) V).from 𝒢) ≫
        (continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
          (Over.mk (𝟙 V))).inv ≫
        (J.over U).sheafifiedRepresentableMap
          (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk (𝟙 U) from
            eqToHom (over_map_obj_terminal_eq (f := f)) ≫
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) := by
  -- The codomain is terminal, so any two arrows into it agree.
  exact (localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).hom_ext _ _

/-- Helper for Lemma 7.25.9: the terminal arrow from the localized identity representable to
itself is the identity. -/
private theorem localized_identity_terminal_from_self
    (U : C) :
    (localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).from
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) =
      𝟙 _ := by
  -- Both endomorphisms of a terminal object agree.
  exact (localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).hom_ext _ _

/-- Helper for Lemma 7.25.9: the canonical map attached to the terminal slice representable is
just the inverse representable comparison. -/
private theorem representableLocalizationHom_terminal
    (U : C) :
    J.representableLocalizationHom U
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) =
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).symm.hom := by
  -- The terminal arrow is the identity, so only the representable comparison remains.
  simp [GrothendieckTopology.representableLocalizationHom]

/-- Helper for Lemma 7.25.9: on the representable associated to `Over.mk f`, the unique map to the
terminal slice representable is the sheafified representable map induced by `Over.homMk f`. -/
private theorem localized_identity_terminal_from_homMk :
    (localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).from
        ((J.over U).sheafifiedRepresentable (Over.mk f)) =
      (J.over U).sheafifiedRepresentableMap
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f) := by
  -- Both maps land in the terminal object `h[U/U]^#`, so terminality identifies them.
  exact (localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).hom_ext _ _

/-- Helper for Lemma 7.25.9: on the pulled-back terminal representable, the hidden terminal arrow
inside `representableLocalizationHom` is the explicit factorization through `Over.homMk f`. -/
private theorem representableLocalizationHom_over_map_terminal :
    J.representableLocalizationHom U
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
          ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))) =
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv ≫
            (J.over U).sheafifiedRepresentableMap
              (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk (𝟙 U) from
                eqToHom (over_map_obj_terminal_eq (f := f)) ≫
                  (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) ≫
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).symm.hom := by
  -- Unfold the definition once, then replace the hidden terminal arrow by the explicit
  -- factorization from the terminality computation in the slice.
  rw [GrothendieckTopology.representableLocalizationHom]
  let F := (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J
  have hfactor :
      F.map
          ((localized_identity_sheafifiedRepresentable_isTerminal (J := J) U).from
            (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))))) =
        F.map
          (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).map
              ((localized_identity_sheafifiedRepresentable_isTerminal (J := J) V).from
                ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))) ≫
            (continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv ≫
            (J.over U).sheafifiedRepresentableMap
              (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk (𝟙 U) from
                eqToHom (over_map_obj_terminal_eq (f := f)) ≫
                  (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) := by
    exact congrArg F.map
      (relocalization_terminal_hom_factorization (J := J) (f := f)
        ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))))
  have hfactor' := congrArg (fun k ↦ k ≫
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).symm.hom) hfactor
  simpa [F, Functor.map_comp, Category.assoc,
    localized_identity_terminal_from_self (J := J) V] using hfactor'

/-- Helper for Lemma 7.25.9: the canonical localization morphisms are natural for the terminal
slice arrow `Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 U)`. -/
private theorem representableLocalizationHom_homMk_naturality :
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
      J.representableLocalizationHom U
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) =
    J.representableLocalizationHom U
      ((J.over U).sheafifiedRepresentable (Over.mk f)) := by
  -- Read off the commutativity of `representableLocalizationComparison.map` on the terminal slice
  -- arrow `Over.homMk f`.
  simpa [GrothendieckTopology.representableLocalizationComparison, Functor.toOver_map_left,
    Over.comp_left] using
    ((J.representableLocalizationComparison U).map
      ((J.over U).sheafifiedRepresentableMap
        (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))).w

/-- Helper for Lemma 7.25.9: the canonical localization morphism on `h[f]^#` is the pullback of
the terminal comparison along the slice arrow `Over.homMk f`. -/
private theorem representableLocalizationHom_homMk :
    J.representableLocalizationHom U
      ((J.over U).sheafifiedRepresentable (Over.mk f)) =
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
      J.representableLocalizationHom U
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))) := by
  -- This is just the specialized naturality square rewritten with the target on the left.
  simpa using (representableLocalizationHom_homMk_naturality (J := J) (U := U) (f := f)).symm

/-- Helper for Lemma 7.25.9: after evaluating at `X.left`, postcomposing the comparison map with
the relocalized slice representable comparison is computed by the pullback functor map on
sections. -/
private theorem relocalized_slice_representable_map_section
    {X Y : Over U} (g : X ⟶ Y) :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable Y))
        X.left
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap g)).hom.app (op X.left)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable X))
          X.left
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom) := by
  -- Evaluate the composite through the canonical Hom/section equivalence on sheafified
  -- representables.
  exact J.uliftSheafifiedRepresentableHomEquiv_comp
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X).hom
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
      ((J.over U).sheafifiedRepresentableMap g))

/-- Helper for Lemma 7.25.9: the global sheafified representable map acts on the comparison
section by restriction along the underlying arrow in `C`. -/
private theorem global_representable_map_section_naturality
    {X Y : Over U} (g : X ⟶ Y) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable Y)).obj.map
        ((Over.forget U).map g).op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable Y))
          Y.left
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J Y).hom) =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable Y))
        X.left
        (J.sheafifiedRepresentableMap ((Over.forget U).map g) ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J Y).hom) := by
  -- This is the naturality of the representable Hom/section equivalence in the source object.
  simpa [GrothendieckTopology.sheafifiedRepresentableMap] using
    (J.uliftSheafifiedRepresentableHomEquiv_naturality ((Over.forget U).map g)
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable Y))
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J Y).hom).symm

/-- Helper for Lemma 7.25.9: the terminal comparison sends the canonical localized `U`-section of
`h[U/U]^#` back to the canonical global section of `h[U]^#`. -/
private theorem terminal_comparison_canonical_section :
    J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom) =
      J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
        (𝟙 (J.sheafifiedRepresentable U)) := by
  -- Compose the representable comparison with its inverse and evaluate the resulting identity.
  simpa using
    (J.uliftSheafifiedRepresentableHomEquiv_comp
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).hom
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).symm.hom)

/-- Helper for Lemma 7.25.9: after restricting the canonical localized `U`-section along `f`, the
terminal comparison still agrees with the restriction of the canonical global section. -/
private theorem terminal_comparison_canonical_section_restrict :
    J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) V
        (J.sheafifiedRepresentableMap f) =
      (J.sheafifiedRepresentable U).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
          (𝟙 (J.sheafifiedRepresentable U))) := by
  -- Rewrite the global map `h[V]^# ⟶ h[U]^#` as restriction of the identity section of `h[U]^#`.
  simpa [Category.comp_id, GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor] using
    J.uliftSheafifiedRepresentableHomEquiv_naturality f (J.sheafifiedRepresentable U)
      (𝟙 (J.sheafifiedRepresentable U))

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_homMk_target_section
    {W : C} (a : W ⟶ U) :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        W
        (J.sheafifiedRepresentableMap a ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map a.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
  -- Evaluate the target composite by the source-object naturality of the global Hom/section
  -- equivalence at the chosen arrow `a : W ⟶ U`.
  simpa [GrothendieckTopology.sheafifiedRepresentableMap,
    GrothendieckTopology.sheafifiedRepresentableFunctor] using
    J.uliftSheafifiedRepresentableHomEquiv_naturality a
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).hom)

/-- Helper for Lemma 7.25.9: to prove naturality for `Over.homMk f`, it is enough to identify the
induced `V`-section of the left-hand composite with the restricted canonical `U`-section. -/
private theorem continuous_sheafified_representable_iso_homMk_naturality_of_section
    (hsection :
      J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          V
          ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk f)).hom ≫
            ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
              ((J.over U).sheafifiedRepresentableMap
                (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) =
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map f.op
          (J.uliftSheafifiedRepresentableHomEquiv
            (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
              ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
            U
            (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk (𝟙 U))).hom)) :
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk f)).hom ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) =
    J.sheafifiedRepresentableMap f ≫
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).hom := by
  -- The source is `h[V]^#`, so equality of the induced `V`-sections determines the morphism.
  apply
    (J.uliftSheafifiedRepresentableHomEquiv
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
      V).injective
  exact hsection.trans
    (continuous_sheafified_representable_iso_homMk_target_section
      (J := J) (U := U) (a := f)).symm

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_over_homMk_section_as_map
    {W : C} (a : W ⟶ U) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk a ⟶ Over.mk (𝟙 U) from Over.homMk a))).hom.app (op W)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk a)))
          W
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk a)).hom) =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        W
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk a)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap
              (show Over.mk a ⟶ Over.mk (𝟙 U) from Over.homMk a))) := by
  -- Freeze the owner-level postcomposition before comparing it with the restricted terminal
  -- section. This separates the map-on-sections interface step from the remaining naturality
  -- comparison.
  simpa using
    (relocalized_slice_representable_map_section (J := J) (U := U)
      (g := (show Over.mk a ⟶ Over.mk (𝟙 U) from Over.homMk a))).symm

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_homMk_left_section_as_map :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        V
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap
            (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk f)))
          V
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom) := by
  -- This is the specialization of the general map-on-sections computation to `a = f`.
  simpa using
    (continuous_sheafified_representable_iso_over_homMk_section_as_map
      (J := J) (U := U) (a := f))

/-- Helper for Lemma 7.25.9: specializing the global representable map naturality to
`Over.homMk a` rewrites the target-side section as restriction along `a`. -/
private theorem global_representable_map_homMk_section
    {W : C} (a : W ⟶ U) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map a.op
      (J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        U
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).hom) =
    J.uliftSheafifiedRepresentableHomEquiv
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
      W
      (J.sheafifiedRepresentableMap a ≫
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).hom) := by
  -- This is the global representable map naturality specialized to the forgotten arrow of
  -- `Over.homMk a`.
  let g : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a
  let Fterminal :=
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
      ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))
  simpa [Fterminal, g, over_forget_map_homMk (U := U) a] using
    (global_representable_map_section_naturality (J := J) (U := U) (g := g))

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_over_homMk_section
    {W : C} (a : W ⟶ U) :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk a ⟶ Over.mk (𝟙 U) from Over.homMk a))).hom.app (op W)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk a)))
          W
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk a)).hom) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map a.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
  -- Route correction: the interface step has been separated out as
  -- `continuous_sheafified_representable_iso_over_homMk_section_as_map`. What remains is the
  -- owner-level naturality comparison for the composite attached to `Over.homMk a`.
  let g : Over.mk a ⟶ Over.mk (𝟙 U) := Over.homMk a
  let Fterminal :=
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
      ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))
  calc
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap g)).hom.app (op W)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk a)))
          W
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk a)).hom) =
      J.uliftSheafifiedRepresentableHomEquiv
        Fterminal
        W
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk a)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)) := by
              -- First rewrite the left-hand section as evaluation of the owner-level composite.
              simpa [Fterminal, g] using
                (continuous_sheafified_representable_iso_over_homMk_section_as_map
                  (J := J) (U := U) (a := a))
    _ =
      J.uliftSheafifiedRepresentableHomEquiv
        Fterminal
        W
        (J.sheafifiedRepresentableMap a ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
          -- Replace the owner-level composite by naturality of the representable comparison.
          exact congrArg
            (J.uliftSheafifiedRepresentableHomEquiv Fterminal W)
            (by
              simpa [g, over_forget_map_homMk (U := U) a] using
                (continuous_sheafified_representable_iso_over_naturality
                  (J := J)
                  (U := U)
                  (g := g)))
    _ =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map a.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
              -- Evaluate the global map `h[W]^# ⟶ h[U]^#` on the canonical section of `h[U]^#`.
              simpa [Fterminal, g] using
                (global_representable_map_homMk_section (J := J) (U := U) (a := a)).symm

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_homMk_left_section_sigma_pair :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        V
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
  -- Route correction: isolate the single-object sigma computation controlled by the source proof
  -- before returning to the owner-level morphism equality.
  let g : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  calc
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
        V
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap g)).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk f)))
          V
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom) := by
            -- First isolate the action of the relocalized representable map on the canonical
            -- section of `h[f]^#`.
            simpa [g] using
              (continuous_sheafified_representable_iso_homMk_left_section_as_map
                (J := J) (U := U) (V := V) (f := f))
    _ = (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
              -- Specialize the shared canonical-section lemma to `a = f`.
              simpa using
                (continuous_sheafified_representable_iso_over_homMk_section
                  (J := J) (U := U) (a := f))

/-- Helper for Lemma 7.25.9: the continuous representable comparison is natural for the terminal
slice arrow `Over.homMk f`. -/
private theorem continuous_sheafified_representable_iso_homMk_naturality :
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk f)).hom ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) =
    J.sheafifiedRepresentableMap f ≫
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).hom := by
  -- Route correction: reduce the owner-level equality to the single section computation at `V`;
  -- this matches the source proof, where both sides are identified with the same fibre element
  -- over `f`.
  exact continuous_sheafified_representable_iso_homMk_naturality_of_section
    (J := J) (U := U) (V := V) (f := f)
    (continuous_sheafified_representable_iso_homMk_left_section_sigma_pair
      (J := J) (U := U) (V := V) (f := f))

/-- Helper for Lemma 7.25.9: the relocalized representable section attached to `Over.homMk f`
restricts to the same `V`-section as the global representable map `h[V]^# ⟶ h[U]^#`. -/
private theorem continuous_sheafified_representable_iso_homMk_section :
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk f)))
          V
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
  let g : Over.mk f ⟶ Over.mk (𝟙 U) := Over.homMk f
  let Fterminal :=
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
      ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))
  -- First rewrite each side as the section induced by the corresponding morphism into
  -- `J.sheafifiedRepresentable U`.
  calc
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk f)))
          V
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom) =
      J.uliftSheafifiedRepresentableHomEquiv
        Fterminal
        V
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk f)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap g)) := by
              simpa [g] using
                (relocalized_slice_representable_map_section (J := J) (U := U)
                  (g := g)).symm
    _ = J.uliftSheafifiedRepresentableHomEquiv
        Fterminal
        V
        (J.sheafifiedRepresentableMap f ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
          -- The remaining comparison is exactly the specialized naturality square for the
          -- representable comparison map.
          exact congrArg (J.uliftSheafifiedRepresentableHomEquiv Fterminal V)
            (continuous_sheafified_representable_iso_homMk_naturality (J := J) (f := f))
    _ =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U))))
          U
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom) := by
              simpa [Fterminal] using
                (global_representable_map_section_naturality (J := J) (U := U) g).symm

/-- Helper for Lemma 7.25.9: evaluating the terminal component of `Functor.sheafPullbackComp'` on
the canonical `V`-section yields the canonical section of the localized representable `h[f]^#`. -/
private theorem sheafPullbackComp_terminal_left_section_as_map :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
          (Functor.sheafPullbackComp'
              (J.over V) (J.over U) J (Over.map f) (Over.forget U)
              (Over.mapForget f)).inv.app
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                  eqToHom (over_map_obj_terminal_eq (f := f))))) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv ≫
            (J.over U).sheafifiedRepresentableMap
              (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                eqToHom (over_map_obj_terminal_eq (f := f))))).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))))
          V
          ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
              (Over.mk (𝟙 V))).hom ≫
            (Functor.sheafPullbackComp'
                (J.over V) (J.over U) J (Over.map f) (Over.forget U)
                (Over.mapForget f)).inv.app
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))))) := by
  -- Evaluate the final postcomposition with the relocalized representable map at the object `V`.
  let α :=
    (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
        (Over.mk (𝟙 V))).hom ≫
      (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app
        ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))
  let β :=
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
      ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
          (Over.mk (𝟙 V))).inv ≫
        (J.over U).sheafifiedRepresentableMap
          (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
            eqToHom (over_map_obj_terminal_eq (f := f))))
  simpa [α, β] using J.uliftSheafifiedRepresentableHomEquiv_comp α β

/-- Helper for Lemma 7.25.9: evaluating the terminal component of `Functor.sheafPullbackComp'` on
the canonical `V`-section yields the canonical section of the localized representable `h[f]^#`. -/
private theorem sheafPullbackComp_terminal_preserves_canonical_section :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable
            ((Over.map f).obj (Over.mk (𝟙 V)))))
        V
        ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
          (Functor.sheafPullbackComp'
              (J.over V) (J.over U) J (Over.map f) (Over.forget U)
              (Over.mapForget f)).inv.app
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv)) =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable
            ((Over.map f).obj (Over.mk (𝟙 V)))))
        V
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          ((Over.map f).obj (Over.mk (𝟙 V)))).hom := by
  -- Route correction: isolate the terminal component of `Functor.sheafPullbackComp'` before the
  -- final object-identification map to `Over.mk f`. This matches the source proof's terminal case
  -- `j_{U!} j_! = j_{V!}` exactly.
  let X₀ : Over U := (Over.map f).obj (Over.mk (𝟙 V))
  -- Apply the owner-level comparison to the canonical `V`-section of the source representable.
  exact congrArg
    (J.uliftSheafifiedRepresentableHomEquiv
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
        ((J.over U).sheafifiedRepresentable X₀))
      V)
    (by
      simpa [X₀] using
        (continuous_sheafified_representable_iso_comp_terminal
          (J := J)
          (U := U)
          (V := V)
          (f := f)))

/-- Helper for Lemma 7.25.9: evaluating the terminal component of `Functor.sheafPullbackComp'` on
the canonical `V`-section yields the canonical section of the localized representable `h[f]^#`. -/
private theorem sheafPullbackComp_terminal_left_section_sigma_pair :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
          (Functor.sheafPullbackComp'
              (J.over V) (J.over U) J (Over.map f) (Over.forget U)
              (Over.mapForget f)).inv.app
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                  eqToHom (over_map_obj_terminal_eq (f := f))))) =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk f)).hom := by
  -- Route correction: isolate the second terminal-case sigma computation from the source proof
  -- before packaging it back into the `Functor.sheafPullbackComp'` comparison.
  let X₀ : Over U := (Over.map f).obj (Over.mk (𝟙 V))
  let g₀ : X₀ ⟶ Over.mk f :=
    eqToHom (over_map_obj_terminal_eq (f := f))
  calc
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
          (Functor.sheafPullbackComp'
              (J.over V) (J.over U) J (Over.map f) (Over.forget U)
              (Over.mapForget f)).inv.app
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                  eqToHom (over_map_obj_terminal_eq (f := f))))) =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
              (Over.mk (𝟙 V))).inv ≫
            (J.over U).sheafifiedRepresentableMap
              (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                eqToHom (over_map_obj_terminal_eq (f := f))))).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))))
          V
          ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
              (Over.mk (𝟙 V))).hom ≫
            (Functor.sheafPullbackComp'
                (J.over V) (J.over U) J (Over.map f) (Over.forget U)
                (Over.mapForget f)).inv.app
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))))) := by
            -- First expose the terminal component of `Functor.sheafPullbackComp'` as the
            -- intermediate `V`-section transported by the final representable map.
            exact sheafPullbackComp_terminal_left_section_as_map
              (J := J) (U := U) (V := V) (f := f)
    _ =
      (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
          ((J.over U).sheafifiedRepresentableMap g₀)).hom.app (op V)
        (J.uliftSheafifiedRepresentableHomEquiv
          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
            ((J.over U).sheafifiedRepresentable X₀))
          V
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J X₀).hom) := by
            -- The terminal component first lands in the canonical section of the pulled-back
            -- representable indexed by `X₀`; only then do we transport to `Over.mk f`.
            rw [Functor.map_comp]
            rw [J.uliftSheafifiedRepresentableHomEquiv_comp]
            exact congrArg
              ((((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
                  ((J.over U).sheafifiedRepresentableMap g₀)).hom.app (op V))
              (sheafPullbackComp_terminal_preserves_canonical_section
                (J := J) (U := U) (V := V) (f := f))
    _ =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk f)).hom := by
            -- The final step is only the `eqToHom` transport
            -- `((Over.map f).obj (Over.mk (𝟙 V))) = Over.mk f`.
            calc
              (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
                      ((J.over U).sheafifiedRepresentableMap g₀)).hom.app (op V)
                  (J.uliftSheafifiedRepresentableHomEquiv
                    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
                      ((J.over U).sheafifiedRepresentable X₀))
                    V
                    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                      X₀).hom) =
                J.uliftSheafifiedRepresentableHomEquiv
                  (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
                    ((J.over U).sheafifiedRepresentable (Over.mk f)))
                  V
                  ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                      X₀).hom ≫
                    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
                      ((J.over U).sheafifiedRepresentableMap g₀)) := by
                        simpa [X₀, g₀] using
                          (relocalized_slice_representable_map_section (J := J) (U := U)
                            (g := g₀)).symm
              _ =
                J.uliftSheafifiedRepresentableHomEquiv
                  (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
                    ((J.over U).sheafifiedRepresentable (Over.mk f)))
                  V
                  (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                    (Over.mk f)).hom := by
                      -- Normalize the final `eqToHom` transport before evaluating the section.
                      exact congrArg
                        (J.uliftSheafifiedRepresentableHomEquiv
                          (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
                            ((J.over U).sheafifiedRepresentable (Over.mk f)))
                          V)
                        (by
                          simpa [X₀, g₀] using
                            (continuous_sheafified_representable_iso_over_map_terminal_transport
                              (J := J)
                              (U := U)
                              (V := V)
                              (f := f)))

/-- Helper for Lemma 7.25.9: evaluating the terminal component of `Functor.sheafPullbackComp'` on
the canonical `V`-section yields the canonical section of the localized representable `h[f]^#`. -/
private theorem relocalization_terminal_pullback_component_section :
    J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).hom ≫
          (Functor.sheafPullbackComp'
              (J.over V) (J.over U) J (Over.map f) (Over.forget U)
              (Over.mapForget f)).inv.app
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                  eqToHom (over_map_obj_terminal_eq (f := f))))) =
      J.uliftSheafifiedRepresentableHomEquiv
        (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
          ((J.over U).sheafifiedRepresentable (Over.mk f)))
        V
        (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk f)).hom := by
  -- Route correction: evaluate the terminal component of `Functor.sheafPullbackComp'` on the
  -- canonical `V`-section, rewrite both sides to the sigma pair `⟨f, Over.homMk f⟩`, and use the
  -- same transport normalization strategy as in
  -- `continuous_sheafified_representable_iso_homMk_naturality`.
  exact sheafPullbackComp_terminal_left_section_sigma_pair
    (J := J) (U := U) (V := V) (f := f)

/-- Helper for Lemma 7.25.9: after identifying the pulled-back terminal slice representables with
`h[V]^#` and the relocalized representable `h_f^#`, the terminal component of
`Functor.sheafPullbackComp'` agrees with the canonical comparison for `Over.mk f`. -/
private theorem relocalization_terminal_pullback_comparison :
    (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
        (Over.mk (𝟙 V))).hom ≫
      (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)).inv.app
        ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
            (Over.mk (𝟙 V))).inv ≫
          (J.over U).sheafifiedRepresentableMap
            (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
              eqToHom (over_map_obj_terminal_eq (f := f)))) =
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
      (Over.mk f)).hom := by
  -- Compare the two morphisms after evaluating them at the canonical `V`-section of `h[V]^#`.
  apply (J.uliftSheafifiedRepresentableHomEquiv
    (((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
      ((J.over U).sheafifiedRepresentable (Over.mk f))) V).injective
  simpa using relocalization_terminal_pullback_component_section (J := J) (f := f)

/-- Helper for Lemma 7.25.9: after identifying the pulled-back terminal slice representables with
`h[V]^#` and `h[U]^#`, the slice morphism `Over.homMk f` becomes the global map
`J.sheafifiedRepresentableMap f`. -/
private theorem continuous_sheafified_representable_iso_over_homMk :
    (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk f)).hom ≫
      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
        ((J.over U).sheafifiedRepresentableMap
          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).symm.hom =
    J.sheafifiedRepresentableMap f := by
  -- Compare both morphisms on the canonical `V`-section of `h[V]^#[J]`.
  -- Route correction: instead of proving the owner-level morphism equality first, evaluate both
  -- sides on the canonical `V`-section and use the already isolated section comparison.
  apply (J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) V).injective
  let FU :=
    ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj
      ((J.over U).sheafifiedRepresentable (Over.mk (𝟙 U)))
  let secU :=
    J.uliftSheafifiedRepresentableHomEquiv FU U
      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
        (Over.mk (𝟙 U))).hom
  have hleft :
      J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) V
          ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk f)).hom ≫
            ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
              ((J.over U).sheafifiedRepresentableMap
                (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
            (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk (𝟙 U))).symm.hom) =
        ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom).hom.app (op V)
          (FU.obj.map f.op secU) := by
    -- Evaluate the final composite, then rewrite the middle section via the `Over.homMk f`
    -- comparison.
    rw [J.uliftSheafifiedRepresentableHomEquiv_comp]
    simpa [FU, secU] using
      congrArg
        (((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom).hom.app (op V))
        (continuous_sheafified_representable_iso_homMk_section (J := J) (f := f))
  have hterminalU :
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).symm.hom).hom.app (op U) secU =
        J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
          (𝟙 (J.sheafifiedRepresentable U)) := by
    -- Collapse the terminal comparison on the `U`-section.
    have hcompU :
        J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
            ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                (Over.mk (𝟙 U))).hom ≫
              (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                (Over.mk (𝟙 U))).symm.hom) =
          ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk (𝟙 U))).symm.hom).hom.app (op U) secU := by
      simpa [secU, Category.assoc] using
        (J.uliftSheafifiedRepresentableHomEquiv_comp
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).hom
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom)
    exact hcompU.symm.trans (terminal_comparison_canonical_section (J := J) (U := U))
  have hnatV :
      ((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).symm.hom).hom.app (op V)
        (FU.obj.map f.op secU) =
      (J.sheafifiedRepresentable U).obj.map f.op
        (((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom).hom.app (op U) secU) := by
    -- Use naturality of the inverse comparison map itself.
    simpa [FU, secU] using congrFun
      (((continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
          (Over.mk (𝟙 U))).symm.hom).hom.naturality f.op) secU
  have hrestrict :
      (J.sheafifiedRepresentable U).obj.map f.op
        (J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) U
          (𝟙 (J.sheafifiedRepresentable U))) =
      J.uliftSheafifiedRepresentableHomEquiv (J.sheafifiedRepresentable U) V
        (J.sheafifiedRepresentableMap f) := by
    simpa [Category.comp_id, GrothendieckTopology.sheafifiedRepresentableMap,
      GrothendieckTopology.sheafifiedRepresentableFunctor] using
      (terminal_comparison_canonical_section_restrict
        (J := J) (U := U) (V := V) (f := f)).symm
  exact hleft.trans <| hnatV.trans <| by
    rw [hterminalU]
    exact hrestrict

-- Proof sketch: the component of `Functor.sheafPullbackComp'` at `𝒢` identifies
-- `j_{U!}(j_! 𝒢)` with `j_{V!} 𝒢`; under `J.representableLocalizationComparison`, this upgrades
-- the raw commutative square to an isomorphism in the slice category over `h_U^#`, comparing
-- relocalization lower shriek with `Over.map (J.sheafifiedRepresentableMap f)`. The comparison is
-- the slice specialization of the canonical owner `Functor.sheafPullbackComp'`.
/-- The canonical comparison square in `Sh(C, J)` upgrading the relocalization lower-shriek
comparison to a morphism in the slice over `h_U^#`. -/
private theorem relocalization_lower_shriek_over_map_square
    (𝒢 : Sheaf (J.over V) (Type (max u v))) :
    CommSq
      ((Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
            (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
                (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
              (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).inv.app 𝒢)
      (J.representableLocalizationHom V 𝒢)
      (J.representableLocalizationHom U
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢))
      (J.sheafifiedRepresentableMap f) := by
  let e :
      (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
          (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
        (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J :=
    Functor.sheafPullbackComp'
      (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f)
  let η :
      𝒢 ⟶ (J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)) :=
    (localized_identity_sheafifiedRepresentable_isTerminal (J := J) V).from 𝒢
  -- Reduce the general sheaf to the terminal representable using naturality against the unique
  -- map `η : 𝒢 ⟶ h_{V/V}^#`.
  refine CommSq.mk ?_
  have hnat :
      ((Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).map η ≫
          e.inv.app ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) =
        e.inv.app 𝒢 ≫
          ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
            (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η := by
    simpa [e] using e.inv.naturality η
  have hleft :
      ((Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).map η ≫
          J.representableLocalizationHom V
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) =
        J.representableLocalizationHom V 𝒢 := by
    -- Read off the commutativity condition of `representableLocalizationComparison.map η`.
    simpa [GrothendieckTopology.representableLocalizationComparison, Functor.toOver_map_left,
      Over.comp_left] using ((J.representableLocalizationComparison V).map η).w
  have hright :
      ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
            (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η ≫
          J.representableLocalizationHom U
            (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))) =
        J.representableLocalizationHom U
          (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢) := by
    -- This is the same `Over`-morphism compatibility after relocalizing along `f`.
    simpa [GrothendieckTopology.representableLocalizationComparison, Functor.toOver_map_left,
      Over.comp_left, Functor.comp_map] using
      ((J.representableLocalizationComparison U).map
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).map η)).w
  have hterminal_goal :
      e.inv.app ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          J.representableLocalizationHom U
            (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj
              ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V)))) =
        J.representableLocalizationHom V
            ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          J.sheafifiedRepresentableMap f := by
    -- Rewrite both canonical maps so the terminal representable case becomes an explicit
    -- comparison between the two sheafified representable morphisms induced by `Over.homMk f`.
    rw [representableLocalizationHom_terminal (J := J) (U := V)]
    rw [representableLocalizationHom_over_map_terminal (J := J) (f := f)]
    -- Route correction: split the target-side composite into the object-identification step
    -- `((Over.map f).obj (Over.mk (𝟙 V))) = Over.mk f` and the actual slice arrow `Over.homMk f`.
    calc
      e.inv.app ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk (𝟙 U) from
                  eqToHom (over_map_obj_terminal_eq (f := f)) ≫
                    (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f))) ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom =
        e.inv.app ((J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))) ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((continuous_sheafified_representable_iso (Over.map f) (J.over V) (J.over U)
                (Over.mk (𝟙 V))).inv ≫
              (J.over U).sheafifiedRepresentableMap
                (show ((Over.map f).obj (Over.mk (𝟙 V))) ⟶ Over.mk f from
                  eqToHom (over_map_obj_terminal_eq (f := f))) ≫
              (J.over U).sheafifiedRepresentableMap
                (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom := by
              simp [Functor.map_comp, Category.assoc]
      _ =
        (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).symm.hom ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
              (Over.mk f)).hom ≫
          ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
            ((J.over U).sheafifiedRepresentableMap
              (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
          (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
            (Over.mk (𝟙 U))).symm.hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun x ↦
                    (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
                        (Over.mk (𝟙 V))).symm.hom ≫ x ≫
                      ((Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map
                        ((J.over U).sheafifiedRepresentableMap
                          (show Over.mk f ⟶ Over.mk (𝟙 U) from Over.homMk f)) ≫
                      (continuous_sheafified_representable_iso (Over.forget U) (J.over U) J
                        (Over.mk (𝟙 U))).symm.hom)
                  (relocalization_terminal_pullback_comparison (J := J) (f := f))
      _ =
        (continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
            (Over.mk (𝟙 V))).symm.hom ≫
          J.sheafifiedRepresentableMap f := by
            simpa [Category.assoc] using
              congrArg
                ((continuous_sheafified_representable_iso (Over.forget V) (J.over V) J
                    (Over.mk (𝟙 V))).symm.hom ≫ ·)
                (continuous_sheafified_representable_iso_over_homMk (J := J) (f := f))
  let G₀ : Sheaf (J.over V) (Type (max u v)) :=
    (J.over V).sheafifiedRepresentable (Over.mk (𝟙 V))
  let pulledG₀ : Sheaf (J.over U) (Type (max u v)) :=
    ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj G₀
  let lowerη :
      ((Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).obj 𝒢 ⟶
        ((Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).obj G₀ :=
    ((Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).map η
  let upperη :
      (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
            (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj 𝒢) ⟶
        (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
            (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).obj G₀) :=
    ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
      (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J).map η
  have hnat' :
      (e.inv.app 𝒢 ≫ upperη) ≫ J.representableLocalizationHom U pulledG₀ =
        (lowerη ≫ e.inv.app G₀) ≫ J.representableLocalizationHom U pulledG₀ := by
    simpa [lowerη, upperη, G₀, pulledG₀, Category.assoc] using
      congrArg (fun k ↦ k ≫ J.representableLocalizationHom U pulledG₀) hnat.symm
  calc
    e.inv.app 𝒢 ≫
        J.representableLocalizationHom U
          (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢) =
      e.inv.app 𝒢 ≫
        (upperη ≫
          J.representableLocalizationHom U pulledG₀) := by
            rw [hright]
    _ =
      (e.inv.app 𝒢 ≫ upperη) ≫ J.representableLocalizationHom U pulledG₀ := by
              simp [upperη, Category.assoc]
    _ =
      lowerη ≫ e.inv.app G₀ ≫ J.representableLocalizationHom U pulledG₀ := by
              simpa [Category.assoc] using hnat'
    _ =
      lowerη ≫ (e.inv.app G₀ ≫ J.representableLocalizationHom U pulledG₀) := by
                simp [G₀]
    _ =
      lowerη ≫
        (J.representableLocalizationHom V G₀ ≫ J.sheafifiedRepresentableMap f) := by
            exact congrArg (lowerη ≫ ·) hterminal_goal
    _ = J.representableLocalizationHom V 𝒢 ≫ J.sheafifiedRepresentableMap f := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ J.sheafifiedRepresentableMap f) hleft

/-- Lemma 7.25.9 (2): under the equivalences
`Sh(C/V) ≌ Sh(C, J) / h_V^#` and `Sh(C/U) ≌ Sh(C, J) / h_U^#`, the relocalization lower shriek is
the slice functor `Over.map (h_V^# ⟶ h_U^#)`. -/
noncomputable def relocalization_lower_shriek_over_map :
    (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
        J.representableLocalizationComparison U ≅
      J.representableLocalizationComparison V ⋙
        Over.map (J.sheafifiedRepresentableMap f) :=
  NatIso.ofComponents
    (fun 𝒢 ↦
      let e :=
        (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
            (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
                (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
              (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).app 𝒢
      -- The left component is the owner comparison `j_{U!} j_! 𝒢 ≅ j_{V!} 𝒢`; the square above
      -- upgrades it to an isomorphism in the slice over `h[U]^#[J]`.
      Over.isoMk e <| by
        change
          e.hom ≫
              (J.representableLocalizationHom V 𝒢 ≫ J.sheafifiedRepresentableMap f) =
            J.representableLocalizationHom U
              (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢)
        have h :
            e.inv ≫
                J.representableLocalizationHom U
                  (((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U)).obj 𝒢) =
              J.representableLocalizationHom V 𝒢 ≫ J.sheafifiedRepresentableMap f := by
          simpa [e] using (relocalization_lower_shriek_over_map_square J f 𝒢).w
        have h := congrArg (e.hom ≫ ·) h
        simpa [Category.assoc, Iso.hom_inv_id_assoc] using h.symm)
    (by
      intro 𝒢 𝒢' η
      -- After projecting to left components, naturality is exactly the naturality of the owner
      -- comparison `Functor.sheafPullbackComp'`.
      apply Over.OverMorphism.ext
      simpa [GrothendieckTopology.representableLocalizationComparison, Functor.toOver_map_left,
        Over.comp_left] using
        (Functor.sheafPullbackComp'
          (J.over V) (J.over U) J (Over.map f) (Over.forget U) (Over.mapForget f) :
            (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⋙
                (Over.forget U).sheafPullback (Type (max u v)) (J.over U) J ≅
              (Over.forget V).sheafPullback (Type (max u v)) (J.over V) J).hom.naturality η)

end LowerShriek

-- Proof sketch: transport the right-adjoint description of relocalization across the slice
-- equivalences of Lemma 7.25.4. The resulting object in `Sh(C, J) / h_V^#` is exactly the
-- canonical pullback object along `J.sheafifiedRepresentableMap f`.
/-- Helper for Lemma 7.25.9: conjugating the lower-shriek comparison by the equivalences from
Lemma 7.25.4 produces the left-adjoint comparison needed for right-adjoint uniqueness. -/
private noncomputable def relocalization_lower_shriek_over_map_conjugate
    [(J.representableLocalizationComparison V).IsEquivalence]
    [(J.representableLocalizationComparison U).IsEquivalence] :
    (J.representableLocalizationComparison V).asEquivalence.inverse ⋙
        (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ≅
      Over.map (J.sheafifiedRepresentableMap f) ⋙
        (J.representableLocalizationComparison U).asEquivalence.inverse := by
  let comparisonV := (J.representableLocalizationComparison V).asEquivalence
  let comparisonU := (J.representableLocalizationComparison U).asEquivalence
  let lowerShriekIso := J.relocalization_lower_shriek_over_map f
  -- Route correction: replace the non-definitional object equality route by conjugating the
  -- left-adjoint comparison through the two equivalences.
  exact
    (Functor.rightUnitor (comparisonV.inverse ⋙
      (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U))).symm ≪≫
    Functor.isoWhiskerLeft
      (comparisonV.inverse ⋙
        (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U))
      comparisonU.unitIso ≪≫
    (Functor.associator
      (comparisonV.inverse ⋙
        (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U))
      comparisonU.functor comparisonU.inverse).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator comparisonV.inverse
        ((Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U))
        comparisonU.functor).symm
      comparisonU.inverse ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft comparisonV.inverse lowerShriekIso)
      comparisonU.inverse ≪≫
    Functor.isoWhiskerLeft comparisonV.inverse
      (Functor.associator (J.representableLocalizationComparison V)
        (Over.map (J.sheafifiedRepresentableMap f))
        comparisonU.inverse) ≪≫
    Functor.associator comparisonV.inverse
      (J.representableLocalizationComparison V)
      (Over.map (J.sheafifiedRepresentableMap f) ⋙ comparisonU.inverse) ≪≫
    comparisonV.invFunIdAssoc
      (Over.map (J.sheafifiedRepresentableMap f) ⋙ comparisonU.inverse)

/-- Helper for Lemma 7.25.9: the relocalization inverse image is identified with slice pullback by
uniqueness of right adjoints after conjugating clause `(2)`. -/
private noncomputable def relocalization_inverse_image_over_pullback_iso :
    J.overMapPullback (Type (max u v)) f ⋙ J.representableLocalizationComparison V ≅
      J.representableLocalizationComparison U ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) := by
  haveI : (J.representableLocalizationComparison V).IsEquivalence :=
    J.representableLocalizationComparison_isEquivalence V
  haveI : (J.representableLocalizationComparison U).IsEquivalence :=
    J.representableLocalizationComparison_isEquivalence U
  let comparisonV := (J.representableLocalizationComparison V).asEquivalence
  let comparisonU := (J.representableLocalizationComparison U).asEquivalence
  let localizedAdj :
      comparisonV.inverse ⋙
          (Over.map f).sheafPullback (Type (max u v)) (J.over V) (J.over U) ⊣
        J.overMapPullback (Type (max u v)) f ⋙ comparisonV.functor :=
    (comparisonV.symm.toAdjunction).comp
      ((Over.map f).sheafAdjunctionContinuous (Type (max u v)) (J.over V) (J.over U))
  let globalAdj :
      Over.map (J.sheafifiedRepresentableMap f) ⋙ comparisonU.inverse ⊣
        comparisonU.functor ⋙ Over.pullback (J.sheafifiedRepresentableMap f) :=
    (Over.mapPullbackAdj (J.sheafifiedRepresentableMap f)).comp
      comparisonU.symm.toAdjunction
  let localizedAdj' :
      Over.map (J.sheafifiedRepresentableMap f) ⋙ comparisonU.inverse ⊣
        J.overMapPullback (Type (max u v)) f ⋙ comparisonV.functor :=
    localizedAdj.ofNatIsoLeft (J.relocalization_lower_shriek_over_map_conjugate f)
  -- Both functors are right adjoints to the conjugated lower-shriek comparison from clause `(2)`.
  exact Adjunction.rightAdjointUniq localizedAdj' globalAdj

/-- Lemma 7.25.9 (1): under the equivalences
`Sh(C/U) ≌ Sh(C, J) / h_U^#` and `Sh(C/V) ≌ Sh(C, J) / h_V^#`, the relocalization inverse image is
pullback along `h_V^# ⟶ h_U^#`. -/
noncomputable def relocalization_inverse_image_over_pullback :
    J.overMapPullback (Type (max u v)) f ⋙ J.representableLocalizationComparison V ≅
      J.representableLocalizationComparison U ⋙
        Over.pullback (J.sheafifiedRepresentableMap f) :=
  J.relocalization_inverse_image_over_pullback_iso f

end

end CategoryTheory.GrothendieckTopology

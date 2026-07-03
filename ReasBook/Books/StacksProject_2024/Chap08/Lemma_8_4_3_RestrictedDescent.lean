import StacksProject_2024.Chap08.Lemma_8_4_3_PullbackComparison
import StacksProject_2024.Chap08.Lemma_8_4_3_AmbientIsoClosure
import StacksProject_2024.Chap08.Lemma_8_4_3.RestrictedDescentForward

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: a restricted descent datum over the cover `S` determines an ambient
descent datum whose components land in the corresponding fiberwise `isoClosure` of `P`. -/
noncomputable def restricted_cover_descent_isoClosure_obj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f))) :
    (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).FullSubcategory := by
  refine ⟨?_, ?_⟩
  · refine
      { obj := fun I ↦
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj (D.obj I)).obj
        hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
        pullHom_hom := fun Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦ by
          -- The overlap map is already packaged as the comparison-conjugated shell in the forward
          -- helper file, so its pullback law is delegated there unchanged.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_pullHom_hom
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y' := Y') (Y := Y) (I₁ := I₁) (I₂ := I₂)
              (g := g) (q := q) (q' := q') (hq := hq) (f₁ := f₁) (f₂ := f₂)
              (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
              (hgf₁ := hgf₁) (hgf₂ := hgf₂)
        hom_self := fun Y q I g hg ↦ by
          -- On equal legs, the comparison shell cancels to the identity in the helper file.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_self
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y := Y) (I := I) (q := q) (g := g) (hg := hg)
        hom_comp := fun Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦ by
          -- The cocycle law for the comparison-conjugated overlap maps is likewise already
          -- proved in the forward helper file.
          simpa using
            restricted_cover_descent_isoClosure_obj_hom_comp
              (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
              (Y := Y) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
              (q := q) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
              (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }
  · intro I
    -- Each component is already strict in the inverse-image full subcategory, hence belongs to
    -- the ambient `isoClosure` target via the tautological identity isomorphism.
    exact
      ObjectProperty.le_isoClosure
        (P := P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X))
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
          (D.obj I)).obj)
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
          (D.obj I)).property)

/-- Helper for Lemma 8.4.3: the source-faithful forward bridge sends restricted fixed-cover
descent data to the ambient componentwise-`isoClosure` target objectwise. -/
noncomputable def restricted_cover_descent_to_isoClosure
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)) ⥤
      (cover_componentwise_isoClosure_property (J := J) (p := p) (P := P) S).FullSubcategory where
  obj D :=
    restricted_cover_descent_isoClosure_obj (J := J) (p := p) (P := P) hpullback S D
  map {D₁ D₂} φ :=
    ObjectProperty.homMk
      { hom := fun I ↦
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
            (φ.hom I)).hom
        comm := by
          intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
          -- The morphism compatibility is the corresponding shell naturality from the forward
          -- helper file.
          simpa using
            restricted_cover_descent_to_isoClosure_map_comm_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    -- The forward bridge functor acts componentwise, so identities are preserved strictly.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl
  map_comp φ ψ := by
    -- Composition is computed componentwise in each overlap fiber.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl


-- Route correction: `PullbackComparison.lean` is the canonical owner of the inclusion/pullback
-- comparison API. This file now reuses those declarations instead of rebuilding them in a
-- second elaboration context before the restricted descent-equivalence construction.

/-- Helper for Lemma 8.4.3: the reverse overlap morphism is first defined in the inverse-image
full subcategory, where the chosen component isomorphisms and the pullback-comparison maps live
without extra coercions. -/
noncomputable def restricted_cover_overlap_hom_in_inverseImage_fiber
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.obj
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
            (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))) ⟶
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.obj
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
            (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))) :=
  ObjectProperty.homMk <|
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))).hom ≫
      (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_component_total_iso
          (J := J) (p := p) (P := P) S D I₁).hom) ≫
      D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_cover_component_total_iso
          (J := J) (p := p) (P := P) S D I₂).inv) ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₂
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))).inv

/-- Helper for Lemma 8.4.3: the restricted overlap morphism is the image of the inverse-image
overlap morphism under the ambient-to-restricted fiber bridge. -/
noncomputable def restricted_cover_isoClosure_to_descent_obj_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))) ⟶
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.obj
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
          (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))) :=
  (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) Y).map
    (restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)

/-- Helper for Lemma 8.4.3: the reverse overlap morphisms still need the single vertical
pullback-compatibility calculation from the source proof, now isolated in the inverse-image
category. -/
theorem restricted_cover_isoClosure_to_descent_obj_pullHom_hom
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (restricted_cover_isoClosure_to_descent_obj_hom
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  sorry

/-- Helper for Lemma 8.4.3: the reverse overlap map is the identity on equal legs once the
component conjugations are normalized. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_self
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I : S.Arrow} (g : Y ⟶ I.Y)
    (hg : g ≫ I.f = q := by cat_disch) :
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q g g hg hg =
      𝟙 _ := by
  let E := fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y
  let FY := E.functor
  letI : FY.Faithful := E.faithful_functor
  apply FY.map_injective
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q g g hg hg) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q g g hg hg by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q g g hg hg)]
  change restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q g g hg hg = 𝟙 _
  apply ObjectProperty.hom_ext
  let Fg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor
  let c :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I))
  let t := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [D.obj.hom_self q g hg]
  have ht : Fg.map t.hom ≫ Fg.map t.inv = 𝟙 _ := by
    simpa using (Fg.mapIso t).hom_inv_id
  have hself :
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv = 𝟙 _ := by
    calc
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv =
          c.hom ≫ Fg.map t.hom ≫ Fg.map t.inv ≫ c.inv := by
            simp [Category.assoc]
      _ = c.hom ≫ (Fg.map t.hom ≫ Fg.map t.inv) ≫ c.inv := by
            simp [Category.assoc]
      _ = c.hom ≫ 𝟙 _ ≫ c.inv := by
            exact congrArg (fun k ↦ c.hom ≫ k ≫ c.inv) ht
      _ = 𝟙 _ := by
            simp
  simpa only [ObjectProperty.homMk, Fg, c, t, restricted_cover_component_total_iso_hom,
    restricted_cover_component_total_iso_inv, Functor.map_comp] using hself

/-- Helper for Lemma 8.4.3: the reverse overlap maps satisfy the cocycle relation after the same
conjugation normal-form reduction. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_comp
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ I₃ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y) (f₃ : Y ⟶ I₃.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (hf₃ : f₃ ≫ I₃.f = q := by cat_disch) :
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
    restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ := by
  let E := fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y
  let FY := E.functor
  letI : FY.Faithful := E.faithful_functor
  apply FY.map_injective
  change
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂) ≫
        FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃) =
      FY.map
        (restricted_cover_isoClosure_to_descent_obj_hom
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃)
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)]
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃)]
  rw [show
      FY.map
          (restricted_cover_isoClosure_to_descent_obj_hom
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃) =
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃ by
      exact
        fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
          (p := p) (P := P) Y
          (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃)]
  change
      restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        restricted_cover_overlap_hom_in_inverseImage_fiber
          (J := J) (p := p) (P := P) hpullback S D q f₂ f₃ hf₂ hf₃ =
      restricted_cover_overlap_hom_in_inverseImage_fiber
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₃ hf₁ hf₃
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  rw [restricted_cover_overlap_hom_in_inverseImage_fiber]
  let F₁ := ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor
  let F₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let F₃ := ((canonicalFiberPseudofunctor p).map f₃.op.toLoc).toFunctor
  let c₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))
  let c₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))
  let c₃ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₃
      ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₃.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₃))
  let t₁ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₁
  let t₂ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₂
  let t₃ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₃
  have ht₂ : F₂.map t₂.inv ≫ F₂.map t₂.hom = 𝟙 _ := by
    simpa using (F₂.mapIso t₂).inv_hom_id
  simpa [ObjectProperty.homMk, F₁, F₂, F₃, c₁, c₂, c₃, t₁, t₂, t₃,
    restricted_cover_component_total_iso_hom, restricted_cover_component_total_iso_inv,
    Functor.map_comp, Category.assoc] using
    calc
      (c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫ F₂.map t₂.inv ≫ c₂.inv) ≫
          (c₂.hom ≫ F₂.map t₂.hom ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv) =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
          (F₂.map t₂.inv ≫ F₂.map t₂.hom) ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫
          F₃.map t₃.inv ≫ c₃.inv := by
            simp [Category.assoc]
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
          𝟙 _ ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv := by
            exact
              congrArg
                (fun k ↦
                  c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
                    k ≫ D.obj.hom q f₂ f₃ hf₂ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv)
                ht₂
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫
          (D.obj.hom q f₁ f₂ hf₁ hf₂ ≫ D.obj.hom q f₂ f₃ hf₂ hf₃) ≫
          F₃.map t₃.inv ≫ c₃.inv := by
            simp [Category.assoc]
      _ =
        c₁.hom ≫ F₁.map t₁.hom ≫ D.obj.hom q f₁ f₃ hf₁ hf₃ ≫ F₃.map t₃.inv ≫ c₃.inv := by
            exact
              congrArg
                (fun k ↦ c₁.hom ≫ F₁.map t₁.hom ≫ k ≫ F₃.map t₃.inv ≫ c₃.inv)
                (D.obj.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)

/-- Helper for Lemma 8.4.3: strictify an ambient fixed-cover object in the componentwise
`isoClosure` target to a restricted descent datum by choosing strict representatives of its cover
components. -/
noncomputable def restricted_cover_isoClosure_to_descent_obj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)) :=
  { obj := fun I ↦
      (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I)
    hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
      restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
    pullHom_hom := fun Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
      restricted_cover_isoClosure_to_descent_obj_pullHom_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y' := Y') (Y := Y) (g := g) (q := q) (q' := q') (hq := hq)
        (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
        (hgf₁ := hgf₁) (hgf₂ := hgf₂)
    hom_self := fun Y q I g hg ↦
      restricted_cover_isoClosure_to_descent_obj_hom_self
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y := Y) (q := q) (I := I) (g := g) (hg := hg)
    hom_comp := fun Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
      restricted_cover_isoClosure_to_descent_obj_hom_comp
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
        (Y := Y) (q := q) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
        (f₁ := f₁) (f₂ := f₂) (f₃ := f₃) (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }

end RestrictedFibered

end

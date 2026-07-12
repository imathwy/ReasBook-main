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
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
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
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
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

/-- Helper for Chap08 Lemma 8 4 3 RestrictedDescent: forgetting the restricted reverse
overlap morphism returns its defining inverse-image overlap morphism. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_forward_map
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y).functor.map
        (restricted_cover_isoClosure_to_descent_obj_hom
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂) =
      restricted_cover_overlap_hom_in_inverseImage_fiber
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ := by
  -- The restricted morphism was defined by applying the inverse equivalence to the
  -- inverse-image overlap, so the functor-inverse map identity removes that round trip.
  exact
    fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
      (p := p) (P := P) Y
      (φ := restricted_cover_overlap_hom_in_inverseImage_fiber
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 4 3 RestrictedDescent: transporting an inverse-image morphism to
the restricted fiber and then pulling it back returns the ambient pullback shell conjugated by the
restricted/ambient comparison maps. -/
private theorem restricted_pullback_preimage_component_map_normal_form
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U)
    {x₁ x₂ : (P.ι ⋙ p).Fiber U}
    (ψ : (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x₁ ⟶
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x₂) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) V).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map ψ))).hom =
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f x₁).hom ≫
        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map ψ.hom) ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f x₂).inv := by
  let φ : x₁ ⟶ x₂ :=
    (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map ψ
  let e₁ := restricted_pullback_vs_ambient_pullback_comparison
    (J := J) (p := p) (P := P) hpullback f x₁
  let e₂ := restricted_pullback_vs_ambient_pullback_comparison
    (J := J) (p := p) (P := P) hpullback f x₂
  have hnat :
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) V).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map φ)).hom ≫
        e₂.hom =
      e₁.hom ≫
        ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ).hom := by
    -- Use the inverse-side naturality square for the inclusion comparison, translated through
    -- the local restricted/ambient comparison isomorphism.
    simpa [φ, e₁, e₂, restricted_pullback_vs_ambient_pullback_comparison] using
      fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
        (J := J) (p := p) (P := P) (hpullback := hpullback) (f := f) (φ := φ)
  have hround :
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ = ψ := by
    -- The inverse-image/restricted-fiber equivalence is strict on morphisms after one roundtrip.
    change
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map ψ) =
        ψ
    exact
      fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
        (p := p) (P := P) U (φ := ψ)
  have hmap :
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ).hom =
        ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map ψ.hom := by
    -- Apply the ambient pullback functor to the strict roundtrip identity on the middle
    -- inverse-image morphism.
    simpa using
      congrArg
        (fun η ↦ ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map η.hom)
        hround
  have hnat_post :
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) V).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map φ)).hom =
        e₁.hom ≫
          ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
            ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ).hom ≫
          e₂.inv := by
    -- Postcompose by the inverse comparison and cancel the right boundary.
    have hnat' := congrArg (fun k ↦ k ≫ e₂.inv) hnat
    simpa [Category.assoc, e₂] using hnat'
  calc
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) V).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f.op.toLoc).toFunctor.map
            ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) U).map ψ))).hom =
      e₁.hom ≫
        ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ).hom ≫
        e₂.inv := by
          simpa [φ] using hnat_post
    _ =
        e₁.hom ≫
          ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map ψ.hom ≫
          e₂.inv := by
            rw [hmap]

/-- Helper for Chap08 Lemma 8 4 3 RestrictedDescent: a functor maps a fivefold composite to the
corresponding fivefold composite of mapped arrows. -/
private theorem functor_map_fivefold_comp
    {D E : Type*} [Category D] [Category E] (F : D ⥤ E)
    {A B C D' E' F' : D} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D')
    (i : D' ⟶ E') (j : E' ⟶ F') :
    F.map (f ≫ g ≫ h ≫ i ≫ j) =
      F.map f ≫ F.map g ≫ F.map h ≫ F.map i ≫ F.map j := by
  -- Split the visible fivefold composite into binary functoriality steps.
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]

/-- Chap08 Lemma 8 4 3 RestrictedDescent: the reverse overlap morphisms satisfy the
vertical pullback-compatibility calculation from the source proof, isolated in the inverse-image
category. -/
theorem restricted_cover_isoClosure_to_descent_obj_pullHom_hom
  (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
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
  have hgf₁base : gf₁ ≫ I₁.f = q' := by
    rw [← hq, ← hgf₁, Category.assoc, hf₁]
  have hgf₂base : gf₂ ≫ I₂.f = q' := by
    rw [← hq, ← hgf₂, Category.assoc, hf₂]
  let E := fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) Y'
  let FY' := E.functor
  letI : FY'.Faithful := E.faithful_functor
  -- Map through the faithful restricted/inverse-image fiber equivalence; the target side
  -- becomes the defining inverse-image overlap by the bridge lemma above.
  apply FY'.map_injective
  rw [restricted_cover_isoClosure_to_descent_obj_hom_forward_map
    (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
    (q := q') (I₁ := I₁) (I₂ := I₂) (f₁ := gf₁) (f₂ := gf₂)
    (hf₁ := hgf₁base) (hf₂ := hgf₂base)]
  apply ObjectProperty.hom_ext
  -- Unfold the restricted `pullHom` once and name the three pieces that Agent C isolated:
  -- the restricted left boundary, the pulled middle overlap, and the restricted right boundary.
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  let x₁ :=
    ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).obj
      (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₁))
  let x₂ :=
    ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).obj
      (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I₂))
  let y₁ :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.obj x₁)
  let y₂ :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.obj x₂)
  let left :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app x₁)
  let middle :=
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).map g.op.toLoc).toFunctor.map
      (restricted_cover_isoClosure_to_descent_obj_hom
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
  let right :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app x₂)
  let Fg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor
  let cg₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g y₁
  let cg₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback g y₂
  let ψ :=
    restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
  change (FY'.map (left ≫ middle ≫ right)).hom =
    (restricted_cover_overlap_hom_in_inverseImage_fiber
      (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
      hgf₁base hgf₂base).hom
  -- Route correction: the earlier all-in-one transport shell left the same comparison
  -- mismatch; split the mapped pullback shell first, prove the middle transport, and leave only
  -- the two one-leg boundary adapters.
  have hsplit :
      (FY'.map (left ≫ middle ≫ right)).hom =
        (FY'.map left).hom ≫ (FY'.map middle).hom ≫ (FY'.map right).hom := by
    -- Split only this visible threefold functorial image; this avoids broad rewriting under
    -- the full-subcategory `.hom` projection.
    exact congrArg (fun k ↦ k.hom) (functor_map_threefold_comp FY' left middle right)
  have hmiddle :
      (FY'.map middle).hom = cg₁.hom ≫ Fg.map ψ.hom ≫ cg₂.inv := by
    -- The middle factor is exactly the already-proved inverse-image/restricted-fiber transport
    -- normal form for pulling an inverse-image morphism back along `g`.
    simpa [FY', E, middle, ψ, cg₁, cg₂, Fg, y₁, y₂,
      restricted_cover_isoClosure_to_descent_obj_hom] using
      restricted_pullback_preimage_component_map_normal_form
        (J := J) (p := p) (P := P) (hpullback := hpullback) (f := g)
        (x₁ := y₁) (x₂ := y₂) (ψ := ψ)
  rw [hsplit, hmiddle]
  let cf₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ x₁
  let cf₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ x₂
  let cgf₁ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback gf₁ x₁
  let cgf₂ :=
    restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback gf₂ x₂
  let t₁ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₁
  let t₂ := restricted_cover_component_total_iso (J := J) (p := p) (P := P) S D I₂
  let Ff₁ := ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor
  let Ff₂ := ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor
  let Fgf₁ := ((canonicalFiberPseudofunctor p).map gf₁.op.toLoc).toFunctor
  let Fgf₂ := ((canonicalFiberPseudofunctor p).map gf₂.op.toLoc).toFunctor
  let leftAmbient :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
        (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app (D.obj.obj I₁))
  let rightAmbient :=
    (((canonicalFiberPseudofunctor p).mapComp'
        f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
        (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app (D.obj.obj I₂))
  have hψ :
      Fg.map ψ.hom =
        Fg.map cf₁.hom ≫ Fg.map (Ff₁.map t₁.hom) ≫
          Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫
          Fg.map (Ff₂.map t₂.inv) ≫ Fg.map cf₂.inv := by
    -- Unfold the inverse-image overlap once, then split only the visible fivefold mapped
    -- composite.
    change
      Fg.map (cf₁.hom ≫ Ff₁.map t₁.hom ≫ D.obj.hom q f₁ f₂ hf₁ hf₂ ≫
          Ff₂.map t₂.inv ≫ cf₂.inv) =
        Fg.map cf₁.hom ≫ Fg.map (Ff₁.map t₁.hom) ≫
          Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫
          Fg.map (Ff₂.map t₂.inv) ≫ Fg.map cf₂.inv
    exact
      functor_map_fivefold_comp Fg cf₁.hom (Ff₁.map t₁.hom)
        (D.obj.hom q f₁ f₂ hf₁ hf₂) (Ff₂.map t₂.inv) cf₂.inv
  have hambient :
      leftAmbient ≫ Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫ rightAmbient =
        D.obj.hom q' gf₁ gf₂ hgf₁base hgf₂base := by
    -- The central three factors are exactly the ambient descent datum's pullback law.
    simpa [leftAmbient, rightAmbient, Fg] using
      D.obj.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
  have hboundaries :
      (FY'.map left).hom ≫ (cg₁.hom ≫ Fg.map ψ.hom ≫ cg₂.inv) ≫
          (FY'.map right).hom =
        cgf₁.hom ≫ Fgf₁.map t₁.hom ≫
          (leftAmbient ≫ Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫ rightAmbient) ≫
          Fgf₂.map t₂.inv ≫ cgf₂.inv := by
    -- The inverse-image overlap has been expanded; the remaining work is to move the two
    -- restricted comparison shells across the ambient `mapComp' boundaries.
    rw [hψ]
    let H := fullSubcategory_inclusion_fibredMor (J := J) (p := p) (P := P) hpullback
    let leftAtRestricted :=
      (((canonicalFiberPseudofunctor p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj x₁).obj)
    let rightAtRestricted :=
      (((canonicalFiberPseudofunctor p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj x₂).obj)
    have hleftRaw :
        leftAtRestricted ≫ Fg.map cf₁.inv =
          cgf₁.inv ≫ (FY'.map left).hom ≫ cg₁.hom := by
      -- Translate the owner left-boundary theorem through the local `symm` convention for the
      -- restricted/ambient comparison isomorphisms.
      simpa [H, FY', E, leftAtRestricted, left, Fg, cf₁, cg₁, cgf₁,
        restricted_pullback_vs_ambient_pullback_comparison] using
        FibredCategoryMor.pullHomLeftBoundary H f₁ g gf₁ hgf₁ x₁
    have hleftPre :
        cgf₁.hom ≫ leftAtRestricted ≫ Fg.map cf₁.inv =
          (FY'.map left).hom ≫ cg₁.hom := by
      -- Precompose by the composite-leg comparison to put the source-first prefix in the
      -- orientation used by the expanded goal.
      have h := congrArg (fun k ↦ cgf₁.hom ≫ k) hleftRaw
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h
    have hcf₁ : Fg.map cf₁.inv ≫ Fg.map cf₁.hom = 𝟙 _ := by
      -- The ambient pullback functor preserves the inverse/hom cancellation for `cf₁`.
      calc
        Fg.map cf₁.inv ≫ Fg.map cf₁.hom = Fg.map (cf₁.inv ≫ cf₁.hom) := by
          exact (Fg.map_comp cf₁.inv cf₁.hom).symm
        _ = Fg.map (𝟙 _) := by
          exact congrArg Fg.map cf₁.inv_hom_id
        _ = 𝟙 _ := by
          exact Fg.map_id _
    have hleftBoundary :
        (FY'.map left).hom ≫ cg₁.hom ≫ Fg.map cf₁.hom =
          cgf₁.hom ≫ leftAtRestricted := by
      -- Cancel the remaining mapped `cf₁` inverse/hom pair after the left boundary rewrite.
      have hcancel :
          ((FY'.map left).hom ≫ cg₁.hom) ≫ Fg.map cf₁.hom =
            (cgf₁.hom ≫ leftAtRestricted ≫ Fg.map cf₁.inv) ≫
              Fg.map cf₁.hom := by
        exact congrArg (fun k ↦ k ≫ Fg.map cf₁.hom) hleftPre.symm
      have hcancel' :
          (cgf₁.hom ≫ leftAtRestricted ≫ Fg.map cf₁.inv) ≫
              Fg.map cf₁.hom =
            cgf₁.hom ≫ leftAtRestricted := by
        calc
          (cgf₁.hom ≫ leftAtRestricted ≫ Fg.map cf₁.inv) ≫
              Fg.map cf₁.hom =
            cgf₁.hom ≫ (leftAtRestricted ≫
              (Fg.map cf₁.inv ≫ Fg.map cf₁.hom)) := by
              simp only [Category.assoc]
          _ = cgf₁.hom ≫ (leftAtRestricted ≫ 𝟙 _) := by
              exact congrArg (fun k ↦ cgf₁.hom ≫ (leftAtRestricted ≫ k)) hcf₁
          _ = cgf₁.hom ≫ leftAtRestricted := by
              simp only [Category.comp_id]
      exact (Category.assoc (FY'.map left).hom cg₁.hom (Fg.map cf₁.hom)).symm.trans
        (hcancel.trans hcancel')
    have hrightRaw :
        cg₂.hom ≫ Fg.map cf₂.hom ≫ rightAtRestricted =
          (FY'.map right).hom ≫ cgf₂.hom := by
      -- Translate the owner right-boundary theorem through the same restricted/ambient
      -- comparison convention.
      simpa [H, FY', E, rightAtRestricted, right, Fg, cf₂, cg₂, cgf₂,
        restricted_pullback_vs_ambient_pullback_comparison] using
        FibredCategoryMor.pullHomRightBoundary H f₂ g gf₂ hgf₂ x₂
    have hrightPre :
        Fg.map cf₂.hom ≫ rightAtRestricted =
          cg₂.inv ≫ (FY'.map right).hom ≫ cgf₂.hom := by
      -- Precompose by the `g`-leg comparison inverse so the right boundary can be read
      -- source-first from the expanded goal.
      have h := congrArg (fun k ↦ cg₂.inv ≫ k) hrightRaw
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
    have hcf₂ : Fg.map cf₂.inv ≫ Fg.map cf₂.hom = 𝟙 _ := by
      -- The ambient pullback functor preserves the inverse/hom cancellation for `cf₂`.
      calc
        Fg.map cf₂.inv ≫ Fg.map cf₂.hom = Fg.map (cf₂.inv ≫ cf₂.hom) := by
          exact (Fg.map_comp cf₂.inv cf₂.hom).symm
        _ = Fg.map (𝟙 _) := by
          exact congrArg Fg.map cf₂.inv_hom_id
        _ = 𝟙 _ := by
          exact Fg.map_id _
    have hrightBoundary :
        Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom =
          rightAtRestricted ≫ cgf₂.inv := by
      -- Cancel the mapped `cf₂` inverse/hom pair after the right boundary rewrite.
      have hsource :
          Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom =
            Fg.map cf₂.inv ≫ (cg₂.inv ≫ (FY'.map right).hom ≫ cgf₂.hom) ≫
              cgf₂.inv := by
        calc
          Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom =
            Fg.map cf₂.inv ≫ (cg₂.inv ≫ (FY'.map right).hom ≫ 𝟙 _) := by
              simp only [Category.comp_id]
          _ = Fg.map cf₂.inv ≫
              (cg₂.inv ≫ (FY'.map right).hom ≫ (cgf₂.hom ≫ cgf₂.inv)) := by
              exact congrArg
                (fun k ↦ Fg.map cf₂.inv ≫ (cg₂.inv ≫ (FY'.map right).hom ≫ k))
                cgf₂.hom_inv_id.symm
          _ = Fg.map cf₂.inv ≫ (cg₂.inv ≫ (FY'.map right).hom ≫ cgf₂.hom) ≫
              cgf₂.inv := by
              simp only [Category.assoc]
      have hmiddle :
          Fg.map cf₂.inv ≫ (cg₂.inv ≫ (FY'.map right).hom ≫ cgf₂.hom) ≫
              cgf₂.inv =
            Fg.map cf₂.inv ≫ (Fg.map cf₂.hom ≫ rightAtRestricted) ≫ cgf₂.inv := by
        exact congrArg (fun k ↦ Fg.map cf₂.inv ≫ k ≫ cgf₂.inv) hrightPre.symm
      have htarget :
          Fg.map cf₂.inv ≫ (Fg.map cf₂.hom ≫ rightAtRestricted) ≫ cgf₂.inv =
            rightAtRestricted ≫ cgf₂.inv := by
        calc
          Fg.map cf₂.inv ≫ (Fg.map cf₂.hom ≫ rightAtRestricted) ≫ cgf₂.inv =
            (Fg.map cf₂.inv ≫ Fg.map cf₂.hom) ≫ rightAtRestricted ≫
              cgf₂.inv := by
              simp only [Category.assoc]
          _ = 𝟙 _ ≫ rightAtRestricted ≫ cgf₂.inv := by
              exact congrArg (fun k ↦ k ≫ rightAtRestricted ≫ cgf₂.inv) hcf₂
          _ = rightAtRestricted ≫ cgf₂.inv := by
              simp only [Category.id_comp]
      exact hsource.trans (hmiddle.trans htarget)
    have hleftNat :
        leftAtRestricted ≫ Fg.map (Ff₁.map t₁.hom) =
          Fgf₁.map t₁.hom ≫ leftAmbient := by
      -- Naturality moves the chosen component isomorphism across the left ambient
      -- `mapComp'.hom` component.
      simpa [leftAtRestricted, leftAmbient, Fg, Ff₁, Fgf₁] using
        (((canonicalFiberPseudofunctor p).mapComp'
          f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.naturality t₁.hom).symm
    have hrightNat :
        Fg.map (Ff₂.map t₂.inv) ≫ rightAtRestricted =
          rightAmbient ≫ Fgf₂.map t₂.inv := by
      -- Naturality moves the inverse component isomorphism across the right ambient
      -- `mapComp'.inv` component.
      exact
        (((canonicalFiberPseudofunctor p).mapComp'
          f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.naturality t₂.inv)
    -- Normalize the reassociation noise once, then apply the boundary comparison and
    -- naturality lemmas in the order dictated by the expanded overlap shell.
    let a := Fg.map (Ff₁.map t₁.hom)
    let b := Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂)
    let c := Fg.map (Ff₂.map t₂.inv)
    have h₀ :
        (FY'.map left).hom ≫
            (cg₁.hom ≫
                (Fg.map cf₁.hom ≫
                    Fg.map (Ff₁.map t₁.hom) ≫
                      Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫
                      Fg.map (Ff₂.map t₂.inv) ≫ Fg.map cf₂.inv) ≫
                  cg₂.inv) ≫
              (FY'.map right).hom =
          (((FY'.map left).hom ≫ cg₁.hom ≫ Fg.map cf₁.hom) ≫ a ≫ b ≫ c) ≫
            (Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom) := by
      simp only [a, b, c, Category.assoc]
    have h₁ :
        (((FY'.map left).hom ≫ cg₁.hom ≫ Fg.map cf₁.hom) ≫ a ≫ b ≫ c) ≫
            (Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom) =
          ((cgf₁.hom ≫ leftAtRestricted) ≫ a ≫ b ≫ c) ≫
            (Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom) := by
      -- Replace the left boundary under the fixed middle and right suffix.
      simpa only [a, b, c, ← Category.assoc] using
        congrArg
          (fun k ↦
            k ≫ a ≫ b ≫ c ≫
              (Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom))
          hleftBoundary
    have h₂ :
        ((cgf₁.hom ≫ leftAtRestricted) ≫ a ≫ b ≫ c) ≫
            (Fg.map cf₂.inv ≫ cg₂.inv ≫ (FY'.map right).hom) =
          ((cgf₁.hom ≫ leftAtRestricted) ≫ a ≫ b ≫ c) ≫
            (rightAtRestricted ≫ cgf₂.inv) := by
      -- Replace the right boundary under the fixed normalized prefix.
      exact
        congrArg
          (fun k ↦ ((cgf₁.hom ≫ leftAtRestricted) ≫ a ≫ b ≫ c) ≫ k)
          hrightBoundary
    have h₃ :
        ((cgf₁.hom ≫ leftAtRestricted) ≫ a ≫ b ≫ c) ≫
            (rightAtRestricted ≫ cgf₂.inv) =
          cgf₁.hom ≫ (leftAtRestricted ≫ a) ≫ b ≫ (c ≫ rightAtRestricted) ≫
            cgf₂.inv := by
      simp only [Category.assoc]
    have h₄ :
        cgf₁.hom ≫ (leftAtRestricted ≫ a) ≫ b ≫ (c ≫ rightAtRestricted) ≫
            cgf₂.inv =
          cgf₁.hom ≫ (Fgf₁.map t₁.hom ≫ leftAmbient) ≫ b ≫
            (c ≫ rightAtRestricted) ≫ cgf₂.inv := by
      -- Move the left component isomorphism through ambient `mapComp'.hom`.
      simpa only [a, b, c] using
        congrArg
          (fun k ↦ cgf₁.hom ≫ k ≫ b ≫ (c ≫ rightAtRestricted) ≫ cgf₂.inv)
          hleftNat
    have h₅ :
        cgf₁.hom ≫ (Fgf₁.map t₁.hom ≫ leftAmbient) ≫ b ≫
            (c ≫ rightAtRestricted) ≫ cgf₂.inv =
          cgf₁.hom ≫ (Fgf₁.map t₁.hom ≫ leftAmbient) ≫ b ≫
            (rightAmbient ≫ Fgf₂.map t₂.inv) ≫ cgf₂.inv := by
      -- Move the right inverse component isomorphism through ambient `mapComp'.inv`.
      simpa only [a, b, c] using
        congrArg
          (fun k ↦ cgf₁.hom ≫ (Fgf₁.map t₁.hom ≫ leftAmbient) ≫ b ≫ k ≫ cgf₂.inv)
          hrightNat
    have h₆ :
        cgf₁.hom ≫ (Fgf₁.map t₁.hom ≫ leftAmbient) ≫ b ≫
            (rightAmbient ≫ Fgf₂.map t₂.inv) ≫ cgf₂.inv =
          cgf₁.hom ≫ Fgf₁.map t₁.hom ≫
            (leftAmbient ≫ Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫ rightAmbient) ≫
            Fgf₂.map t₂.inv ≫ cgf₂.inv := by
      simp only [b, Category.assoc]
    simpa only [a, b, c] using
      h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans h₆)))))
  calc
    (FY'.map left).hom ≫ (cg₁.hom ≫ Fg.map ψ.hom ≫ cg₂.inv) ≫
        (FY'.map right).hom =
      cgf₁.hom ≫ Fgf₁.map t₁.hom ≫
          (leftAmbient ≫ Fg.map (D.obj.hom q f₁ f₂ hf₁ hf₂) ≫ rightAmbient) ≫
          Fgf₂.map t₂.inv ≫ cgf₂.inv := hboundaries
    _ =
      cgf₁.hom ≫ Fgf₁.map t₁.hom ≫
          D.obj.hom q' gf₁ gf₂ hgf₁base hgf₂base ≫
          Fgf₂.map t₂.inv ≫ cgf₂.inv := by
        exact
          congrArg
            (fun k ↦ cgf₁.hom ≫ Fgf₁.map t₁.hom ≫ k ≫ Fgf₂.map t₂.inv ≫ cgf₂.inv)
            hambient
    _ =
      (restricted_cover_overlap_hom_in_inverseImage_fiber
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        hgf₁base hgf₂base).hom := by
        simp [restricted_cover_overlap_hom_in_inverseImage_fiber, cgf₁, cgf₂, t₁, t₂, x₁, x₂,
          Fgf₁, Fgf₂, ObjectProperty.homMk]

/-- Helper for Lemma 8.4.3: the reverse overlap map is the identity on equal legs once the
component conjugations are normalized. -/
theorem restricted_cover_isoClosure_to_descent_obj_hom_self
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
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
    simp
  have hself :
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv = 𝟙 _ := by
    calc
      c.hom ≫ Fg.map t.hom ≫ 𝟙 _ ≫ Fg.map t.inv ≫ c.inv =
          c.hom ≫ Fg.map t.hom ≫ Fg.map t.inv ≫ c.inv := by
            simp
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
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
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
    simp
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

/-- Helper for Chap08 Lemma 8 4 3 RestrictedDescent: strictify an ambient fixed-cover object in the
componentwise `isoClosure` target to a restricted descent datum by choosing strict representatives
of its cover components. -/
noncomputable def restricted_cover_isoClosure_to_descent_obj
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : (cover_componentwise_isoClosure_property
      (J := J) (p := p) (P := P) S).FullSubcategory) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData (fun I : S.Arrow ↦ I.f)) :=
  { obj := fun I ↦
      (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).obj
        (restricted_cover_component_choice (J := J) (p := p) (P := P) S D I)
    hom := fun _Y q _I₁ _I₂ f₁ f₂ hf₁ hf₂ ↦
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

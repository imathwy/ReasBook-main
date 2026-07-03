import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Small

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_8_4_3 (from Chap08) -/
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

/-- Helper for Lemma 8.4.3: every component of a restricted fixed-cover descent datum already lies
in the ambient fiberwise `isoClosure`, so the remaining forward-bridge work is only the overlap
morphism packaging. -/
theorem restricted_cover_descent_component_mem_isoClosure
    [(P.ι ⋙ p).IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f))) (I : S.Arrow) :
    ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
      (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        (D.obj I)).obj) := by
  -- Route correction: the hpullback-free obstruction is not the objectwise `isoClosure` proof.
  -- Each restricted component is already strict in the inverse-image property, so the ambient
  -- `isoClosure` membership follows from the identity isomorphism.
  exact
    ObjectProperty.le_isoClosure
      (P := P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X))
      (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        (D.obj I)).obj)
      (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        (D.obj I)).property)

/-- Helper for Lemma 8.4.3: after transporting the source pullback law through the inverse-image
fiber functor, the middle morphism in the forward comparison shell already has the target form. -/
private theorem restricted_cover_descent_pullHom_middle_map_eq
    [(P.ι ⋙ p).IsFibered] {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (D.hom q f₁ f₂ hf₁ hf₂) g gf₁ gf₂ hgf₁ hgf₂)).hom =
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map
        (D.hom q' gf₁ gf₂
          (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]))).hom := by
  -- The source descent datum already satisfies the pullback law, and the inverse-image fiber
  -- functor preserves that equality on morphisms strictly.
  exact
    congrArg
      (fun k ↦
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y').map k).hom)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)

/-- Helper for Lemma 8.4.3: unfolding the ambient `pullHom` on the comparison-conjugated overlap
map exposes the raw `mapComp'` shell whose two outer boundaries still need transport
normalization. -/
private theorem restricted_cover_descent_componentwise_pullHom_unfolded_raw_shell
    [(P.ι ⋙ p).IsFibered] {U : C} (S : J.Cover U)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    let e :=
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
    let FYg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom e g gf₁ gf₂ hgf₁ hgf₂ =
      (((canonicalFiberPseudofunctor p).mapComp'
            f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
            (comp_toLoc_eq f₁ g gf₁ hgf₁)).hom.toNatTrans.app _) ≫
        FYg.map e ≫
        (((canonicalFiberPseudofunctor p).mapComp'
              f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
              (comp_toLoc_eq f₂ g gf₂ hgf₂)).inv.toNatTrans.app _) := by
  -- Expand the ambient `pullHom` once; the remaining blocker is only the two boundary
  -- normalizations and the source pullback law on the middle term.
  rfl

/-- Helper for Lemma 8.4.3: the comparison-conjugated forward overlap map satisfies the fixed-
cover pullback law after the two comparison boundaries are moved through the vertical naturality
squares and the middle term is rewritten by the source pullback law. -/
private theorem restricted_cover_descent_componentwise_pullHom_hom
    [(P.ι ⋙ p).IsFibered] {U : C} (S : J.Cover U)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y' Y : C} (g : Y' ⟶ Y) (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : g ≫ q = q')
    {I₁ I₂ : S.Arrow} (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch)
    (gf₁ : Y' ⟶ I₁.Y) (gf₂ : Y' ⟶ I₂.Y)
    (hgf₁ : g ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : g ≫ f₂ = gf₂ := by cat_disch) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂)
        g gf₁ gf₂ hgf₁ hgf₂ =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q' gf₁ gf₂
        (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
        (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) := by
  -- The new raw-shell helper isolates the actual remaining work: normalize the two outer
  -- `mapComp'` boundaries to the `gf₁`/`gf₂` comparison maps, then rewrite the middle factor by
  -- `restricted_cover_descent_pullHom_middle_map_eq`.
  have hunfolded :=
    restricted_cover_descent_componentwise_pullHom_unfolded_raw_shell
      (J := J) (p := p) (P := P) (S := S) (hpullback := hpullback) (D := D)
      (g := g) (q := q) (I₁ := I₁) (I₂ := I₂)
      (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
      (gf₁ := gf₁) (gf₂ := gf₂) (hgf₁ := hgf₁) (hgf₂ := hgf₂)
  -- The forward shell already matches the owner theorem from `RestrictedDescentForward`; the
  -- local file keeps that exact source-faithful comparison route while the remaining work stays
  -- focused on the fixed-cover ambient shell.
  simpa using
    restricted_cover_descent_isoClosure_obj_hom_pullHom_hom
      (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
      (Y' := Y') (Y := Y) (g := g) (q := q) (q' := q') (hq := hq)
      (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
      (gf₁ := gf₁) (gf₂ := gf₂) (hgf₁ := hgf₁) (hgf₂ := hgf₂)

/-- Helper for Lemma 8.4.3: the restricted fixed-cover descent datum can be compared to the
ambient componentwise-`isoClosure` target. -/
noncomputable def restricted_cover_descent_to_componentwise_isoClosure
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)) ⥤
      (cover_componentwise_isoClosure_property
        (J := J) (p := p) (P := P) S).FullSubcategory where
  obj D := by
    refine ⟨?_, ?_⟩
    · refine
        { obj := fun I ↦
            ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj (D.obj I)).obj
          hom := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
            restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂
          pullHom_hom := fun Y' Y g q q' hq I₁ I₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ ↦
            by
              -- Route correction: the forward overlap map is the comparison-conjugated shell, and
              -- the target file now keeps its pullback normalization local.
              simpa using
                restricted_cover_descent_componentwise_pullHom_hom
                  (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
                  (Y' := Y') (Y := Y) (I₁ := I₁) (I₂ := I₂)
                  (g := g) (q := q) (q' := q') (hq := hq) (f₁ := f₁) (f₂ := f₂)
                  (hf₁ := hf₁) (hf₂ := hf₂) (gf₁ := gf₁) (gf₂ := gf₂)
                  (hgf₁ := hgf₁) (hgf₂ := hgf₂)
          hom_self := fun Y q I g hg ↦
            by
              -- The identity axiom is exactly the shell-cancellation lemma from the helper file.
              simpa using
                restricted_cover_descent_isoClosure_obj_hom_self
                  (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
                  (Y := Y) (I := I)
                  (q := q) (g := g) (hg := hg)
          hom_comp := fun Y q I₁ I₂ I₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦
            by
              -- The cocycle axiom is likewise already isolated for the comparison-conjugated
              -- shell, so the local functor just reuses that statement.
              simpa using
                restricted_cover_descent_isoClosure_obj_hom_comp
                  (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D)
                  (Y := Y) (I₁ := I₁) (I₂ := I₂) (I₃ := I₃)
                  (q := q) (f₁ := f₁) (f₂ := f₂) (f₃ := f₃)
                  (hf₁ := hf₁) (hf₂ := hf₂) (hf₃ := hf₃) }
    · intro I
      -- The objectwise `isoClosure` membership was already proved separately.
      exact restricted_cover_descent_component_mem_isoClosure
        (J := J) (p := p) (P := P) S D I
  map {D₁ D₂} φ :=
    ObjectProperty.homMk
      { hom := fun I ↦
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
            (φ.hom I)).hom
        comm := by
          intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
          -- The shell naturality for morphisms of restricted descent data is already packaged in
          -- `RestrictedDescentForward`.
          simpa using
            restricted_cover_descent_to_isoClosure_map_comm_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S φ q f₁ f₂ hf₁ hf₂ }
  map_id D := by
    -- The forward bridge acts componentwise on morphisms, so identity preservation is strict.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl
  map_comp φ ψ := by
    -- Composition is also computed componentwise in each cover component.
    apply ObjectProperty.hom_ext
    apply Pseudofunctor.DescentData.hom_ext
    intro I
    rfl

/-- Helper for Lemma 8.4.3: on each cover component, the corrected forward bridge uses the same
ambient object obtained by forgetting the restricted component into the inverse-image fiber. -/
@[simp] theorem restricted_cover_descent_to_componentwise_isoClosure_obj_obj
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f))) (I : S.Arrow) :
    (((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D).obj.obj I) =
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        (D.obj I)).obj := by
  -- The corrected forward bridge was defined componentwise, so its object field is definitional.
  rfl

/-- Helper for Lemma 8.4.3: the overlap morphism in the corrected forward bridge is exactly the
comparison-conjugated shell exported by `RestrictedDescentForward`. -/
@[simp] theorem restricted_cover_descent_to_componentwise_isoClosure_obj_hom
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((restricted_cover_descent_to_componentwise_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj D).obj).hom
        q f₁ f₂ hf₁ hf₂) =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ := by
  -- The corrected bridge stores this shell as its overlap morphism by definition.
  rfl

/-- Helper for Lemma 8.4.3: the ambient fixed-cover `isoClosure` functor keeps the canonical
ambient overlap morphism definitionally unchanged after forgetting the full-subcategory wrapper. -/
@[simp] theorem ambient_cover_toDescentData_isoClosure_obj_hom
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).obj).hom
        q f₁ f₂ hf₁ hf₂) =
      (((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
              ((canonicalFiberPseudofunctor p).toDescentData
                (fun I : S.Arrow ↦ I.f))).obj
            ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).hom
        q f₁ f₂ hf₁ hf₂) := by
  -- The ambient `isoClosure` target is defined by a full-subcategory lift, so the overlap field
  -- is definitionally the ambient canonical one.
  rfl

/-- Helper for Lemma 8.4.3: mapping a transported component morphism from the restricted fiber to
the inverse-image fiber yields the ambient component morphism conjugated by the two pullback-
comparison boundaries. -/
private theorem restricted_pullback_preimage_component_map_normal_form
    [(P.ι ⋙ p).IsFibered]
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
    -- Use the owner inverse-side naturality square specialized to the transported component
    -- morphism, then rewrite the owner comparison to the local restricted/ambient comparison.
    simpa [φ, e₁, e₂, restricted_pullback_vs_ambient_pullback_comparison] using
      fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
        (J := J) (p := p) (P := P) (hpullback := hpullback) (f := f) (φ := φ)
  have hround :
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ = ψ := by
    -- The inverse-image/restricted-fiber equivalence is strict on morphisms, so the transported
    -- component returns to the original ambient morphism before applying the ambient pullback.
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
    -- Apply the ambient pullback functor to the strict roundtrip identity on the component
    -- morphism.
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
    -- Postcompose the naturality square by the inverse comparison map and simplify the resulting
    -- `hom ≫ inv` cancellation on the right boundary.
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

/-- Helper for Lemma 8.4.3: every morphism between two images of the corrected fixed-cover bridge
comes from a morphism of restricted descent data after transporting each component back through
the inverse fiber equivalence. -/
private theorem restricted_cover_descent_mapped_overlap_shell
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (D : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f)))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
        (D.hom q f₁ f₂ hf₁ hf₂)).hom =
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).hom ≫
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).inv := by
  -- Unfold the comparison-conjugated forward overlap once and cancel the outer comparison
  -- boundaries to recover the raw mapped restricted overlap.
  symm
  simpa [restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison, Category.assoc] using
    congrArg
      (fun k ↦
        (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).hom ≫
          k ≫
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).inv)
      (show
        restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
            (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ =
          (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
            ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
              (D.hom q f₁ f₂ hf₁ hf₂)).hom ≫
            (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom by
        rfl)

/-- Helper for Lemma 8.4.3: every morphism between two images of the corrected fixed-cover bridge
comes from a morphism of restricted descent data after transporting each component back through
the inverse fiber equivalence. -/
theorem restricted_cover_descent_preimage_transport_comm
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f))}
    (φ :
      ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₁) ⟶
        ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₂))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).map
          (ObjectProperty.homMk (φ.hom.hom I₁))) ≫
      D₂.hom q f₁ f₂ hf₁ hf₂ =
    D₁.hom q f₁ f₂ hf₁ hf₂ ≫
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).map
          (ObjectProperty.homMk (φ.hom.hom I₂))) := by
  -- Route correction: after transporting to the inverse-image fiber, both the pulled-back
  -- component morphisms and the overlap morphisms normalize to the same comparison-conjugated
  -- ambient shell.  The restricted square is then the ambient inverse-image square with the two
  -- surviving outer comparison boundaries attached.
  have hmap :
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₁.op.toLoc).toFunctor.map
              ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₁.Y).map
                (ObjectProperty.homMk (φ.hom.hom I₁))) ≫
            D₂.hom q f₁ f₂ hf₁ hf₂) =
        (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (D₁.hom q f₁ f₂ hf₁ hf₂ ≫
            ((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
              ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).map
                (ObjectProperty.homMk (φ.hom.hom I₂)))) := by
      apply ObjectProperty.hom_ext
      rw [Functor.map_comp, Functor.map_comp]
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
      rw [restricted_pullback_preimage_component_map_normal_form
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (f := f₁) (x₁ := D₁.obj I₁) (x₂ := D₂.obj I₁)
          (ψ := ObjectProperty.homMk (φ.hom.hom I₁))]
      have hD₂ :=
        restricted_cover_descent_mapped_overlap_shell
          (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D₂)
          (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
          (hf₁ := hf₁) (hf₂ := hf₂)
      have hD₁ :=
        restricted_cover_descent_mapped_overlap_shell
          (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (D := D₁)
          (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
          (hf₁ := hf₁) (hf₂ := hf₂)
      have hmid :=
        show
          ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
              (ObjectProperty.homMk (φ.hom.hom I₁)).hom ≫
            restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
          restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
              (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫
            ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
              (ObjectProperty.homMk (φ.hom.hom I₂)).hom by
          simpa [restricted_cover_descent_to_componentwise_isoClosure_obj_hom] using
            φ.hom.comm q f₁ f₂ hf₁ hf₂
      have hC₂ :=
        restricted_pullback_preimage_component_map_normal_form
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (f := f₂) (x₁ := D₁.obj I₂) (x₂ := D₂.obj I₂)
          (ψ := ObjectProperty.homMk (φ.hom.hom I₂))
      -- Package the two raw overlap terms into the comparison shell, use the ambient inverse-
      -- image square on the middle shell, and then unpack the source-side overlap again.
      calc
        (((restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
            ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
              (ObjectProperty.homMk (φ.hom.hom I₁)).hom ≫
            (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)).inv) ≫
          ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
            (D₂.hom q f₁ f₂ hf₁ hf₂)).hom) =
            (((restricted_pullback_vs_ambient_pullback_comparison
                  (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
                ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                  (ObjectProperty.homMk (φ.hom.hom I₁)).hom ≫
                (restricted_pullback_vs_ambient_pullback_comparison
                  (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)).inv) ≫
              ((restricted_pullback_vs_ambient_pullback_comparison
                  (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)).hom ≫
                restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
                  (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ ≫
                (restricted_pullback_vs_ambient_pullback_comparison
                  (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    ((restricted_pullback_vs_ambient_pullback_comparison
                          (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
                        ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                          (ObjectProperty.homMk (φ.hom.hom I₁)).hom ≫
                        (restricted_pullback_vs_ambient_pullback_comparison
                          (J := J) (p := p) (P := P) hpullback f₁ (D₂.obj I₁)).inv) ≫
                      k)
                  hD₂
        _ =
            (restricted_pullback_vs_ambient_pullback_comparison
                (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
              ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                (ObjectProperty.homMk (φ.hom.hom I₁)).hom ≫
              restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
                (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ ≫
              (restricted_pullback_vs_ambient_pullback_comparison
                (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv := by
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
        _ =
            (restricted_pullback_vs_ambient_pullback_comparison
                (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
              restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
                (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫
              ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
                (ObjectProperty.homMk (φ.hom.hom I₂)).hom ≫
              (restricted_pullback_vs_ambient_pullback_comparison
                (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    (restricted_pullback_vs_ambient_pullback_comparison
                        (J := J) (p := p) (P := P) hpullback f₁ (D₁.obj I₁)).hom ≫
                      k ≫
                      (restricted_pullback_vs_ambient_pullback_comparison
                        (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv)
                  hmid
        _ =
            ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
                (D₁.hom q f₁ f₂ hf₁ hf₂)).hom ≫
              ((restricted_pullback_vs_ambient_pullback_comparison
                    (J := J) (p := p) (P := P) hpullback f₂ (D₁.obj I₂)).hom ≫
                  ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
                    (ObjectProperty.homMk (φ.hom.hom I₂)).hom ≫
                  (restricted_pullback_vs_ambient_pullback_comparison
                    (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv) := by
              symm
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    k ≫
                      ((restricted_pullback_vs_ambient_pullback_comparison
                            (J := J) (p := p) (P := P) hpullback f₂ (D₁.obj I₂)).hom ≫
                          ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
                            (ObjectProperty.homMk (φ.hom.hom I₂)).hom ≫
                          (restricted_pullback_vs_ambient_pullback_comparison
                            (J := J) (p := p) (P := P) hpullback f₂ (D₂.obj I₂)).inv))
                  hD₁
        _ =
            ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
                (D₁.hom q f₁ f₂ hf₁ hf₂)).hom ≫
              ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
                  (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map f₂.op.toLoc).toFunctor.map
                    ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I₂.Y).map
                      (ObjectProperty.homMk (φ.hom.hom I₂))))).hom := by
              symm
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
                        (D₁.hom q f₁ f₂ hf₁ hf₂)).hom ≫
                      k)
                  hC₂
  have hround := congrArg
    ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) Y).map) hmap
  simpa using hround

/-- Helper for Lemma 8.4.3: before transporting back to the restricted fiber, a morphism between
two forward-bridge images already satisfies the ambient inverse-image overlap square. -/
theorem restricted_cover_descent_preimage_transport_comm_in_inverseImage
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f))}
    (φ :
      ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₁) ⟶
        ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₂))
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (φ.hom.hom I₁) ≫
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₂ q f₁ f₂ hf₁ hf₂ =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D₁ q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (φ.hom.hom I₂) := by
  -- Rewrite both forward overlap maps to the normalized ambient shell, then read off the
  -- commutativity axiom already carried by the ambient descent-data morphism `φ.hom`.
  simpa [restricted_cover_descent_to_componentwise_isoClosure_obj_hom] using
    φ.hom.comm q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.3: every morphism between two images of the corrected fixed-cover bridge
comes from a morphism of restricted descent data after transporting each component back through
the inverse fiber equivalence. -/
theorem restricted_cover_descent_hom_of_componentwise_isoClosure_hom
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor (P.ι ⋙ p)).DescentData
      (fun I : S.Arrow ↦ I.f))}
    (φ :
      ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₁) ⟶
        ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj D₂)) :
    ∃ ψ : D₁ ⟶ D₂,
      (restricted_cover_descent_to_componentwise_isoClosure
        (J := J) (p := p) (P := P) hpullback S).map ψ = φ := by
  let ψ : D₁ ⟶ D₂ :=
    { hom := fun I ↦
        (inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map
          (ObjectProperty.homMk (φ.hom.hom I))
      comm := fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
        restricted_cover_descent_preimage_transport_comm
          (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (φ := φ)
          (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
          (hf₁ := hf₁) (hf₂ := hf₂) }
  refine ⟨ψ, ?_⟩
  -- Compare the forward image of the transported morphism with `φ` componentwise and cancel the
  -- strict inverse-image/restricted-fiber roundtrip on each cover component.
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  have hround :
      (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
          ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map
            (ObjectProperty.homMk (φ.hom.hom I))) =
        ObjectProperty.homMk (φ.hom.hom I) := by
    exact
      fullSubcategory_fiber_equiv_inverseImage_functor_inverse_map
        (p := p) (P := P) I.Y
        (φ := ObjectProperty.homMk (φ.hom.hom I))
  -- Read the roundtrip cancellation on the inverse-image full subcategory at the level of the
  -- underlying ambient fiber morphism.
  simpa [ψ, restricted_cover_descent_to_componentwise_isoClosure] using
    congrArg (fun η ↦ η.hom) hround

/-- Helper for Lemma 8.4.3: for a fixed source object in the restricted fiber, the componentwise
pullback-comparison isomorphisms satisfy the descent square relating the restricted and ambient
canonical fixed-cover descent data. -/
private theorem restricted_cover_transport_component_naturality
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y) (I : S.Arrow) :
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).map I.f.op.toLoc).toFunctor.map φ)).hom ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f y).hom =
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback I.f x).hom ≫
      ((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).map φ).hom := by
  -- This is the inverse-side pullback-comparison square specialized to the cover leg `I.f`,
  -- with the restricted-side pullback map written explicitly via the fiber-inclusion functors.
  simpa using
    fullSubcategory_inclusion_pullbackComparison_inv_naturality_over_vertical
      (J := J) (p := p) (P := P) (hpullback := hpullback) (f := I.f) (φ := φ)

/-- Helper for Lemma 8.4.3: the inclusion fibred morphism sends the restricted chosen pullback
arrow to the same underlying ambient morphism. -/
@[simp] private theorem fullSubcategory_inclusion_fibredMor_map_pullbackChoice
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U V : C} (f : V ⟶ U) (x : (P.ι ⋙ p).Fiber U) :
    (fullSubcategory_inclusion_fibredMor
        (J := J) (p := p) (P := P) hpullback).toHom.map
        ((canonicalPullbackChoice (P.ι ⋙ p)).map f x) =
      ((canonicalPullbackChoice (P.ι ⋙ p)).map f x).hom := by
  -- The inclusion fibred morphism acts by forgetting the full-subcategory wrapper on total
  -- morphisms, so the chosen pullback arrow is unchanged on the underlying ambient arrow.
  rfl

/-- Helper for Lemma 8.4.3: precomposing the ambient fixed-cover overlap map by the left
pullback-comparison boundary is unchanged by peeling the ambient full-subcategory lift. -/
private theorem restricted_cover_toDescentData_component_ambient_side_peel
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
        (((ambient_cover_toDescentData_isoClosure
              (J := J) (p := p) (P := P) hpullback S).obj
            ((fullSubcategory_fiber_equiv_inverseImage
                (p := p) (P := P) U).functor.obj x)).obj).hom
          q f₁ f₂ hf₁ hf₂ =
      ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
        ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
              ((canonicalFiberPseudofunctor p).toDescentData
                (fun I : S.Arrow ↦ I.f))).obj
            ((fullSubcategory_fiber_equiv_inverseImage
                (p := p) (P := P) U).functor.obj x)).hom
          q f₁ f₂ hf₁ hf₂ := by
  -- Peel only the ambient full-subcategory wrapper; the left boundary stays untouched.
  exact
    congrArg
      (fun k ↦
        ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
          k)
      (ambient_cover_toDescentData_isoClosure_obj_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (x := x)
        (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂))

/-- Helper for Lemma 8.4.3: postcomposing the restricted fixed-cover overlap map by the right
pullback-comparison boundary is unchanged by unfolding the restricted bridge to its
comparison-conjugated shell. -/
private theorem restricted_cover_toDescentData_component_restricted_side_expand
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((restricted_cover_descent_to_componentwise_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj x)).obj).hom q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom =
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)
        q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom := by
  -- Expand only the restricted bridge wrapper; the right boundary stays untouched.
  exact
    congrArg
      (fun k ↦
        k ≫
          ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
            (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback I₂.f x).hom)
      (restricted_cover_descent_to_componentwise_isoClosure_obj_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S)
        (D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x))
        (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂))

/-- Helper for Lemma 8.4.3: the raw left ambient `mapComp'.inv` boundary is the restricted
componentwise `mapComp'.inv` boundary conjugated by the two pullback-comparison maps over `f₁`
and the common overlap leg `q`. -/
private theorem restricted_cover_toDescentData_component_left_boundary_postcompose
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    (((canonicalFiberPseudofunctor p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x').1 ≫
      (canonicalPullbackChoice p).map q x' =
    (canonicalPullbackChoice p).map f₁
        (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x' := by
  let _ := hpullback
  let x' :=
    (((fullSubcategory_fiber_equiv_inverseImage
        (p := p) (P := P) U).functor.obj x).obj)
  let φq := (canonicalPullbackChoice p).map q x'
  simpa [φq, x'] using
    FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
      (p := p) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) x'

/-- Helper for Lemma 8.4.3: the raw left ambient `mapComp'.inv` boundary is the restricted
componentwise `mapComp'.inv` boundary conjugated by the two pullback-comparison maps over `f₁`
and the common overlap leg `q`. -/
private theorem restricted_cover_toDescentData_component_left_boundary_cancel
    [p.IsFibered] {U Y : C} (q : Y ⟶ U) (x' : p.Fiber U)
    {z : p.Fiber Y}
    (a b : z ⟶ ((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.obj x')
    (hpost :
      a.1 ≫ (canonicalPullbackChoice p).map q x' =
        b.1 ≫ (canonicalPullbackChoice p).map q x') :
    a = b := by
  -- The chosen ambient pullback over `q` is strongly cartesian, so equality after
  -- postcomposition by its universal arrow already determines the vertical morphism uniquely.
  have hφq :
      p.IsStronglyCartesian q ((canonicalPullbackChoice p).map q x') := by
    simpa using (canonicalPullbackChoice p).isStronglyCartesian q x'
  letI : p.IsStronglyCartesian q ((canonicalPullbackChoice p).map q x') := hφq
  have ha : p.IsHomLift (𝟙 Y) a.1 := a.2
  have hb : p.IsHomLift (𝟙 Y) b.1 := b.2
  apply Functor.Fiber.hom_ext
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      q ((canonicalPullbackChoice p).map q x') inferInstance _ _
      (𝟙 Y) a.1 b.1 ha hb hpost

/-- Helper for Lemma 8.4.3: the ambient right `mapComp'.hom` boundary becomes the chosen ambient
composite pullback arrow after postcomposition by the two chosen pullback arrows over `f₂` and
`I₂.f`. -/
private theorem restricted_cover_toDescentData_component_right_boundary_postcompose
    [(P.ι ⋙ p).IsFibered]
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₂ : S.Arrow}
    (f₂ : Y ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (((canonicalFiberPseudofunctor p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x').1 ≫
      (canonicalPullbackChoice p).map f₂
        (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₂.f x' =
    (canonicalPullbackChoice p).map q x' := by
  let x' :=
    (((fullSubcategory_fiber_equiv_inverseImage
        (p := p) (P := P) U).functor.obj x).obj)
  -- Read the ambient `mapComp'.hom` component through the standard chosen pullback
  -- composition factorization.
  simpa [x'] using
    FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      (p := p) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x'

/-- Helper for Lemma 8.4.3: the `I`-component of the restricted canonical descent datum is not
definitionally the ambient chosen pullback object, but it is canonically identified with that
ambient pullback by the restricted/ambient pullback-comparison isomorphism. -/
private noncomputable def restricted_cover_descent_component_pullback_object_identification
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) (I : S.Arrow) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
        (D.obj I)).obj) ≅
      (((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.obj x') :=
  restricted_pullback_vs_ambient_pullback_comparison
    (J := J) (p := p) (P := P) hpullback I.f x

/-- Helper for Lemma 8.4.3: the specialized component comparison is exactly the owner comparison
isomorphism, now stated with the `D.obj I` and `x'` notation used in the fixed-cover boundary
proofs. -/
@[simp] private theorem restricted_cover_descent_component_pullback_object_identification_hom
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) (I : S.Arrow) :
    (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I).hom =
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f x).hom := by
  -- The specialized component comparison is defined by reusing the owner pullback-comparison
  -- isomorphism with the fixed-cover notation.
  rfl

/-- Helper for Lemma 8.4.3: postcomposing the specialized component comparison with the ambient
chosen pullback arrow over `I.f` recovers the restricted chosen pullback arrow. -/
@[simp] private theorem restricted_cover_descent_component_pullback_object_identification_hom_postcompose
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) (I : S.Arrow) :
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I).hom.1 ≫
      (canonicalPullbackChoice p).map I.f x' =
    ((canonicalPullbackChoice (P.ι ⋙ p)).map I.f x).hom := by
  -- This is just the owner postcompose identity specialized to the fixed-cover leg `I.f`.
  simpa [restricted_cover_descent_component_pullback_object_identification] using
    restricted_pullback_vs_ambient_pullback_comparison_hom_postcompose
      (J := J) (p := p) (P := P) hpullback I.f x

/-- Helper for Lemma 8.4.3: postcomposing the inverse of the specialized component comparison with
the restricted chosen pullback arrow over `I.f` recovers the ambient chosen pullback arrow. -/
@[simp] private theorem restricted_cover_descent_component_pullback_object_identification_inv_postcompose
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) (I : S.Arrow) :
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I).inv.1 ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map I.f x).hom =
    (canonicalPullbackChoice p).map I.f x' := by
  -- The inverse-side postcompose identity is the dual owner comparison equation on the same
  -- fixed-cover leg.
  simpa [restricted_cover_descent_component_pullback_object_identification] using
    restricted_pullback_vs_ambient_pullback_comparison_inv_postcompose
      (J := J) (p := p) (P := P) hpullback I.f x

/-- Helper for Lemma 8.4.3: pulling back the component-object identification along a further leg
`f` matches the chosen ambient pullback arrows on the two identified component objects. -/
private theorem
    restricted_cover_descent_component_pullback_object_identification_hom_map_pullbackChoice
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} {I : S.Arrow} (f : Y ⟶ I.Y) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
        (restricted_cover_descent_component_pullback_object_identification
          (J := J) (p := p) (P := P) hpullback S x I).hom).1 ≫
      (canonicalPullbackChoice p).map f
        (((canonicalFiberPseudofunctor p).map I.f.op.toLoc).toFunctor.obj x') =
    (canonicalPullbackChoice p).map f
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).obj
          (D.obj I)).obj) ≫
      (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I).hom.1 := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    (((fullSubcategory_fiber_equiv_inverseImage
        (p := p) (P := P) U).functor.obj x).obj)
  -- Apply ambient pullback functoriality to the vertical component-object identification.
  simpa [D, x', restricted_cover_descent_component_pullback_object_identification] using
    (FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := p) (f := f)
      (φ := (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I).hom))

/-- Helper for Lemma 8.4.3: after peeling the ambient full-subcategory wrapper, the ambient
fixed-cover overlap morphism is already the raw `mapComp'` shell from the source proof. -/
private theorem restricted_cover_toDescentData_component_ambient_raw_shell
    [(P.ι ⋙ p).IsFibered]
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    ((((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).ι) ⋙
          ((canonicalFiberPseudofunctor p).toDescentData
            (fun I : S.Arrow ↦ I.f))).obj
        ((fullSubcategory_fiber_equiv_inverseImage
            (p := p) (P := P) U).functor.obj x)).hom
      q f₁ f₂ hf₁ hf₂ =
      (((canonicalFiberPseudofunctor p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x') ≫
        (((canonicalFiberPseudofunctor p).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x') := by
  -- This is the definitional raw shell for the canonical ambient descent datum attached to `x'`.
  rfl

/-- Helper for Lemma 8.4.3: the ambient left `mapComp'.inv` postcompose identity can be used in
reassociated form without reopening the `mapComp'` shell. -/
private theorem restricted_cover_toDescentData_component_left_boundary_postcompose_reassoc
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let x' :=
      (((fullSubcategory_fiber_equiv_inverseImage
          (p := p) (P := P) U).functor.obj x).obj)
    (((canonicalFiberPseudofunctor p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x').1 ≫
      (canonicalPullbackChoice p).map q x' =
    (canonicalPullbackChoice p).map f₁
      (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x' := by
  let x' :=
    (((fullSubcategory_fiber_equiv_inverseImage
        (p := p) (P := P) U).functor.obj x).obj)
  -- This is just the owner left-boundary factorization, written with the local `x'` notation.
  simpa [x'] using
    restricted_cover_toDescentData_component_left_boundary_postcompose
      (J := J) (p := p) (P := P) (hpullback := hpullback)
      (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)

/-- Helper for Lemma 8.4.3: after unfolding the canonical restricted fixed-cover descent datum,
the right-hand side comparison shell splits into its raw `mapComp'.inv` and `mapComp'.hom`
factors. -/
private theorem restricted_cover_toDescentData_component_restricted_raw_shell_split
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom =
    ((restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)).hom) ≫
      (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)).hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
        ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom) := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  -- Unfold the canonical restricted overlap once; its middle term is definitionally the
  -- `mapComp'.inv ≫ mapComp'.hom` composite, and the inverse-image fiber functor preserves
  -- that composite by `Functor.map_comp`.
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let leftLeg :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightLeg :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)
  have hmap :
      (F.map (leftLeg ≫ rightLeg)).hom = (F.map leftLeg).hom ≫ (F.map rightLeg).hom := by
    -- The inverse-image fiber functor preserves the canonical overlap composite strictly.
    simpa [F, leftLeg, rightLeg] using
      congrArg (fun k ↦ k.hom) (F.map_comp leftLeg rightLeg)
  let leftBoundary :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv
  let rightBoundary :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom
  -- After that single functoriality rewrite, both sides are definitionally the same raw shell.
  simp only [Pseudofunctor.toDescentData_obj,
    Pseudofunctor.DescentData.ofObj_hom,
    restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison, Category.assoc]
  change leftBoundary ≫ (F.map (leftLeg ≫ rightLeg)).hom ≫ rightBoundary =
    leftBoundary ≫ (F.map leftLeg).hom ≫ (F.map rightLeg).hom ≫ rightBoundary
  calc
    leftBoundary ≫ (F.map (leftLeg ≫ rightLeg)).hom ≫ rightBoundary =
        leftBoundary ≫ ((F.map leftLeg).hom ≫ (F.map rightLeg).hom) ≫ rightBoundary := by
          exact congrArg (fun k ↦ leftBoundary ≫ k ≫ rightBoundary) hmap
    _ = leftBoundary ≫ (F.map leftLeg).hom ≫ (F.map rightLeg).hom ≫ rightBoundary := by
          simp only [Category.assoc]

/-- Helper for Lemma 8.4.3: the ambient left `mapComp'.inv` postcompose factorization is stable
when the source object is written directly in the inverse-image fiber. -/
private theorem restricted_cover_toDescentData_component_left_boundary_postcompose_inverseImage
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    (((canonicalFiberPseudofunctor p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x').1 ≫
      (canonicalPullbackChoice p).map q x' =
    (canonicalPullbackChoice p).map f₁
      (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x' := by
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  -- This is the same owner factorization as above, with the inverse-image-fiber object spelling
  -- substituted for the equivalent full-subcategory spelling.
  simpa [x', fullSubcategory_fiber_equiv_inverseImage] using
    restricted_cover_toDescentData_component_left_boundary_postcompose_reassoc
      (J := J) (p := p) (P := P) (hpullback := hpullback)
      (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)

/-- Helper for Lemma 8.4.3: transporting the specialized component-object identification through
the ambient pullback over `f₁` gives the precise left boundary rewrite needed before the final
common-shell postcompose. -/
private theorem restricted_cover_toDescentData_component_left_boundary_transport_f₁
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    (canonicalPullbackChoice p).map f₁
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
            (D.obj I₁)).obj) ≫
      (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I₁).hom.1 =
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_descent_component_pullback_object_identification
          (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
      (canonicalPullbackChoice p).map f₁
        (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') := by
  let _ := hf₁
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  -- This is exactly the ambient pullback-functoriality square for the specialized component
  -- comparison, now written with the fixed-cover `D.obj I₁` and inverse-image `x'` notation.
  simpa [D, x'] using
    (restricted_cover_descent_component_pullback_object_identification_hom_map_pullbackChoice
      (J := J) (p := p) (P := P) (hpullback := hpullback)
      (S := S) (x := x) (I := I₁) (f := f₁)).symm

/-- Helper for Lemma 8.4.3: after postcomposing the ambient left boundary by the chosen ambient
`q`-pullback, the source proof lands on the common ambient shell used for the final comparison. -/
private theorem restricted_cover_toDescentData_component_left_boundary_postcompose_common_shell
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    (((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (restricted_cover_descent_component_pullback_object_identification
            (J := J) (p := p) (P := P) hpullback S x I₁).hom) ≫
        (((canonicalFiberPseudofunctor p).mapComp'
              I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x')).1 ≫
      (canonicalPullbackChoice p).map q x') =
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_descent_component_pullback_object_identification
          (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
      (canonicalPullbackChoice p).map f₁
        (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x' := by
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let pre :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      (restricted_cover_descent_component_pullback_object_identification
        (J := J) (p := p) (P := P) hpullback S x I₁).hom
  let mid :=
    (((canonicalFiberPseudofunctor p).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x')
  have hassoc :
      ((pre ≫ mid).1 ≫ (canonicalPullbackChoice p).map q x') =
        pre.1 ≫ (mid.1 ≫ (canonicalPullbackChoice p).map q x') := by
    -- Reassociate once so the owner postcompose factorization applies directly to `mid`.
    change (pre.1 ≫ mid.1) ≫ (canonicalPullbackChoice p).map q x' =
      pre.1 ≫ (mid.1 ≫ (canonicalPullbackChoice p).map q x')
    simp only [Category.assoc]
  -- The ambient side is the owner `mapComp'.inv` factorization with the fixed-cover comparison
  -- over `I₁.f` precomposed once and then reassociated.
  calc
    ((pre ≫ mid).1 ≫ (canonicalPullbackChoice p).map q x') =
      pre.1 ≫ (mid.1 ≫ (canonicalPullbackChoice p).map q x') := hassoc
    _ = (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
          (restricted_cover_descent_component_pullback_object_identification
            (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
        (canonicalPullbackChoice p).map f₁
          (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
        (canonicalPullbackChoice p).map I₁.f x' := by
            exact
              congrArg
                (fun k ↦
                  (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
                      (restricted_cover_descent_component_pullback_object_identification
                        (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
                    k)
              (restricted_cover_toDescentData_component_left_boundary_postcompose_inverseImage
                  (J := J) (p := p) (P := P) (hpullback := hpullback)
                  (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁))

/-- Helper for Lemma 8.4.3: once the restricted left shell is postcomposed by the ambient chosen
`q`-pullback, the `q`-comparison disappears and only the iterated restricted chosen pullbacks
remain. -/
private theorem restricted_cover_toDescentData_component_left_boundary_postcompose_to_restricted_pullbacks
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    let shell :=
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
            x)).hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback q x).hom
    (shell.1 ≫ (canonicalPullbackChoice p).map q x') =
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let leftBoundary :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv
  let middle :=
    (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
          I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)
  let rightBoundary :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback q x).hom
  -- First remove the ambient `q`-comparison by postcomposing with the chosen ambient pullback.
  have hq :
      rightBoundary.1 ≫ (canonicalPullbackChoice p).map q x' =
        ((canonicalPullbackChoice (P.ι ⋙ p)).map q x).hom := by
    simpa [x', rightBoundary] using
      restricted_pullback_vs_ambient_pullback_comparison_hom_postcompose
        (J := J) (p := p) (P := P) hpullback q x
  -- Then read the restricted `mapComp'.inv` factorization through the inverse-image fiber
  -- functor, so the shell is expressed by the two restricted chosen pullback legs.
  have hmiddleRaw :=
    (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
      (p := P.ι ⋙ p) (f := I₁.f) (g := f₁) (gf := q) (hgf := hf₁) x)
  have hmiddle :
      (F.map middle).hom.1 ≫ ((canonicalPullbackChoice (P.ι ⋙ p)).map q x).hom =
        ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
    simpa [F, middle, D] using congrArg (fun k ↦ k.hom) hmiddleRaw
  -- Reassociate once on each side and apply the two structural rewrites in sequence.
  calc
    (((leftBoundary ≫ (F.map middle).hom ≫ rightBoundary).1) ≫
        (canonicalPullbackChoice p).map q x') =
      leftBoundary.1 ≫ (F.map middle).hom.1 ≫
        (rightBoundary.1 ≫ (canonicalPullbackChoice p).map q x') := by
          calc
            (((leftBoundary ≫ (F.map middle).hom ≫ rightBoundary).1) ≫
                (canonicalPullbackChoice p).map q x') =
              ((leftBoundary.1 ≫ (F.map middle).hom.1 ≫ rightBoundary.1) ≫
                (canonicalPullbackChoice p).map q x') := by
                  rfl
            _ =
              leftBoundary.1 ≫ (F.map middle).hom.1 ≫
                (rightBoundary.1 ≫ (canonicalPullbackChoice p).map q x') := by
                  simp [Category.assoc]
    _ =
      leftBoundary.1 ≫ (F.map middle).hom.1 ≫
        ((canonicalPullbackChoice (P.ι ⋙ p)).map q x).hom := by
          exact congrArg (fun k ↦ leftBoundary.1 ≫ (F.map middle).hom.1 ≫ k) hq
    _ =
      leftBoundary.1 ≫
        (((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom) := by
          exact congrArg (fun k ↦ leftBoundary.1 ≫ k) hmiddle
    _ =
      leftBoundary.1 ≫ ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
        ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
          rfl

/-- Helper for Lemma 8.4.3: the iterated restricted chosen pullbacks transport once to the common
ambient shell used by the fixed-cover source proof. -/
private theorem restricted_cover_toDescentData_component_left_boundary_restricted_pullbacks_common_shell
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
      ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_descent_component_pullback_object_identification
          (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
      (canonicalPullbackChoice p).map f₁
        (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x' := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let comparison :=
    restricted_cover_descent_component_pullback_object_identification
      (J := J) (p := p) (P := P) hpullback S x I₁
  -- Rewrite the front restricted/ambient comparison over `f₁` to the ambient chosen pullback.
  have hfront :
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
        ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom =
      (canonicalPullbackChoice p).map f₁
        (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
          (D.obj I₁)).obj) := by
    simpa [D] using
      restricted_pullback_vs_ambient_pullback_comparison_inv_postcompose
        (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)
  -- Rewrite the trailing restricted `I₁.f`-pullback through the component-object comparison.
  have htail :
      comparison.hom.1 ≫ (canonicalPullbackChoice p).map I₁.f x' =
        ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
    simpa [comparison, x'] using
      restricted_cover_descent_component_pullback_object_identification_hom_postcompose
        (J := J) (p := p) (P := P) (hpullback := hpullback)
        (S := S) (x := x) I₁
  -- The already-isolated transport square over `f₁` moves the middle comparison once, after
  -- which the ambient common shell is visible by reassociation.
  have hfirst :
      (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
        (canonicalPullbackChoice p).map f₁
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
              (D.obj I₁)).obj) ≫
          comparison.hom.1 ≫
          (canonicalPullbackChoice p).map I₁.f x' := by
    have hfrontPost :
        (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
          (canonicalPullbackChoice p).map f₁
              (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
                (D.obj I₁)).obj) ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
      have hfrontPostRaw :
          ((restricted_pullback_vs_ambient_pullback_comparison
                (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
              ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom) ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
          (canonicalPullbackChoice p).map f₁
              (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
                (D.obj I₁)).obj) ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
        exact
          congrArg
            (fun k ↦ k ≫ ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom)
            hfront
      simpa [Category.assoc] using hfrontPostRaw
    have htailPre :
        (canonicalPullbackChoice p).map f₁
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
              (D.obj I₁)).obj) ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
        (canonicalPullbackChoice p).map f₁
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
              (D.obj I₁)).obj) ≫
          comparison.hom.1 ≫
          (canonicalPullbackChoice p).map I₁.f x' := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (canonicalPullbackChoice p).map f₁
                (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
                  (D.obj I₁)).obj) ≫
              k)
          htail.symm
    exact hfrontPost.trans htailPre
  have htransport :
      (canonicalPullbackChoice p).map f₁
          (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
            (D.obj I₁)).obj) ≫
        comparison.hom.1 =
      (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map comparison.hom).1 ≫
        (canonicalPullbackChoice p).map f₁
          (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') := by
    simpa [comparison, D, x'] using
      restricted_cover_toDescentData_component_left_boundary_transport_f₁
        (J := J) (p := p) (P := P) (hpullback := hpullback)
        (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hsecond :
      (canonicalPullbackChoice p).map f₁
          (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
            (D.obj I₁)).obj) ≫
        comparison.hom.1 ≫
        (canonicalPullbackChoice p).map I₁.f x' =
      (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map comparison.hom).1 ≫
        (canonicalPullbackChoice p).map f₁
          (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
        (canonicalPullbackChoice p).map I₁.f x' := by
    have htransportPost :
        ((canonicalPullbackChoice p).map f₁
              (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₁.Y).obj
                (D.obj I₁)).obj) ≫
            comparison.hom.1) ≫
          (canonicalPullbackChoice p).map I₁.f x' =
        ((((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map comparison.hom).1 ≫
            (canonicalPullbackChoice p).map f₁
              (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₁.f x' := by
      exact congrArg (fun k ↦ k ≫ (canonicalPullbackChoice p).map I₁.f x') htransport
    simpa [Category.assoc] using htransportPost
  exact hfirst.trans hsecond

/-- Helper for Lemma 8.4.3: the raw left ambient `mapComp'.inv` boundary is the restricted
componentwise `mapComp'.inv` boundary conjugated by the two pullback-comparison maps over `f₁`
and the common overlap leg `q`. -/
private theorem restricted_cover_toDescentData_component_left_boundary_normal_form
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
      (((canonicalFiberPseudofunctor p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
          (((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x).obj)) =
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
        ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
            x)).hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback q x).hom := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let ambientLeft :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
      (((canonicalFiberPseudofunctor p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
          (((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x).obj))
  let restrictedLeft :=
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
              I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app
          x)).hom
  let restrictedMiddle :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback q x).hom
  let commonShell :=
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_cover_descent_component_pullback_object_identification
          (J := J) (p := p) (P := P) hpullback S x I₁).hom).1 ≫
      (canonicalPullbackChoice p).map f₁
        (((canonicalFiberPseudofunctor p).map I₁.f.op.toLoc).toFunctor.obj x') ≫
      (canonicalPullbackChoice p).map I₁.f x'
  have hambient :
      ambientLeft.1 ≫ (canonicalPullbackChoice p).map q x' = commonShell := by
    -- The ambient left boundary already lands on the common shell after one postcompose.
    simpa [ambientLeft, commonShell, x'] using
      restricted_cover_toDescentData_component_left_boundary_postcompose_common_shell
        (J := J) (p := p) (P := P) (hpullback := hpullback)
        (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hrestricted :
      (restrictedLeft ≫ restrictedMiddle).1 ≫ (canonicalPullbackChoice p).map q x' =
        commonShell := by
    -- The restricted side reaches the same shell by first collapsing the `q`-comparison and
    -- then transporting the restricted iterated pullbacks once to ambient notation.
    have hpostpullbacks :
        (restrictedLeft ≫ restrictedMiddle).1 ≫ (canonicalPullbackChoice p).map q x' =
          (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom := by
      simpa [restrictedLeft, restrictedMiddle, D, x'] using
        restricted_cover_toDescentData_component_left_boundary_postcompose_to_restricted_pullbacks
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
    have hcommon :
        (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv.1 ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map f₁ (D.obj I₁)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₁.f x).hom =
        commonShell := by
      simpa [commonShell, D, x', Category.assoc] using
        restricted_cover_toDescentData_component_left_boundary_restricted_pullbacks_common_shell
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
    exact hpostpullbacks.trans hcommon
  -- Since both boundaries have the same postcomposition with the strongly cartesian ambient
  -- `q`-pullback, the boundaries themselves are equal.
  simpa [D, ambientLeft, restrictedLeft, restrictedMiddle] using
    restricted_cover_toDescentData_component_left_boundary_cancel
      (p := p) (q := q) (x' := x') ambientLeft (restrictedLeft ≫ restrictedMiddle)
      (hambient.trans hrestricted.symm)

/-- Helper for Lemma 8.4.3: the raw right restricted `mapComp'.hom` boundary, followed by the
legwise pullback-comparison over `f₂`, is the common `q`-comparison followed by the ambient
canonical right `mapComp'.hom` boundary. -/
private theorem restricted_cover_toDescentData_component_right_boundary_two_stage_postcompose_common_shell
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₂ : S.Arrow}
    (f₂ : Y ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    let x' :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
    let shell :=
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
            (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                  I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                  (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)).hom ≫
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
          ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
            (restricted_pullback_vs_ambient_pullback_comparison
              (J := J) (p := p) (P := P) hpullback I₂.f x).hom
    (((shell.1 ≫
        (canonicalPullbackChoice p).map f₂
          (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
      (canonicalPullbackChoice p).map I₂.f x') =
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback q x).hom.1 ≫
      (canonicalPullbackChoice p).map q x') := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let F := restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y
  let comparison :=
    restricted_cover_descent_component_pullback_object_identification
      (J := J) (p := p) (P := P) hpullback S x I₂
  let restrictedBoundary :=
    (F.map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)).hom.1
  let ambientLegComparison :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom.1
  let ambientTailComparison :=
    (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
      comparison.hom).1
  let shell :=
    (F.map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
            x)).hom ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map comparison.hom
  have htail :
      ambientTailComparison ≫
          (canonicalPullbackChoice p).map f₂
            (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
          (canonicalPullbackChoice p).map I₂.f x' =
        (canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom := by
    -- First move the component-object comparison across the ambient `f₂`-pullback, then
    -- collapse the remaining `I₂.f` comparison to the restricted chosen pullback.
    have htransport :
        ambientTailComparison ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') =
          (canonicalPullbackChoice p).map f₂
              (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
                (D.obj I₂)).obj) ≫
            comparison.hom.1 := by
      simpa [ambientTailComparison, comparison, D, x'] using
        restricted_cover_descent_component_pullback_object_identification_hom_map_pullbackChoice
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (S := S) (x := x) (I := I₂) (f := f₂)
    have htransportPost :
        ambientTailComparison ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
            (canonicalPullbackChoice p).map I₂.f x' =
          (canonicalPullbackChoice p).map f₂
              (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
                (D.obj I₂)).obj) ≫
            comparison.hom.1 ≫
            (canonicalPullbackChoice p).map I₂.f x' := by
      have htransportPostRaw :
          (ambientTailComparison ≫
                (canonicalPullbackChoice p).map f₂
                  (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
              (canonicalPullbackChoice p).map I₂.f x' =
            ((canonicalPullbackChoice p).map f₂
                  (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
                    (D.obj I₂)).obj) ≫
                comparison.hom.1) ≫
              (canonicalPullbackChoice p).map I₂.f x' := by
        exact
          congrArg
            (fun k ↦ k ≫ (canonicalPullbackChoice p).map I₂.f x')
            htransport
      simpa [Category.assoc] using htransportPostRaw
    have hpost :
        (canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) ≫
          comparison.hom.1 ≫
          (canonicalPullbackChoice p).map I₂.f x' =
        (canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦
            (canonicalPullbackChoice p).map f₂
                (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
                  (D.obj I₂)).obj) ≫
              k)
          (restricted_cover_descent_component_pullback_object_identification_hom_postcompose
            (J := J) (p := p) (P := P) (hpullback := hpullback)
            (S := S) (x := x) I₂)
    exact htransportPost.trans hpost
  have hmiddle :
      ambientLegComparison ≫
          (canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) =
        ((canonicalPullbackChoice (P.ι ⋙ p)).map f₂ (D.obj I₂)).hom := by
    -- The legwise restricted/ambient comparison over `f₂` converts the ambient chosen pullback
    -- back to the restricted one.
    simpa [ambientLegComparison, D] using
      restricted_pullback_vs_ambient_pullback_comparison_hom_postcompose
        (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)
  have hq :
      (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback q x).hom.1 ≫
        (canonicalPullbackChoice p).map q x' =
      ((canonicalPullbackChoice (P.ι ⋙ p)).map q x).hom := by
    -- Finally rewrite the restricted chosen pullback over `q` back to the ambient comparison
    -- shell used throughout the fixed-cover argument.
    simpa [x'] using
      restricted_pullback_vs_ambient_pullback_comparison_hom_postcompose
        (J := J) (p := p) (P := P) hpullback q x
  have hfirst :
      ((shell.1 ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₂.f x') =
        restrictedBoundary ≫
          ambientLegComparison ≫
          (ambientTailComparison ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₂.f x' := by
    have hshell_expand :
        shell.1 = restrictedBoundary ≫ ambientLegComparison ≫ ambientTailComparison := by
      rfl
    calc
      ((shell.1 ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₂.f x') =
        (((restrictedBoundary ≫ ambientLegComparison ≫ ambientTailComparison) ≫
              (canonicalPullbackChoice p).map f₂
                (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
            (canonicalPullbackChoice p).map I₂.f x') := by
              rw [hshell_expand]
      _ =
        restrictedBoundary ≫
          ambientLegComparison ≫
          (ambientTailComparison ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₂.f x' := by
            simp only [Category.assoc]
  have hsecond :
      restrictedBoundary ≫
          ambientLegComparison ≫
          (ambientTailComparison ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
          (canonicalPullbackChoice p).map I₂.f x' =
        restrictedBoundary ≫
          ambientLegComparison ≫
          ((canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ restrictedBoundary ≫ ambientLegComparison ≫ k) htail
  have hthird :
      restrictedBoundary ≫
          ambientLegComparison ≫
          ((canonicalPullbackChoice p).map f₂
            (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
              (D.obj I₂)).obj) ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom) =
        restrictedBoundary ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map f₂ (D.obj I₂)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom := by
    have hthirdRaw :
        (restrictedBoundary ≫
              (ambientLegComparison ≫
                (canonicalPullbackChoice p).map f₂
                  (((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I₂.Y).obj
                    (D.obj I₂)).obj))) ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom =
          (restrictedBoundary ≫
              ((canonicalPullbackChoice (P.ι ⋙ p)).map f₂ (D.obj I₂)).hom) ≫
            ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom := by
      exact
        congrArg
          (fun k ↦ k ≫ ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom)
          (congrArg (fun k ↦ restrictedBoundary ≫ k) hmiddle)
    simpa [Category.assoc] using hthirdRaw
  have hfourth_raw :=
    (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
      (p := P.ι ⋙ p) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x)
  have hfourth :
      restrictedBoundary ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map f₂ (D.obj I₂)).hom ≫
          ((canonicalPullbackChoice (P.ι ⋙ p)).map I₂.f x).hom =
        ((canonicalPullbackChoice (P.ι ⋙ p)).map q x).hom := by
    simpa [restrictedBoundary, Category.assoc, D] using
      congrArg (fun k ↦ k.hom) hfourth_raw
  exact hfirst.trans <| hsecond.trans <| hthird.trans <| hfourth.trans <|
    (by simpa [Category.assoc] using hq.symm)

/-- Helper for Lemma 8.4.3: the raw right restricted `mapComp'.hom` boundary, followed by the
legwise pullback-comparison over `f₂`, is the common `q`-comparison followed by the ambient
canonical right `mapComp'.hom` boundary. -/
private theorem restricted_cover_toDescentData_component_right_boundary_normal_form
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₂ : S.Arrow}
    (f₂ : Y ⟶ I₂.Y)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)).obj x)
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
          x)).hom ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom =
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback q x).hom ≫
      (((canonicalFiberPseudofunctor p).mapComp'
            I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
        (((fullSubcategory_fiber_equiv_inverseImage
            (p := p) (P := P) U).functor.obj x).obj)) := by
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) U).obj x).obj
  let shell :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
                I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
                (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app
            x)).hom ≫
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
        ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom
  let restrictedMiddle :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback q x).hom
  let ambientRight :=
    (((canonicalFiberPseudofunctor p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x')
  let ambientRightInv :=
    (((canonicalFiberPseudofunctor p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).inv.toNatTrans.app x')
  have hstage :
      ((shell.1 ≫
          (canonicalPullbackChoice p).map f₂
            (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
        (canonicalPullbackChoice p).map I₂.f x') =
      restrictedMiddle.1 ≫ (canonicalPullbackChoice p).map q x' := by
    -- The structural right-boundary lemma already identifies the full postcomposition shell with
    -- the common ambient `q`-boundary.
    simpa [shell, restrictedMiddle, D, x'] using
      restricted_cover_toDescentData_component_right_boundary_two_stage_postcompose_common_shell
        (J := J) (p := p) (P := P) (hpullback := hpullback)
        (S := S) (x := x) (q := q) (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hrightpost :
      ambientRight.1 ≫
          (canonicalPullbackChoice p).map f₂
            (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
          (canonicalPullbackChoice p).map I₂.f x' =
        (canonicalPullbackChoice p).map q x' := by
    -- The ambient `mapComp'.hom` boundary postcomposes to the ambient chosen pullback over `q`.
    simpa [ambientRight, x'] using
      restricted_cover_toDescentData_component_right_boundary_postcompose
        (J := J) (p := p) (P := P) (S := S) (x := x)
        (q := q) (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hrightinvpost :
      ambientRightInv.1 ≫ (canonicalPullbackChoice p).map q x' =
        (canonicalPullbackChoice p).map f₂
          (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
        (canonicalPullbackChoice p).map I₂.f x' := by
    -- This is the owner-side inverse `mapComp'` factorization for the ambient chosen pullbacks.
    simpa [ambientRightInv, x'] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := p) (f := I₂.f) (g := f₂) (gf := q) (hgf := hf₂) x'
  have hcancelPost :
      (shell ≫ ambientRightInv).1 ≫ (canonicalPullbackChoice p).map q x' =
        restrictedMiddle.1 ≫ (canonicalPullbackChoice p).map q x' := by
    -- Reexpress the postcomposition of `shell ≫ ambientRightInv` using the previous two
    -- identities; this isolates exactly the common `q`-postcomposition needed for cancellation.
    have hshellpost :
        shell.1 ≫ ambientRightInv.1 ≫ (canonicalPullbackChoice p).map q x' =
          shell.1 ≫
            (canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x') ≫
            (canonicalPullbackChoice p).map I₂.f x' := by
      simpa [Category.assoc] using congrArg (fun k ↦ shell.1 ≫ k) hrightinvpost
    calc
      (shell ≫ ambientRightInv).1 ≫ (canonicalPullbackChoice p).map q x' =
          (shell.1 ≫ ambientRightInv.1) ≫ (canonicalPullbackChoice p).map q x' := by
            rfl
      _ =
          shell.1 ≫ ambientRightInv.1 ≫ (canonicalPullbackChoice p).map q x' := by
            simp only [Category.assoc]
      _ =
          shell.1 ≫
            ((canonicalPullbackChoice p).map f₂
              (((canonicalFiberPseudofunctor p).map I₂.f.op.toLoc).toFunctor.obj x')) ≫
            (canonicalPullbackChoice p).map I₂.f x' := by
              exact hshellpost
      _ =
          restrictedMiddle.1 ≫ (canonicalPullbackChoice p).map q x' := by
            simpa [Category.assoc] using hstage
  have hcancel :
      shell ≫ ambientRightInv = restrictedMiddle := by
    -- The common `q`-postcomposition determines vertical morphisms uniquely because the chosen
    -- pullback over `q` is strongly cartesian.
    exact
      restricted_cover_toDescentData_component_left_boundary_cancel
        (p := p) (q := q) (x' := x') (shell ≫ ambientRightInv) restrictedMiddle hcancelPost
  -- Cancel the inverse `mapComp'` component on the right to recover the desired raw-shell
  -- normalization.
  have hshell :
      shell = (shell ≫ ambientRightInv) ≫ ambientRight := by
    let e :=
      ((canonicalFiberPseudofunctor p).mapComp'
        I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
        (comp_toLoc_eq I₂.f f₂ q hf₂))
    have hisoNat :
        e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 _ := by
      exact congrArg (fun k ↦ k.1) e.inv_hom_id
    have hiso :
        ambientRightInv.1 ≫ ambientRight.1 = 𝟙 _ := by
      simpa [ambientRight, ambientRightInv, e] using
        congrArg (fun η ↦ (η.app x').1) hisoNat
    apply Functor.Fiber.hom_ext
    have hshell' :
        shell.1 ≫ ambientRightInv.1 ≫ ambientRight.1 = shell.1 := by
      have hshellMid :
          shell.1 ≫ (ambientRightInv.1 ≫ ambientRight.1) =
            shell.1 ≫ 𝟙 _ := by
        exact congrArg (fun k ↦ shell.1 ≫ k) hiso
      calc
        shell.1 ≫ ambientRightInv.1 ≫ ambientRight.1 =
            shell.1 ≫ (ambientRightInv.1 ≫ ambientRight.1) := by
          rfl
        _ = shell.1 ≫ 𝟙 _ := hshellMid
        _ = shell.1 := by
          simp only [Category.comp_id]
    simpa [Category.assoc] using hshell'.symm
  calc
    shell = (shell ≫ ambientRightInv) ≫ ambientRight := hshell
    _ = restrictedMiddle ≫ ambientRight := by
      rw [hcancel]

/-- Helper for Lemma 8.4.3: for a fixed restricted fiber object, the component pullback-
comparison isomorphisms satisfy the fixed-cover overlap square between the restricted
componentwise bridge and the ambient canonical descent datum. -/
private theorem restricted_cover_toDescentData_component_app_comm
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
      (((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).obj).hom q f₁ f₂ hf₁ hf₂ =
    (((restricted_cover_descent_to_componentwise_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj x)).obj).hom q f₁ f₂ hf₁ hf₂ ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom := by
  -- Route correction: the definitional wrappers are now isolated in a separate helper, so the
  -- only remaining work is the raw shell normalization between the ambient and restricted
  -- boundaries.
  rw [restricted_cover_toDescentData_component_ambient_side_peel
      (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (x := x)
      (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
      (hf₁ := hf₁) (hf₂ := hf₂)]
  rw [restricted_cover_toDescentData_component_restricted_side_expand
      (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S) (x := x)
      (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
      (hf₁ := hf₁) (hf₂ := hf₂)]
  -- Unfold the ambient overlap shell and the restricted comparison shell to the common fixed-
  -- cover comparison route; the remaining gap is exactly the two boundary normalizations.
  rw [restricted_cover_toDescentData_component_ambient_raw_shell
      (J := J) (p := p) (P := P) (S := S) (x := x)
      (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
      (hf₁ := hf₁) (hf₂ := hf₂)]
  -- Split the restricted canonical overlap into its `mapComp'.inv` and `mapComp'.hom` factors,
  -- then rewrite the left and right boundaries to the common ambient `q`-comparison shell.
  let D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
    (fun I : S.Arrow ↦ I.f)).obj x)
  let x' :=
    (((fullSubcategory_fiber_equiv_inverseImage
        (p := p) (P := P) U).functor.obj x).obj)
  -- Expose the ambient and restricted shells that the two boundary normal-form lemmas control.
  -- Route correction: the remaining blocker is not the left/right transport anymore, but the
  -- final split of the restricted mapped composite into these two named factors.
  let ambientLeft :=
    ((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom ≫
      (((canonicalFiberPseudofunctor p).mapComp'
            I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
            (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x')
  let ambientRight :=
    (((canonicalFiberPseudofunctor p).mapComp'
          I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
          (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x')
  let restrictedLeft :=
    (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₁ (D.obj I₁)).inv ≫
      ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
              I₁.f.op.toLoc f₁.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₁.f f₁ q hf₁)).inv.toNatTrans.app x)).hom
  let restrictedMiddle :=
    (restricted_pullback_vs_ambient_pullback_comparison
      (J := J) (p := p) (P := P) hpullback q x).hom
  let restrictedRight :=
    ((restrictedFiber_to_inverseImage_fiber (p := p) (P := P) Y).map
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).mapComp'
              I₂.f.op.toLoc f₂.op.toLoc q.op.toLoc
              (comp_toLoc_eq I₂.f f₂ q hf₂)).hom.toNatTrans.app x)).hom ≫
      (restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback f₂ (D.obj I₂)).hom ≫
      ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₂.f x).hom
  have hleft : ambientLeft = restrictedLeft ≫ restrictedMiddle := by
    -- The left boundary normalization is the dedicated fixed-cover transport lemma.
    simpa [ambientLeft, restrictedLeft, restrictedMiddle, D, x']
      using
        restricted_cover_toDescentData_component_left_boundary_normal_form
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (S := S) (x := x) (q := q) (I₁ := I₁) (f₁ := f₁) (hf₁ := hf₁)
  have hright : restrictedRight = restrictedMiddle ≫ ambientRight := by
    -- The right boundary normalization identifies the same middle `q`-comparison shell.
    simpa [ambientRight, restrictedMiddle, restrictedRight, D, x']
      using
        restricted_cover_toDescentData_component_right_boundary_normal_form
          (J := J) (p := p) (P := P) (hpullback := hpullback)
          (S := S) (x := x) (q := q) (I₂ := I₂) (f₂ := f₂) (hf₂ := hf₂)
  have hsplit :
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
          (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ ≫
        ((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom =
      restrictedLeft ≫ restrictedRight := by
    -- Expose the restricted canonical overlap as the raw `mapComp'.inv ≫ mapComp'.hom` shell.
    simpa [restrictedLeft, restrictedRight, D] using
      restricted_cover_toDescentData_component_restricted_raw_shell_split
        (J := J) (p := p) (P := P) (hpullback := hpullback)
        (S := S) (x := x) (q := q) (I₁ := I₁) (I₂ := I₂)
        (f₁ := f₁) (f₂ := f₂) (hf₁ := hf₁) (hf₂ := hf₂)
  have hcompare : ambientLeft ≫ ambientRight = restrictedLeft ≫ restrictedRight := by
    -- Reassociate through the common middle `q`-comparison shell identified by `hleft` and
    -- `hright`.
    rw [hleft]
    calc
      (restrictedLeft ≫ restrictedMiddle) ≫ ambientRight =
          restrictedLeft ≫ (restrictedMiddle ≫ ambientRight) := by
            simp only [Category.assoc]
      _ = restrictedLeft ≫ restrictedRight := by
            exact congrArg (fun k ↦ restrictedLeft ≫ k) hright.symm
  -- After exposing the restricted raw shell, both sides are the same comparison route up to
  -- reassociation through the common middle `q`-comparison shell.
  simpa [ambientLeft, ambientRight, restrictedLeft, restrictedRight, D, x'] using
    hcompare.trans hsplit.symm

/-- Helper for Lemma 8.4.3: for a fixed restricted source object, the legwise pullback-
comparison isomorphisms package to an isomorphism between the restricted and ambient
fixed-cover descent data. -/
noncomputable def restricted_cover_toDescentData_component_iso
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) :
    ((restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)) ≅
      ((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)) := by
  -- Package the cover-leg comparison isomorphisms into one descent-data isomorphism.
  refine ObjectProperty.isoMk (P := cover_componentwise_isoClosure_property
    (J := J) (p := p) (P := P) S) <|
    Pseudofunctor.DescentData.isoMk
      (fun I ↦ restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f x) ?_
  intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
  -- The fixed-cover component square is the dedicated normalization lemma just above.
  exact
    restricted_cover_toDescentData_component_app_comm
      (J := J) (p := p) (P := P) (hpullback := hpullback) S x q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.3: after passing through the restricted bridge, the restricted canonical
descent functor matches the ambient one through the fiberwise comparison equivalence. -/
noncomputable def restricted_cover_toDescentData_componentwise_transport_iso
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S ≅
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
        ambient_cover_toDescentData_isoClosure
          (J := J) (p := p) (P := P) hpullback S := by
  -- Route correction: build the fixed-cover transport directly in the theorem’s orientation,
  -- using the componentwise pullback-comparison isomorphisms instead of the proxy owner file.
  refine
    NatIso.ofComponents
      (fun x ↦ restricted_cover_toDescentData_component_iso
        (J := J) (p := p) (P := P) hpullback S x) ?_
  intro x y φ
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  -- Naturality reduces to the inverse-side pullback-comparison square on the cover leg `I.f`.
  simpa using
    restricted_cover_transport_component_naturality
      (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S)
      (φ := φ) (I := I)

/-- Helper for Lemma 8.4.3: the ambient inverse-image comparison and the ambient
componentwise-`isoClosure` descent functor compose to an equivalence for each fixed cover. -/
theorem fullSubcategory_coverwise_comparison_isEquivalence
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (_hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x)
    {U : C} (S : J.Cover U) :
    (((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor) ⋙
      ambient_cover_toDescentData_isoClosure
        (J := J) (p := p) (P := P) hpullback S).IsEquivalence := by
  let K := (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor
  let Fambient :=
    ambient_cover_toDescentData_isoClosure (J := J) (p := p) (P := P) hpullback S
  have hK : K.IsEquivalence := by
    -- The fiber comparison is packaged as an equivalence already, so its functor part is one.
    dsimp [K]
    infer_instance
  have hFambient : Fambient.IsEquivalence :=
    ambient_cover_toDescentData_isoClosure_isEquivalence
      (J := J) (p := p) (P := P) hpullback hlocal S
  letI : K.IsEquivalence := hK
  letI : Fambient.IsEquivalence := hFambient
  -- Compose the two ambient equivalences exactly as in the source proof.
  simpa [K, Fambient] using (Functor.isEquivalence_trans K Fambient)

/-- Helper for Lemma 8.4.3: once the restricted bridge is identified with the ambient coverwise
comparison by the transport isomorphism, the restricted canonical descent functor followed by
that bridge is an equivalence. -/
theorem restricted_cover_to_componentwise_isoClosure_comp_isEquivalence
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (_hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x)
    {U : C} (S : J.Cover U) :
    ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
        (fun I : S.Arrow ↦ I.f)) ⋙
      restricted_cover_descent_to_componentwise_isoClosure
        (J := J) (p := p) (P := P) hpullback S)).IsEquivalence := by
  have hcomp :
      (((fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor) ⋙
        ambient_cover_toDescentData_isoClosure
          (J := J) (p := p) (P := P) hpullback S).IsEquivalence :=
    fullSubcategory_coverwise_comparison_isEquivalence
      (J := J) (p := p) (P := P) hpullback hlocal S
  -- Transport the ambient equivalence back across the fixed-cover comparison isomorphism.
  exact
    (Functor.isEquivalence_iff_of_iso
      (restricted_cover_toDescentData_componentwise_transport_iso
        (J := J) (p := p) (P := P) hpullback S)).2 hcomp

/-- Helper for Lemma 8.4.3: essential surjectivity of the restricted fixed-cover bridge already
follows from essential surjectivity of its composite with the restricted canonical descent
functor. -/
theorem restricted_cover_descent_to_componentwise_isoClosure_essSurj_of_composite
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U)
    (hcomp :
      ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S)).EssSurj) :
    (restricted_cover_descent_to_componentwise_isoClosure
      (J := J) (p := p) (P := P) hpullback S).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  -- Choose a restricted source object whose image under the composite comparison already lands on
  -- the target datum `D`, then drop the first functor in the composite.
  rcases hcomp.mem_essImage D with ⟨x, ⟨e⟩⟩
  exact
    ⟨((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
        (fun I : S.Arrow ↦ I.f)).obj x, ⟨e⟩⟩

/-- Helper for Lemma 8.4.3: the corrected fixed-cover bridge is fully faithful componentwise, and
its essential surjectivity can be inherited from the already-established composite equivalence. -/
theorem restricted_cover_descent_to_componentwise_isoClosure_isEquivalence
    [(P.ι ⋙ p).IsFibered]
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (_hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x)
    {U : C} (S : J.Cover U) :
    (restricted_cover_descent_to_componentwise_isoClosure
      (J := J) (p := p) (P := P) hpullback S).IsEquivalence := by
  let F := restricted_cover_descent_to_componentwise_isoClosure
    (J := J) (p := p) (P := P) hpullback S
  have hBij :
      ∀ D₁ D₂, Function.Bijective
        (F.map :
          (D₁ ⟶ D₂) →
            (F.obj D₁ ⟶ F.obj D₂)) := by
    intro D₁ D₂
    refine ⟨?_, ?_⟩
    · intro ψ₁ ψ₂ hψ
      -- Compare the two restricted morphisms componentwise after canceling the strict
      -- inverse-image/restricted-fiber roundtrip on each cover object.
      apply Pseudofunctor.DescentData.hom_ext
      intro I
      have hI :
          (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
              (ψ₁.hom I) =
            (restrictedFiber_to_inverseImage_fiber (p := p) (P := P) I.Y).map
              (ψ₂.hom I) := by
        apply ObjectProperty.hom_ext
        simpa [F, restricted_cover_descent_to_componentwise_isoClosure] using
          congrArg (fun η ↦ η.hom.hom I) hψ
      have hI' := congrArg
        ((inverseImage_fiber_to_restrictedFiber (p := p) (P := P) I.Y).map) hI
      simpa using hI'
    · intro φ
      -- Fullness is already packaged by transporting each component back through the inverse
      -- fiber equivalence and checking the overlap square in the restricted fiber.
      exact restricted_cover_descent_hom_of_componentwise_isoClosure_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) S φ
  have hcompEquiv :
      ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_componentwise_isoClosure
          (J := J) (p := p) (P := P) hpullback S)).IsEquivalence := by
    -- The coverwise comparison with the ambient componentwise-`isoClosure` functor is already an
    -- equivalence by the local transport theorem.
    simpa using
      restricted_cover_to_componentwise_isoClosure_comp_isEquivalence
        (J := J) (p := p) (P := P) hpullback hlocal S
  letI : ((((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
      (fun I : S.Arrow ↦ I.f)) ⋙
    restricted_cover_descent_to_componentwise_isoClosure
      (J := J) (p := p) (P := P) hpullback S)).IsEquivalence := hcompEquiv
  have hEss : F.EssSurj :=
    restricted_cover_descent_to_componentwise_isoClosure_essSurj_of_composite
      (J := J) (p := p) (P := P) hpullback S inferInstance
  letI : F.Faithful := ⟨fun {D₁ D₂} ↦ (hBij D₁ D₂).injective⟩
  letI : F.Full := ⟨fun {D₁ D₂} ↦ (hBij D₁ D₂).surjective⟩
  letI : F.EssSurj := hEss
  exact
    { faithful := by infer_instance
      full := by infer_instance
      essSurj := by infer_instance }

/-- Lemma 8.4.3: if a stack over the site `(C, J)` has a full subcategory that is closed under
strongly cartesian pullback up to fiberwise isomorphism and is local for descent of objects in
each fiber, then the projection from that full subcategory to `C` is again a stack. -/
theorem fullSubcategory_projection_isStackOnSite
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    (hlocal : ∀ ⦃U : C⦄ (S : J.Cover U) (x : p.Fiber U)
      (_hx : ∀ I : S.Arrow,
        ((P.inverseImage (fiberInclusion : p.Fiber I.Y ⥤ X)).isoClosure)
          (I.f ^*[canonicalPullbackChoice p] x)),
      ((P.inverseImage (fiberInclusion : p.Fiber U ⥤ X)).isoClosure) x) :
    IsStackOnSite J (P.ι ⋙ p) := by
  letI : (P.ι ⋙ p).IsFibered :=
    fullSubcategory_projection_isFibered (p := p) (P := P) hpullback
  -- Check the stack condition coverwise and compare the restricted descent functor to the ambient
  -- one through the fixed-cover transport isomorphism.
  rw [isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence]
  intro U S
  let F :=
    (canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData (fun I : S.Arrow ↦ I.f)
  let TF :=
    restricted_cover_descent_to_componentwise_isoClosure
      (J := J) (p := p) (P := P) hpullback S
  have hTF : TF.IsEquivalence :=
    restricted_cover_descent_to_componentwise_isoClosure_isEquivalence
      (J := J) (p := p) (P := P) hpullback hlocal S
  letI : TF.IsEquivalence := hTF
  have htransport : (F ⋙ TF).IsEquivalence := by
    -- The source-proof comparison with the ambient fixed-cover functor has already been packaged
    -- in the dedicated transport lemma above.
    simpa [F, TF] using
      restricted_cover_to_componentwise_isoClosure_comp_isEquivalence
        (J := J) (p := p) (P := P) hpullback hlocal S
  letI : (F ⋙ TF).IsEquivalence := htransport
  simpa [F] using (Functor.isEquivalence_of_comp_right F TF : F.IsEquivalence)

end

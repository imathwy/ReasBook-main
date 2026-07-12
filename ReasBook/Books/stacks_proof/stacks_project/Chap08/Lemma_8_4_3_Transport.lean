import StacksProject_2024.Chap08.Lemma_8_4_3_RestrictedDescent

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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the overlap morphism in the corrected forward bridge is exactly the
comparison-conjugated shell exported by `RestrictedDescentForward`. -/
@[simp] private theorem restricted_cover_descent_to_isoClosure_obj_hom
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
    ((((restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj D).obj).hom
        q f₁ f₂ hf₁ hf₂) =
      restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison
        (J := J) (p := p) (P := P) hpullback S D q f₁ f₂ hf₁ hf₂ := by
  -- The corrected bridge stores this shell as its overlap morphism by definition.
  rfl

/-- Helper for Chap08 Lemma 8 4 3 Transport: the ambient fixed-cover `isoClosure` functor keeps the canonical
ambient overlap morphism definitionally unchanged after forgetting the full-subcategory wrapper. -/
@[simp] private theorem ambient_cover_toDescentData_isoClosure_obj_hom
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


/-- Helper for Chap08 Lemma 8 4 3 Transport: for a fixed source object in the restricted fiber, the componentwise
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the inclusion fibred morphism sends the restricted chosen pullback
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: precomposing the ambient fixed-cover overlap map by the left
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: postcomposing the restricted fixed-cover overlap map by the right
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
    (((restricted_cover_descent_to_isoClosure
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
      (restricted_cover_descent_to_isoClosure_obj_hom
        (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S)
        (D := (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x))
        (q := q) (I₁ := I₁) (I₂ := I₂) (f₁ := f₁) (f₂ := f₂)
        (hf₁ := hf₁) (hf₂ := hf₂))

/-- Helper for Chap08 Lemma 8 4 3 Transport: the raw left ambient `mapComp'.inv` boundary is the restricted
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the raw left ambient `mapComp'.inv` boundary is the restricted
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the ambient right `mapComp'.hom` boundary becomes the chosen ambient
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the `I`-component of the restricted canonical descent datum is not
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the specialized component comparison is exactly the owner comparison
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: postcomposing the specialized component comparison with the ambient
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: postcomposing the inverse of the specialized component comparison with
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: pulling back the component-object identification along a further leg
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: after peeling the ambient full-subcategory wrapper, the ambient
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the ambient left `mapComp'.inv` postcompose identity can be used in
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: after unfolding the canonical restricted fixed-cover descent datum,
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the ambient left `mapComp'.inv` postcompose factorization is stable
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: transporting the specialized component-object identification through
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: after postcomposing the ambient left boundary by the chosen ambient
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: once the restricted left shell is postcomposed by the ambient chosen
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the iterated restricted chosen pullbacks transport once to the common
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the raw left ambient `mapComp'.inv` boundary is the restricted
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the raw right restricted `mapComp'.hom` boundary, followed by the
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: the raw right restricted `mapComp'.hom` boundary, followed by the
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

/-- Helper for Chap08 Lemma 8 4 3 Transport: for a fixed restricted fiber object, the component pullback-
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
    (((restricted_cover_descent_to_isoClosure
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


/-- Helper for Chap08 Lemma 8 4 3 Transport: for a fixed source object in the restricted fiber, the componentwise
pullback-comparison isomorphisms satisfy the descent square relating the restricted and ambient
canonical fixed-cover descent data. -/
private theorem restricted_cover_toDescentData_transport_iso_app_comm
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom) ≫
      (((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).obj).hom q f₁ f₂ hf₁ hf₂ =
    (((restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj x)).obj).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom) := by
  -- The component square is the fixed-cover normal-form comparison proved by the private helper
  -- family above.
  exact
    restricted_cover_toDescentData_component_app_comm
      (J := J) (p := p) (P := P) (hpullback := hpullback) S x q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 4 3 Transport: for a fixed source object in the restricted fiber, the legwise
pullback-comparison isomorphisms package to an isomorphism between the restricted and ambient
fixed-cover descent data. -/
private noncomputable def restricted_cover_toDescentData_transport_component_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) :
    ((restricted_cover_descent_to_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)) ≅
      ((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)) :=
  ObjectProperty.isoMk (P := cover_componentwise_isoClosure_property
    (J := J) (p := p) (P := P) S) <|
    Pseudofunctor.DescentData.isoMk
      (fun I ↦ restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f x)
      (fun Y q I₁ I₂ f₁ f₂ hf₁ hf₂ ↦
        restricted_cover_toDescentData_transport_iso_app_comm
          (J := J) (p := p) (P := P) (hpullback := hpullback) S x q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 4 3 Transport: the componentwise transport isomorphisms are natural
in the restricted fiber object. -/
private theorem restricted_cover_toDescentData_transport_component_iso_naturality
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ∀ {x y : (P.ι ⋙ p).Fiber U} (φ : x ⟶ y),
      (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f) ⋙
          restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S).map φ) ≫
        (restricted_cover_toDescentData_transport_component_iso
          (J := J) (p := p) (P := P) hpullback S y).hom =
      (restricted_cover_toDescentData_transport_component_iso
          (J := J) (p := p) (P := P) hpullback S x).hom ≫
        (((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor ⋙
            ambient_cover_toDescentData_isoClosure
              (J := J) (p := p) (P := P) hpullback S).map φ) := by
  intro x y φ
  -- Naturality reduces componentwise to the inverse-side pullback-comparison square on each
  -- cover leg.
  apply ObjectProperty.hom_ext
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  simpa [restricted_cover_toDescentData_transport_component_iso] using
    restricted_cover_transport_component_naturality
      (J := J) (p := p) (P := P) (hpullback := hpullback) (S := S)
      (φ := φ) (I := I)

/-- Chap08 Lemma 8 4 3 Transport: compare the restricted canonical descent functor composed with
the forward bridge to the ambient canonical descent functor on the inverse-image full subcategory. -/
noncomputable def restricted_cover_toDescentData_transport_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_isoClosure (J := J) (p := p) (P := P) hpullback S ≅
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
        ambient_cover_toDescentData_isoClosure (J := J) (p := p) (P := P) hpullback S :=
  NatIso.ofComponents
    (fun x ↦
      restricted_cover_toDescentData_transport_component_iso
        (J := J) (p := p) (P := P) hpullback S x)
    (restricted_cover_toDescentData_transport_component_iso_naturality
      (J := J) (p := p) (P := P) hpullback S)

end RestrictedFibered

end

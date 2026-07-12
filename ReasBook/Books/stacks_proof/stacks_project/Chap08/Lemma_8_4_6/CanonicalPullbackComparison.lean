import StacksProject_2024.Chap04.Lemma_4_31_7
import StacksProject_2024.Chap04.Lemma_4_32_5
import StacksProject_2024.Chap04.Lemma_4_33_10
import StacksProject_2024.Chap04.Lemma_4_35_7
import StacksProject_2024.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import StacksProject_2024.Chap08.Definition_8_4_1
import StacksProject_2024.Chap08.Definition_8_4_5
import StacksProject_2024.Chap08.Lemma_8_4_2
import StacksProject_2024.Chap08.Lemma_8_4_4.EquivalenceTransport

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Lemma 8.4.6: the explicit stack-level `2`-fibre product projection is already
fibred, so the coverwise criterion from Lemma `8.4.2` applies directly to its canonical descent
functors. -/
theorem stack_two_fibre_product_projection_isFibered
    (F : X ⟶ S) (G : Y ⟶ S) :
    (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered :=
  FibredCategoryOver.isFibred
    (X := FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G))

/-- Helper for Lemma 8.4.6: composing in `C` and then passing to the locally discrete opposite is
the same as composing the corresponding `toLoc` arrows in the owner order used by `pullHom`. -/
theorem comp_toLoc_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := by
  -- Translate the composite equality to `LocallyDiscrete Cᵒᵖ`.
  simpa [← Quiver.Hom.comp_toLoc, ← op_comp] using
    congrArg Quiver.Hom.toLoc (congrArg Quiver.Hom.op hgf)

/-- Helper for Lemma 8.4.6: the hom component of the flexible pullback-composition comparison for
the canonical fiber pseudofunctor satisfies the same factorization identity as the chosen
pullback-composition comparison. -/
theorem canonicalFiberPseudofunctor_mapComp'_hom_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).hom.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x =
      (canonicalPullbackChoice p).map gf x := by
  -- Reduce the flexible comparison to the chosen pullback-composition comparison.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_fac f g x

/-- Helper for Lemma 8.4.6: the inverse component of the flexible pullback-composition
comparison for the canonical fiber pseudofunctor factors the composite pullback arrow through the
iterated chosen pullback arrows. -/
theorem canonicalFiberPseudofunctor_mapComp'_inv_app_fac
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : p.Fiber D) :
    (((canonicalFiberPseudofunctor p).mapComp'
          f.op.toLoc g.op.toLoc gf.op.toLoc
          (comp_toLoc_eq f g gf hgf)).inv.toNatTrans.app x).1 ≫
        (canonicalPullbackChoice p).map gf x =
      (canonicalPullbackChoice p).map g
          (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj x) ≫
        (canonicalPullbackChoice p).map f x := by
  -- Read the same chosen pullback-composition comparison in the inverse direction.
  subst gf
  simpa [PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackCompIso,
    Pseudofunctor.mapComp'_eq_mapComp] using
    (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f g x

/-- Helper for Lemma 8.4.6: after postcomposing both sides with the chosen target pullback arrow,
the pullback-comparison square for a stack morphism reduces to the mapped source pullback
factorization identity. -/
theorem map_canonical_pullbackFunctor_map_fac
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
        (H).toHom.map φ.1 =
      (H).toHom.map
          ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Apply the stack morphism to the source pullback factorization and normalize the composites.
  rw [← Functor.map_comp, ← Functor.map_comp]
  have hfac :
      ((canonicalPullbackChoice A.p).map f x) ≫ φ.1 =
        ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (canonicalPullbackChoice A.p).map f y := by
    exact
      (canonical_pullbackFunctor_map_fac
        (p := A.p) (f := f) (x := x) (y := y) (φ := φ)).symm
  exact congrArg (fun k ↦ (H).toHom.map k) hfac

/-- Helper for Lemma 8.4.6: after postcomposing both sides with the chosen target pullback arrow,
the pullback-comparison square for a stack morphism reduces to the mapped source pullback
factorization identity. -/
theorem stack_morphism_pullbackComparison_hom_postcompose_eq
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
        (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
      ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
  -- Compare the two candidates only after postcomposing with the common strongly cartesian
  -- target, which is the source-faithful uniqueness step from Lemma `8.2.3`.
  let lhs :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let mid₁ :=
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y)
  let mid₂ :=
    (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
      ((FibredCategoryMor.fiberFunctor H U).map φ).1
  let mid₃ :=
    ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
        (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
      ((FibredCategoryMor.fiberFunctor H U).map φ).1
  let mid₄ :=
    (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
      ((FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  let rhs :=
    ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
        ((FibredCategoryMor.fiberFunctor H V).map
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
      (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison isomorphism at `y` to the canonical target pullback arrow.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (FibredCategoryMor.pullbackComparison (H) f y).hom.1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y)
    exact
      congrArg
        (fun k ↦
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫ k)
        (FibredCategoryMor.pullbackComparison_hom_postcompose (H) f y)
  have h₂ : mid₁ = mid₂ := by
    -- Pullback in the target fiber is already natural on the vertical morphism `H.map φ`.
    change
      ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
          (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj y) =
        (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1
    exact
      canonical_pullbackFunctor_map_fac
        (p := B.p) (f := f) (φ := (FibredCategoryMor.fiberFunctor H U).map φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the target pullback arrow at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice B.p).map f ((FibredCategoryMor.fiberFunctor H U).obj x) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1 =
        (((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
          ((FibredCategoryMor.fiberFunctor H U).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((FibredCategoryMor.fiberFunctor H U).map φ).1)
        (FibredCategoryMor.pullbackComparison_hom_postcompose
          (H) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Map the source pullback factorization across `H` and then reassociate.
    calc
      (((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f x)) ≫
        ((FibredCategoryMor.fiberFunctor H U).map φ).1) =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((H).toHom.map ((canonicalPullbackChoice A.p).map f x) ≫
              ((FibredCategoryMor.fiberFunctor H U).map φ).1) := by
            rw [Category.assoc]
      _ =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((H).toHom.map
                ((((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
              (H).toHom.map ((canonicalPullbackChoice A.p).map f y)) := by
            exact
              congrArg
                (fun k ↦
                  (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫ k)
                (map_canonical_pullbackFunctor_map_fac
                  (H := H) (f := f) (φ := φ))
      _ =
          (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
            (H).toHom.map ((canonicalPullbackChoice A.p).map f y) := by
            rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y) =
        ((FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
            ((FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1) ≫
          (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.4.6: after forgetting to the total categories, the pullback-comparison
isomorphism for a stack morphism intertwines pullback of vertical morphisms with the image of the
pulled-back morphism. -/
theorem stack_morphism_pullbackComparison_hom_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ))).1 ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom.1 =
        (FibredCategoryMor.pullbackComparison (H) f x).hom.1 ≫
          ((FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)).1 := by
  -- Compare the two ambient arrows after postcomposing with the common strongly cartesian
  -- image of the chosen source pullback arrow.
  let ex := FibredCategoryMor.pullbackComparison (H) f x
  let ey := FibredCategoryMor.pullbackComparison (H) f y
  let η :
      ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor H U).obj x) ⟶
        ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.obj
          ((FibredCategoryMor.fiberFunctor H U).obj y) :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ)
  let θ :
      ((FibredCategoryMor.fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj x)) ⟶
        ((FibredCategoryMor.fiberFunctor H V).obj
          (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.obj y)) :=
    ((FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ))
  let φH :
      (((FibredCategoryMor.fiberFunctor H V).obj (f ^*[canonicalPullbackChoice A.p] y)).1 ⟶
        (((FibredCategoryMor.fiberFunctor H U).obj y).1)) :=
    (H).toHom.map ((canonicalPullbackChoice A.p).map f y)
  have hφH : B.p.IsStronglyCartesian f φH := by
    -- Transport the chosen source pullback lift across the stack morphism.
    change
      B.p.IsStronglyCartesian f
        ((H).toHom.map ((canonicalPullbackChoice A.p).map f y))
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (H) f
        ((canonicalPullbackChoice A.p).map f y)
        ((canonicalPullbackChoice A.p).isStronglyCartesian f y)
  letI : B.p.IsStronglyCartesian f φH := hφH
  letI : B.p.IsHomLift (𝟙 V) η.1 := by
    exact η.2
  letI : B.p.IsHomLift (𝟙 V) θ.1 := by
    exact θ.2
  letI : B.p.IsHomLift (𝟙 V) ex.hom.1 := by
    exact ex.hom.2
  letI : B.p.IsHomLift (𝟙 V) ey.hom.1 := by
    exact ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) η.1 η.2 V ey.hom.1 ey.hom.2
  letI : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ B.p _ _ _ _ _
      (𝟙 V) ex.hom.1 ex.hom.2 V θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φH = (ex.hom.1 ≫ θ.1) ≫ φH := by
    simpa only [η, θ, φH, Category.assoc] using
      stack_morphism_pullbackComparison_hom_postcompose_eq H f φ
  have hηey : B.p.IsHomLift (𝟙 V) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : B.p.IsHomLift (𝟙 V) (ex.hom.1 ≫ θ.1) := by infer_instance
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ B.p _ _ _ _
      f φH inferInstance _ _ (𝟙 V) (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.4.6: the pullback-comparison isomorphism for a stack morphism is fiberwise
natured on vertical morphisms. -/
theorem stack_morphism_pullbackComparison_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
        ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫
      (FibredCategoryMor.pullbackComparison (H) f y).hom =
        (FibredCategoryMor.pullbackComparison (H) f x).hom ≫
          (FibredCategoryMor.fiberFunctor H V).map
            (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) := by
  -- Reduce the fiber statement to the owner-level equality above with `Functor.Fiber.hom_ext`.
  apply Functor.Fiber.hom_ext
  exact stack_morphism_pullbackComparison_hom_naturality_over_vertical H f φ

/-- Helper for Lemma 8.4.6: the inverse pullback-comparison isomorphism carries the vertical
naturality square into the conjugation form needed for fixed-cover descent-data transport. -/
theorem stack_morphism_pullbackComparison_inv_naturality_over_vertical
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered] {U V : C} (f : V ⟶ U)
    {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) ≫
      (FibredCategoryMor.pullbackComparison (H) f y).inv =
        (FibredCategoryMor.pullbackComparison (H) f x).inv ≫
          (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor H U).map φ)) := by
  -- Route correction: move the already proved hom-side square across the two comparison inverses.
  let ex := FibredCategoryMor.pullbackComparison (H) f x
  let ey := FibredCategoryMor.pullbackComparison (H) f y
  let η :=
    ((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ)
  let θ :=
    (FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)
  have hhom : η ≫ ey.hom = ex.hom ≫ θ := by
    simpa only [ex, ey, η, θ] using
      stack_morphism_pullbackComparison_naturality_over_vertical H f φ
  symm
  apply (Iso.eq_comp_inv ey).2
  -- Precompose by `ex.inv` so the left comparison isomorphism cancels immediately.
  have hpre :
      ex.inv ≫
          ((((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫ ey.hom) =
        ex.inv ≫
          (ex.hom ≫
            (FibredCategoryMor.fiberFunctor H V).map
              (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

end CategoryTheory

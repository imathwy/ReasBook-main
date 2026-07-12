import StacksProject_2024.Chap04.Lemma_4_31_7
import StacksProject_2024.Chap04.Lemma_4_32_5
import StacksProject_2024.Chap04.Lemma_4_33_10
import StacksProject_2024.Chap04.Lemma_4_35_7
import StacksProject_2024.Chap08.Lemma_8_2_3.PullbackComparisonNaturality
import StacksProject_2024.Chap08.Definition_8_4_1
import StacksProject_2024.Chap08.Definition_8_4_5
import StacksProject_2024.Chap08.Lemma_8_4_2
import StacksProject_2024.Chap08.Lemma_8_4_6.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open InducedCategory.Hom
open CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : StackOver J}

/-- Helper for Chap08 Lemma 8 4 6: two fiber morphisms into a canonical pullback object are
equal when they agree after postcomposition with the chosen cartesian pullback arrow. -/
private theorem fiber_hom_ext_of_postcomp_canonicalPullback
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x : p.Fiber V} (y : p.Fiber U)
    (φ ψ :
      x ⟶ ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj y)
    (hpost :
      φ.1 ≫ (canonicalPullbackChoice p).map f y =
        ψ.1 ≫ (canonicalPullbackChoice p).map f y) :
    φ = ψ := by
  -- Forget to the total category, then use cartesian uniqueness against the common chosen
  -- pullback arrow of the target object.
  apply Functor.Fiber.hom_ext
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f ((canonicalPullbackChoice p).map f y)
      ((canonicalPullbackChoice p).isStronglyCartesian f y)
      _ _ (𝟙 V) φ.1 ψ.1 φ.2 ψ.2 hpost

/-- Helper for Chap08 Lemma 8 4 6: forgetting a composite in a fiber category gives the
composite of the forgotten underlying morphisms. -/
private theorem fiberInclusion_map_comp
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U : C} {x y z : p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    Functor.Fiber.fiberInclusion.map (φ ≫ ψ) =
      Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ := by
  -- This is just functoriality of the inclusion of the fiber into the total category.
  exact Functor.map_comp Functor.Fiber.fiberInclusion φ ψ

/-- Helper for Chap08 Lemma 8 4 6: forgetting a fiber composite whose first factor was built
from a total-category morphism exposes that morphism as the first factor. -/
private theorem fiberInclusion_map_homMk_comp
    {T : Type*} [Category T] (p : T ⥤ C) {U : C}
    {x y : T} (φ : x ⟶ y) [p.IsHomLift (𝟙 U) φ]
    {z : p.Fiber U}
    (ψ : Functor.Fiber.mk (IsHomLift.codomain_eq p (𝟙 U) φ) ⟶ z) :
    Functor.Fiber.fiberInclusion.map (Functor.Fiber.homMk p U φ ≫ ψ) =
      φ ≫ Functor.Fiber.fiberInclusion.map ψ := by
  -- The fiber inclusion is a functor, and `homMk` forgets to the total morphism used to build it.
  rw [Functor.map_comp, Functor.Fiber.fiberInclusion_homMk]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the same fiber-inclusion functoriality, stated on the
canonical fiber pseudofunctor surface used by descent-data components. -/
private theorem canonicalFiberPseudofunctor_fiberInclusion_map_comp
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U : LocallyDiscrete Cᵒᵖ} {x y z : (canonicalFiberPseudofunctor p).obj U}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    Functor.Fiber.fiberInclusion.map (φ ≫ ψ) =
      Functor.Fiber.fiberInclusion.map φ ≫ Functor.Fiber.fiberInclusion.map ψ := by
  -- The canonical pseudofunctor object is the fiber category, so this is the same inclusion law.
  exact Functor.map_comp Functor.Fiber.fiberInclusion φ ψ

/-- Helper for Chap08 Lemma 8 4 6: forgetting a component of a composite morphism of canonical
descent data is the composite of the forgotten components. -/
private theorem canonicalDescentData_hom_comp_underlying
    {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ C) [p.IsFibered]
    {U : C} {ι : Type*} {X : ι → C} {f : ∀ i, X i ⟶ U}
    {D₁ D₂ D₃ : (canonicalFiberPseudofunctor p).DescentData f}
    (φ : D₁ ⟶ D₂) (ψ : D₂ ⟶ D₃) (i : ι) :
    Functor.Fiber.fiberInclusion.map ((φ ≫ ψ).hom i) =
      Functor.Fiber.fiberInclusion.map (φ.hom i) ≫
        Functor.Fiber.fiberInclusion.map (ψ.hom i) := by
  -- Descent-data composition and fiber-category composition are both componentwise, so forgetting
  -- the component just removes the two subtype wrappers.
  rw [Pseudofunctor.DescentData.comp_hom]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover descent functor induced by a
fibred-category morphism acts componentwise on descent-data morphisms. -/
private theorem cover_descent_data_functor_map_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U : C} (T : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f))}
    (φ : D₁ ⟶ D₂) (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism (J := J) H T).map φ).hom I) =
      (FibredCategoryMor.fiberFunctor H I.Y).map (φ.hom I) := by
  -- Read off the componentwise definition of the fixed-cover transport functor on morphisms.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: a self-transport between descent data has identity
underlying component on each cover leg. -/
private theorem descentData_eqToHom_self_hom_underlying
    {𝒳 : Type*} [Category 𝒳] (p : 𝒳 ⥤ C) [p.IsFibered]
    {U : C} {ι : Type*} {Xc : ι → C} {f : ∀ i, Xc i ⟶ U}
    {D : (canonicalFiberPseudofunctor p).DescentData f}
    (h : D = D) (i : ι) :
    Functor.Fiber.fiberInclusion.map ((eqToHom h).hom i) =
      𝟙 (Functor.Fiber.fiberInclusion.obj (D.obj i)) := by
  -- Eliminate the object equality before evaluating the descent-data component.
  cases h
  exact Functor.map_id Functor.Fiber.fiberInclusion (D.obj i)

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover descent functor has the expected
comparison-conjugated overlap morphism on each object. -/
private theorem cover_descent_data_functor_obj_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U : C} (T : J.Cover U)
    (D : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    ((cover_descent_data_functor_of_stack_morphism (J := J) H T).obj D).hom
        q f₁ f₂ hf₁ hf₂ =
      cover_descent_data_functor_hom_of_stack_morphism
        (J := J) H T D q f₁ f₂ hf₁ hf₂ := by
  -- The object part of the fixed-cover functor stores exactly this transported overlap map.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the pullback-comparison isomorphism for a composite
fibred-category morphism is the composite of the two comparison isomorphisms. -/
private theorem fibredCategoryMor_pullbackComparison_comp_hom
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂) (G : X₂ ⟶ X₃)
    {U V : C} (f : V ⟶ U) (x : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (F ≫ G) f x).hom =
      (FibredCategoryMor.pullbackComparison G f
          ((FibredCategoryMor.fiberFunctor F U).obj x)).hom ≫
        (FibredCategoryMor.fiberFunctor G V).map
          (FibredCategoryMor.pullbackComparison F f x).hom := by
  let eF := FibredCategoryMor.pullbackComparison F f x
  let eG :=
    FibredCategoryMor.pullbackComparison G f ((FibredCategoryMor.fiberFunctor F U).obj x)
  let eGF := FibredCategoryMor.pullbackComparison (F ≫ G) f x
  have hcomp :
      eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom = eGF.hom := by
    -- Compare the two candidates after postcomposing with the image of the chosen source
    -- pullback arrow, where strong cartesian uniqueness applies.
    apply Functor.Fiber.hom_ext
    let θ := (F ≫ G).toHom.map ((canonicalPullbackChoice X₁.p).map f x)
    have hθ : X₃.p.IsStronglyCartesian f θ := by
      change X₃.p.IsStronglyCartesian f
        (G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)))
      exact
        FibredCategoryMor.map_stronglyCartesian_of_lift
          G f
          (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x))
          (FibredCategoryMor.map_stronglyCartesian_of_lift
            F f ((canonicalPullbackChoice X₁.p).map f x)
            ((canonicalPullbackChoice X₁.p).isStronglyCartesian f x))
    have hleft : X₃.p.IsHomLift (𝟙 V)
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1) := by
      exact (eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom).2
    have hright : X₃.p.IsHomLift (𝟙 V) eGF.hom.1 := by
      exact eGF.hom.2
    have hpost :
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1) ≫ θ =
          eGF.hom.1 ≫ θ := by
      -- The boundary of the two-step comparison and the direct comparison are both the
      -- canonical target pullback arrow.
      have hF :
          eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x) =
            (canonicalPullbackChoice X₂.p).map f
              ((FibredCategoryMor.fiberFunctor F U).obj x) := by
        simpa only [eF] using
          FibredCategoryMor.pullbackComparison_hom_postcompose F f x
      have hG :
          eG.hom.1 ≫ G.toHom.map
              ((canonicalPullbackChoice X₂.p).map f
                ((FibredCategoryMor.fiberFunctor F U).obj x)) =
            (canonicalPullbackChoice X₃.p).map f
              ((FibredCategoryMor.fiberFunctor G U).obj
                ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        simpa only [eG] using
          FibredCategoryMor.pullbackComparison_hom_postcompose G f
            ((FibredCategoryMor.fiberFunctor F U).obj x)
      have hGF :
          eGF.hom.1 ≫ θ =
            (canonicalPullbackChoice X₃.p).map f
              ((FibredCategoryMor.fiberFunctor G U).obj
                ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        simpa only [eGF, θ, BasedFunctor.comp] using
          FibredCategoryMor.pullbackComparison_hom_postcompose (F ≫ G) f x
      change
        (eG.hom.1 ≫ G.toHom.map eF.hom.1) ≫
            G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
          eGF.hom.1 ≫ θ
      have hstep₁ :
          (eG.hom.1 ≫ G.toHom.map eF.hom.1) ≫
              G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
            eG.hom.1 ≫
              G.toHom.map
                (eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) := by
        rw [Functor.map_comp]
        exact Category.assoc eG.hom.1 (G.toHom.map eF.hom.1)
          (G.toHom.map (F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)))
      have hstep₂ :
          eG.hom.1 ≫
              G.toHom.map
                (eF.hom.1 ≫ F.toHom.map ((canonicalPullbackChoice X₁.p).map f x)) =
            eG.hom.1 ≫
              G.toHom.map
                ((canonicalPullbackChoice X₂.p).map f
                  ((FibredCategoryMor.fiberFunctor F U).obj x)) := by
        exact congrArg (fun m ↦ eG.hom.1 ≫ G.toHom.map m) hF
      exact hstep₁.trans (hstep₂.trans (hG.trans hGF.symm))
    exact
      @Functor.IsStronglyCartesian.ext _ _ _ _ X₃.p _ _ _ _
        f θ hθ _ _ (𝟙 V)
        (eG.hom.1 ≫ ((FibredCategoryMor.fiberFunctor G V).map eF.hom).1)
        eGF.hom.1 hleft hright hpost
  exact hcomp.symm

/-- Helper for Chap08 Lemma 8 4 6: the inverse pullback-comparison for a composite fibred-category
morphism is the reverse composite of the inverse comparison isomorphisms. -/
private theorem fibredCategoryMor_pullbackComparison_comp_inv
    {X₁ X₂ X₃ : FibredCategoryOver C}
    (F : X₁ ⟶ X₂) (G : X₂ ⟶ X₃)
    {U V : C} (f : V ⟶ U) (x : X₁.p.Fiber U) :
    (FibredCategoryMor.pullbackComparison (F ≫ G) f x).inv =
      (FibredCategoryMor.fiberFunctor G V).map
          (FibredCategoryMor.pullbackComparison F f x).inv ≫
        (FibredCategoryMor.pullbackComparison G f
          ((FibredCategoryMor.fiberFunctor F U).obj x)).inv := by
  let eF := FibredCategoryMor.pullbackComparison F f x
  let eG :=
    FibredCategoryMor.pullbackComparison G f ((FibredCategoryMor.fiberFunctor F U).obj x)
  let eGF := FibredCategoryMor.pullbackComparison (F ≫ G) f x
  have hhom :
      eGF.hom = eG.hom ≫ (FibredCategoryMor.fiberFunctor G V).map eF.hom := by
    simpa only [eF, eG, eGF] using
      fibredCategoryMor_pullbackComparison_comp_hom F G f x
  -- Cancel against the direct composite comparison hom; the two inverse identities and
  -- functoriality of `G` leave the desired reverse composite.
  rw [← cancel_mono eGF.hom]
  calc
    eGF.inv ≫ eGF.hom = 𝟙 _ := by
      simp only [Iso.inv_hom_id]
    _ =
        ((FibredCategoryMor.fiberFunctor G V).map eF.inv ≫ eG.inv) ≫ eGF.hom := by
      rw [hhom]
      symm
      calc
        ((FibredCategoryMor.fiberFunctor G V).map eF.inv ≫ eG.inv) ≫ eG.hom ≫
            (FibredCategoryMor.fiberFunctor G V).map eF.hom =
          (FibredCategoryMor.fiberFunctor G V).map eF.inv ≫
            (eG.inv ≫ eG.hom) ≫
              (FibredCategoryMor.fiberFunctor G V).map eF.hom := by
          simp only [Category.assoc]
        _ = 𝟙 _ := by
          simp only [Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]

/-- Helper for Chap08 Lemma 8 4 6: fixed-cover descent transport along a composite fibred
category morphism is the same overlap morphism as transporting successively along the two
factors. -/
private theorem cover_descent_data_functor_hom_of_stack_morphism_comp
    {A B D : FibredCategoryOver C}
    (K : A ⟶ B) (H : B ⟶ D)
    [A.p.IsFibered] [B.p.IsFibered] [D.p.IsFibered]
    {U : C} (T : J.Cover U)
    (E : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    cover_descent_data_functor_hom_of_stack_morphism
        (J := J) (K ≫ H) T E q f₁ f₂ hf₁ hf₂ =
      (((cover_descent_data_functor_of_stack_morphism
          (J := J) K T ⋙
        cover_descent_data_functor_of_stack_morphism
          (J := J) H T).obj E).hom q f₁ f₂ hf₁ hf₂) := by
  -- Unfold both fixed-cover transports to the same comparison-conjugate shell, then use the
  -- composite comparison identities for the two boundary isomorphisms.
  simp only [Functor.comp_obj, cover_descent_data_functor_of_stack_morphism,
    cover_descent_data_functor_hom_of_stack_morphism]
  rw [fibredCategoryMor_pullbackComparison_comp_hom,
    fibredCategoryMor_pullbackComparison_comp_inv]
  let eH₁ :=
    FibredCategoryMor.pullbackComparison H f₁
      ((FibredCategoryMor.fiberFunctor K I₁.Y).obj (E.obj I₁))
  let eK₁ := FibredCategoryMor.pullbackComparison K f₁ (E.obj I₁)
  let d := E.hom q f₁ f₂ hf₁ hf₂
  let eK₂ := FibredCategoryMor.pullbackComparison K f₂ (E.obj I₂)
  let eH₂ :=
    FibredCategoryMor.pullbackComparison H f₂
      ((FibredCategoryMor.fiberFunctor K I₂.Y).obj (E.obj I₂))
  have hmap :
      (FibredCategoryMor.fiberFunctor (K ≫ H) V).map d =
        (FibredCategoryMor.fiberFunctor H V).map
          ((FibredCategoryMor.fiberFunctor K V).map d) := rfl
  -- Now both sides live in the same `H`-fiber functor normal form, so ordinary functoriality
  -- turns the mapped triple composite into the triple composite of mapped arrows.
  calc
    (eH₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map eK₁.hom) ≫
        (FibredCategoryMor.fiberFunctor (K ≫ H) V).map d ≫
          (FibredCategoryMor.fiberFunctor H V).map eK₂.inv ≫ eH₂.inv =
      (eH₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map eK₁.hom) ≫
        (FibredCategoryMor.fiberFunctor H V).map
            ((FibredCategoryMor.fiberFunctor K V).map d) ≫
          (FibredCategoryMor.fiberFunctor H V).map eK₂.inv ≫ eH₂.inv := by
        simpa only [Category.assoc] using
          congrArg
            (fun m =>
              (eH₁.hom ≫ (FibredCategoryMor.fiberFunctor H V).map eK₁.hom) ≫ m ≫
                (FibredCategoryMor.fiberFunctor H V).map eK₂.inv ≫ eH₂.inv)
            hmap
    _ =
      eH₁.hom ≫
        (FibredCategoryMor.fiberFunctor H V).map
          (eK₁.hom ≫ (FibredCategoryMor.fiberFunctor K V).map d ≫ eK₂.inv) ≫
          eH₂.inv := by
        rw [Functor.map_comp, Functor.map_comp]
        simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 4 6: applying a fibred-category morphism to a canonically
reindexed vertical morphism is the target reindexing of the mapped morphism conjugated by the
pullback-comparison isomorphisms. -/
private theorem fiberFunctor_map_reindexed_hom
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : A.p.Fiber U} (φ : x ⟶ y) :
    (FibredCategoryMor.fiberFunctor H V).map
        (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ) =
      (FibredCategoryMor.pullbackComparison H f x).inv ≫
        (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
          ((FibredCategoryMor.fiberFunctor H U).map φ)) ≫
        (FibredCategoryMor.pullbackComparison H f y).hom := by
  -- Start from the inverse-natural pullback-comparison square and cancel the target comparison
  -- inverse on the right.
  let ex := FibredCategoryMor.pullbackComparison H f x
  let ey := FibredCategoryMor.pullbackComparison H f y
  let θ :=
    (FibredCategoryMor.fiberFunctor H V).map
      (((canonicalFiberPseudofunctor A.p).map f.op.toLoc).toFunctor.map φ)
  let η :=
    (((canonicalFiberPseudofunctor B.p).map f.op.toLoc).toFunctor.map
      ((FibredCategoryMor.fiberFunctor H U).map φ))
  have hnat : θ ≫ ey.inv = ex.inv ≫ η := by
    simpa only [θ, η, ex, ey] using
      FibredCategoryMor.pullbackComparison_inv_naturality_over_vertical H (f := f) (φ := φ)
  have hpost : (θ ≫ ey.inv) ≫ ey.hom = (ex.inv ≫ η) ≫ ey.hom :=
    congrArg (fun k => k ≫ ey.hom) hnat
  have hleft : (θ ≫ ey.inv) ≫ ey.hom = θ := by
    calc
      (θ ≫ ey.inv) ≫ ey.hom = θ ≫ (ey.inv ≫ ey.hom) := by
        exact Category.assoc θ ey.inv ey.hom
      _ = θ ≫ 𝟙 _ := by
        exact congrArg (fun k => θ ≫ k) ey.inv_hom_id
      _ = θ := by
        rw [Category.comp_id]
  have hresult : θ = ex.inv ≫ η ≫ ey.hom :=
    hleft.symm.trans (hpost.trans (Category.assoc ex.inv η ey.hom))
  simpa only [θ, η, ex, ey] using hresult

/-- Helper for Chap08 Lemma 8 4 6: a square conjugated by pullback-comparison isomorphisms gives
the corresponding unconjugated square after cancelling the outer comparisons. -/
private theorem conjugated_square_cancel
    {𝒟 : Type*} [Category 𝒟]
    {A B C D E F G H : 𝒟}
    (e₁₁ : A ≅ B) (e₁₂ : C ≅ D) (e₂₁ : F ≅ E) (e₂₂ : H ≅ G)
    (m₁ : A ⟶ C) (d₂ : D ⟶ G) (d₁ : B ⟶ E) (m₂ : F ⟶ H)
    (h : m₁ ≫ e₁₂.hom ≫ d₂ ≫ e₂₂.inv =
      e₁₁.hom ≫ d₁ ≫ e₂₁.inv ≫ m₂) :
    e₁₁.inv ≫ m₁ ≫ e₁₂.hom ≫ d₂ =
      d₁ ≫ e₂₁.inv ≫ m₂ ≫ e₂₂.hom := by
  -- Precompose and postcompose the stored conjugated square, then cancel the two outer
  -- comparison isomorphism pairs.
  have hwrap :
      e₁₁.inv ≫ (m₁ ≫ e₁₂.hom ≫ d₂ ≫ e₂₂.inv) ≫ e₂₂.hom =
        e₁₁.inv ≫ (e₁₁.hom ≫ d₁ ≫ e₂₁.inv ≫ m₂) ≫ e₂₂.hom := by
    exact congrArg (fun k => e₁₁.inv ≫ k ≫ e₂₂.hom) h
  have hright :
      e₁₁.inv ≫ (e₁₁.hom ≫ d₁ ≫ e₂₁.inv ≫ m₂) ≫ e₂₂.hom =
        d₁ ≫ e₂₁.inv ≫ m₂ ≫ e₂₂.hom := by
    calc
      e₁₁.inv ≫ (e₁₁.hom ≫ d₁ ≫ e₂₁.inv ≫ m₂) ≫ e₂₂.hom =
          ((e₁₁.inv ≫ e₁₁.hom) ≫ d₁ ≫ e₂₁.inv ≫ m₂) ≫ e₂₂.hom := by
        simp only [Category.assoc]
      _ = ((𝟙 B ≫ d₁ ≫ e₂₁.inv ≫ m₂) ≫ e₂₂.hom) := by
        rw [e₁₁.inv_hom_id]
      _ = d₁ ≫ e₂₁.inv ≫ m₂ ≫ e₂₂.hom := by
        simp only [Category.id_comp, Category.assoc]
  have hleft :
      e₁₁.inv ≫ (m₁ ≫ e₁₂.hom ≫ d₂ ≫ e₂₂.inv) ≫ e₂₂.hom =
        e₁₁.inv ≫ m₁ ≫ e₁₂.hom ≫ d₂ := by
    calc
      e₁₁.inv ≫ (m₁ ≫ e₁₂.hom ≫ d₂ ≫ e₂₂.inv) ≫ e₂₂.hom =
          e₁₁.inv ≫ m₁ ≫ e₁₂.hom ≫ d₂ ≫ (e₂₂.inv ≫ e₂₂.hom) := by
        simp only [Category.assoc]
      _ = e₁₁.inv ≫ m₁ ≫ e₁₂.hom ≫ d₂ ≫ 𝟙 G := by
        rw [e₂₂.inv_hom_id]
      _ = e₁₁.inv ≫ m₁ ≫ e₁₂.hom ≫ d₂ := by
        simp only [Category.comp_id]
  exact hleft.symm.trans (hwrap.trans hright)

/-- Helper for Chap08 Lemma 8 4 6: a `𝟙`-lift can be reinterpreted over an equal base object. Stated with
both base objects as bound variables so that the substitution is type-correct (the entangled cover
leg `I.Y` need never be abstracted). -/
private theorem isHomLift_id_of_base_eq {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {U V : 𝒮} (h : U = V) {a b : 𝒳} (φ : a ⟶ b)
    (hlift : p.IsHomLift (𝟙 U) φ) : p.IsHomLift (𝟙 V) φ := by
  subst h; exact hlift

/-- Helper for Chap08 Lemma 8 4 6: a lift over an identity can be reinterpreted over the equality
transport between two objects of the same fiber. -/
private theorem isHomLift_eqToHom_comp_eqToHom_of_id {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {U V W : 𝒮} (hU : U = W) (hV : V = W) {a b : 𝒳}
    (φ : a ⟶ b) (hlift : p.IsHomLift (𝟙 W) φ) :
    p.IsHomLift (eqToHom hU ≫ eqToHom hV.symm) φ := by
  -- Substitute the two fiber-identification proofs; the transported base arrow becomes `𝟙 W`.
  subst hU
  subst hV
  simpa using hlift

/-- Helper for Chap08 Lemma 8 4 6: a lift over the equality transport between two objects of the same
fiber is a lift over the identity of that fiber. -/
private theorem isHomLift_id_of_eqToHom_comp_eqToHom {𝒳 𝒮 : Type*} [Category 𝒳] [Category 𝒮]
    (p : 𝒳 ⥤ 𝒮) {U V W : 𝒮} (hU : U = W) (hV : V = W) {a b : 𝒳}
    (φ : a ⟶ b) (hlift : p.IsHomLift (eqToHom hU ≫ eqToHom hV.symm) φ) :
    p.IsHomLift (𝟙 W) φ := by
  -- The same substitution turns the equality-transport base arrow back into an identity.
  subst hU
  subst hV
  simpa using hlift

/-- Helper for Chap08 Lemma 8 4 6: after taking the right projection and then applying `G`, the
fixed-cover owner object on each cover leg is definitionally the stored right component of the
explicit pullback object. -/
private theorem explicit_two_fibre_product_cover_descent_right_composite_obj_owner_typed
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
        (J := J) (toFibredCategoryMor G) T).obj
      ((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T).obj D)).obj I).1 =
      (FibredCategoryMor.toFunctor (toFibredCategoryMor G)).obj
        (((((D.obj I).1).obj.snd)).1) := by
  -- The right composite is the symmetric owner-level identification.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after normalizing the outer fiber equality on a fixed cover leg, the
stored explicit pullback comparison already has the exact projected target type in the `S`-fiber
over that leg. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_component_transport_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D).obj I) ≅
      (((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T).obj D).obj I) := by
  -- On the cover leg `I`, both projected objects are `F(x_I)` and `G(y_I)` for the stored explicit
  -- pullback object `D.obj I`, and the required comparison is its stored fibrewise pullback
  -- isomorphism, reinterpreted in the `S`-fiber over `I.Y` via the leg-membership base equality.
  have hU : ((D.obj I).1).U = I.Y := (D.obj I).2
  haveI hh : S.p.IsHomLift (𝟙 I.Y) (((D.obj I).1).obj.iso.hom).1 :=
    isHomLift_id_of_base_eq S.p hU _ ((D.obj I).1).obj.iso.hom.2
  haveI hi : S.p.IsHomLift (𝟙 I.Y) (((D.obj I).1).obj.iso.inv).1 :=
    isHomLift_id_of_base_eq S.p hU _ ((D.obj I).1).obj.iso.inv.2
  exact
    { hom := Functor.Fiber.homMk S.p I.Y (((D.obj I).1).obj.iso.hom).1
      inv := Functor.Fiber.homMk S.p I.Y (((D.obj I).1).obj.iso.inv).1
      hom_inv_id := by
        -- Equality in the fiber is checked after forgetting to the total category.
        apply Functor.Fiber.hom_ext
        change (((D.obj I).1).obj.iso.hom).1 ≫ (((D.obj I).1).obj.iso.inv).1 = 𝟙 _
        exact congrArg (Functor.Fiber.fiberInclusion.map) ((D.obj I).1).obj.iso.hom_inv_id
      inv_hom_id := by
        -- The second inverse law is the same underlying equality in the opposite direction.
        apply Functor.Fiber.hom_ext
        change (((D.obj I).1).obj.iso.inv).1 ≫ (((D.obj I).1).obj.iso.hom).1 = 𝟙 _
        exact congrArg (Functor.Fiber.fiberInclusion.map) ((D.obj I).1).obj.iso.inv_hom_id }

/-- Helper for Chap08 Lemma 8 4 6: the transported projection comparison has the stored explicit
pullback comparison as its underlying total-category morphism. -/
private theorem explicit_two_fibre_product_cover_descent_projection_component_transport_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I).hom =
      (((D.obj I).1).obj.iso.hom).1 := by
  -- Unfold only the local adapter iso; its hom was built from this explicit comparison.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: applying the ambient left projection to any morphism in the
fiber of the explicit two-fibre product reads off its stored left component. -/
private theorem explicit_two_fibre_product_left_projection_map_component
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C}
    {P Q :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) :
    Functor.Fiber.fiberInclusion.map
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) U).map φ) =
      (Functor.Fiber.fiberInclusion.map φ).a := by
  -- The explicit left projection is implemented by selecting the `a` field of the owner morphism.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: applying the ambient right projection to any morphism in the
fiber of the explicit two-fibre product reads off its stored right component. -/
private theorem explicit_two_fibre_product_right_projection_map_component
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C}
    {P Q :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) :
    Functor.Fiber.fiberInclusion.map
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) U).map φ) =
      (Functor.Fiber.fiberInclusion.map φ).b := by
  -- The explicit right projection is implemented by selecting the `b` field of the owner morphism.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the left component of a reindexed explicit-product morphism is
the reindexed left projection, conjugated by the left pullback-comparison isomorphisms. -/
private theorem explicit_two_fibre_product_left_projection_canonical_pullback_map_component
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U V : C} (f : V ⟶ U)
    {P Q :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) :
    (Functor.Fiber.fiberInclusion.map
      (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f.op.toLoc).toFunctor.map φ)).a =
      Functor.Fiber.fiberInclusion.map
        ((FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) f P).inv ≫
          (((canonicalFiberPseudofunctor X.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) U).map φ)) ≫
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) f Q).hom) := by
  -- Apply the generic reindexing normal form and then read the left explicit-product component.
  have h :=
    fiberFunctor_map_reindexed_hom
      (FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)) f φ
  simpa only [explicit_two_fibre_product_left_projection_map_component] using
    congrArg (fun α => Functor.Fiber.fiberInclusion.map α) h

/-- Helper for Chap08 Lemma 8 4 6: the right component of a reindexed explicit-product morphism is
the reindexed right projection, conjugated by the right pullback-comparison isomorphisms. -/
private theorem explicit_two_fibre_product_right_projection_canonical_pullback_map_component
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U V : C} (f : V ⟶ U)
    {P Q :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) :
    (Functor.Fiber.fiberInclusion.map
      (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f.op.toLoc).toFunctor.map φ)).b =
      Functor.Fiber.fiberInclusion.map
        ((FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) f P).inv ≫
          (((canonicalFiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
            ((FibredCategoryMor.fiberFunctor
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) U).map φ)) ≫
          (FibredCategoryMor.pullbackComparison
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) f Q).hom) := by
  -- The right projection follows the same generic normal form, reading the `b` component.
  have h :=
    fiberFunctor_map_reindexed_hom
      (FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)) f φ
  simpa only [explicit_two_fibre_product_right_projection_map_component] using
    congrArg (fun α => Functor.Fiber.fiberInclusion.map α) h

/-- Helper for Chap08 Lemma 8 4 6: the left component of a composite morphism in the explicit
two-fibre-product fiber is the composite of the left components. -/
private theorem explicit_two_fibre_product_hom_a_comp
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C}
    {P Q R :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (Functor.Fiber.fiberInclusion.map (φ ≫ ψ)).a =
      (Functor.Fiber.fiberInclusion.map φ).a ≫
        (Functor.Fiber.fiberInclusion.map ψ).a := by
  -- Composition of explicit-product morphisms is componentwise.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the right component of a composite morphism in the explicit
two-fibre-product fiber is the composite of the right components. -/
private theorem explicit_two_fibre_product_hom_b_comp
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C}
    {P Q R :
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U}
    (φ : P ⟶ Q) (ψ : Q ⟶ R) :
    (Functor.Fiber.fiberInclusion.map (φ ≫ ψ)).b =
      (Functor.Fiber.fiberInclusion.map φ).b ≫
        (Functor.Fiber.fiberInclusion.map ψ).b := by
  -- The right projection is computed componentwise as well.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: applying the fixed-cover left projection to an overlap morphism
extracts the left component of the explicit pullback morphism. -/
private theorem explicit_two_fibre_product_cover_descent_left_projection_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    Functor.Fiber.fiberInclusion.map
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (D.hom q f₁ f₂ hf₁ hf₂)) =
      ((D.hom q f₁ f₂ hf₁ hf₂).1).a := by
  -- Specialize the general left-projection component formula to this overlap morphism.
  exact
    explicit_two_fibre_product_left_projection_map_component
      (J := J) F G (φ := D.hom q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 4 6: applying the fixed-cover right projection to an overlap morphism
extracts the right component of the explicit pullback morphism. -/
private theorem explicit_two_fibre_product_cover_descent_right_projection_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    Functor.Fiber.fiberInclusion.map
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
        (D.hom q f₁ f₂ hf₁ hf₂)) =
      ((D.hom q f₁ f₂ hf₁ hf₂).1).b := by
  -- Specialize the general right-projection component formula to this overlap morphism.
  exact
    explicit_two_fibre_product_right_projection_map_component
      (J := J) F G (φ := D.hom q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 4 6: reindexing the explicit-product comparison and then applying
the right projected comparison has the same boundary as applying the left projected comparison
and then reading the comparison of the reindexed explicit product. -/
private theorem explicit_two_fibre_product_comparison_reindex_left_boundary
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) {V : C} (f : V ⟶ I.Y) :
    Functor.Fiber.fiberInclusion.map
        (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map
          (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
            (J := J) F G T D I).hom) ≫
      (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G)
        f (D.obj I)).hom.1 =
    (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F)
        f (D.obj I)).hom.1 ≫
      CategoryOver.ExplicitTwoFibreProductObject.comparison
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G))
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj (D.obj I)).1) := by
  -- Compare the two boundary morphisms after the right projected cartesian pullback arrow of the
  -- explicit product; both postcomposites reduce to the defining pullback comparison square.
  let HR := FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G
  let HL := FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F
  let α := ((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map
    (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
      (J := J) F G T D I).hom
  let eR := FibredCategoryMor.pullbackComparison HR f (D.obj I)
  let eL := FibredCategoryMor.pullbackComparison HL f (D.obj I)
  let compQ := CategoryOver.ExplicitTwoFibreProductObject.comparison
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G))
    ((((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f.op.toLoc).toFunctor.obj (D.obj I)).1)
  have hcompQ : S.p.IsHomLift (𝟙 V) compQ := by
    -- The comparison of the pulled-back explicit object lies over the identity of its stored
    -- base; the fiber membership equality identifies that base with `V`.
    have hbase :
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj (D.obj I)).1).U = V :=
      ((((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
            f.op.toLoc).toFunctor.obj (D.obj I)).2)
    exact isHomLift_id_of_base_eq S.p hbase compQ
      (CategoryOver.ExplicitTwoFibreProductObject.comparison_over
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G))
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj (D.obj I)).1))
  let tailR := HR.toHom.map
    ((canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f (D.obj I))
  have htail : S.p.IsStronglyCartesian f tailR := by
    dsimp only [tailR, HR]
    exact FibredCategoryMor.map_stronglyCartesian_of_lift
      (FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G) f _
      ((canonicalPullbackChoice
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).isStronglyCartesian f (D.obj I))
  have hleftLift :
      S.p.IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) := by
    exact (α ≫ eR.hom).2
  have hrightLift : S.p.IsHomLift (𝟙 V) (eL.hom.1 ≫ compQ) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ S.p _ _ _ _ _
      (𝟙 V) eL.hom.1 eL.hom.2 V compQ hcompQ
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ S.p _ _ _ _ f tailR htail _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) (eL.hom.1 ≫ compQ)
    hleftLift hrightLift ?_
  -- After postcomposition, both sides are the defining comparison square of the pulled-back
  -- explicit product object, expressed through the owner pullback-comparison maps.
  let η := (canonicalPullbackChoice
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f (D.obj I)
  let γ :=
    explicit_two_fibre_product_cover_descent_projection_component_transport_iso
      (J := J) F G T D I
  have hR :
      eR.hom.1 ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
          ((FibredCategoryMor.fiberFunctor HR I.Y).obj (D.obj I)) := by
    simpa only [eR, η, HR] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HR f (D.obj I)
  have hL :
      eL.hom.1 ≫ HL.toHom.map η =
        (canonicalPullbackChoice S.p).map f
          ((FibredCategoryMor.fiberFunctor HL I.Y).obj (D.obj I)) := by
    simpa only [eL, η, HL] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HL f (D.obj I)
  have hγ :
      Functor.Fiber.fiberInclusion.map α ≫
          (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HR I.Y).obj (D.obj I)) =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL I.Y).obj (D.obj I)) ≫
          Functor.Fiber.fiberInclusion.map γ.hom := by
    simpa only [α, γ] using
      canonical_pullbackFunctor_map_fac
        (p := S.p) (f := f) (φ := γ.hom)
  have hη :
      HL.toHom.map η ≫ Functor.Fiber.fiberInclusion.map γ.hom =
        compQ ≫ HR.toHom.map η := by
    simpa only [η, γ, HR, HL, compQ,
      explicit_two_fibre_product_cover_descent_projection_component_transport_hom_underlying]
      using η.comm.w
  have hleft :
      (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL I.Y).obj (D.obj I)) ≫
          Functor.Fiber.fiberInclusion.map γ.hom := by
    exact
      (Category.assoc (Functor.Fiber.fiberInclusion.map α) eR.hom.1
        (HR.toHom.map η)).trans
        ((congrArg (fun k ↦ Functor.Fiber.fiberInclusion.map α ≫ k) hR).trans hγ)
  have hright :
      (eL.hom.1 ≫ compQ) ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL I.Y).obj (D.obj I)) ≫
          Functor.Fiber.fiberInclusion.map γ.hom := by
    exact
      (Category.assoc eL.hom.1 compQ (HR.toHom.map η)).trans
        ((congrArg (fun k ↦ eL.hom.1 ≫ k) hη.symm).trans
          ((Category.assoc eL.hom.1 (HL.toHom.map η)
            (Functor.Fiber.fiberInclusion.map γ.hom)).symm.trans
            (congrArg (fun k ↦ k ≫ Functor.Fiber.fiberInclusion.map γ.hom) hL)))
  rw [show tailR = HR.toHom.map η by rfl]
  exact hleft.trans hright.symm

/-- Helper for Chap08 Lemma 8 4 6: the componentwise transported explicit pullback comparisons satisfy
the overlap square required to package an isomorphism of projected fixed-cover descent data. -/
private theorem explicit_two_fibre_product_cover_descent_projection_component_transport_comm
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₁).hom) ≫
      (((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T ⋙
            cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T).obj D).hom
        q f₁ f₂ hf₁ hf₂) =
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D).hom
      q f₁ f₂ hf₁ hf₂) ≫
    (((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T D I₂).hom) := by
  -- Work in the fiber over `V`.  The two projected fixed-cover transports are the transports
  -- along the composite morphisms `π₂ ≫ G` and `π₁ ≫ F`; after the two boundary rewrites, the
  -- middle square is exactly the explicit-product commutator stored in `D.hom`.
  let HR := FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G
  let HL := FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F
  let γ₁ :=
    explicit_two_fibre_product_cover_descent_projection_component_transport_iso
      (J := J) F G T D I₁
  let γ₂ :=
    explicit_two_fibre_product_cover_descent_projection_component_transport_iso
      (J := J) F G T D I₂
  let α₁ := ((canonicalFiberPseudofunctor S.p).map f₁.op.toLoc).toFunctor.map γ₁.hom
  let α₂ := ((canonicalFiberPseudofunctor S.p).map f₂.op.toLoc).toFunctor.map γ₂.hom
  let d := D.hom q f₁ f₂ hf₁ hf₂
  let eR₁ := FibredCategoryMor.pullbackComparison HR f₁ (D.obj I₁)
  let eL₁ := FibredCategoryMor.pullbackComparison HL f₁ (D.obj I₁)
  let eR₂ := FibredCategoryMor.pullbackComparison HR f₂ (D.obj I₂)
  let eL₂ := FibredCategoryMor.pullbackComparison HL f₂ (D.obj I₂)
  let P₁ :=
    (((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₁.op.toLoc).toFunctor.obj (D.obj I₁)).1
  let P₂ :=
    (((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₂.op.toLoc).toFunctor.obj (D.obj I₂)).1
  let c₁ := CategoryOver.ExplicitTwoFibreProductObject.comparison
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)) P₁
  let c₂ := CategoryOver.ExplicitTwoFibreProductObject.comparison
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
    (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)) P₂
  have hc₁ : S.p.IsHomLift (𝟙 V) c₁ := by
    -- The comparison of the reindexed explicit product lies over the identity of the new base.
    have hbase : P₁.U = V := by
      dsimp only [P₁]
      exact
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f₁.op.toLoc).toFunctor.obj (D.obj I₁)).2)
    exact isHomLift_id_of_base_eq S.p hbase c₁
      (CategoryOver.ExplicitTwoFibreProductObject.comparison_over
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)) P₁)
  have hc₂ : S.p.IsHomLift (𝟙 V) c₂ := by
    -- The target-leg comparison has the same identity-lift property over `V`.
    have hbase : P₂.U = V := by
      dsimp only [P₂]
      exact
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f₂.op.toLoc).toFunctor.obj (D.obj I₂)).2)
    exact isHomLift_id_of_base_eq S.p hbase c₂
      (CategoryOver.ExplicitTwoFibreProductObject.comparison_over
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F))
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)) P₂)
  let c₁Hom := Functor.Fiber.homMk S.p V c₁
  let c₂Hom := Functor.Fiber.homMk S.p V c₂
  have htarget :
      c₁ ≫
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)).map
          ((D.hom q f₁ f₂ hf₁ hf₂).1).b =
      (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F)).map
          ((D.hom q f₁ f₂ hf₁ hf₂).1).a ≫
        c₂ := by
    -- This is the source descent-data square read in the explicit two-fibre-product fiber.
    dsimp only [c₁, c₂, P₁, P₂]
    exact ((D.hom q f₁ f₂ hf₁ hf₂).1).comm.w.symm
  have hleftBoundary : α₁ ≫ eR₁.hom = eL₁.hom ≫ c₁Hom := by
    -- The source-leg boundary is exactly the reusable reindexing comparison lemma.
    apply Functor.Fiber.hom_ext
    dsimp only [α₁, eR₁, eL₁, c₁Hom, c₁, P₁, HR, HL]
    exact explicit_two_fibre_product_comparison_reindex_left_boundary
      (J := J) F G T D I₁ f₁
  have hrightSource : α₂ ≫ eR₂.hom = eL₂.hom ≫ c₂Hom := by
    -- The same boundary on the target leg will be inverted below.
    apply Functor.Fiber.hom_ext
    dsimp only [α₂, eR₂, eL₂, c₂Hom, c₂, P₂, HR, HL]
    exact explicit_two_fibre_product_comparison_reindex_left_boundary
      (J := J) F G T D I₂ f₂
  have hrightBoundary : eL₂.inv ≫ α₂ = c₂Hom ≫ eR₂.inv := by
    -- Cancel the right comparison isomorphism after applying the target-leg boundary.
    have hsourcePost :
        (eL₂.inv ≫ α₂) ≫ eR₂.hom = c₂Hom := by
      have hraw :
          eL₂.inv ≫ (α₂ ≫ eR₂.hom) =
            eL₂.inv ≫ (eL₂.hom ≫ c₂Hom) :=
        congrArg (fun k ↦ eL₂.inv ≫ k) hrightSource
      have hcollapse :
          eL₂.inv ≫ (eL₂.hom ≫ c₂Hom) = c₂Hom :=
        (Category.assoc eL₂.inv eL₂.hom c₂Hom).symm.trans
          ((congrArg (fun k ↦ k ≫ c₂Hom) eL₂.inv_hom_id).trans
            (Category.id_comp c₂Hom))
      exact (Category.assoc eL₂.inv α₂ eR₂.hom).trans (hraw.trans hcollapse)
    have htargetPost :
        (c₂Hom ≫ eR₂.inv) ≫ eR₂.hom = c₂Hom := by
      exact (Category.assoc c₂Hom eR₂.inv eR₂.hom).trans
        ((congrArg (fun k ↦ c₂Hom ≫ k) eR₂.inv_hom_id).trans
          (Category.comp_id c₂Hom))
    exact (cancel_mono eR₂.hom).mp (hsourcePost.trans htargetPost.symm)
  have hmiddle :
      c₁Hom ≫ (FibredCategoryMor.fiberFunctor HR V).map d =
        (FibredCategoryMor.fiberFunctor HL V).map d ≫ c₂Hom := by
    -- After forgetting to the total category, this is exactly `htarget`.
    apply Functor.Fiber.hom_ext
    dsimp only [c₁Hom, c₂Hom, c₁, c₂, P₁, P₂, HR, HL, d]
    exact htarget
  simp only [← cover_descent_data_functor_hom_of_stack_morphism_comp]
  change α₁ ≫ cover_descent_data_functor_hom_of_stack_morphism
      (J := J) HR T D q f₁ f₂ hf₁ hf₂ =
    cover_descent_data_functor_hom_of_stack_morphism
      (J := J) HL T D q f₁ f₂ hf₁ hf₂ ≫ α₂
  dsimp only [cover_descent_data_functor_hom_of_stack_morphism]
  change α₁ ≫ eR₁.hom ≫ (FibredCategoryMor.fiberFunctor HR V).map d ≫ eR₂.inv =
    (eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫ eL₂.inv) ≫ α₂
  -- With the two boundary terms removed, the proof is the middle explicit-product square.
  have hstart :
      α₁ ≫ eR₁.hom ≫ (FibredCategoryMor.fiberFunctor HR V).map d ≫ eR₂.inv =
        (eL₁.hom ≫ c₁Hom) ≫
          (FibredCategoryMor.fiberFunctor HR V).map d ≫ eR₂.inv := by
    simpa only [← Category.assoc] using congrArg
      (fun k ↦ (k ≫ (FibredCategoryMor.fiberFunctor HR V).map d) ≫ eR₂.inv)
      hleftBoundary
  have hmid₁ :
      (eL₁.hom ≫ c₁Hom) ≫
          (FibredCategoryMor.fiberFunctor HR V).map d ≫ eR₂.inv =
        eL₁.hom ≫ (c₁Hom ≫ (FibredCategoryMor.fiberFunctor HR V).map d) ≫
          eR₂.inv := by
    simp only [Category.assoc]
  have hmid₂ :
      eL₁.hom ≫ (c₁Hom ≫ (FibredCategoryMor.fiberFunctor HR V).map d) ≫
          eR₂.inv =
        eL₁.hom ≫
          ((FibredCategoryMor.fiberFunctor HL V).map d ≫ c₂Hom) ≫ eR₂.inv := by
    exact congrArg (fun k ↦ eL₁.hom ≫ k ≫ eR₂.inv) hmiddle
  have hmid₃ :
      eL₁.hom ≫ ((FibredCategoryMor.fiberFunctor HL V).map d ≫ c₂Hom) ≫
          eR₂.inv =
        eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫
          (c₂Hom ≫ eR₂.inv) := by
    simp only [Category.assoc]
  have hmid₄ :
      eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫
          (c₂Hom ≫ eR₂.inv) =
        eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫
          (eL₂.inv ≫ α₂) := by
    exact congrArg
      (fun k ↦ eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫ k)
      hrightBoundary.symm
  have hend :
      eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫
          (eL₂.inv ≫ α₂) =
        (eL₁.hom ≫ (FibredCategoryMor.fiberFunctor HL V).map d ≫ eL₂.inv) ≫
          α₂ := by
    simp only [Category.assoc]
  exact hstart.trans (hmid₁.trans (hmid₂.trans (hmid₃.trans (hmid₄.trans hend))))

/-- Helper for Chap08 Lemma 8 4 6: for a fixed explicit pullback descent datum, the two projected
composites into `S` are isomorphic as descent data by the stored explicit pullback comparisons on
each cover leg. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_data_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f))) :
    ((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj D) ≅
      ((explicit_two_fibre_product_cover_descent_right_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T).obj D) :=
  Pseudofunctor.DescentData.isoMk
    (fun I ↦
      explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦
      -- The overlap condition is the componentwise commutativity established just above.
      explicit_two_fibre_product_cover_descent_projection_component_transport_comm
        (J := J) F G T D q f₁ f₂ hf₁ hf₂)

/-- Helper for Chap08 Lemma 8 4 6: packaging the componentwise explicit pullback comparisons objectwise
produces the natural comparison iso between the left-then-`F` and right-then-`G` fixed-cover
projection functors. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_projection_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor F) T) ≅
    (explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T ⋙
      cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor G) T) :=
  -- Package the objectwise comparisons; naturality is, on each cover leg, exactly the commuting
  -- square `comm` carried by the underlying explicit `2`-fibre-product morphism of `φ.hom I`.
  NatIso.ofComponents
    (fun D ↦ explicit_two_fibre_product_cover_descent_projection_data_iso (J := J) F G T D)
    (fun {D₁ D₂} φ ↦ by
      apply Pseudofunctor.DescentData.hom_ext
      intro I
      rw [Pseudofunctor.DescentData.comp_hom, Pseudofunctor.DescentData.comp_hom]
      apply Functor.Fiber.hom_ext
      exact ((φ.hom I).1).comm.w)

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover comparison square carried by descent data on the
explicit stack-level `2`-fibre product lands in the categorical pullback of the projected
descent-data categories over `S`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_square
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    CatCommSqOver
      (cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor F) T)
      (cover_descent_data_functor_of_stack_morphism (J := J) (toFibredCategoryMor G) T)
      ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) where
  fst := explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T
  snd := explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T
  iso := explicit_two_fibre_product_cover_descent_projection_iso (J := J) F G T

/-- Helper for Chap08 Lemma 8 4 6: the square isomorphism in the fixed-cover pullback bridge
evaluates on a cover leg to the explicit transported component comparison. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_square_iso_hom_component
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    ((explicit_two_fibre_product_cover_descent_pullback_square
        (J := J) F G T).iso.hom.app D).hom I =
      (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I).hom := by
  -- Unfold the square only to the objectwise descent-data iso packaged above.
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after forgetting a fixed-cover pullback-square component to
the total category, it is the stored explicit two-fibre-product comparison. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_square_iso_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      (((explicit_two_fibre_product_cover_descent_pullback_square
        (J := J) F G T).iso.hom.app D).hom I) =
      (((D.obj I).1).obj.iso.hom).1 := by
  -- First identify the square component with the transport adapter, then unfold that adapter.
  rw [explicit_two_fibre_product_cover_descent_pullback_square_iso_hom_component,
    explicit_two_fibre_product_cover_descent_projection_component_transport_hom_underlying]

/-- Helper for Chap08 Lemma 8 4 6: fixed-cover descent data on the explicit stack-level `2`-fibre
product map canonically to the categorical pullback of the two projected fixed-cover
descent-data categories. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_bridge
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) ⥤
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)) :=
  (CatCommSqOver.toFunctorToCategoricalPullback
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor F) T)
    (cover_descent_data_functor_of_stack_morphism
      (J := J) (toFibredCategoryMor G) T)
    ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
          (fun I : T.Arrow ↦ I.f))).obj
    (explicit_two_fibre_product_cover_descent_pullback_square (J := J) F G T)

/-- Helper for Chap08 Lemma 8 4 6: the transported legwise map preserves identities because the inverse
fibre equivalence carries identity morphisms in the fixed-cover pullback back to identities on
each reconstructed leg. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_id
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (Q :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)))
    (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
        (J := J) F G T (𝟙 Q) I =
      𝟙 _ := by
  -- The legwise map is `eI.inverse.map` of the owner-side component map; on the identity this is
  -- `eI.inverse.map (𝟙) = 𝟙` by functoriality.
  change (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (𝟙 Q) I) = 𝟙 _
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_id,
    Functor.map_id]

/-- Helper for Chap08 Lemma 8 4 6: the transported legwise map preserves composition because the inverse
functor of the Chapter 4 fibre equivalence preserves composition. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_comp
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ Q₃ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (ψ : Q₂ ⟶ Q₃) (I : T.Arrow) :
    explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
        (J := J) F G T (φ ≫ ψ) I =
      explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I ≫
        explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T ψ I := by
  -- The legwise map is `eI.inverse.map` of the owner-side component map; composition is preserved
  -- because the owner-side component map preserves composition and `eI.inverse` is a functor.
  change (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T (φ ≫ ψ) I) =
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T φ I) ≫
    (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).inverse.map
      (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
        (J := J) F G T ψ I)
  rw [explicit_two_fibre_product_cover_descent_pullback_inverse_component_map_comp,
    Functor.map_comp]

/-- Helper for Chap08 Lemma 8 4 6: after applying the forward fibre equivalence over `I.Y`, the
transported legwise map becomes the owner-side component map, with boundary given by the counit
of the Chapter 4 fibre equivalence. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom_counit_naturality
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    {Q₁ Q₂ :
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T))}
    (φ : Q₁ ⟶ Q₂) (I : T.Arrow) :
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) I.Y).functor.map
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_hom
          (J := J) F G T φ I)) ≫
      (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
        (J := J) F G T Q₂ I).hom =
        (explicit_two_fibre_product_cover_descent_pullback_inverse_leg_counit
          (J := J) F G T Q₁ I).hom ≫
          explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
            (J := J) F G T φ I := by
  -- This is exactly the naturality square of the counit isomorphism of the Chapter 4 fibre
  -- equivalence over `I.Y`, evaluated at the owner-side component map of `φ`.
  exact (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) I.Y).counitIso.hom.naturality
    (explicit_two_fibre_product_cover_descent_pullback_inverse_component_map
      (J := J) F G T φ I)

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover canonical descent functor of the explicit
stack-level `2`-fibre product is the source of the remaining comparison with the owner pullback
model. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U ⥤
      ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
            (fun I : T.Arrow ↦ I.f)) :=
  ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).toDescentData
      (fun I : T.Arrow ↦ I.f))

/-- Helper for Chap08 Lemma 8 4 6: the owner pullback model for the fixed-cover comparison is the
`two_fibre_product_map` induced by the canonical transport isomorphisms for `F` and `G`. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_model_functor
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U) :
    ((fiberFunctor F U) ⊡ (fiberFunctor G U)) ⥤
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ⊡
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T)) :=
  two_fibre_product_map
    (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor G) T)
    ((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
      (J := J) (toFibredCategoryMor F) T).symm)


/-- Helper for Chap08 Lemma 8 4 6: after postcomposing with `π₁`, the explicit bridge from fixed-cover
descent data matches the owner pullback model through the left projection comparison. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
        explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T ⋙
        π₁
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) ≅
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T ⋙
        π₁
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) := by
  -- `bridge ⋙ π₁ = left_projection` definitionally, so the left leg is the projected canonical
  -- descent comparison; `model ⋙ π₁ = π₁ ⋙ ΦX` (rfl) and `eFib ⋙ π₁ = leftProj.fiberFunctor`
  -- (Lemma 4.32.5) identify the two right legs.
  refine (cover_descent_data_functor_of_stack_morphism_toDescentData_iso (J := J)
    (FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)) T).trans (eqToIso ?_)
  rw [show FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) U
      = (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙ π₁ _ _
      from (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
        (toBasedFunctor F) (toBasedFunctor G) U).symm]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after postcomposing with `π₂`, the explicit bridge from fixed-cover
descent data matches the owner pullback model through the right projection comparison. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
        explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T ⋙
        π₂
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) ≅
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T ⋙
        π₂
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T)
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T)) := by
  -- Symmetric to the left leg: the projected canonical descent comparison for the right
  -- projection, then `model ⋙ π₂ = π₂ ⋙ ΦY` (rfl) and `eFib ⋙ π₂ = rightProj.fiberFunctor`.
  refine (cover_descent_data_functor_of_stack_morphism_toDescentData_iso (J := J)
    (FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)) T).trans (eqToIso ?_)
  have hRightProjectionFunctor :
      FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G)) U =
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
          π₂ (fiberFunctor F U) (fiberFunctor G U) := by
    exact (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
      (toBasedFunctor F) (toBasedFunctor G) U).symm
  rw [hRightProjectionFunctor]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the left projected comparison isomorphism evaluates coverwise to the
inverse pullback-comparison morphism for the left projection of the explicit owner. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso_hom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
        (J := J) F G T).hom.app x).hom I) =
      (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
        (J := J) F G T).hom.app x).hom I) := by
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the right projected comparison isomorphism evaluates coverwise to the
inverse pullback-comparison morphism for the right projection of the explicit owner. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso_hom_hom
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
        (J := J) F G T).hom.app x).hom I) =
      (((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
        (J := J) F G T).hom.app x).hom I) := by
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after forgetting a fixed-cover comparison component to the
total category, its hom is the underlying inverse pullback-comparison morphism. -/
private theorem cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_underlying
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U : C} (T : J.Cover U) (x : A.p.Fiber U) (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
        (J := J) H T).hom.app x).hom I) =
      (FibredCategoryMor.pullbackComparison H I.f x).inv.1 := by
  -- Forget the already packaged fiber equality to obtain an owner-level rewrite lemma.
  exact congrArg (fun φ ↦ Functor.Fiber.fiberInclusion.map φ)
    (cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_hom
      (J := J) H T x I)

/-- Helper for Chap08 Lemma 8 4 6: the model pullback functor's comparison
component is the fixed-cover comparison for `F`, followed by the canonical descent image of the
stored pullback comparison, followed by the inverse fixed-cover comparison for `G`. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_model_iso_hom_component
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (P : ((fiberFunctor F U) ⊡ (fiberFunctor G U))) (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).obj P).iso.hom).hom I =
      (((cover_descent_data_functor_of_stack_morphism_toDescentData_iso
            (J := J) (toFibredCategoryMor F) T).hom.app P.fst ≫
          ((canonicalFiberPseudofunctor S.toFibredCategoryOver.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).map P.iso.hom ≫
          (cover_descent_data_functor_of_stack_morphism_toDescentData_iso
            (J := J) (toFibredCategoryMor G) T).inv.app P.snd).hom I) := by
  -- Expose only the categorical-pullback model computation; the component projection is then
  -- the component of the displayed descent-data composite.
  simp only [explicit_two_fibre_product_cover_descent_pullback_model_functor,
    two_fibre_product_map_obj_iso_hom, Iso.symm_inv]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: on a single cover leg, the projected comparison square
specialized to the identity overlap is the bridge square that remains after boundary
normalization. -/
private theorem explicit_two_fibre_product_cover_descent_projection_identity_comm
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((canonicalFiberPseudofunctor S.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T
          ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x) I).hom) ≫
      (((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T ⋙
            cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T).obj
          ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x)).hom
        I.f (𝟙 I.Y) (𝟙 I.Y) (Category.id_comp I.f) (Category.id_comp I.f)) =
    (((explicit_two_fibre_product_cover_descent_left_projection
        (J := J) F G T ⋙
          cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).obj
        ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x)).hom
      I.f (𝟙 I.Y) (𝟙 I.Y) (Category.id_comp I.f) (Category.id_comp I.f)) ≫
      (((canonicalFiberPseudofunctor S.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
        (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T
          ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x) I).hom) := by
  -- Specialize the already isolated projected descent compatibility to the identity overlap of
  -- the chosen cover leg.
  exact
    explicit_two_fibre_product_cover_descent_projection_component_transport_comm
      (J := J) F G T
      ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x)
      (q := I.f) (I₁ := I) (I₂ := I) (f₁ := 𝟙 I.Y) (f₂ := 𝟙 I.Y)
      (hf₁ := Category.id_comp I.f) (hf₂ := Category.id_comp I.f)

/-- Helper for Chap08 Lemma 8 4 6: after forgetting to the total category, the identity-overlap
projection square has the same orientation needed for the bridge comparison. -/
private theorem explicit_two_fibre_product_projection_identity_comm_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      ((((explicit_two_fibre_product_cover_descent_left_projection
          (J := J) F G T ⋙
            cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T).obj
          ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x)).hom
        I.f (𝟙 I.Y) (𝟙 I.Y) (Category.id_comp I.f) (Category.id_comp I.f)) ≫
        (((canonicalFiberPseudofunctor S.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
          (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
            (J := J) F G T
            ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x) I).hom)) =
    Functor.Fiber.fiberInclusion.map
      ((((canonicalFiberPseudofunctor S.p).map (𝟙 I.Y).op.toLoc).toFunctor.map
          (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
            (J := J) F G T
            ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x) I).hom) ≫
        (((explicit_two_fibre_product_cover_descent_right_projection
          (J := J) F G T ⋙
            cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T).obj
          ((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x)).hom
        I.f (𝟙 I.Y) (𝟙 I.Y) (Category.id_comp I.f) (Category.id_comp I.f))) := by
  -- Forget the already-proved identity-overlap square to the total category.
  exact congrArg (fun φ ↦ Functor.Fiber.fiberInclusion.map φ)
    ((explicit_two_fibre_product_cover_descent_projection_identity_comm (J := J) F G T x I).symm)

/-- Helper for Chap08 Lemma 8 4 6: naturality of a descent-data natural isomorphism remains an
equality after taking one component and forgetting the fiber morphism. -/
private theorem descentDataNatIso_hom_naturality_underlying
    {𝒜 𝒳 : Type*} [Category 𝒜] [Category 𝒳]
    (p : 𝒳 ⥤ C) [p.IsFibered]
    {U : C} {ι : Type*} {Xc : ι → C} {f : ∀ i, Xc i ⟶ U}
    {K L : 𝒜 ⥤ (canonicalFiberPseudofunctor p).DescentData f}
    (α : K ≅ L) {a b : 𝒜} (g : a ⟶ b) (i : ι) :
    Functor.Fiber.fiberInclusion.map (((K.map g ≫ α.hom.app b).hom i)) =
      Functor.Fiber.fiberInclusion.map (((α.hom.app a ≫ L.map g).hom i)) := by
  -- Apply the cover-leg component and forgetful functor to the ordinary naturality square.
  exact congrArg (fun φ ↦ Functor.Fiber.fiberInclusion.map (φ.hom i))
    (α.hom.naturality g)

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover pullback model comparison has the expected
three-factor underlying component on each cover leg. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_model_iso_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (P : ((toBasedFunctor F).fiberFunctor U) ⊡ ((toBasedFunctor G).fiberFunctor U))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      ((((explicit_two_fibre_product_cover_descent_pullback_model_functor
        (J := J) F G T).obj P).iso.hom).hom I) =
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
        Functor.Fiber.fiberInclusion.map
          ((((canonicalFiberPseudofunctor S.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor G) I.f P.snd).hom.1 := by
  -- Unfold the model comparison once: it is built from the fixed-cover comparison for `F`,
  -- the transported central comparison, and the inverse fixed-cover comparison for `G`.
  simp only [explicit_two_fibre_product_cover_descent_pullback_model_functor,
    two_fibre_product_map_obj_iso_hom, Pseudofunctor.DescentData.comp_hom,
    cover_descent_data_functor_of_stack_morphism_toDescentData_iso_inv_hom]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the three-factor fixed-cover model
comparison collapses after postcomposition with the chosen right pullback arrow. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_model_iso_hom_postcompose
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (P : ((toBasedFunctor F).fiberFunctor U) ⊡ ((toBasedFunctor G).fiberFunctor U))
    (I : T.Arrow) :
    ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
        Functor.Fiber.fiberInclusion.map
          ((((canonicalFiberPseudofunctor S.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor G) I.f P.snd).hom.1) ≫
      (SubTwoCategory.Hom.toHom (toFibredCategoryMor G)).map
        ((canonicalPullbackChoice Y.p).map I.f P.snd) =
    (SubTwoCategory.Hom.toHom (toFibredCategoryMor F)).map
        ((canonicalPullbackChoice X.p).map I.f P.fst) ≫ P.iso.hom.1 := by
  -- Collapse the right comparison, use the canonical pullback functor factorization for the middle
  -- descent component, and then collapse the left comparison.
  have hRight :=
    FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor G) I.f P.snd
  have hMiddle :=
    canonical_pullbackFunctor_map_fac (p := S.p) (f := I.f) (φ := P.iso.hom)
  have hLeft :=
    FibredCategoryMor.pullbackComparison_inv_postcompose_owner (toFibredCategoryMor F) I.f P.fst
  have hmain :
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
            Functor.Fiber.fiberInclusion.map
              ((((canonicalFiberPseudofunctor S.p).toDescentData
                (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor G) I.f P.snd).hom.1) ≫
          (SubTwoCategory.Hom.toHom (toFibredCategoryMor G)).map
            ((canonicalPullbackChoice Y.p).map I.f P.snd) =
        ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
            (canonicalPullbackChoice S.toFibredCategoryOver.p).map I.f
              ((BasedFunctor.fiberFunctor
                (SubTwoCategory.Hom.toHom (toFibredCategoryMor F)) U).obj P.fst)) ≫
          P.iso.hom.1 := by
    calc
      ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
            Functor.Fiber.fiberInclusion.map
              ((((canonicalFiberPseudofunctor S.p).toDescentData
                (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
            (FibredCategoryMor.pullbackComparison (toFibredCategoryMor G) I.f P.snd).hom.1) ≫
          (SubTwoCategory.Hom.toHom (toFibredCategoryMor G)).map
            ((canonicalPullbackChoice Y.p).map I.f P.snd) =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
          Functor.Fiber.fiberInclusion.map
            ((((canonicalFiberPseudofunctor S.p).toDescentData
              (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
          (canonicalPullbackChoice S.p).map I.f
            ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) U).obj P.snd) := by
          simpa only [Category.assoc] using
            congrArg
              (fun k ↦
                (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
                  Functor.Fiber.fiberInclusion.map
                    ((((canonicalFiberPseudofunctor S.p).toDescentData
                      (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫ k)
              hRight
      _ =
        (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
          ((canonicalPullbackChoice S.toFibredCategoryOver.p).map I.f
              ((BasedFunctor.fiberFunctor
                (SubTwoCategory.Hom.toHom (toFibredCategoryMor F)) U).obj P.fst) ≫
            P.iso.hom.1) := by
          simpa only [StackOver.p, StackOver.toFibredCategoryOver, FibredCategoryMor.fiberFunctor,
            Category.assoc] using
            congrArg
              (fun k ↦
                (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫ k)
              hMiddle
      _ =
        ((FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
            (canonicalPullbackChoice S.toFibredCategoryOver.p).map I.f
              ((BasedFunctor.fiberFunctor
                (SubTwoCategory.Hom.toHom (toFibredCategoryMor F)) U).obj P.fst)) ≫
          P.iso.hom.1 := by
          simp only [Category.assoc]
  exact hmain.trans (congrArg (fun k ↦ k ≫ P.iso.hom.1) hLeft)

/-- Helper for Chap08 Lemma 8 4 6: the fixed-cover pullback bridge comparison is the stored
explicit two-fibre-product comparison on each cover leg after forgetting the fiber component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_iso_hom_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      ((((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj D).iso.hom).hom I) =
      (((D.obj I).1).obj.iso.hom).1 := by
  -- The bridge functor is the categorical-pullback functor attached to the explicit square, so
  -- its midpoint comparison is the square comparison already normalized above.
  exact
    explicit_two_fibre_product_cover_descent_pullback_square_iso_hom_underlying
      (J := J) F G T D I

/-- Helper for Chap08 Lemma 8 4 6: before forgetting to the total category,
the fixed-cover bridge comparison component is the transported explicit-product component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_iso_hom_component
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj D).iso.hom).hom I =
      (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I).hom := by
  -- Unfold the categorical-pullback bridge only to its object comparison; that comparison is
  -- the objectwise projection isomorphism already packaged in the fixed-cover square.
  dsimp only [explicit_two_fibre_product_cover_descent_pullback_bridge,
    CatCommSqOver.toFunctorToCategoricalPullback]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after forgetting the bridge comparison
component to the total category, it is the transported explicit-product component. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_iso_hom_underlying_transport
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (D : ((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).DescentData
        (fun I : T.Arrow ↦ I.f)))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      ((((explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).obj D).iso.hom).hom I) =
    Functor.Fiber.fiberInclusion.map
      (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T D I).hom := by
  -- Forget the component-level bridge normal form; no further pullback-model unfolding is needed.
  exact congrArg (fun φ ↦ Functor.Fiber.fiberInclusion.map φ)
    (explicit_two_fibre_product_cover_descent_pullback_bridge_iso_hom_component
      (J := J) F G T D I)

/-- Helper for Chap08 Lemma 8 4 6: the left projected bridge composite
evaluates componentwise as the left boundary component followed by the model comparison. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_component_split
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
          (J := J) F G T).hom.app x)) ≫
      ((explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).obj
        ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x)).iso.hom).hom I =
    ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
          (J := J) F G T).hom.app x)).hom I ≫
      (((explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).obj
        ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x)).iso.hom).hom I := by
  -- Descent-data composition is componentwise, so evaluating at `I` exposes the two factors.
  rw [Pseudofunctor.DescentData.comp_hom]

/-- Helper for Chap08 Lemma 8 4 6: the right projected bridge composite
evaluates as the transported explicit-product component followed by the right boundary component. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_component_transport
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj
        ((explicit_two_fibre_product_cover_descent_functor
          (J := J) F G T).obj x)).iso.hom ≫
      (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
          (J := J) F G T).hom.app x)).hom I =
    (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T
        ((explicit_two_fibre_product_cover_descent_functor
          (J := J) F G T).obj x) I).hom ≫
      ((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
          (J := J) F G T).hom.app x)).hom I := by
  -- First split the descent-data composite, then replace the bridge midpoint by the transported
  -- explicit-product component.
  rw [Pseudofunctor.DescentData.comp_hom,
    explicit_two_fibre_product_cover_descent_pullback_bridge_iso_hom_component]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: after postcomposing by the right owner pullback arrow,
the fixed-cover pullback model component reduces to the left owner pullback arrow followed by
the stored comparison in the fibre product. -/
private theorem explicit_two_fibre_product_pullback_model_postcompose_right_tail_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    (P : ((toBasedFunctor F).fiberFunctor U) ⊡ ((toBasedFunctor G).fiberFunctor U))
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
        ((((explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).obj P).iso.hom).hom I) ≫
      (toFibredCategoryMor G).toHom.map ((canonicalPullbackChoice Y.p).map I.f P.snd) =
    (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map I.f P.fst) ≫
      P.iso.hom.1 := by
  -- First expose the three model factors: left inverse comparison, central pulled comparison,
  -- and right comparison.
  rw [explicit_two_fibre_product_cover_descent_pullback_model_iso_hom_underlying]
  -- The right comparison cancels against the common right owner pullback arrow.
  have hRight :
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor G) I.f P.snd).hom.1 ≫
        (toFibredCategoryMor G).toHom.map ((canonicalPullbackChoice Y.p).map I.f P.snd) =
      (canonicalPullbackChoice S.p).map I.f
        ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) U).obj P.snd) := by
    exact FibredCategoryMor.pullbackComparison_hom_postcompose (toFibredCategoryMor G) I.f P.snd
  -- Naturality of the canonical pullback functor moves the central comparison across that
  -- target pullback arrow.
  have hMiddle :
      Functor.Fiber.fiberInclusion.map
          ((((canonicalFiberPseudofunctor S.p).toDescentData
            (fun I : T.Arrow ↦ I.f)).map P.iso.hom).hom I) ≫
        (canonicalPullbackChoice S.p).map I.f
          ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor G) U).obj P.snd) =
      (canonicalPullbackChoice S.p).map I.f
          ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) U).obj P.fst) ≫
        P.iso.hom.1 := by
    simpa only [Pseudofunctor.toDescentData_map_hom] using
      canonical_pullbackFunctor_map_fac (p := S.p) (f := I.f) (φ := P.iso.hom)
  -- The left inverse comparison then cancels against the left target pullback arrow.
  have hLeft :
      (FibredCategoryMor.pullbackComparison (toFibredCategoryMor F) I.f P.fst).inv.1 ≫
        (canonicalPullbackChoice S.p).map I.f
          ((FibredCategoryMor.fiberFunctor (toFibredCategoryMor F) U).obj P.fst) =
      (toFibredCategoryMor F).toHom.map ((canonicalPullbackChoice X.p).map I.f P.fst) := by
    exact FibredCategoryMor.pullbackComparison_inv_postcompose_owner (toFibredCategoryMor F) I.f P.fst
  -- Reassociate the exposed model factors so the three directed normal forms apply in order.
  erw [Category.assoc]
  erw [Category.assoc]
  erw [hRight]
  erw [hMiddle]
  erw [← Category.assoc]
  erw [hLeft]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: the chosen pullback arrow in the explicit two-fibre product
has the comparison square used as the live endpoint normal form. -/
private theorem explicit_two_fibre_product_eta_comm_live_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    {V : C} (f : V ⟶ U) :
    let η := (canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f x
    (toBasedFunctor F).map η.a ≫
        CategoryOver.ExplicitTwoFibreProductObject.comparison
          (toBasedFunctor F) (toBasedFunctor G) x.1 =
      CategoryOver.ExplicitTwoFibreProductObject.comparison
          (toBasedFunctor F) (toBasedFunctor G)
          (f ^*[canonicalPullbackChoice
            (FibredCategoryOver.twoFibreProduct
              (toFibredCategoryMor F) (toFibredCategoryMor G)).p] x).1 ≫
        (toBasedFunctor G).map η.b := by
  -- This adapter keeps the source object in the same live spelling used by the bridge proof.
  dsimp only
  exact
    ((canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f x).comm.w

/-- Helper for Chap08 Lemma 8 4 6: the left projection object of the owner fibre equivalence
is the left component of the categorical pullback model. -/
private theorem explicit_two_fibre_product_left_projection_owner_obj_eq
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U) :
    (FibredCategoryMor.fiberFunctor
      (FibredCategoryOver.twoFibreProductLeftProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)) U).obj x =
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x).fst := by
  -- Apply the Chapter 4 fibre-equivalence projection identity to the current owner object.
  simpa only using
    congrArg (fun K => K.obj x)
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
        (toBasedFunctor F) (toBasedFunctor G) U).symm

/-- Helper for Chap08 Lemma 8 4 6: the right projection object of the owner fibre equivalence
is the right component of the categorical pullback model. -/
private theorem explicit_two_fibre_product_right_projection_owner_obj_eq
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U) :
    (FibredCategoryMor.fiberFunctor
      (FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G)) U).obj x =
      ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x).snd := by
  -- The right projection is the symmetric component of the same Chapter 4 fibre equivalence.
  simpa only using
    congrArg (fun K => K.obj x)
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
        (toBasedFunctor F) (toBasedFunctor G) U).symm

/-- Helper for Chap08 Lemma 8 4 6: on a cover leg, the transported fixed-cover comparison is
the comparison morphism of the reindexed explicit two-fibre-product object. -/
private theorem explicit_two_fibre_product_cover_descent_transport_comparison_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    Functor.Fiber.fiberInclusion.map
      (explicit_two_fibre_product_cover_descent_projection_component_transport_iso
        (J := J) F G T
        ((explicit_two_fibre_product_cover_descent_functor
          (J := J) F G T).obj x) I).hom =
      CategoryOver.ExplicitTwoFibreProductObject.comparison
        (toBasedFunctor F) (toBasedFunctor G)
        (I.f ^*[canonicalPullbackChoice
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p] x).1 := by
  -- Evaluating the canonical descent functor at `I` gives the chosen pullback of `x` along
  -- `I.f`; the transport adapter then forgets to that object's stored comparison.
  rw [explicit_two_fibre_product_cover_descent_projection_component_transport_hom_underlying]
  rfl

/-- Helper for Chap08 Lemma 8 4 6: reindexing any explicit-product comparison along a base
arrow satisfies the same boundary square with the two projected pullback comparisons. -/
private theorem explicit_two_fibre_product_comparison_reindex_boundary_underlying
    (F : X ⟶ S) (G : Y ⟶ S) {U V : C} (f : V ⟶ U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (γ :
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F) U).obj x) ⟶
      ((FibredCategoryMor.fiberFunctor
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G) U).obj x))
    (hγ :
      Functor.Fiber.fiberInclusion.map γ =
        CategoryOver.ExplicitTwoFibreProductObject.comparison
          (toBasedFunctor F) (toBasedFunctor G) x.1) :
    Functor.Fiber.fiberInclusion.map
        (((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map γ) ≫
      (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductRightProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G)
        f x).hom.1 =
    (FibredCategoryMor.pullbackComparison
        (FibredCategoryOver.twoFibreProductLeftProjection
          (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F)
        f x).hom.1 ≫
      CategoryOver.ExplicitTwoFibreProductObject.comparison
        (toBasedFunctor F) (toBasedFunctor G)
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj x).1) := by
  -- Put the projected stack morphisms and their pullback comparisons into stable names, then
  -- compare the two candidate boundaries after the right projected cartesian pullback arrow.
  let HR := FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G
  let HL := FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor F
  let α := ((canonicalFiberPseudofunctor S.p).map f.op.toLoc).toFunctor.map γ
  let eR := FibredCategoryMor.pullbackComparison HR f x
  let eL := FibredCategoryMor.pullbackComparison HL f x
  let compQ := CategoryOver.ExplicitTwoFibreProductObject.comparison
    (toBasedFunctor F) (toBasedFunctor G)
    ((((canonicalFiberPseudofunctor
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f.op.toLoc).toFunctor.obj x).1)
  have hcompQ : S.p.IsHomLift (𝟙 V) compQ := by
    -- The comparison of the reindexed explicit object is vertical over the reindexed base.
    have hbase :
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj x).1).U = V :=
      ((((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
            f.op.toLoc).toFunctor.obj x).2)
    exact isHomLift_id_of_base_eq S.p hbase compQ
      (CategoryOver.ExplicitTwoFibreProductObject.comparison_over
        (toBasedFunctor F) (toBasedFunctor G)
        ((((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
              f.op.toLoc).toFunctor.obj x).1))
  let tailR := HR.toHom.map
    ((canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f x)
  have htail : S.p.IsStronglyCartesian f tailR := by
    dsimp only [tailR, HR]
    exact FibredCategoryMor.map_stronglyCartesian_of_lift
      (FibredCategoryOver.twoFibreProductRightProjection
        (toFibredCategoryMor F) (toFibredCategoryMor G) ≫ toFibredCategoryMor G) f _
      ((canonicalPullbackChoice
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).isStronglyCartesian f x)
  have hleftLift :
      S.p.IsHomLift (𝟙 V) (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) := by
    exact (α ≫ eR.hom).2
  have hrightLift : S.p.IsHomLift (𝟙 V) (eL.hom.1 ≫ compQ) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ S.p _ _ _ _ _
      (𝟙 V) eL.hom.1 eL.hom.2 V compQ hcompQ
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ S.p _ _ _ _ f tailR htail _ _ (𝟙 V)
    (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) (eL.hom.1 ≫ compQ)
    hleftLift hrightLift ?_
  -- Postcompose by the cartesian right boundary and reduce both sides to the commutative square
  -- carried by the chosen pullback of the explicit two-fibre-product object.
  let η := (canonicalPullbackChoice
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map f x
  have hR :
      eR.hom.1 ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
          ((FibredCategoryMor.fiberFunctor HR U).obj x) := by
    simpa only [eR, η, HR] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HR f x
  have hL :
      eL.hom.1 ≫ HL.toHom.map η =
        (canonicalPullbackChoice S.p).map f
          ((FibredCategoryMor.fiberFunctor HL U).obj x) := by
    simpa only [eL, η, HL] using
      FibredCategoryMor.pullbackComparison_hom_postcompose HL f x
  have hγPull :
      Functor.Fiber.fiberInclusion.map α ≫
          (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HR U).obj x) =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL U).obj x) ≫
          Functor.Fiber.fiberInclusion.map γ := by
    simpa only [α] using
      canonical_pullbackFunctor_map_fac (p := S.p) (f := f) (φ := γ)
  have hη :
      HL.toHom.map η ≫ Functor.Fiber.fiberInclusion.map γ =
        compQ ≫ HR.toHom.map η := by
    rw [hγ]
    simpa only [η, HR, HL, compQ] using η.comm.w
  have hleft :
      (Functor.Fiber.fiberInclusion.map α ≫ eR.hom.1) ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL U).obj x) ≫
          Functor.Fiber.fiberInclusion.map γ := by
    exact
      (Category.assoc (Functor.Fiber.fiberInclusion.map α) eR.hom.1
        (HR.toHom.map η)).trans
        ((congrArg (fun k ↦ Functor.Fiber.fiberInclusion.map α ≫ k) hR).trans hγPull)
  have hright :
      (eL.hom.1 ≫ compQ) ≫ HR.toHom.map η =
        (canonicalPullbackChoice S.p).map f
            ((FibredCategoryMor.fiberFunctor HL U).obj x) ≫
          Functor.Fiber.fiberInclusion.map γ := by
    exact
      (Category.assoc eL.hom.1 compQ (HR.toHom.map η)).trans
        ((congrArg (fun k ↦ eL.hom.1 ≫ k) hη.symm).trans
          ((Category.assoc eL.hom.1 (HL.toHom.map η)
            (Functor.Fiber.fiberInclusion.map γ)).symm.trans
            (congrArg (fun k ↦ k ≫ Functor.Fiber.fiberInclusion.map γ) hL)))
  simpa only [tailR, η] using hleft.trans hright.symm

/-- Helper for Chap08 Lemma 8 4 6: the categorical pullback model object associated to an
explicit two-fibre-product owner object. -/
private noncomputable abbrev explicit_two_fibre_product_cover_descent_pullback_model_object
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U) :
    ((toBasedFunctor F).fiberFunctor U) ⊡ ((toBasedFunctor G).fiberFunctor U) :=
  (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x

/-- Helper for Chap08 Lemma 8 4 6: an explicit two-fibre-product object, packaged as an object of
the owner fibre over its base. -/
private abbrev explicit_two_fibre_product_owner_fiber_object
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    (Qfst : X.p.Fiber U) (Qsnd : Y.p.Fiber U)
    (Qiso :
      ((toBasedFunctor F).fiberFunctor U).obj Qfst ≅
        ((toBasedFunctor G).fiberFunctor U).obj Qsnd) :
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U :=
  ⟨{ U := U, obj := { fst := Qfst, snd := Qsnd, iso := Qiso } }, rfl⟩

/-- Helper for Chap08 Lemma 8 4 6: for a concrete owner object, the left side of the
postcomposed bridge component reduces to the live left pullback leg followed by the stored
comparison. -/
private theorem explicit_two_fibre_product_left_composite_tail_concrete
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Qfst : X.p.Fiber U) (Qsnd : Y.p.Fiber U)
    (Qiso :
      ((toBasedFunctor F).fiberFunctor U).obj Qfst ≅
        ((toBasedFunctor G).fiberFunctor U).obj Qsnd)
    (T : J.Cover U) (I : T.Arrow) :
    let x := explicit_two_fibre_product_owner_fiber_object (J := J) F G Qfst Qsnd Qiso
    let P := explicit_two_fibre_product_cover_descent_pullback_model_object (J := J) F G x
    let η := (canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map I.f x
    Functor.Fiber.fiberInclusion.map
        (((cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T).map
            ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
              (J := J) F G T).hom.app x)).hom I ≫
          (((explicit_two_fibre_product_cover_descent_pullback_model_functor
              (J := J) F G T).obj P).iso.hom).hom I) ≫
      (toFibredCategoryMor G).toHom.map
        ((canonicalPullbackChoice Y.p).map I.f P.snd) =
    (toBasedFunctor F).map η.a ≫ Qiso.hom.1 := by
  let x := explicit_two_fibre_product_owner_fiber_object (J := J) F G Qfst Qsnd Qiso
  let P := explicit_two_fibre_product_cover_descent_pullback_model_object (J := J) F G x
  let ηY := (canonicalPullbackChoice Y.p).map I.f P.snd
  let tail := (toFibredCategoryMor G).toHom.map ηY
  -- Expose the fixed-cover model component, then cancel its right cartesian boundary.
  change
    Functor.Fiber.fiberInclusion.map
        (((cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T).map
            ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
              (J := J) F G T).hom.app x)).hom I ≫
          (((explicit_two_fibre_product_cover_descent_pullback_model_functor
              (J := J) F G T).obj P).iso.hom).hom I) ≫
      (toFibredCategoryMor G).toHom.map
        ((canonicalPullbackChoice Y.p).map I.f P.snd) =
    (toBasedFunctor F).map
      (((canonicalPullbackChoice
        (FibredCategoryOver.twoFibreProduct
          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map I.f x).a) ≫
      Qiso.hom.1
  rw [Functor.map_comp]
  erw [Category.assoc]
  dsimp only [tail, ηY]
  erw [explicit_two_fibre_product_pullback_model_postcompose_right_tail_underlying
    (J := J) F G T P I]
  simp only [
    explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso,
    cover_descent_data_functor_of_stack_morphism,
    cover_descent_data_functor_hom_of_stack_morphism,
    Pseudofunctor.DescentData.comp_hom,
    cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_hom,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  erw [Functor.map_comp]
  have hLeftTail := FibredCategoryMor.pullbackComparison_inv_postcompose_owner
    (FibredCategoryOver.twoFibreProductLeftProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)) I.f x
  simp only [FibredCategoryMor.toBasedFunctor, StackOver.toFibredCategoryOver] at hLeftTail
  dsimp only [x, P, explicit_two_fibre_product_owner_fiber_object,
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres,
    CategoryOver.ExplicitTwoFibreProductObject.comparison] at hLeftTail ⊢
  have hLeftObj := explicit_two_fibre_product_left_projection_owner_obj_eq (J := J) F G x
  have hRightObj := explicit_two_fibre_product_right_projection_owner_obj_eq (J := J) F G x
  cases hLeftObj
  cases hRightObj
  -- The concrete owner object forgets through the fibre equivalence to the original stored
  -- comparison, so the remaining boundary square is exactly the left pullback-comparison law.
  have hPiso :
      ↑(explicit_two_fibre_product_cover_descent_pullback_model_object (J := J) F G x).iso.hom =
        ↑Qiso.hom := by
    simp only [explicit_two_fibre_product_cover_descent_pullback_model_object,
      CategoryOver.fibreOfPullback_equiv_pullbackOfFibres]
    rfl
  erw [hPiso]
  convert congrArg (fun k ↦ (toBasedFunctor F).map k ≫ Qiso.hom.1) hLeftTail using 1
  · -- The generated endpoint transport is a self-transport, hence maps to an identity before
    -- the left pullback-comparison square is applied.
    have hEqTo
        (D : ((canonicalFiberPseudofunctor X.p).DescentData (fun I : T.Arrow ↦ I.f)))
        (h : D = D) :
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F)).map (((eqToHom h).hom I).1) =
          𝟙 _ := by
      simpa only [Functor.map_id] using
        congrArg (fun m ↦ (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor F)).map m)
          (descentData_eqToHom_self_hom_underlying (p := X.p) h I)
    erw [hEqTo]
    -- After the generated self-transport is removed, only functoriality and associativity
    -- identify the mapped pullback-comparison composite.
    erw [Category.comp_id]
    conv_rhs => erw [Functor.map_comp]
    simp only [Category.assoc]
    rfl

/-- Helper for Chap08 Lemma 8 4 6: for a concrete owner object, the right side of the
postcomposed bridge component reduces to the live reindexed comparison followed by the right
pullback leg. -/
private theorem explicit_two_fibre_product_right_composite_tail_concrete
    (F : X ⟶ S) (G : Y ⟶ S) {U : C}
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (Qfst : X.p.Fiber U) (Qsnd : Y.p.Fiber U)
    (Qiso :
      ((toBasedFunctor F).fiberFunctor U).obj Qfst ≅
        ((toBasedFunctor G).fiberFunctor U).obj Qsnd)
    (T : J.Cover U) (I : T.Arrow) :
    let x := explicit_two_fibre_product_owner_fiber_object (J := J) F G Qfst Qsnd Qiso
    let P := explicit_two_fibre_product_cover_descent_pullback_model_object (J := J) F G x
    let η := (canonicalPullbackChoice
      (FibredCategoryOver.twoFibreProduct
        (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map I.f x
    Functor.Fiber.fiberInclusion.map
        ((explicit_two_fibre_product_cover_descent_projection_component_transport_iso
            (J := J) F G T
            ((explicit_two_fibre_product_cover_descent_functor
              (J := J) F G T).obj x) I).hom ≫
          ((cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T).map
            ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
              (J := J) F G T).hom.app x)).hom I) ≫
      (toFibredCategoryMor G).toHom.map
        ((canonicalPullbackChoice Y.p).map I.f P.snd) =
    CategoryOver.ExplicitTwoFibreProductObject.comparison
        (toBasedFunctor F) (toBasedFunctor G)
        (I.f ^*[canonicalPullbackChoice
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p] x).1 ≫
      (toBasedFunctor G).map η.b := by
  let x := explicit_two_fibre_product_owner_fiber_object (J := J) F G Qfst Qsnd Qiso
  let P := explicit_two_fibre_product_cover_descent_pullback_model_object (J := J) F G x
  let η := (canonicalPullbackChoice
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map I.f x
  let ηY := (canonicalPullbackChoice Y.p).map I.f P.snd
  let tail := (toFibredCategoryMor G).toHom.map ηY
  -- Unfold the right bridge surface while keeping the transported comparison visible.
  dsimp only
  simp only [
    explicit_two_fibre_product_cover_descent_pullback_model_object,
    explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso,
    cover_descent_data_functor_of_stack_morphism,
    cover_descent_data_functor_hom_of_stack_morphism,
    Pseudofunctor.DescentData.comp_hom,
    cover_descent_data_functor_of_stack_morphism_toDescentData_iso_hom_hom,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
  erw [fiberInclusion_map_homMk_comp (p := S.p)]
  erw [Functor.map_comp]
  have hRightTail := FibredCategoryMor.pullbackComparison_inv_postcompose_owner
    (FibredCategoryOver.twoFibreProductRightProjection
      (toFibredCategoryMor F) (toFibredCategoryMor G)) I.f x
  have hComp :=
    explicit_two_fibre_product_cover_descent_transport_comparison_underlying
      (J := J) F G T x I
  simp only [FibredCategoryMor.toBasedFunctor, StackOver.toFibredCategoryOver] at hRightTail
  dsimp only [x, P, η, tail, ηY, explicit_two_fibre_product_owner_fiber_object,
    CategoryOver.fibreOfPullback_equiv_pullbackOfFibres,
    CategoryOver.ExplicitTwoFibreProductObject.comparison] at hComp hRightTail ⊢
  have hRightObj := explicit_two_fibre_product_right_projection_owner_obj_eq (J := J) F G x
  cases hRightObj
  convert congrArg (fun k ↦
      CategoryOver.ExplicitTwoFibreProductObject.comparison (toBasedFunctor F) (toBasedFunctor G)
        (I.f ^*[canonicalPullbackChoice
          (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p]
          x).1 ≫
      (toBasedFunctor G).map k) hRightTail using 1
  · -- The right bridge has the same generated endpoint self-transport; remove it before
    -- reassociating the mapped pullback-comparison tail.
    have hEqTo
        (D : ((canonicalFiberPseudofunctor Y.p).DescentData (fun I : T.Arrow ↦ I.f)))
        (h : D = D) :
        (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)).map (((eqToHom h).hom I).1) =
          𝟙 _ := by
      simpa only [Functor.map_id] using
        congrArg (fun m ↦ (FibredCategoryMor.toBasedFunctor (toFibredCategoryMor G)).map m)
          (descentData_eqToHom_self_hom_underlying (p := Y.p) h I)
    erw [hEqTo]
    -- The transported stored comparison is the comparison of the reindexed explicit product;
    -- then the right pullback-comparison tail is just functoriality.
    erw [Category.comp_id]
    conv_rhs => erw [Functor.map_comp]
    have hComp' :
        ((((explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x).obj I).1).obj.iso.hom.1 =
          CategoryOver.ExplicitTwoFibreProductObject.comparison (toBasedFunctor F) (toBasedFunctor G)
            (I.f ^*[canonicalPullbackChoice
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p] x).1 := by
      exact hComp
    rw [hComp']
    erw [Category.assoc]
    rfl

/-- Chap08 Lemma 8 4 6: after postcomposing with the owner right pullback boundary, the
component square for the fixed-cover bridge agrees with the objectwise comparison carried by the
categorical pullback model. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_components_w_postcompose
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    let P := (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x
    let ηY := (canonicalPullbackChoice Y.p).map I.f P.snd
    let tail := (toFibredCategoryMor G).toHom.map ηY
    Functor.Fiber.fiberInclusion.map
        (((cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T).map
            ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
              (J := J) F G T).hom.app x)).hom I ≫
          (((explicit_two_fibre_product_cover_descent_pullback_model_functor
              (J := J) F G T).obj P).iso.hom).hom I) ≫ tail =
      Functor.Fiber.fiberInclusion.map
          ((explicit_two_fibre_product_cover_descent_projection_component_transport_iso
              (J := J) F G T
              ((explicit_two_fibre_product_cover_descent_functor
                (J := J) F G T).obj x) I).hom ≫
            ((cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T).map
              ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
                (J := J) F G T).hom.app x)).hom I) ≫ tail := by
  -- Reduce the abstract owner object to its concrete pullback data, then use the two side
  -- normal forms and the live explicit-product square.
  rcases x with ⟨⟨U₀, ⟨Qfst, Qsnd, Qiso⟩⟩, hx⟩
  cases hx
  let xConcrete :=
    explicit_two_fibre_product_owner_fiber_object (J := J) F G Qfst Qsnd Qiso
  let η := (canonicalPullbackChoice
    (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map I.f xConcrete
  have hη :
      (toBasedFunctor F).map η.a ≫ Qiso.hom.1 =
        CategoryOver.ExplicitTwoFibreProductObject.comparison
            (toBasedFunctor F) (toBasedFunctor G)
            (I.f ^*[canonicalPullbackChoice
              (FibredCategoryOver.twoFibreProduct
                (toFibredCategoryMor F) (toFibredCategoryMor G)).p] xConcrete).1 ≫
          (toBasedFunctor G).map η.b := by
    simpa only [xConcrete, explicit_two_fibre_product_owner_fiber_object, η,
      CategoryOver.ExplicitTwoFibreProductObject.comparison] using
      explicit_two_fibre_product_eta_comm_live_underlying (J := J) F G xConcrete I.f
  exact
    (explicit_two_fibre_product_left_composite_tail_concrete
      (J := J) F G Qfst Qsnd Qiso T I).trans
      (hη.trans
        (explicit_two_fibre_product_right_composite_tail_concrete
          (J := J) F G Qfst Qsnd Qiso T I).symm)

/-- Helper for Chap08 Lemma 8 4 6: the component square for the fixed-cover
bridge agrees with the objectwise comparison carried by the categorical pullback model. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_components_w
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    (x : (FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.Fiber U)
    (I : T.Arrow) :
    (((cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
          (J := J) F G T).hom.app x)) ≫
      ((explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).obj
        ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x)).iso.hom).hom I =
    (((explicit_two_fibre_product_cover_descent_pullback_bridge
          (J := J) F G T).obj
        ((explicit_two_fibre_product_cover_descent_functor
          (J := J) F G T).obj x)).iso.hom ≫
      (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor G) T).map
        ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
          (J := J) F G T).hom.app x)).hom I := by
  -- Split the two component composites, then compare the exposed fiber morphisms after the common
  -- cartesian right boundary arrow.
  rw [explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_component_split]
  rw [explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_component_transport]
  let P := (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
    (toBasedFunctor F) (toBasedFunctor G) U).functor.obj x
  let ηY := (canonicalPullbackChoice Y.p).map I.f P.snd
  let tail := (toFibredCategoryMor G).toHom.map ηY
  have htail : S.p.IsStronglyCartesian I.f tail := by
    dsimp only [tail, ηY]
    exact
      FibredCategoryMor.map_stronglyCartesian_of_lift
        (toFibredCategoryMor G) I.f _
        ((canonicalPullbackChoice Y.p).isStronglyCartesian I.f P.snd)
  apply Functor.Fiber.hom_ext
  refine @Functor.IsStronglyCartesian.ext _ _ _ _ S.p _ _ _ _
    I.f tail htail _ _ (𝟙 I.Y) _ _ ?_ ?_ ?_
  · exact
      (((cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor F) T).map
          ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
            (J := J) F G T).hom.app x)).hom I ≫
        (((explicit_two_fibre_product_cover_descent_pullback_model_functor
            (J := J) F G T).obj P).iso.hom).hom I).2
  · exact
      ((explicit_two_fibre_product_cover_descent_projection_component_transport_iso
          (J := J) F G T
          ((explicit_two_fibre_product_cover_descent_functor
            (J := J) F G T).obj x) I).hom ≫
        ((cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T).map
          ((explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
            (J := J) F G T).hom.app x)).hom I).2
  · -- The cartesian-extensionality boundary is exactly the isolated postcomposition helper.
    exact
      explicit_two_fibre_product_cover_descent_comp_pullback_bridge_components_w_postcompose
        (J := J) F G T x I

/-- Helper for Chap08 Lemma 8 4 6: the whiskered explicit bridge agrees with the owner pullback model
once the two pullback projections are matched and the midpoint coherence is checked objectwise. -/
private theorem explicit_two_fibre_product_cover_descent_comp_pullback_bridge_projection_coherence
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    Functor.whiskerRight
        (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso
          (J := J) F G T).hom
        (cover_descent_data_functor_of_stack_morphism
          (J := J) (toFibredCategoryMor F) T) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
              (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
            explicit_two_fibre_product_cover_descent_pullback_model_functor
              (J := J) F G T)
          (CatCommSq.iso
            (π₁
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (π₂
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T)
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T)).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
            explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T)
          (CatCommSq.iso
            (π₁
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (π₂
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor F) T)
              (cover_descent_data_functor_of_stack_morphism
                (J := J) (toFibredCategoryMor G) T))
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor F) T)
            (cover_descent_data_functor_of_stack_morphism
              (J := J) (toFibredCategoryMor G) T)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso
            (J := J) F G T).hom
          (cover_descent_data_functor_of_stack_morphism
            (J := J) (toFibredCategoryMor G) T) := by
  -- Reduce the natural-transformation coherence to its coverwise component. The remaining
  -- transport is isolated in the component square for the bridge and model comparison.
  ext x I
  -- The functorial associators and whiskers only expose the component equality above.
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, CatCommSq.iso, NatIso.ofComponents_hom_app] using
      explicit_two_fibre_product_cover_descent_comp_pullback_bridge_components_w
        (J := J) F G T x I

private noncomputable abbrev explicit_two_fibre_product_cover_descent_comp_pullback_bridge_iso
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
      explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T) ≅
    ((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor ⋙
      explicit_two_fibre_product_cover_descent_pullback_model_functor
        (J := J) F G T) :=
  -- Package the left/right projection comparisons together with the midpoint coherence exactly as
  -- the universal constructor `CategoricalPullback.mkNatIso` for natural isomorphisms of functors
  -- into a categorical pullback.
  CategoricalPullback.mkNatIso
    (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_left_iso (J := J) F G T)
    (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_right_iso (J := J) F G T)
    (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_projection_coherence
      (J := J) F G T)

/-- Helper for Chap08 Lemma 8 4 6: once the explicit bridge to the categorical pullback is known to be
an equivalence, the whiskered comparison with the owner pullback model closes the fixed-cover
descent argument by `2`-out-of-`3`. -/
private theorem explicit_two_fibre_product_cover_descent_isEquivalence_close
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U)
    (hBridge :
      (explicit_two_fibre_product_cover_descent_pullback_bridge
        (J := J) F G T).IsEquivalence)
    (hPullbackModel :
      (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor) ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).IsEquivalence) :
    (explicit_two_fibre_product_cover_descent_functor
      (J := J) F G T).IsEquivalence := by
  -- `2`-out-of-`3`: the explicit bridge and the owner fibre equivalence are equivalences, and the
  -- whiskered comparison `…_comp_pullback_bridge_iso` identifies `descent ⋙ bridge` with
  -- `eFib ⋙ pullbackModel`. The latter being an equivalence forces `pullbackModel` to be one, and
  -- then `isEquivalence_iff_of_whiskered_iso` transports equivalence back to the descent functor.
  letI : (explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T).IsEquivalence :=
    hBridge
  letI : (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
      (toBasedFunctor F) (toBasedFunctor G) U).functor.IsEquivalence := inferInstance
  have hmodel :
      (explicit_two_fibre_product_cover_descent_pullback_model_functor (J := J) F G T).IsEquivalence := by
    letI : (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
          (toBasedFunctor F) (toBasedFunctor G) U).functor) ⋙
        explicit_two_fibre_product_cover_descent_pullback_model_functor
          (J := J) F G T).IsEquivalence := hPullbackModel
    exact Functor.isEquivalence_of_comp_left
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor
      (explicit_two_fibre_product_cover_descent_pullback_model_functor (J := J) F G T)
  exact
    (isEquivalence_iff_of_whiskered_iso
      (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres
        (toBasedFunctor F) (toBasedFunctor G) U).functor
      (explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T)
      (explicit_two_fibre_product_cover_descent_functor (J := J) F G T)
      (explicit_two_fibre_product_cover_descent_pullback_model_functor (J := J) F G T)
      (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_iso (J := J) F G T)).2 hmodel

/-- Helper for Chap08 Lemma 8 4 6: the bridge from fixed-cover descent data on the explicit `2`-fibre
product to the categorical pullback of the projected descent-data categories is faithful, because a
morphism of descent data is determined on each leg by its two explicit-pullback components. -/
private instance explicit_two_fibre_product_cover_descent_pullback_bridge_faithful
    (F : X ⟶ S) (G : Y ⟶ S) {U : C} (T : J.Cover U)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered] :
    (explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T).Faithful := by
  refine ⟨fun {D₁ D₂} ψ ψ' h => ?_⟩
  -- The two projections of `h` are the equalities of the left/right projected descent morphisms.
  have hX :
      (explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T).map ψ =
        (explicit_two_fibre_product_cover_descent_left_projection (J := J) F G T).map ψ' :=
    congrArg (CategoricalPullback.π₁ _ _).map h
  have hY :
      (explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T).map ψ =
        (explicit_two_fibre_product_cover_descent_right_projection (J := J) F G T).map ψ' :=
    congrArg (CategoricalPullback.π₂ _ _).map h
  apply Pseudofunctor.DescentData.hom_ext
  intro I
  apply Functor.Fiber.hom_ext
  apply CategoryOver.ExplicitTwoFibreProductHom.ext
  · exact congrArg
      (fun m => Functor.Fiber.fiberInclusion.map (Pseudofunctor.DescentData.Hom.hom m I)) hX
  · exact congrArg
      (fun m => Functor.Fiber.fiberInclusion.map (Pseudofunctor.DescentData.Hom.hom m I)) hY

/-- Helper for Chap08 Lemma 8 4 6: the commutativity field of a descent-data morphism can be
specialized while keeping the two overlap equalities as explicit arguments. -/
private theorem descentDataHom_comm_explicit
    {ι : Type*} {S₀ : C} {X₀ : ι → C} {f : ∀ i, X₀ i ⟶ S₀}
    {F₀ : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {D₁ D₂ : F₀.DescentData f} (φ : D₁ ⟶ D₂)
    {V : C} (q : V ⟶ S₀) {i₁ i₂ : ι}
    (f₁ : V ⟶ X₀ i₁) (f₂ : V ⟶ X₀ i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F₀.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫
        D₂.hom q f₁ f₂ hf₁ hf₂ =
      D₁.hom q f₁ f₂ hf₁ hf₂ ≫
        (F₀.map f₂.op.toLoc).toFunctor.map (φ.hom i₂) := by
  -- This is exactly the structure field, with the overlap proof arguments pinned explicitly.
  exact φ.comm q f₁ f₂ hf₁ hf₂

/-- Helper for Chap08 Lemma 8 4 6: a morphism between fixed-cover transports satisfies the
same descent square after conjugating its components by the stack-morphism pullback comparisons. -/
private theorem cover_descent_data_functor_comm_conjugated_of_stack_morphism
    {A B : FibredCategoryOver C} (H : A ⟶ B) [A.p.IsFibered] [B.p.IsFibered]
    {U : C} (T : J.Cover U)
    {D₁ D₂ : ((canonicalFiberPseudofunctor A.p).DescentData (fun I : T.Arrow ↦ I.f))}
    (φ : (cover_descent_data_functor_of_stack_morphism (J := J) H T).obj D₁ ⟶
      (cover_descent_data_functor_of_stack_morphism (J := J) H T).obj D₂)
    {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
    (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch)
    (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (FibredCategoryMor.pullbackComparison H f₁ (D₁.obj I₁)).inv ≫
      ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁) ≫
      (FibredCategoryMor.pullbackComparison H f₁ (D₂.obj I₁)).hom ≫
      (FibredCategoryMor.fiberFunctor H V).map (D₂.hom q f₁ f₂ hf₁ hf₂) =
    (FibredCategoryMor.fiberFunctor H V).map (D₁.hom q f₁ f₂ hf₁ hf₂) ≫
      (FibredCategoryMor.pullbackComparison H f₂ (D₁.obj I₂)).inv ≫
      ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂) ≫
      (FibredCategoryMor.pullbackComparison H f₂ (D₂.obj I₂)).hom := by
  -- Unfold the transported overlap maps in `φ.comm`, then cancel the outer comparison pair to
  -- move from the transported descent square to the conjugated square used componentwise below.
  let e₁₁ := FibredCategoryMor.pullbackComparison H f₁ (D₁.obj I₁)
  let e₁₂ := FibredCategoryMor.pullbackComparison H f₁ (D₂.obj I₁)
  let e₂₁ := FibredCategoryMor.pullbackComparison H f₂ (D₁.obj I₂)
  let e₂₂ := FibredCategoryMor.pullbackComparison H f₂ (D₂.obj I₂)
  let α₁ := ((canonicalFiberPseudofunctor B.p).map f₁.op.toLoc).toFunctor.map (φ.hom I₁)
  let α₂ := ((canonicalFiberPseudofunctor B.p).map f₂.op.toLoc).toFunctor.map (φ.hom I₂)
  let d₁ := (FibredCategoryMor.fiberFunctor H V).map (D₁.hom q f₁ f₂ hf₁ hf₂)
  let d₂ := (FibredCategoryMor.fiberFunctor H V).map (D₂.hom q f₁ f₂ hf₁ hf₂)
  have hφ :
      α₁ ≫ (e₁₂.hom ≫ d₂ ≫ e₂₂.inv) =
        (e₁₁.hom ≫ d₁ ≫ e₂₁.inv) ≫ α₂ := by
    simpa only [α₁, α₂, d₁, d₂, e₁₁, e₁₂, e₂₁, e₂₂,
      cover_descent_data_functor_of_stack_morphism,
      cover_descent_data_functor_hom_of_stack_morphism] using
      φ.comm q f₁ f₂ hf₁ hf₂
  have hinsertRight :
      e₁₁.inv ≫ α₁ ≫ e₁₂.hom ≫ d₂ =
        e₁₁.inv ≫ (α₁ ≫ (e₁₂.hom ≫ d₂ ≫ e₂₂.inv)) ≫ e₂₂.hom := by
    let A := e₁₁.inv ≫ α₁ ≫ e₁₂.hom ≫ d₂
    have hid : A ≫ 𝟙 _ = A := Category.comp_id A
    have hins : A ≫ 𝟙 _ = A ≫ e₂₂.inv ≫ e₂₂.hom := by
      simpa only [A, Category.assoc] using
        congrArg (fun k ↦ A ≫ k) e₂₂.inv_hom_id.symm
    simpa only [A, Category.assoc] using hid.symm.trans hins
  have hwhisker :
      e₁₁.inv ≫ (α₁ ≫ (e₁₂.hom ≫ d₂ ≫ e₂₂.inv)) ≫ e₂₂.hom =
        e₁₁.inv ≫ ((e₁₁.hom ≫ d₁ ≫ e₂₁.inv) ≫ α₂) ≫ e₂₂.hom := by
    exact congrArg (fun k ↦ e₁₁.inv ≫ k ≫ e₂₂.hom) hφ
  have hcancelLeft :
      e₁₁.inv ≫ ((e₁₁.hom ≫ d₁ ≫ e₂₁.inv) ≫ α₂) ≫ e₂₂.hom =
        d₁ ≫ e₂₁.inv ≫ α₂ ≫ e₂₂.hom := by
    simpa only [Category.assoc] using
      stack_morphism_pullbackComparison_inv_hom_postcompose_normalized
        H f₁ (D₁.obj I₁) (k := d₁ ≫ e₂₁.inv ≫ α₂ ≫ e₂₂.hom)
  have hmain : e₁₁.inv ≫ α₁ ≫ e₁₂.hom ≫ d₂ =
      d₁ ≫ e₂₁.inv ≫ α₂ ≫ e₂₂.hom :=
    hinsertRight.trans (hwhisker.trans hcancelLeft)
  simpa only [e₁₁, e₁₂, e₂₁, e₂₂, α₁, α₂, d₁, d₂] using hmain

/-- Helper for Chap08 Lemma 8 4 6: the remaining fixed-cover source comparison is the equivalence from
descent data on the explicit stack-level `2`-fibre product to the categorical pullback of the two
projected descent-data categories. The current blocker is the transport-heavy inverse-functor
comparison in the owner pullback-of-fibres category. -/
private theorem explicit_two_fibre_product_cover_descent_pullback_bridge_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct
      (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    (explicit_two_fibre_product_cover_descent_pullback_bridge
      (J := J) F G T).IsEquivalence := by
  -- The bridge is faithful and full; essential surjectivity is FREE: `descent ⋙ bridge` is an
  -- equivalence (it is isomorphic to `eFib ⋙ pullbackModel`, an equivalence), so every `Q` is hit
  -- by `bridge (descent x)`, hence by `bridge` itself.
  haveI hComp :
      (explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
        explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T).IsEquivalence :=
    (Functor.isEquivalence_iff_of_iso
      (explicit_two_fibre_product_cover_descent_comp_pullback_bridge_iso (J := J) F G T)).2
      (cover_descent_pullback_model_isEquivalence_bridge_explicit (J := J) F G T)
  haveI : (explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T).Full := by
    refine ⟨fun {D₁ D₂} ψ => ?_⟩
    let componentHom (I : T.Arrow) : D₁.obj I ⟶ D₂.obj I :=
      ⟨{ base := eqToHom (D₁.obj I).2 ≫ eqToHom (D₂.obj I).2.symm,
          a := (ψ.fst.hom I).1,
          a_over := by
            exact isHomLift_eqToHom_comp_eqToHom_of_id X.p
              (D₁.obj I).2 (D₂.obj I).2 (ψ.fst.hom I).1 (ψ.fst.hom I).2,
          b := (ψ.snd.hom I).1,
          b_over := by
            exact isHomLift_eqToHom_comp_eqToHom_of_id Y.p
              (D₁.obj I).2 (D₂.obj I).2 (ψ.snd.hom I).1 (ψ.snd.hom I).2,
          comm := by
            -- The categorical-pullback morphism condition is a descent-data morphism equation;
            -- evaluating it on `I` and forgetting the fiber gives the explicit pullback square.
            constructor
            have h := congrArg (fun α => α.hom I) ψ.w
            have h' := congrArg (fun α => Functor.Fiber.fiberInclusion.map α) h
            simpa only [Pseudofunctor.DescentData.comp_hom,
              explicit_two_fibre_product_cover_descent_pullback_square,
              explicit_two_fibre_product_cover_descent_projection_data_iso,
              explicit_two_fibre_product_cover_descent_projection_component_transport_hom_underlying] using h' },
        by
          -- The explicit morphism's stored base is the equality transport between the two
          -- representatives of the same cover-leg fiber, hence it lies over `𝟙 I.Y`.
          refine IsHomLift.of_fac'
            (FibredCategoryOver.twoFibreProduct
              (toFibredCategoryMor F) (toFibredCategoryMor G)).p
            (𝟙 I.Y) _ (D₁.obj I).2 (D₂.obj I).2 ?_
          change eqToHom (D₁.obj I).2 ≫ eqToHom (D₂.obj I).2.symm =
            eqToHom (D₁.obj I).2 ≫ 𝟙 I.Y ≫ eqToHom (D₂.obj I).2.symm
          simp only [Category.id_comp]⟩
    have hcomponent_comm :
        ∀ {V : C} (q : V ⟶ U) {I₁ I₂ : T.Arrow}
          (f₁ : V ⟶ I₁.Y) (f₂ : V ⟶ I₂.Y)
          (hf₁ : f₁ ≫ I₁.f = q) (hf₂ : f₂ ≫ I₂.f = q),
          (((canonicalFiberPseudofunctor
                        (FibredCategoryOver.twoFibreProduct
                          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                    f₁.op.toLoc).toFunctor.map (componentHom I₁)) ≫
              D₂.hom q f₁ f₂ hf₁ hf₂ =
          D₁.hom q f₁ f₂ hf₁ hf₂ ≫
              (((canonicalFiberPseudofunctor
                        (FibredCategoryOver.twoFibreProduct
                          (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
                    f₂.op.toLoc).toFunctor.map (componentHom I₂)) := by
      intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
      -- Project the product equality to the explicit pullback components, where the reconstructed
      -- morphism is exactly the pair `ψ.fst`, `ψ.snd` and the conjugated descent square applies.
      apply Functor.Fiber.hom_ext
      apply CategoryOver.ExplicitTwoFibreProductHom.ext
      · have hcomponent₁ :
            (FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₁.Y).map
              (componentHom I₁) = ψ.fst.hom I₁ := by
          apply Functor.Fiber.hom_ext
          rfl
        have hcomponent₂ :
            (FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₂.Y).map
              (componentHom I₂) = ψ.fst.hom I₂ := by
          apply Functor.Fiber.hom_ext
          rfl
        let φ₁ := (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₁.op.toLoc).toFunctor.map (componentHom I₁))
        let δ₂ := D₂.hom q f₁ f₂ hf₁ hf₂
        let δ₁ := D₁.hom q f₁ f₂ hf₁ hf₂
        let φ₂ := (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₂.op.toLoc).toFunctor.map (componentHom I₂))
        change (Functor.Fiber.fiberInclusion.map (φ₁ ≫ δ₂)).a =
          (Functor.Fiber.fiberInclusion.map (δ₁ ≫ φ₂)).a
        rw [explicit_two_fibre_product_hom_a_comp (J := J) F G φ₁ δ₂,
          explicit_two_fibre_product_hom_a_comp (J := J) F G δ₁ φ₂]
        dsimp only [δ₁, δ₂]
        rw [explicit_two_fibre_product_left_projection_canonical_pullback_map_component
            (J := J) F G f₁ (componentHom I₁),
          explicit_two_fibre_product_left_projection_canonical_pullback_map_component
            (J := J) F G f₂ (componentHom I₂),
          ← explicit_two_fibre_product_left_projection_map_component
            (J := J) F G (φ := D₂.hom q f₁ f₂ hf₁ hf₂),
          ← explicit_two_fibre_product_left_projection_map_component
            (J := J) F G (φ := D₁.hom q f₁ f₂ hf₁ hf₂)]
        have h := cover_descent_data_functor_comm_conjugated_of_stack_morphism
            (J := J)
            (H := FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) T ψ.fst q f₁ f₂ hf₁ hf₂
        rw [← hcomponent₁, ← hcomponent₂] at h
        -- Keep the outer inclusion functoriality separate from the transport square, so only one
        -- `Functor.map_comp` is used on each side.
        let κ₁ :=
          (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₁ (D₁.obj I₁)).inv ≫
            ((canonicalFiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₁.Y).map
                (componentHom I₁)) ≫
            (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₁ (D₂.obj I₁)).hom
        let d₂' :=
          (FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
            (D₂.hom q f₁ f₂ hf₁ hf₂)
        let d₁' :=
          (FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductLeftProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
            (D₁.hom q f₁ f₂ hf₁ hf₂)
        let κ₂ :=
          (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₂ (D₁.obj I₂)).inv ≫
            ((canonicalFiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductLeftProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₂.Y).map
                (componentHom I₂)) ≫
            (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductLeftProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₂ (D₂.obj I₂)).hom
        change Functor.Fiber.fiberInclusion.map κ₁ ≫
            Functor.Fiber.fiberInclusion.map d₂' =
          Functor.Fiber.fiberInclusion.map d₁' ≫
            Functor.Fiber.fiberInclusion.map κ₂
        have hmain : κ₁ ≫ d₂' = d₁' ≫ κ₂ := by
          dsimp only [κ₁, κ₂, d₁', d₂']
          simpa only [StackOver.p, StackOver.toFibredCategoryOver, Category.assoc] using h
        calc
          Functor.Fiber.fiberInclusion.map κ₁ ≫
              Functor.Fiber.fiberInclusion.map d₂' =
            Functor.Fiber.fiberInclusion.map (κ₁ ≫ d₂') := by
              exact (Functor.map_comp Functor.Fiber.fiberInclusion κ₁ d₂').symm
          _ = Functor.Fiber.fiberInclusion.map (d₁' ≫ κ₂) := by
              exact congrArg (fun m => Functor.Fiber.fiberInclusion.map m) hmain
          _ = Functor.Fiber.fiberInclusion.map d₁' ≫
              Functor.Fiber.fiberInclusion.map κ₂ := by
              exact Functor.map_comp Functor.Fiber.fiberInclusion d₁' κ₂
      · have hcomponent₁ :
            (FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₁.Y).map
              (componentHom I₁) = ψ.snd.hom I₁ := by
          apply Functor.Fiber.hom_ext
          rfl
        have hcomponent₂ :
            (FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₂.Y).map
              (componentHom I₂) = ψ.snd.hom I₂ := by
          apply Functor.Fiber.hom_ext
          rfl
        let φ₁ := (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₁.op.toLoc).toFunctor.map (componentHom I₁))
        let δ₂ := D₂.hom q f₁ f₂ hf₁ hf₂
        let δ₁ := D₁.hom q f₁ f₂ hf₁ hf₂
        let φ₂ := (((canonicalFiberPseudofunctor
          (FibredCategoryOver.twoFibreProduct
            (toFibredCategoryMor F) (toFibredCategoryMor G)).p).map
          f₂.op.toLoc).toFunctor.map (componentHom I₂))
        change (Functor.Fiber.fiberInclusion.map (φ₁ ≫ δ₂)).b =
          (Functor.Fiber.fiberInclusion.map (δ₁ ≫ φ₂)).b
        rw [explicit_two_fibre_product_hom_b_comp (J := J) F G φ₁ δ₂,
          explicit_two_fibre_product_hom_b_comp (J := J) F G δ₁ φ₂]
        dsimp only [δ₁, δ₂]
        rw [explicit_two_fibre_product_right_projection_canonical_pullback_map_component
            (J := J) F G f₁ (componentHom I₁),
          explicit_two_fibre_product_right_projection_canonical_pullback_map_component
            (J := J) F G f₂ (componentHom I₂),
          ← explicit_two_fibre_product_right_projection_map_component
            (J := J) F G (φ := D₂.hom q f₁ f₂ hf₁ hf₂),
          ← explicit_two_fibre_product_right_projection_map_component
            (J := J) F G (φ := D₁.hom q f₁ f₂ hf₁ hf₂)]
        have h := cover_descent_data_functor_comm_conjugated_of_stack_morphism
            (J := J)
            (H := FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) T ψ.snd q f₁ f₂ hf₁ hf₂
        rw [← hcomponent₁, ← hcomponent₂] at h
        -- The right projection is symmetric to the left: expose the four projected pieces,
        -- consume the conjugated square, and then map the resulting equality.
        let κ₁ :=
          (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₁ (D₁.obj I₁)).inv ≫
            ((canonicalFiberPseudofunctor Y.p).map f₁.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₁.Y).map
                (componentHom I₁)) ≫
            (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₁ (D₂.obj I₁)).hom
        let d₂' :=
          (FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
            (D₂.hom q f₁ f₂ hf₁ hf₂)
        let d₁' :=
          (FibredCategoryMor.fiberFunctor
            (FibredCategoryOver.twoFibreProductRightProjection
              (toFibredCategoryMor F) (toFibredCategoryMor G)) V).map
            (D₁.hom q f₁ f₂ hf₁ hf₂)
        let κ₂ :=
          (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₂ (D₁.obj I₂)).inv ≫
            ((canonicalFiberPseudofunctor Y.p).map f₂.op.toLoc).toFunctor.map
              ((FibredCategoryMor.fiberFunctor
                (FibredCategoryOver.twoFibreProductRightProjection
                  (toFibredCategoryMor F) (toFibredCategoryMor G)) I₂.Y).map
                (componentHom I₂)) ≫
            (FibredCategoryMor.pullbackComparison
              (FibredCategoryOver.twoFibreProductRightProjection
                (toFibredCategoryMor F) (toFibredCategoryMor G)) f₂ (D₂.obj I₂)).hom
        change Functor.Fiber.fiberInclusion.map κ₁ ≫
            Functor.Fiber.fiberInclusion.map d₂' =
          Functor.Fiber.fiberInclusion.map d₁' ≫
            Functor.Fiber.fiberInclusion.map κ₂
        have hmain : κ₁ ≫ d₂' = d₁' ≫ κ₂ := by
          dsimp only [κ₁, κ₂, d₁', d₂']
          simpa only [StackOver.p, StackOver.toFibredCategoryOver, Category.assoc] using h
        calc
          Functor.Fiber.fiberInclusion.map κ₁ ≫
              Functor.Fiber.fiberInclusion.map d₂' =
            Functor.Fiber.fiberInclusion.map (κ₁ ≫ d₂') := by
              exact (Functor.map_comp Functor.Fiber.fiberInclusion κ₁ d₂').symm
          _ = Functor.Fiber.fiberInclusion.map (d₁' ≫ κ₂) := by
              exact congrArg (fun m => Functor.Fiber.fiberInclusion.map m) hmain
          _ = Functor.Fiber.fiberInclusion.map d₁' ≫
              Functor.Fiber.fiberInclusion.map κ₂ := by
              exact Functor.map_comp Functor.Fiber.fiberInclusion d₁' κ₂
    refine ⟨{ hom := componentHom, comm := ?_ }, ?_⟩
    · intro V q I₁ I₂ f₁ f₂ hf₁ hf₂
      -- The descent-morphism compatibility is now isolated in one normal-form statement instead
      -- of duplicating the same projection transport for left and right components.
      exact hcomponent_comm q f₁ f₂ hf₁ hf₂
    · -- The bridge sends this reconstructed morphism back to `ψ` because the two categorical
      -- pullback projections are definitionally the chosen components.
      apply CategoricalPullback.hom_ext
      · rfl
      · rfl
  haveI : (explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T).EssSurj := by
    refine ⟨fun Q => ?_⟩
    obtain ⟨x, ⟨e⟩⟩ :=
      Functor.EssSurj.mem_essImage
        (F := explicit_two_fibre_product_cover_descent_functor (J := J) F G T ⋙
          explicit_two_fibre_product_cover_descent_pullback_bridge (J := J) F G T) Q
    exact ⟨(explicit_two_fibre_product_cover_descent_functor (J := J) F G T).obj x, ⟨e⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Helper for Chap08 Lemma 8 4 6: for a fixed cover, the remaining source-faithful frontier is to show
that descent data on the explicit stack-level `2`-fibre product are equivalent to the categorical
pullback of the two projected fixed-cover descent-data categories. This now depends only on the
blocked explicit bridge and the already frozen owner-model comparison. -/
private theorem explicit_two_fibre_product_cover_descent_isEquivalence
    (F : X ⟶ S) (G : Y ⟶ S)
    [(FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p.IsFibered]
    {U : C} (T : J.Cover U) :
    ((canonicalFiberPseudofunctor
        (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p).toDescentData
          (fun I : T.Arrow ↦ I.f)).IsEquivalence :=
  -- Combine the explicit bridge equivalence with the owner-model whiskered equivalence (proved in
  -- `FixedCoverEquivalenceBridge`) through the `2`-out-of-`3` closing lemma.
  explicit_two_fibre_product_cover_descent_isEquivalence_close (J := J) F G (T := T)
    (explicit_two_fibre_product_cover_descent_pullback_bridge_isEquivalence (J := J) F G T)
    (cover_descent_pullback_model_isEquivalence_bridge_explicit (J := J) F G T)

/-- Helper for Chap08 Lemma 8 4 6: the `(2,1)`-category of stacks over the site `(C, J)` has `2`-fibre products,
and the explicit pullback owner from Categories, Lemma `4.32.3`, is again a stack over `(C, J)`.
-/
@[stacks 026G]
theorem stackTwoFibreProduct_isStack
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p := by
  -- Route correction: first reduce the stack condition to fixed covers via Lemma `8.4.2`; the
  -- entire remaining source-faithful content is the fixed-cover equivalence isolated above.
  let P := FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)
  letI : P.p.IsFibered := stack_two_fibre_product_projection_isFibered F G
  exact
    (isStackOnSite_iff_coverwise_canonicalDescentFunctor_isEquivalence J P.p).2
      (fun U T ↦ by
        exact explicit_two_fibre_product_cover_descent_isEquivalence (J := J) F G (T := T))

/-- Helper for Chap08 Lemma 8 4 6: the explicit `2`-fibre product of morphisms of stacks over `(C, J)`
carries the induced stack structure by the owner theorem `stackTwoFibreProduct_isStack`. -/
instance instIsStackOnSiteObjToCategoryOverTwoFibreProductP
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStackOnSite J
      (FibredCategoryOver.twoFibreProduct (toFibredCategoryMor F) (toFibredCategoryMor G)).p :=
  stackTwoFibreProduct_isStack F G

end CategoryTheory

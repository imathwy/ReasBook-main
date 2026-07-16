import stacks_proof.stacks_project.Chap04.Lemma_4_35_17
import stacks_proof.stacks_project.Chap04.Lemma_4_2_18
import stacks_proof.stacks_project.Chap04.Definition_4_2_17
import stacks_proof.stacks_project.Chap04.Definition_4_35_1
import stacks_proof.stacks_project.Chap04.Lemma_4_33_3
import stacks_proof.stacks_project.Chap04.Lemma_4_33_7
import stacks_proof.stacks_project.Chap04.Lemma_4_33_8
import stacks_proof.stacks_project.Chap07.Definition_7_13_1
import stacks_proof.stacks_project.Chap08.Definition_8_2_2
import stacks_proof.stacks_project.Chap08.Definition_8_3_5
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_5_3_PullbackNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_10_1
import stacks_proof.stacks_project.Chap08.Lemma_8_10_4
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.ForgetToSource

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open FibredCategoryOver
open Functor IsStronglyCartesian
open Opposite
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: for any fibred category, the canonical pullback functor maps a
vertical morphism to the unique factorization through the chosen pullback arrow. This local owner
keeps the inherited-source naturality proof flat. -/
theorem canonical_pullbackFunctor_map_fac_owner
    {T : Type*} [Category T] (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) {x y : p.Fiber U} (φ : x ⟶ y) :
    ((((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map φ)).1 ≫
        (canonicalPullbackChoice p).map f y =
      (canonicalPullbackChoice p).map f x ≫ φ.1 := by
  -- Compare the chosen pullback of `y` with the factorization induced by the vertical map `φ`.
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  have hpull : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f x) :=
    (canonicalPullbackChoice p).isStronglyCartesian f x
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x) := hpull.toIsHomLift
  letI : p.IsHomLift f ((canonicalPullbackChoice p).map f x ≫ φ.1) :=
    IsHomLift.comp_lift_id_right' p f ((canonicalPullbackChoice p).map f x) U φ.1
  letI : p.IsStronglyCartesian f ((canonicalPullbackChoice p).map f y) :=
    (canonicalPullbackChoice p).isStronglyCartesian f y
  -- The owner `map` of a strongly cartesian arrow gives exactly the desired factorization.
  change
      Functor.IsStronglyCartesian.map p f ((canonicalPullbackChoice p).map f y)
        (Category.id_comp f).symm
        ((canonicalPullbackChoice p).map f x ≫ φ.1) ≫
          (canonicalPullbackChoice p).map f y =
        (canonicalPullbackChoice p).map f x ≫ φ.1
  exact
    Functor.IsStronglyCartesian.fac p f ((canonicalPullbackChoice p).map f y)
      (Category.id_comp f).symm
      ((canonicalPullbackChoice p).map f x ≫ φ.1)

/-- Helper for Lemma 8.10.5: postcomposing the inverse pullback-comparison morphism with the
chosen pullback arrow in `(G F)` recovers the chosen downstairs pullback arrow in `Xₛ`. -/
theorem inherited_source_pullback_comparison_inv_postcompose_owner
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) (x : (G F).Fiber yi) :
    (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).inv.1 ≫
        (canonicalPullbackChoice (G F)).map f x =
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
        (inherited_source_fiber_obj (F := F) x) := by
  let e :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  have hcancel : e.inv.1 ≫ e.hom.1 = 𝟙 _ := by
    exact congrArg Subtype.val e.inv_hom_id
  -- Rewrite the chosen `(G F)` pullback through the comparison hom, then cancel `e.inv ≫ e.hom`.
  rw [← inherited_source_pullback_comparison_hom_postcompose
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x]
  calc
    e.inv.1 ≫ e.hom.1 ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
            (inherited_source_fiber_obj (F := F) x) =
        (e.inv.1 ≫ e.hom.1) ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
            (inherited_source_fiber_obj (F := F) x) := by
              simp [Category.assoc]
    _ =
        𝟙 _ ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
            (inherited_source_fiber_obj (F := F) x) := by
              exact congrArg
                (fun k ↦
                  k ≫ (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
                    (inherited_source_fiber_obj (F := F) x))
                hcancel
    _ =
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
          (inherited_source_fiber_obj (F := F) x) := by
            simp

/-- Helper for Lemma 8.10.5: after postcomposing both candidate composites with the common chosen
downstairs pullback arrow, the owner-level composites for `inherited_source_pullback_comparison`
agree. This is the rewrite-stable core of the vertical naturality square. -/
theorem inherited_source_pullback_comparison_hom_postcompose_eq_owner
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) {x y : (G F).Fiber yi} (φ : x ⟶ y) :
    (((inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
      (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).hom.1) ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y) =
    (((inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
        ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) yi).map φ))).1)) ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y) := by
  -- Compare the two candidates only after postcomposing with the common chosen pullback arrow.
  let lhs :=
    (((inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
      (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).hom.1) ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
  let mid₁ :=
    ((inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
      (canonicalPullbackChoice (G F)).map f y
  let mid₂ :=
    (canonicalPullbackChoice (G F)).map f x ≫
      ((inherited_source_fiber_forget (F := F) yi).map φ).1
  let mid₃ :=
    (((inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
          (inherited_source_fiber_obj (F := F) x)) ≫
      ((inherited_source_fiber_forget (F := F) yi).map φ).1)
  let mid₄ :=
    (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
      ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) yi).map φ))).1 ≫
        (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
  let rhs :=
    (((inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
        ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) yi).map φ))).1)) ≫
      (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
  have h₁ : lhs = mid₁ := by
    -- Rewrite the comparison at `y` to the canonical chosen pullback arrow in `(G F)`.
    calc
      (((inherited_source_fiber_forget (F := F) Z).map
            ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).hom.1) ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
            (inherited_source_fiber_obj (F := F) y) =
          ((inherited_source_fiber_forget (F := F) Z).map
              ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
            ((inherited_source_pullback_comparison
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).hom.1 ≫
              (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
                (inherited_source_fiber_obj (F := F) y)) := by
              simp [Category.assoc]
      _ =
          ((inherited_source_fiber_forget (F := F) Z).map
              ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))).1 ≫
            (canonicalPullbackChoice (G F)).map f y := by
              exact
                congrArg
                  (fun k ↦
                    ((inherited_source_fiber_forget (F := F) Z).map
                        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map
                            φ))).1 ≫ k)
                  (inherited_source_pullback_comparison_hom_postcompose
                    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y)
  have h₂ : mid₁ = mid₂ := by
    -- The chosen pullback in `(G F)` is already natural on the vertical morphism `φ`.
    simpa only [mid₁, mid₂, inherited_source_fiber_forget] using
      canonical_pullbackFunctor_map_fac_owner
        (p := G F) (f := f) (φ := φ)
  have h₃ : mid₂ = mid₃ := by
    -- Rewrite the chosen pullback at `x` back through the comparison isomorphism.
    change
      (canonicalPullbackChoice (G F)).map f x ≫
          ((inherited_source_fiber_forget (F := F) yi).map φ).1 =
        (((inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
            (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
              (inherited_source_fiber_obj (F := F) x)) ≫
          ((inherited_source_fiber_forget (F := F) yi).map φ).1)
    exact
      (congrArg
        (fun k ↦ k ≫ ((inherited_source_fiber_forget (F := F) yi).map φ).1)
        (inherited_source_pullback_comparison_hom_postcompose
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x)).symm
  have h₄ : mid₃ = mid₄ := by
    -- Move the forgotten source-fiber map across the chosen source pullback arrow.
    calc
      (((inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
            (inherited_source_fiber_obj (F := F) x)) ≫
        ((inherited_source_fiber_forget (F := F) yi).map φ).1) =
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
            ((canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
              (inherited_source_fiber_obj (F := F) x) ≫
              ((inherited_source_fiber_forget (F := F) yi).map φ).1) := by
            rw [Category.assoc]
      _ =
          (inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
            (((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
                ((inherited_source_fiber_forget (F := F) yi).map φ))).1 ≫
              (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f)
                (inherited_source_fiber_obj (F := F) y)) := by
            exact
              congrArg
                (fun k ↦
                  (inherited_source_pullback_comparison
                    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫ k)
                (canonical_pullbackFunctor_map_fac_owner
                  (p := Xₛ.p) (f := Yₛ.p.map f)
                  (φ := (inherited_source_fiber_forget (F := F) yi).map φ)).symm
      _ = mid₄ := by rfl
  have h₅ : mid₄ = rhs := by
    -- Reassociate the right-hand composite into the packaged naturality shape.
    change
      (inherited_source_pullback_comparison
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
          ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
              ((inherited_source_fiber_forget (F := F) yi).map φ))).1 ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y) =
        (((inherited_source_pullback_comparison
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom.1 ≫
            ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
              ((inherited_source_fiber_forget (F := F) yi).map φ))).1)) ≫
          (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
    exact (Category.assoc _ _ _).symm
  exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))

/-- Helper for Lemma 8.10.5: the inherited source pullback comparison is fiberwise natural on
vertical morphisms in the `G F`-fiber. -/
theorem inherited_source_pullback_comparison_naturality_over_vertical
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) {x y : (G F).Fiber yi} (φ : x ⟶ y) :
    ((inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))) ≫
      (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).hom =
    (inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).hom ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) yi).map φ)) := by
  let ex :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ey :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y
  let η :=
    (inherited_source_fiber_forget (F := F) Z).map
      ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))
  let θ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
      ((inherited_source_fiber_forget (F := F) yi).map φ))
  let φX :
      ((((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
          (inherited_source_fiber_obj (F := F) y)).1 ⟶
        (inherited_source_fiber_obj (F := F) y).1) :=
    (canonicalPullbackChoice Xₛ.p).map (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
  have hφX : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) φX := by
    -- The chosen source pullback in `Xₛ` is strongly cartesian by construction.
    exact
      (canonicalPullbackChoice Xₛ.p).isStronglyCartesian
        (Yₛ.p.map f) (inherited_source_fiber_obj (F := F) y)
  letI : Xₛ.p.IsStronglyCartesian (Yₛ.p.map f) φX := hφX
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) η.1 := by
    exact η.2
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) θ.1 := by
    exact θ.2
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) ex.hom.1 := by
    exact ex.hom.2
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) ey.hom.1 := by
    exact ey.hom.2
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) (η.1 ≫ ey.hom.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Xₛ.p _ _ _ _ _
      (𝟙 (Yₛ.p.obj Z)) η.1 η.2 (Yₛ.p.obj Z) ey.hom.1 ey.hom.2
  letI : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) (ex.hom.1 ≫ θ.1) := by
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ Xₛ.p _ _ _ _ _
      (𝟙 (Yₛ.p.obj Z)) ex.hom.1 ex.hom.2 (Yₛ.p.obj Z) θ.1 θ.2
  have hcomp :
      η.1 ≫ ey.hom.1 ≫ φX = (ex.hom.1 ≫ θ.1) ≫ φX := by
    -- Compare the two candidates only after postcomposing with the common chosen pullback arrow.
    simpa only [η, θ, φX, Category.assoc] using
      inherited_source_pullback_comparison_hom_postcompose_eq_owner
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f φ
  have hηey : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) (η.1 ≫ ey.hom.1) := by infer_instance
  have hexθ : Xₛ.p.IsHomLift (𝟙 (Yₛ.p.obj Z)) (ex.hom.1 ≫ θ.1) := by infer_instance
  apply Functor.Fiber.hom_ext
  exact
    @Functor.IsStronglyCartesian.ext _ _ _ _ Xₛ.p _ _ _ _
      (Yₛ.p.map f) φX inferInstance _ _ (𝟙 (Yₛ.p.obj Z))
      (η.1 ≫ ey.hom.1) (ex.hom.1 ≫ θ.1) hηey hexθ <| by
        rw [Category.assoc]
        exact hcomp

/-- Helper for Lemma 8.10.5: the inverse inherited source pullback comparison rewrites the left
boundary of a conjugated overlap square into the source-side form. -/
theorem inherited_source_pullback_comparison_inv_naturality_over_vertical
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {yi Z : Yₛ.S} (f : Z ⟶ yi) {x y : (G F).Fiber yi} (φ : x ⟶ y) :
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) yi).map φ)) ≫
      (inherited_source_pullback_comparison
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y).inv =
    (inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x).inv ≫
      ((inherited_source_fiber_forget (F := F) Z).map
        ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))) := by
  let ex :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f x
  let ey :=
    inherited_source_pullback_comparison
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f y
  let η :=
    (inherited_source_fiber_forget (F := F) Z).map
      ((((canonicalFiberPseudofunctor (G F)).map f.op.toLoc).toFunctor.map φ))
  let θ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.map
      ((inherited_source_fiber_forget (F := F) yi).map φ))
  have hhom : η ≫ ey.hom = ex.hom ≫ θ := by
    -- First use the direct-side naturality square, then move it across the two inverses.
    simpa only [ex, ey, η, θ] using
      inherited_source_pullback_comparison_naturality_over_vertical
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) f φ
  symm
  apply (Iso.eq_comp_inv ey).2
  have hpre :
      ex.inv ≫ (η ≫ ey.hom) =
        ex.inv ≫ (ex.hom ≫ θ) := by
    exact congrArg (fun k ↦ ex.inv ≫ k) hhom
  simpa only [← Category.assoc, ex.inv_hom_id, Category.id_comp] using hpre

end

end CategoryTheory

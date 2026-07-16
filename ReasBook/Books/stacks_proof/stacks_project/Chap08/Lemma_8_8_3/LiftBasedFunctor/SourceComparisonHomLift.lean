import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor.Objects

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- The chosen source-object comparison is vertical over the identity of the original source
base object. -/
theorem stackificationLiftBasedFunctorObj_sourceIso_isHomLift
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S.S) :
    X.p.IsHomLift (𝟙 (S.p.obj T))
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom := by
  let U : C := S'.p.obj (G.toHom.obj T)
  have hxbase : S.p.obj T = U := by
    dsimp only [U]
    symm
    simpa only [FibredCategoryMor.toFunctor] using
      congrArg (fun H : S.S ⥤ C => H.obj T) (FibredCategoryMor.comm G)
  let x : S.p.Fiber U := Functor.Fiber.mk (p := S.p) (a := T) hxbase
  let ySource : S'.p.Fiber U :=
    Functor.Fiber.mk (p := S'.p) (a := G.toHom.obj T) rfl
  let yImage : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  have hy : ySource = yImage := by
    apply Functor.Fiber.fiberInclusion_obj_inj
    rfl
  let sx := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let eTotal :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).mapIso sx
  have hSourceEq :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) =
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) := by
    dsimp only [stackificationLiftBasedFunctorObj, ySource]
    exact congrArg
      (fun y : S'.p.Fiber U =>
        (stackificationLiftObjectGlued X G hG F y).1)
      hy
  let eSource :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) :=
    eqToIso hSourceEq
  have hTargetEq :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x) =
        F.toHom.obj T :=
    rfl
  let eTarget :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
        F.toHom.obj T :=
    eqToIso hTargetEq
  have hshape :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom =
        (eSource ≪≫ eTotal ≪≫ eTarget).hom := by
    rfl
  have hshape_reduced :
      (stackificationLiftBasedFunctorObj_sourceIso X G hG F T).hom = sx.hom.1 := by
    rw [hshape]
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    cases hSourceEq
    cases hTargetEq
    dsimp only [eSource, eTarget]
    change (𝟙 _ : _ ⟶ _) ≫ eTotal.hom ≫ (𝟙 _ : _ ⟶ _) = sx.hom.1
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [hshape_reduced]
  rw [hxbase]
  exact sx.hom.2

end

end CategoryTheory

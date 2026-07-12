import StacksProject_2024.Chap08.Lemma_8_8_3.SourceImage

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the object part of the eventual descended based functor on
the total category of `S'`. -/
noncomputable def stackificationLiftBasedFunctorObj
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) : X.S :=
  (stackificationLiftObjectGlued X G hG F
    (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).1

/-- Helper for Chap08 Lemma 8 8 3: the object assignment of the eventual descended based functor
lies over the same base object. -/
theorem stackificationLiftBasedFunctorObj_base
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) :
    X.p.obj (stackificationLiftBasedFunctorObj X G hG F T) = S'.p.obj T :=
  (stackificationLiftObjectGlued X G hG F
    (Functor.Fiber.mk (p := S'.p) (a := T) rfl)).2

/-- Helper for Chap08 Lemma 8 8 3: on objects in the literal image of `G`, the eventual
descended object assignment is isomorphic to the original value of `F`. -/
theorem stackificationLiftBasedFunctorObj_sourceIso_nonempty
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S.S) :
    Nonempty
      (stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
        F.toHom.obj T) := by
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
  let eFiber := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let eTotal :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).mapIso eFiber
  let eSource :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) :=
    eqToIso (by
      dsimp only [stackificationLiftBasedFunctorObj, ySource]
      exact congrArg
        (fun y : S'.p.Fiber U =>
          (stackificationLiftObjectGlued X G hG F y).1)
        hy)
  let eTarget :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
        F.toHom.obj T :=
    eqToIso rfl
  exact ⟨eSource ≪≫ eTotal ≪≫ eTarget⟩

/-- Helper for Chap08 Lemma 8 8 3: chosen source-object comparison used for the final
precomposition isomorphism. -/
noncomputable def stackificationLiftBasedFunctorObj_sourceIso
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S.S) :
    stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
      F.toHom.obj T :=
  let U : C := S'.p.obj (G.toHom.obj T)
  let hxbase : S.p.obj T = U := by
    dsimp only [U]
    symm
    simpa only [FibredCategoryMor.toFunctor] using
      congrArg (fun H : S.S ⥤ C => H.obj T) (FibredCategoryMor.comm G)
  let x : S.p.Fiber U := Functor.Fiber.mk (p := S.p) (a := T) hxbase
  let ySource : S'.p.Fiber U :=
    Functor.Fiber.mk (p := S'.p) (a := G.toHom.obj T) rfl
  let yImage : S'.p.Fiber U := (FibredCategoryMor.fiberFunctor G U).obj x
  let hy : ySource = yImage := by
    apply Functor.Fiber.fiberInclusion_obj_inj
    rfl
  let eFiber := stackificationLiftObjectSourceImageGluedIso X G hG F x
  let eTotal :=
    (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).mapIso eFiber
  let eSource :
      stackificationLiftBasedFunctorObj X G hG F (G.toHom.obj T) ≅
        (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          (stackificationLiftObjectGlued X G hG F yImage) :=
    eqToIso (by
      dsimp only [stackificationLiftBasedFunctorObj, ySource]
      exact congrArg
        (fun y : S'.p.Fiber U =>
          (stackificationLiftObjectGlued X G hG F y).1)
        hy)
  let eTarget :
      (Functor.Fiber.fiberInclusion : X.p.Fiber U ⥤ X.S).obj
          ((FibredCategoryMor.fiberFunctor F U).obj x) ≅
        F.toHom.obj T :=
    eqToIso rfl
  eSource ≪≫ eTotal ≪≫ eTarget

end

end CategoryTheory

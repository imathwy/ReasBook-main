import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality.IdentityLocal

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: identity functoriality reduces to the core identity
factorization. -/
theorem stackificationLiftBasedFunctorMap_id_of_core_fac
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S)
    (hcore :
      (stackificationLiftBasedFunctorMapCore X G hG F (𝟙 T)).1 ≫
        (canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T))
          (stackificationLiftObjectGlued X G hG F
            (Functor.Fiber.mk (p := S'.p) (a := T) rfl)) =
        𝟙 (stackificationLiftBasedFunctorObj X G hG F T)) :
    stackificationLiftBasedFunctorMap X G hG F (𝟙 T) =
      𝟙 (stackificationLiftBasedFunctorObj X G hG F T) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
  rw [stackificationLiftBasedFunctorMap_eq_core_comp_cart]
  simpa [y, z] using hcore

/-- Small identity blocker for Chap08 Lemma 8 8 3: for an identity arrow, the core part of the
descended arrow formula followed by the chosen identity pullback arrow is the identity. -/
theorem stackificationLiftBasedFunctorMapCore_id_fac
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) :
    (stackificationLiftBasedFunctorMapCore X G hG F (𝟙 T)).1 ≫
      (canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T))
        (stackificationLiftObjectGlued X G hG F
          (Functor.Fiber.mk (p := S'.p) (a := T) rfl)) =
      𝟙 (stackificationLiftBasedFunctorObj X G hG F T) := by
  let y : S'.p.Fiber (S'.p.obj T) :=
    Functor.Fiber.mk (p := S'.p) (a := T) rfl
  let z : X.p.Fiber (S'.p.obj T) := stackificationLiftObjectGlued X G hG F y
  let cart :
      (S'.p.map (𝟙 T)) ^*[canonicalPullbackChoice X.p] z ⟶ z :=
    ⟨(canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z, by
      have hcart :
          X.p.IsHomLift (S'.p.map (𝟙 T))
            ((canonicalPullbackChoice X.p).map (S'.p.map (𝟙 T)) z) :=
        ((canonicalPullbackChoice X.p).isStronglyCartesian (S'.p.map (𝟙 T)) z).toIsHomLift
      simpa using hcart⟩
  have hFiber :
      stackificationLiftBasedFunctorMapCore X G hG F (𝟙 T) ≫ cart = 𝟙 z := by
    simpa [y, z, cart] using
      stackificationLiftBasedFunctorMapCore_id_fiber_fac X G hG F T
  simpa [cart, y, z] using congrArg (fun f => f.1) hFiber

/-- Helper for Chap08 Lemma 8 8 3: the descended arrow formula sends identity arrows to
identity arrows. -/
theorem stackificationLiftBasedFunctorMap_id
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    (T : S'.S) :
    stackificationLiftBasedFunctorMap X G hG F (𝟙 T) =
      𝟙 (stackificationLiftBasedFunctorObj X G hG F T) := by
  exact stackificationLiftBasedFunctorMap_id_of_core_fac X G hG F T
    (stackificationLiftBasedFunctorMapCore_id_fac X G hG F T)

end

end CategoryTheory

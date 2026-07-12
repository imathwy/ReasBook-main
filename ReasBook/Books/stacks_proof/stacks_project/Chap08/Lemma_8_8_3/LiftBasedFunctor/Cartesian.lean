import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Functoriality
import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.CartesianCore

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the descended based functor preserves strongly cartesian
morphisms. -/
theorem stackificationLiftBasedFunctor_preservesStronglyCartesian
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    BasedFunctor.PreservesStronglyCartesian
      (stackificationLiftBasedFunctor X G hG F) := by
  intro T T' φ hφ
  let L := stackificationLiftBasedFunctor X G hG F
  let m := L.map φ
  change X.p.IsStronglyCartesian (X.p.map m) m
  have hm : m = stackificationLiftBasedFunctorMap X G hG F φ := by
    rfl
  have hcart : X.p.IsStronglyCartesian (S'.p.map φ) m := by
    rw [hm]
    exact stackificationLiftBasedFunctorMap_isStronglyCartesian X G hG F φ hφ
  letI : X.p.IsStronglyCartesian (S'.p.map φ) m := hcart
  exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
    (p := X.p) (R := S'.p.obj T) (S := S'.p.obj T')
    (a := L.obj T) (b := L.obj T') (hb := L.w_obj T')
    (f := S'.p.map φ) (φ := m)

end

end CategoryTheory

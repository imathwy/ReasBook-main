import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Objects

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: the fiber object obtained by pulling back the codomain of a
total arrow in `S'` along its base map. -/
noncomputable def stackificationLiftArrowPullbackTarget
    (φ : T ⟶ T') :
    S'.p.Fiber (S'.p.obj T) :=
  S'.p.map φ ^*[canonicalPullbackChoice S'.p]
    (Functor.Fiber.mk (p := S'.p) (a := T') rfl)

/-- Helper for Chap08 Lemma 8 8 3: the vertical factor of a total arrow in `S'` through the
chosen cartesian pullback of its codomain. -/
noncomputable def stackificationLiftArrowVerticalFactor
    (φ : T ⟶ T') :
    (Functor.Fiber.mk (p := S'.p) (a := T) rfl : S'.p.Fiber (S'.p.obj T)) ⟶
      stackificationLiftArrowPullbackTarget (S' := S') φ :=
  Classical.choose (canonicalPullback_verticalFactor_exists S'.p φ)

/-- Helper for Chap08 Lemma 8 8 3: the vertical factor followed by the chosen cartesian arrow is
the original total arrow. -/
theorem stackificationLiftArrowVerticalFactor_fac
    {T T' : S'.S} (φ : T ⟶ T') :
    (stackificationLiftArrowVerticalFactor (S' := S') φ).1 ≫
      (canonicalPullbackChoice S'.p).map (S'.p.map φ)
        (Functor.Fiber.mk (p := S'.p) (a := T') rfl : S'.p.Fiber (S'.p.obj T')) =
    φ :=
  Classical.choose_spec (canonicalPullback_verticalFactor_exists S'.p φ)

end

end CategoryTheory

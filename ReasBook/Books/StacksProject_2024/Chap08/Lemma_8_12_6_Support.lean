import Mathlib
import stacks_project.Chap04.Lemma_4_27_14
import stacks_project.Chap08.Lemma_8_12_5

open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

namespace Functor

variable (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Lemma 8.12.6: with notation and assumptions as in Lemma `8.12.5`, the localized category
`u ₚ p` is a fibred category over `D` via its canonical projection
`u.pushforwardProjection p`. -/
theorem pushforwardProjection_isFibered_aux :
    (u.pushforwardProjection p).IsFibered := by
  sorry

end Functor

end

end CategoryTheory

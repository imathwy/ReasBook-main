import Mathlib
import StacksProject_2024.stacks_project.Chap34.Lemma_34_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' T T' : Scheme.{u}}
variable (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)

-- Semantic recall: `lean_leansearch` surfaced the generic owner
-- `Functor.sheafPushforwardContinuousComp'`; local Chapter 34 precedent fixes the Zariski
-- surfaces as `smallZariskiToBigZariskiMorphismOfTopoi`, `smallZariskiMorphismOfTopoi`, and
-- `bigZariskiMorphismOfTopoi`.

/-- Lemma 34.3.19 (1): for a cartesian square of schemes, pulling the big Zariski direct image
`f_{big,*}` back along the relocalization morphism `i_g` agrees with first pulling back along
`i_{g'}` and then applying the small Zariski direct image `f'_{small,*}`. -/
@[stacks 0DD9]
theorem smallZariskiToBigZariskiInverseImage_comp_bigZariskiPushforward
    (sq : IsPullback g' f' f g) :
    (bigZariskiMorphismOfTopoi f) _* ⋙
        (smallZariskiToBigZariskiMorphismOfTopoi g)⁻¹ =
      (smallZariskiToBigZariskiMorphismOfTopoi g')⁻¹ ⋙
        (smallZariskiMorphismOfTopoi f') _* := sorry

/-- Lemma 34.3.19 (2): for a cartesian square of schemes, pulling the big Zariski direct image
`f_{big,*}` back along `g_{big}` agrees with first pulling back along `g'_{big}` and then applying
the big Zariski direct image `f'_{big,*}`. -/
@[stacks 0DD9]
theorem bigZariskiInverseImage_comp_bigZariskiPushforward
    (sq : IsPullback g' f' f g) :
    (bigZariskiMorphismOfTopoi f) _* ⋙ (bigZariskiMorphismOfTopoi g)⁻¹ =
      (bigZariskiMorphismOfTopoi g')⁻¹ ⋙ (bigZariskiMorphismOfTopoi f') _* := sorry

end AlgebraicGeometry.Scheme

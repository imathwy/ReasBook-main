import StacksProject_2024.Chap34.Lemma_34_4_17

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' T T' : Scheme.{u}}
variable (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)

-- Semantic recall: `lean_leansearch` surfaced the generic site-square base-change owner
-- `site_square_direct_image_inverse_image_iso`; local Chapter 34 precedent fixes the source
-- surfaces as `smallEtaleToBigEtaleMorphismOfTopoi`, `smallEtaleMorphismOfTopoi`, and
-- `bigEtaleMorphismOfTopoi`.

/-- Lemma 34.4.19 (1): for a cartesian square of schemes, pulling the big étale direct image
`f_{big,*}` back along the relocalization morphism `i_g` agrees with first pulling back along
`i_{g'}` and then applying the small étale direct image `f'_{small,*}`. -/
@[stacks 0DDA]
theorem smallEtaleToBigEtaleInverseImage_comp_bigEtalePushforward
    (sq : IsPullback g' f' f g) :
    (bigEtaleMorphismOfTopoi f) _* ⋙
        (smallEtaleToBigEtaleMorphismOfTopoi g)⁻¹ =
      (smallEtaleToBigEtaleMorphismOfTopoi g')⁻¹ ⋙
        (smallEtaleMorphismOfTopoi f') _* := sorry

/-- Lemma 34.4.19 (2): for a cartesian square of schemes, pulling the big étale direct image
`f_{big,*}` back along `g_{big}` agrees with first pulling back along `g'_{big}` and then applying
the big étale direct image `f'_{big,*}`. -/
@[stacks 0DDA]
theorem bigEtaleInverseImage_comp_bigEtalePushforward
    (sq : IsPullback g' f' f g) :
    (bigEtaleMorphismOfTopoi f) _* ⋙ (bigEtaleMorphismOfTopoi g)⁻¹ =
      (bigEtaleMorphismOfTopoi g')⁻¹ ⋙ (bigEtaleMorphismOfTopoi f') _* := sorry

end AlgebraicGeometry.Scheme

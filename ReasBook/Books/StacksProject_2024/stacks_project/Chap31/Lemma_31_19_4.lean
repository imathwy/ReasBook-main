import Mathlib
import StacksProject_2024.stacks_project.Chap31.Lemma_31_19_3

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned only the ambient associated-graded and flatness
-- owners, while local Chapter 31 inspection verified that Lemma 31.19.3 already fixes the
-- source-faithful affine-local comparison map as `immersionAffineConormalAlgebraMap`. The present
-- item is therefore formalized as the cartesian-square surjectivity and flat-isomorphism
-- properties of that existing map on affine charts.

/-- Lemma 31.19.4 (1): in a fibre product square
`Z ⟶ Z'`, `X ⟶ X'` with immersion maps `i : Z ⟶ X` and `i' : Z' ⟶ X'`, the affine-local
comparison map from Lemma 31.19.3 is surjective on every affine pair `U ⊆ X`, `U' ⊆ X'` with
`g(U) ⊆ U'`. This is the affine chart form of the surjectivity of the canonical morphism
`f^* \mathcal{C}_{Z'/X', *} → \mathcal{C}_{Z/X, *}`. -/
@[stacks 0635]
theorem immersionAffineConormalAlgebraMap_surjective
    {Z X Z' X' : Scheme.{u}}
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    (hpb : IsPullback f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    Function.Surjective
      ((immersionAffineConormalAlgebraMap hpb.toCommSq U U' e) :
        immersionAffineConormalAlgebra i' (U' : X'.Opens) →+*
          immersionAffineConormalAlgebra i (U : X.Opens)) := sorry

/-- Lemma 31.19.4 (2): in the same fibre product situation, if `g` is flat then the affine-local
comparison map from Lemma 31.19.3 is an isomorphism on every affine pair `U ⊆ X`, `U' ⊆ X'`
with `g(U) ⊆ U'`. This is the affine chart form of the source statement that
`f^* \mathcal{C}_{Z'/X', *} → \mathcal{C}_{Z/X, *}` is an isomorphism under flat base change;
here this is recorded as bijectivity of the induced ring hom on affine charts. -/
@[stacks 0635]
theorem immersionAffineConormalAlgebraMap_bijective_of_flat
    {Z X Z' X' : Scheme.{u}}
    (f : Z ⟶ Z') (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i']
    [Flat g]
    (hpb : IsPullback f i i' g)
    (U : X.affineOpens) (U' : X'.affineOpens)
    (e : (U : X.Opens) ≤ g ⁻¹ᵁ (U' : X'.Opens)) :
    Function.Bijective
      ((immersionAffineConormalAlgebraMap hpb.toCommSq U U' e) :
        immersionAffineConormalAlgebra i' (U' : X'.Opens) →+*
          immersionAffineConormalAlgebra i (U : X.Opens)) := sorry

end AlgebraicGeometry

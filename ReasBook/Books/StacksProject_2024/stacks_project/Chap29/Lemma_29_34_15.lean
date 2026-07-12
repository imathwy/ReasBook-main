import Mathlib
import StacksProject_2024.Chap29.Lemma_29_36_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsSmooth` and
-- `isSmooth_isStableUnderBaseChange`; local Chapter 29 precedent supplies the pointwise owner
-- `Scheme.Hom.SmoothAt`, which is the surface used for the smooth loci below.

/-- Lemma 29.34.15 (1): in a cartesian diagram of schemes, if `f` is flat and locally of finite
presentation, and `W` and `W'` are the open subschemes of points where `f` and `f'` are smooth,
then `W'` is the inverse image of `W` under `g'`. -/
@[stacks 02V4]
theorem smoothAt_open_eq_preimage_of_isPullback_of_flat_of_locallyOfFinitePresentation
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
    (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.SmoothAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}) :
    W' = g' ⁻¹ᵁ W := sorry

/-- Lemma 29.34.15 (2): in a cartesian diagram of schemes, if `f` is locally of finite
presentation and the base-change morphism `g` is flat, and `W` and `W'` are the open subschemes of
points where `f` and `f'` are smooth, then `W'` is the inverse image of `W` under `g'`. -/
@[stacks 02V4]
theorem smoothAt_open_eq_preimage_of_isPullback_of_locallyOfFinitePresentation_of_flat_base
    {X' X S' S : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g]
    (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.SmoothAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.SmoothAt x'}) :
    W' = g' ⁻¹ᵁ W := sorry

end AlgebraicGeometry

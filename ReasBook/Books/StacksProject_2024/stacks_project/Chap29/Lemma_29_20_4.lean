import StacksProject_2024.Chap29.Lemma_29_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

section

variable {X S S' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the canonical fiber owner
-- `AlgebraicGeometry.Scheme.Hom.fiber`, and local Chapter 29 precedent records the base-changed
-- morphism of `f : X ⟶ S` along `g : S' ⟶ S` as `pullback.snd f g`.

/-- Lemma 29.20.4: let `f : X ⟶ S` be locally of finite type and let `g : S' ⟶ S` be any
morphism. For a point `x'` of the base change `X' = X ×[S] S'`, if the image point
`pullback.fst f g x'` is closed in the fiber of `f` over `f (pullback.fst f g x')`, then `x'` is
closed in the fiber of the base-changed morphism `pullback.snd f g`. -/
@[stacks 053M]
theorem asFiber_mem_closedPoints_of_pullback_snd
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme))
    (hx :
      f.asFiber (pullback.fst f g x') ∈
        closedPoints (f.fiber (f (pullback.fst f g x')))) :
    (pullback.snd f g).asFiber x' ∈
      closedPoints ((pullback.snd f g).fiber ((pullback.snd f g) x')) := sorry

end

end AlgebraicGeometry

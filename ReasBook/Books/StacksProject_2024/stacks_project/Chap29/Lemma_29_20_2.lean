import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.Topology.JacobsonSpace
import StacksProject_2024.stacks_project.Chap29.Definition_29_10_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

noncomputable section

-- Semantic recall: `Scheme.Hom.asFiber`, `Scheme.Hom.fiberι`, and the fiber scheme owner
-- `Scheme.Hom.fiber` are the canonical fiber API. The residue-field extension in the source is
-- expressed through the algebra structure induced by `f.residueFieldMap x`, and the second clause
-- is the standard locally-of-finite-type closed-point image theorem.

section

variable {X S : Scheme.{u}}

/-- Lemma 29.20.2 (1): if `f : X ⟶ S` is a morphism of schemes and the residue field extension
`κ(x) / κ(f(x))` is algebraic, then the canonical point of the scheme-theoretic fiber of `f`
through `x` is a closed point of that fiber. -/
@[stacks 01TE "(1)"]
theorem asFiber_mem_closedPoints_of_isAlgebraic_residueField
    (f : X ⟶ S) (x : X)
    (halg : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x)) :
    f.asFiber x ∈ closedPoints (f.fiber (f x)) := sorry

/-- Lemma 29.20.2 (2): if `f : X ⟶ S` is a morphism of schemes, the residue field extension
`κ(x) / κ(f(x))` is algebraic, and `f(x)` is a closed point of `S`, then `x` is a closed point
of `X`. -/
@[stacks 01TE "(2)"]
theorem mem_closedPoints_of_isAlgebraic_residueField_of_image_mem_closedPoints
    (f : X ⟶ S) (x : X)
    (halg : Algebra.IsAlgebraic (S.residueField (f x)) (X.residueField x))
    (hs : f x ∈ closedPoints S) :
    x ∈ closedPoints X := sorry

end

end

end AlgebraicGeometry

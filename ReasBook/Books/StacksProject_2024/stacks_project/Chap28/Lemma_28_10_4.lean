import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the generic-point owners
-- `genericPoints.ofComponent` / `genericPoints.isGenericPoint_ofComponent`; local Chapter 31
-- precedent confirms that the source-faithful pointwise packaging is
-- `∃ Z : irreducibleComponents X, IsGenericPoint x (Z : Set X)`.

variable (X : Scheme.{u})

/-- Lemma 28.10.4: a point `x` of a scheme `X` is a generic point of an irreducible component of
`X` if and only if the local ring `X.presheaf.stalk x` has Krull dimension `0`. -/
theorem exists_irreducibleComponent_genericPoint_iff_ringKrullDim_stalk_eq_zero (x : X) :
    (∃ Z : irreducibleComponents X, IsGenericPoint x (Z : Set X)) ↔
      ringKrullDim (X.presheaf.stalk x) = 0 := sorry

end AlgebraicGeometry.Scheme

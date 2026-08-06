import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Theorem_21_4_4

-- Theorem 21.4.4 already exposes the source-facing relative-duality owner
-- `IsBoundaryRelativePoincareDualityMap` and its two atomic degreewise isomorphism clauses, so
-- this corollary should reuse those Chapter 21 declarations directly rather than introduce a
-- duplicate wrapper layer.

/- Corollary 21.4.5. Relative duality includes duality between `H^p(M)` and `H_(n - p)(M, ∂M)`,
and between `H^p(M, ∂M)` and `H_(n - p)(M)`.

This is the degreewise unpacking of Theorem 21.4.4, with the two source-facing clauses:

1. `Corollary 21.4.5 (1)`: the degree-`p` duality isomorphism between `H^p(M)` and
   `H_(n - p)(M, ∂M)`.
2. `Corollary 21.4.5 (2)`: the degree-`p` duality isomorphism between `H^p(M, ∂M)` and
   `H_(n - p)(M)`.

Theorem 21.4.4 now supplies the exact Chapter 21 surface this corollary needs: the source-facing
relative-duality predicate `IsBoundaryRelativePoincareDualityMap` together with the two degreewise
isomorphism clauses
`IsBoundaryRelativePoincareDualityMap.absoluteToRelative_isIso` and
`IsBoundaryRelativePoincareDualityMap.relativeToAbsolute_isIso`. Since those clauses already
have the corollary's interface, the canonical reuse here is to recall those declarations directly
rather than restating them as exact-interface wrappers. The relevant surfaces are recalled below.
-/
#check IsBoundaryRelativePoincareDualityMap
#check IsBoundaryRelativePoincareDualityMap.absoluteToRelative_isIso
#check IsBoundaryRelativePoincareDualityMap.relativeToAbsolute_isIso

import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Lemma_21_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Theorem_21_4_4

-- The current repository already exposes the concrete boundary restriction map
-- `singularCohomologyPullback K (manifoldBoundaryInclusion (4 * k + 1) W) (2 * k)` and the
-- Chapter 21 relative-duality owner `BoundaryRelativeCapProduct` with its induced maps
-- `boundaryRelativeAbsoluteToRelativeMap` and `boundaryRelativeRelativeToAbsoluteMap`.
-- The remaining blocker is the absence of a canonical field-linear owner for the
-- middle-dimensional boundary cup-product form and for the finite-dimensional `K`-cohomology
-- surface on which "isotropic" and "half-dimensional" should be stated.

/- Lemma 21.5.3. If `M = ∂W` for a compact `K`-oriented manifold-with-boundary `W` of dimension
`4 * k + 1`, then the image of the restriction map
`H^(2 * k)(W; K) ⟶ H^(2 * k)(M; K)` is isotropic for the middle-dimensional cup-product form on
`H^(2 * k)(M; K)` and has half the ambient dimension.

Formalization remains blocked at the statement stage. The concrete boundary restriction map, its
image, and the middle-dimensional cup-product form on `H^(2 * k)(∂W; K)` do not yet have a
usable common public owner in the current repository: `singularCohomologyPullback` gives the
underlying restriction map on quotient-model cohomology classes, but the project still lacks the
field-linear finite-dimensional cohomology surface and canonical boundary cup-product form needed
to state "isotropic" and "half-dimensional" source-faithfully. The relative-duality input is no
longer blocked in Theorem 21.4.4: Chapter 21 already provides the source-facing cap-product owner
`BoundaryRelativeCapProduct`, the induced maps
`boundaryRelativeAbsoluteToRelativeMap` and `boundaryRelativeRelativeToAbsoluteMap`, the
predicate `IsBoundaryRelativePoincareDualityMap`, and the theorem
`relativePoincareDuality` together with its two degreewise isomorphism clauses. Until the
remaining boundary-form owners exist, replacing this item by actual theorem declarations would
still force noncanonical cohomology-form data and hence semantic drift. The relevant currently
available surfaces are recalled below. -/

#check singularCohomologyPullback
#check manifoldBoundaryInclusion
#check cupProductTopHomologyClassPairing
#check boundaryRelativeSingularHomology
#check BoundaryRelativeCapProduct
#check boundaryRelativeAbsoluteToRelativeMap
#check boundaryRelativeRelativeToAbsoluteMap
#check IsBoundaryRelativePoincareDualityMap
#check relativePoincareDuality
#check IsBoundaryRelativePoincareDualityMap.absoluteToRelative_isIso
#check IsBoundaryRelativePoincareDualityMap.relativeToAbsolute_isIso
#check sigPos_eq_sigNeg_of_exists_isotropic_finrank_eq_half

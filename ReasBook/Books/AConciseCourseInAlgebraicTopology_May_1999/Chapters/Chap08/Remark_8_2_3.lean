import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2

open scoped unitInterval

universe u w

-- Semantic recall: Definitions 8.2.1 and 8.2.2 already own the reduced cone and reduced
-- suspension. This remark records the collapse-locus API that distinguishes those reduced models
-- from their unreduced counterparts.

/- Remark 8.2.3: the reduced cone and reduced suspension collapse the entire line
`{X.point} × I` through the basepoint, unlike the unreduced cone and suspension. The text uses
the same notation for reduced and unreduced versions, so this file records the reduced convention
already fixed by Definitions 8.2.1 and 8.2.2. -/
recall reducedConeCollapsedSet (X : PointedCompactlyGenerated.{u, w}) :
    Set (X.toCompactlyGenerated × I)

recall reducedSuspensionCollapsedSet (X : PointedCompactlyGenerated.{u, w}) :
    Set (X.toCompactlyGenerated × I)

/- In the reduced cone, the whole segment `{X.point} × I` is identified with the basepoint. -/
recall reducedCone_mk_eq_point_of_fst_eq_point
    (X : PointedCompactlyGenerated.{u, w}) (t : I) :
    reducedConeMk X (X.point, t) = (C X).point

/- In the reduced suspension, the same basepoint segment `{X.point} × I` is identified with the
suspension basepoint. -/
recall reducedSuspensionMk_eq_point_of_fst_eq_point
    (X : PointedCompactlyGenerated.{u, w}) (t : I) :
    reducedSuspensionMk X (X.point, t) = reducedSuspensionPoint X

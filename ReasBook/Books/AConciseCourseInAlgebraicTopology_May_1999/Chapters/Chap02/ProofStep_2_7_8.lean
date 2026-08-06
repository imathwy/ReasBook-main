module

import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.FundamentalGroupoidOpenCover

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Limits
open scoped FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]
variable {ι : Type v}

variable
    (O : ι → TopologicalSpace.Opens X)
    (hPi : IsColimit (fundamental_groupoid_cover_cocone O))
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (x : X)

/- ProofStep 2.7.8: the universal colimit-desc functor `hPi.desc S` induces the canonical
`Functor.mapEnd` homomorphism on the vertex group at `x`,
`π₁(X, x) →* End ((hPi.desc S).obj (FundamentalGroupoid.mk x))`. -/
#check ((hPi.desc S).mapEnd (FundamentalGroupoid.mk x) :
    FundamentalGroup X x →* End ((hPi.desc S).obj (FundamentalGroupoid.mk x)))

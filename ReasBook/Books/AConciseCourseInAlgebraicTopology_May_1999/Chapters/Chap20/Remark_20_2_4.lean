import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_2_3

-- Local Chapter 20 precedent already exposes the source-facing cap-product owner
-- `singularCapProduct`, the cup/cap comparison theorem
-- `singularCapProduct_cup_compatibility`, and the specialized duality map
-- `capWithFundamentalClass`. This remark is therefore recorded as a recall block around those
-- existing owners rather than as a separate adjoint-pairing definition.

/- Remark 20.2.4: the point of the source remark is methodological rather than theorem-level.
For proving duality with supports, the chapter works with the explicit cap-product pairing
`singularCapProduct` of Definition 20.2.1. Proposition 20.2.3 supplies the compatibility with
cup products that would underlie an adjoint cup-product formulation, and Construction 20.2.2
specializes the same cap-product owner to `capWithFundamentalClass`. Accordingly, the chapter
keeps the cap-product pairing as the primary public owner rather than introducing a separate
adjoint-pairing wrapper. -/
#check singularCapProduct
#check singularCapProduct_cup_compatibility
#check capWithFundamentalClass

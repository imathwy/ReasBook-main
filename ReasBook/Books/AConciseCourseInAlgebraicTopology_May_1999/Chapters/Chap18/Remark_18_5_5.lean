import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap18.Theorem_18_5_4

-- Semantic recall via `lean_leansearch`: no exact canonical obstruction-theory summary theorem
-- surfaced. Local Chapter 18 precedent already packages the extension problem and the uniqueness
-- problem through `relativeSkeletonExtensionObstructionCriterion` and
-- `relativeSkeletonHomotopyExtensionObstructionCriterion`, both with coefficients in relative
-- cellular cohomology groups built from `Additive (π_ n Y y₀)`.

/- Remark 18.5.5. In this chapter, obstruction theory turns the extension problem for maps and
the uniqueness problem for extensions into vanishing criteria for cohomology classes with
homotopy-group coefficients. The source remark is therefore formalized as a labeled recall block
pointing to the two preceding obstruction criteria. -/
#check relativeSkeletonExtensionObstructionCriterion
#check relativeSkeletonHomotopyExtensionObstructionCriterion

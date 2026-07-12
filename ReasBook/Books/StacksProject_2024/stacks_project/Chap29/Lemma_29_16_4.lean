import Mathlib
import StacksProject_2024.Chap29.Definition_29_16_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced `closedPoints` and `Scheme.affineOpens`; local
-- Chapter 29 precedent in `Definition_29_16_3` fixes the source-facing owner here as
-- `finiteTypePoints S`.

/-- Lemma 29.16.4 (1): the finite type points of a scheme are exactly the union of the closed
points of its open subschemes, viewed in the ambient scheme. -/
@[stacks 02J2]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_open (S : Scheme.{u}) :
    finiteTypePoints S = ⋃ U : S.Opens, (((↑) : U → S) '' closedPoints U : Set S) := sorry

/-- Lemma 29.16.4 (2): the same description of finite type points holds if the union is taken only
over the affine open subschemes of the scheme. -/
@[stacks 02J2]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_affineOpen (S : Scheme.{u}) :
    finiteTypePoints S =
      ⋃ U : S.affineOpens,
        ((fun x : U.1 ↦ x.1) '' closedPoints U.1 : Set S) := sorry

end AlgebraicGeometry

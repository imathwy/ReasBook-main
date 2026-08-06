import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Problem_1_8_3

open scoped FundamentalGroup

noncomputable section

universe u

-- Semantic recall: mathlib exposes `HSpace.hmul` and `FundamentalGroup`; the verified repo lemma
-- `loop_hmul_class_eq_trans` is the canonical comparison on based loop classes used here.

section HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

/-- Helper for `Problem 18.6.3`: the product on `π₁(X, HSpace.e)` induced by the ambient
`HSpace` multiplication. -/
def hSpaceFundamentalGroupProduct (a b : FundamentalGroup X HSpace.e) :
    FundamentalGroup X HSpace.e :=
  FundamentalGroup.fromPath
    (loop_hmul_class (FundamentalGroup.toPath a) (FundamentalGroup.toPath b))

/-- Problem 18.6.3 (1): for an `HSpace`, the product on `π₁(X, HSpace.e)` induced by
`HSpace.hmul` agrees with the usual fundamental group multiplication, with the argument order
reversed to match Lean's categorical convention for `FundamentalGroup`. -/
theorem hSpaceFundamentalGroupProduct_eq_mul
    (a b : FundamentalGroup X HSpace.e) :
    hSpaceFundamentalGroupProduct a b = b * a := by
  simpa [hSpaceFundamentalGroupProduct] using
    (FundamentalGroup.fromPath_loop_hmul_class
      (FundamentalGroup.toPath a) (FundamentalGroup.toPath b))

/-- Downstream corollary: the fundamental group at the unit of an `HSpace` is commutative. -/
theorem hSpaceFundamentalGroup_mul_comm
    (a b : FundamentalGroup X HSpace.e) :
    a * b = b * a := by
  simpa using fundamentalGroup_mul_comm a b

end HSpace

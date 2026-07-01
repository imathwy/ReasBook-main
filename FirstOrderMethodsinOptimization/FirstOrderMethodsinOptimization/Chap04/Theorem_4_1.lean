import FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsinOptimization.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 4.1 is `source-facing` in the chapter conjugacy API. Its primitive notions are the
owner declarations `is_convex_function` from Definition 2.6 and `conjugate_function` from
Definition 4.1; the canonical `bridge/view` owner is `conjugate_function_primal`, which
specializes the dual-space conjugate to the primal inner-product space through `toDualMap`
without reintroducing a local lambda wrapper. -/
recall conjugate_function_primal

-- Proof sketch: for each fixed `x : E`, the map
-- `f∗` contributes the affine function
-- `y ↦ ⟪y, x⟫ - f x` in the defining supremum of `f*`. Each such affine function is continuous,
-- hence lower semicontinuous, and convex in the chapter-owner sense. Then closedness follows from
-- lower semicontinuity of pointwise suprema, and convexity follows from the chapter closure result
-- `is_convex_function_iSup` after rewriting the conjugate by its defining supremum.
/-- Theorem 4.1: the conjugate function of an extended-real-valued function on a real inner
product space, viewed on the primal space as `f∗`, is closed, i.e. lower semicontinuous, and
convex in the chapter-owner sense. -/
theorem conjugate_function_closed_and_convex (f : E → EReal) :
    LowerSemicontinuous (f∗) ∧ is_convex_function (f∗) :=
  sorry

end

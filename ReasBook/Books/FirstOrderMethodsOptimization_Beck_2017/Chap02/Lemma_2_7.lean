import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- Proof sketch: one inequality is immediate from `A ⊆ closure A`. For the reverse inequality,
-- evaluate the chapter owner `support_function` only along the canonical continuous-dual map
-- `InnerProductSpace.toDualMap ℝ E`, whose values are continuous linear functionals, and use that
-- each such functional has the same supremum on `A` and on `closure A`.
/-- Lemma 2.7 (1): after specializing the chapter owner `support_function` along
`InnerProductSpace.toDualMap`, replacing a set by its topological closure does not change the
support function. -/
lemma support_function_eq_support_function_closure (A : Set E) :
    (fun x ↦ support_function A (InnerProductSpace.toDualMap ℝ E x)) =
      fun x ↦ support_function (closure A) (InnerProductSpace.toDualMap ℝ E x) := sorry

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

-- Proof sketch: one inequality is immediate from `A ⊆ convexHull ℝ A`. For the reverse
-- inequality, write a point of `convexHull ℝ A` as a convex combination of points of `A`, use the
-- linearity of the dual functional, and bound the resulting convex combination by the supremum
-- over `A`.
/-- Lemma 2.7 (2): the chapter owner `support_function` is unchanged when a set is replaced by its
convex hull. Any inner-product-space formula is obtained by specializing this owner-level equality
along `InnerProductSpace.toDualMap`. -/
lemma support_function_eq_support_function_convexHull (A : Set E) :
    support_function A = support_function (convexHull ℝ A) := sorry

end

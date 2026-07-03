import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: if `A = B`, then the specialized chapter owner support functions agree by
-- substitution. Conversely, if the support functions agree after precomposition with
-- `InnerProductSpace.toDualMap`, then completeness identifies every continuous linear functional
-- with an inner-product functional via `InnerProductSpace.toDual`. If one set is empty, the common
-- support function is constantly `⊥`, so both sets are empty. Otherwise, if `x ∈ A \ B`, apply
-- strict separation to the closed convex set `B` and the point `x`; transport the separating
-- functional across Fréchet-Riesz to get a vector representation, yielding a contradiction to
-- support-function equality. Symmetry gives the reverse inclusion.
/-- Lemma 2.6: two closed convex sets in a real inner product space are equal if and only if their
support functions agree after specializing the chapter owner support function along
`InnerProductSpace.toDualMap`; the canonical Fréchet-Riesz identification of the continuous dual
with the inner product space is used through the ambient completeness hypothesis. -/
theorem eq_iff_support_function_eq_of_closed_convex
    (A B : Set E) (hA_closed : IsClosed A) (hA_convex : Convex ℝ A)
    (hB_closed : IsClosed B) (hB_convex : Convex ℝ B) :
    A = B ↔
      (fun x ↦ support_function A (InnerProductSpace.toDualMap ℝ E x)) =
        fun x ↦ support_function B (InnerProductSpace.toDualMap ℝ E x) := sorry

end

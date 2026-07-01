import FirstOrderMethodsinOptimization.Chap03.Theorem_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Bornology
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (f : E → EReal) (X : Set E)

/- Theorem 3.5 is `source-facing` in the Chapter 3 convex-analysis API. Its owner declarations are
already the project primitives `effective_domain`, `is_convex_function`, and the continuous-dual
bridge `strongDualSubdifferential`; this file keeps the textbook compact-union boundedness
statement directly on that owner API instead of introducing any parallel wrapper. The ambient
properness of `f` is derived here from the source-relevant hypotheses `∀ y, f y ≠ ⊥`,
`X.Nonempty`, and `X ⊆ interior (effective_domain f)`, so it does not remain a primitive public
binder. -/
recall effective_domain
recall is_convex_function
recall strongDualSubdifferential

local notation "Y" => ⋃ x ∈ X, strongDualSubdifferential f x

-- Proof sketch: nonemptiness follows by choosing `x ∈ X` and applying the interior-point
-- existence theorem to the continuous-dual bridge `strongDualSubdifferential`. For boundedness,
-- argue by contradiction: choose `x_k ∈ X` and `g_k ∈ ∂f(x_k)` with unbounded dual norm, use
-- compactness of `X` and a positive distance from `X` to the complement of
-- `interior (effective_domain f)`, and combine the subgradient inequality with continuity of `f`
-- on the interior of its effective domain to obtain a uniform contradiction.
/-- Theorem 3.5: if `f` is a convex extended-real-valued function that never takes the value
`⊥`, and `X` is a nonempty compact subset of `interior (dom(f))`, then the union of the
continuous-dual subdifferentials `Y = ⋃ x ∈ X, strongDualSubdifferential f x` is nonempty and
bounded in the dual norm. Under the stated hypotheses, `effective_domain f` is automatically
nonempty, so this is equivalent here to the textbook properness assumption. -/
theorem subdifferential_biUnion_nonempty_and_isBounded_of_isCompact_subset_interior
    (h_ne_bot : ∀ y, f y ≠ ⊥) (hconvex : is_convex_function f) (hX_nonempty : X.Nonempty)
    (hX_compact : IsCompact X) (hX_subset : X ⊆ interior (effective_domain f)) :
    Set.Nonempty Y ∧ IsBounded Y := sorry

end

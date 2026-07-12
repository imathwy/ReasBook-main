import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical topological theorem
-- `Dense.exists_countable_dense_subset`; a quick `lean_run_code` check confirmed the intended
-- scheme-level source statement compiles directly with the Noetherian scheme hypothesis, so the
-- item is kept as a source-facing theorem on dense subsets of a scheme.

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]

/-- Lemma 28.5.13: if `S` is a Noetherian scheme and `T ⊆ S` is an infinite dense subset, then
`T` contains a countable subset which is dense in `S`. -/
@[stacks 0G2F]
theorem exists_countable_dense_subset_of_infinite_dense {T : Set S}
    (hT_dense : Dense T) (hT_infinite : T.Infinite) :
    ∃ E ⊆ T, E.Countable ∧ Dense E := sorry

end AlgebraicGeometry.Scheme

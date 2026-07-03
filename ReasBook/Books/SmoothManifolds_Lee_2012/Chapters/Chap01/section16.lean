import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_16 (from Chap01/Sec01) -/
universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [TopologicalManifold n M]

/-
Proposition 1.16 is the boundaryless special case of the chapter's later owner theorem
`countable_fundamentalGroup` for manifolds with boundary in Proposition 1.40. This file keeps the
source-facing boundaryless statement rather than introducing a parallel owner.
-/
/-- Proposition 1.16: The fundamental group of a topological manifold is countable. -/
theorem countable_fundamentalGroup_of_topologicalManifold (x : M) :
    Countable (FundamentalGroup M x) := by
  -- Reuse the canonical owner theorem for the boundaryless case.
  simpa using countable_fundamentalGroup (x := x)

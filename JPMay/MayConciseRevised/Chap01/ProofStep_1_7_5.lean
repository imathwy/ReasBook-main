import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- ProofStep 1.7.5: the textbook factorization step
`f = (X - C c) * g ⟹ roots.card f = natDegree f`
does not define a new owner theorem in the project. Its mathematical content is already covered by
the canonical algebraically closed field root-count theorem specialized to `ℂ`; the linear-factor
lemmas `roots_mul`, `roots_X_sub_C`, `natDegree_mul`, and `natDegree_X_sub_C` belong to the
derived proof API rather than the public statement surface. -/
#check (IsAlgClosed.card_roots_eq_natDegree : ∀ {p : Polynomial ℂ}, p.roots.card = p.natDegree)

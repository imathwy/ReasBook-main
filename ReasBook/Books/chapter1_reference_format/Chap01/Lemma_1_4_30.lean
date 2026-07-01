import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/- Lemma 1.4.30: for a subspace `W` of a `K`-vector space `V`, the quotient `V ⧸ W`
inherits the canonical quotient-space `K`-vector space structure. -/
recall Submodule.Quotient.module {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    (W : Submodule R M) :
  Module R (M ⧸ W)

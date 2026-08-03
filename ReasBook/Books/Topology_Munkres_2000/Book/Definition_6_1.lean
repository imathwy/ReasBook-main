module

import Mathlib.Data.Set.Card

open Set

/- Definition 6.1. A set `A` is finite precisely when its subtype is equivalent to
`Fin n` for some `n : ℕ`; `n = 0` is the empty case. -/
#check Set.Finite

#check fun {α : Type*} (A : Set α) ↦
  (finite_coe_iff.symm.trans finite_iff_exists_equiv_fin :
    A.Finite ↔ ∃ n : ℕ, Nonempty (A ≃ Fin n))

/- For a finite set, `Set.ncard A` is its cardinality. -/
#check Set.ncard

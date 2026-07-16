import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Lemma 1.1.22: two pairs of natural numbers are equivalent when they determine the same formal
integer difference, i.e. the same integer `p.1 - p.2`. This relation is an equivalence relation.
-/
theorem formal_integer_rel_equivalence :
    Equivalence (fun p q : ℕ × ℕ ↦ Int.subNatNat p.1 p.2 = Int.subNatNat q.1 q.2) :=
  Equivalence.comap eq_equivalence (fun p : ℕ × ℕ ↦ Int.subNatNat p.1 p.2)

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

universe u

/- Definition 1.4.42: a field `K` is algebraically closed when it satisfies the canonical
mathlib predicate `IsAlgClosed K`; equivalently, every polynomial in `K[X]` of degree at least
`1` has a root in `K`. -/
recall IsAlgClosed (K : Type u) [Field K] : Prop

section

variable {K : Type u} [Field K]

/- In an algebraically closed field, every polynomial of nonzero degree has a root. This is the
mathlib formulation of the textbook condition that every polynomial of degree at least `1` has a
root. -/
recall IsAlgClosed.exists_root [IsAlgClosed K] (p : K[X]) (hp : p.degree ≠ 0) :
  ∃ x : K, p.IsRoot x

-- Proof sketch: use `IsAlgClosed.exists_root` for the forward implication; for the reverse
-- implication, specialize the hypothesis to monic irreducible polynomials and apply
-- `IsAlgClosed.of_exists_root`.
/-- A field is algebraically closed exactly when every polynomial of nonzero degree has a root in
the field. -/
theorem isAlgClosed_iff_exists_root_of_degree_ne_zero :
    IsAlgClosed K ↔ ∀ p : K[X], p.degree ≠ 0 → ∃ x : K, p.IsRoot x := by
  constructor
  · intro hK p hp
    let _ : IsAlgClosed K := hK
    exact IsAlgClosed.exists_root p hp
  · intro h
    refine IsAlgClosed.of_exists_root K (fun p _ hp ↦ ?_)
    simpa [Polynomial.IsRoot] using h p (Polynomial.degree_pos_of_irreducible hp).ne'

end

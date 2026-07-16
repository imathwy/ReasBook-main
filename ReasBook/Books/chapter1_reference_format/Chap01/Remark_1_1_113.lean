import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Remark 1.1.113: the textbook notion of "being a field" is the canonical mathlib predicate
`IsField R`. For commutative semirings, the usual characterization by nontriviality and
invertibility of every nonzero element is recorded as a derived companion theorem below. -/
recall IsField (R : Type u) [Semiring R] : Prop

section

variable {R : Type u} [CommSemiring R]

/-- In a commutative semiring, `IsField R` is equivalent to saying that `R` is nontrivial and that
every nonzero element is a unit. -/
theorem isField_iff_nontrivial_and_all_nonzero_are_units :
    IsField R ↔ Nontrivial R ∧ ∀ a : R, a ≠ 0 → IsUnit a := by
  constructor
  · intro h
    refine ⟨h.nontrivial, ?_⟩
    intro a ha
    letI := h.toSemifield
    exact ha.isUnit
  · rintro ⟨hR, hunit⟩
    letI := hR
    refine ⟨exists_pair_ne R, mul_comm, ?_⟩
    intro a ha
    rcases hunit a ha with ⟨u, rfl⟩
    exact ⟨↑u⁻¹, by simp⟩

end

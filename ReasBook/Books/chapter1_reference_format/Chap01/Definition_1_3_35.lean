import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Polynomial

section

variable {R : Type u} [Ring R]
variable (P : R[X]) (a : R) (r : ℕ+)

/- Definition 1.3.35: `a` is an `r`-fold root of `P` exactly when the multiplicity of the factor
`X - C a` in `P` is `r`. -/
#check (P.rootMultiplicity a = (r : ℕ))

end

section

variable {R : Type u} [CommRing R]

/-- A positive multiplicity root is characterized by exact divisibility by successive powers of
`X - C a`. -/
-- Proof sketch: use `pow_rootMultiplicity_dvd` for the divisibility part, and combine it with
-- the maximality characterization of `rootMultiplicity`.
theorem rootMultiplicity_eq_iff (P : R[X]) (a : R) (r : ℕ+) :
    P.rootMultiplicity a = (r : ℕ) ↔
      (X - C a) ^ (r : ℕ) ∣ P ∧ ¬ (X - C a) ^ ((r : ℕ) + 1) ∣ P := by
  constructor
  · intro h
    have hP : P ≠ 0 := by
      intro hP
      exact PNat.ne_zero r <| by simpa [hP] using h.symm
    refine ⟨(le_rootMultiplicity_iff hP).1 ?_, (rootMultiplicity_le_iff hP a (r : ℕ)).1 ?_⟩
    · simp [h]
    · simp [h]
  · rintro ⟨hr, hnotr⟩
    have hP : P ≠ 0 := by
      intro hP
      apply hnotr
      simp [hP]
    exact le_antisymm ((rootMultiplicity_le_iff hP a (r : ℕ)).2 hnotr)
      ((le_rootMultiplicity_iff hP).2 hr)

end

end Polynomial

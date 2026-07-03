import Mathlib

universe u

/-- The Section 7 owner vocabulary for a basis letter together with its exponent sign. -/
abbrev SignedLetter (X : Type u) := X × Bool

namespace SignedLetter

variable {X : Type u}

/-- Inverting a signed letter toggles its sign. -/
def inv (x : SignedLetter X) : SignedLetter X :=
  (x.1, !x.2)

instance : Inv (SignedLetter X) :=
  ⟨inv⟩

@[simp] theorem inv_def (x : SignedLetter X) : x⁻¹ = (x.1, !x.2) :=
  rfl

@[simp] theorem inv_inv (x : SignedLetter X) : x⁻¹⁻¹ = x := by
  cases x
  simp

end SignedLetter

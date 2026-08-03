module

public import Mathlib.SetTheory.Cardinal.Basic

public section

universe u

namespace Set

/-- A set is countably infinite when its subtype is equivalent to the positive integers. -/
def CountablyInfinite {α : Type u} (A : Set α) : Prop :=
  Nonempty (A ≃ ℕ+)

/-- An equivalence with the positive integers exhibits a set as countably infinite. -/
theorem CountablyInfinite.ofEquiv {α : Type u} {A : Set α} (e : A ≃ ℕ+) :
    A.CountablyInfinite := by
  change Nonempty (A ≃ ℕ+)
  exact ⟨e⟩

/-- A countably infinite set can be indexed bijectively by the positive integers. -/
theorem CountablyInfinite.nonemptyEquivPNat {α : Type u} {A : Set α}
    (h : A.CountablyInfinite) : Nonempty (ℕ+ ≃ A) :=
  h.map Equiv.symm

end Set

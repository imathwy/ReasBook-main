module

public import Mathlib.Data.PNat.Find
public import Mathlib.Order.Bounds.Defs

public section

/-- Theorem 4.1 (Well-ordering property). Every nonempty subset of the positive
integers has a smallest element. -/
theorem wellOrderingProperty (A : Set ℕ+) (hA : A.Nonempty) :
    ∃ a, IsLeast A a := by
  classical
  -- The canonical search operator supplies an element of the nonempty set.
  refine ⟨PNat.find hA, PNat.find_spec hA, ?_⟩
  -- Its minimality property gives the required lower bound on every member.
  intro b hb
  exact PNat.find_min' hA hb

end

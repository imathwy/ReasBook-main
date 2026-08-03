module

public import Topology_Munkres_2000.Book.Definition_3_14

public section

universe u

variable {A : Type u} [LinearOrder A] {A₀ : Set A} {b : A}

/- Definition 3.15 (1): The element `b` is an upper bound for `A₀` when
`b ∈ upperBounds A₀`. -/
#check (b ∈ upperBounds A₀)

/- Definition 3.15 (2): The assertion that `A₀` is bounded above is
represented by `BddAbove A₀`. -/
#check (BddAbove A₀)

/- Definition 3.15 (3): The assertion that `b` is a least upper bound, or
supremum, of `A₀` is represented by `IsLUB A₀ b`. -/
#check (IsLUB A₀ b)

namespace IsLUB

/-- Definition 3.15 (4): A least upper bound that belongs to the set is its
greatest element. -/
theorem isGreatest_of_mem {A : Type u} [Preorder A] {A₀ : Set A} {b : A}
    (h : IsLUB A₀ b) (hb : b ∈ A₀) : IsGreatest A₀ b :=
  ⟨hb, h.1⟩

end IsLUB

module

public import Mathlib.Order.Antichain

public section

universe u

section

variable {A : Type u} [LE A] {A₀ : Set A} {a b : A}

/- Definition 3.14 (1): The largest element of `A₀` is represented by
`IsGreatest A₀ b`. -/
#check (IsGreatest A₀ b)

/- Definition 3.14 (2): The smallest element of `A₀` is represented by
`IsLeast A₀ a`. -/
#check (IsLeast A₀ a)

end


section

variable {A : Type u} [PartialOrder A] {A₀ : Set A} {a b : A}

/- Definition 3.14 (3): A subset of an ordered set has at most one largest
element. -/
#check (IsGreatest.unique : IsGreatest A₀ a → IsGreatest A₀ b → a = b)

/- Definition 3.14 (4): A subset of an ordered set has at most one smallest
element. -/
#check (IsLeast.unique : IsLeast A₀ a → IsLeast A₀ b → a = b)

end

module

public import Topology_Munkres_2000.Book.Definition_3_15

public section

universe u

variable {A : Type u} [LinearOrder A] {A₀ : Set A} {a : A}

/- Definition 3.16 (1): A lower bound for `A₀` is represented by membership
in `lowerBounds A₀`. -/
#check (a ∈ lowerBounds A₀)

/- Definition 3.16 (2): A subset `A₀` is bounded below when `BddBelow A₀`
holds. -/
#check (BddBelow A₀)

/- Definition 3.16 (3): The element `a` is a greatest lower bound, or
infimum, of `A₀` when `IsGLB A₀ a` holds. -/
#check (IsGLB A₀ a)

namespace IsGLB

/-- Definition 3.16 (4): An infimum of `A₀` that belongs to `A₀` is its
smallest element. -/
theorem isLeast_of_mem {A : Type u} [Preorder A] {A₀ : Set A} {a : A}
    (h : IsGLB A₀ a) (ha : a ∈ A₀) : IsLeast A₀ a :=
  ⟨ha, h.1⟩

end IsGLB

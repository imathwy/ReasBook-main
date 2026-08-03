module

public import Mathlib.Order.Bounds.Basic

public section

namespace Function

/-- `f.IsLeastUnused` means that `f i` is the least value not attained at an
index strictly before `i`. -/
def IsLeastUnused {ι α : Type*} [Preorder ι] [Preorder α] (f : ι → α) : Prop :=
  ∀ i, IsLeast (Set.univ \ f '' Set.Iio i) (f i)

/-- Construct the least-unused property from its pointwise defining condition. -/
theorem IsLeastUnused.of_forall {ι α : Type*} [Preorder ι] [Preorder α] {f : ι → α}
    (hf : ∀ i, IsLeast (Set.univ \ f '' Set.Iio i) (f i)) :
    f.IsLeastUnused :=
  hf

/-- The defining least-unused property at a specified index. -/
theorem IsLeastUnused.at {ι α : Type*} [Preorder ι] [Preorder α] {f : ι → α}
    (hf : f.IsLeastUnused) (i : ι) :
    IsLeast (Set.univ \ f '' Set.Iio i) (f i) :=
  hf i

/-- A least-unused selection on a linearly ordered index type is injective. -/
theorem IsLeastUnused.injective {ι α : Type*} [LinearOrder ι] [Preorder α] {f : ι → α}
    (hf : f.IsLeastUnused) : f.Injective := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact (hf.at j).1.2 ⟨i, hij', hij⟩
  · exact (hf.at i).1.2 ⟨j, hji', hij.symm⟩

end Function

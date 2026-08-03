module

public import Mathlib.Data.Setoid.Partition

universe u

section

variable {α : Type u} (A : Set α)

/- Definition 3.5: A partition of a set `A` is represented by a partition of the
subtype `A` into pairwise disjoint nonempty subsets whose union is all of `A`. -/
#check (Setoid.IsPartition : Set (Set A) → Prop)

end

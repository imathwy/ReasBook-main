module

public import Mathlib.Data.Setoid.Partition

public section

namespace Setoid

variable {α β : Type*}

/-- The equivalence classes of the kernel of a surjective function are exactly its fibers. -/
public theorem classes_ker_eq_fibers (f : α → β) (hf : Function.Surjective f) :
    (Setoid.ker f).classes = Set.range fun y ↦ {x | f x = y} := by
  apply Set.Subset.antisymm (classes_ker_subset_fiber_set f)
  rintro _ ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := hf y
  exact (Setoid.ker f).mem_classes x

end Setoid

module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Normed.Group.BallSphere

noncomputable section

public section

namespace StandardSphere

/-- The antipodal self-map of the standard sphere. -/
@[expose]
def antipodal (n : ℕ) : C(StandardSphere n, StandardSphere n) :=
  ⟨fun x ↦ -x, continuous_neg⟩

/-- The antipodal map sends each point to its negative. -/
@[simp]
theorem antipodal_apply (n : ℕ) (x : StandardSphere n) : antipodal n x = -x := rfl

/-- The antipodal map is odd. -/
theorem odd_antipodal (n : ℕ) : Function.Odd (antipodal n) := by
  intro x
  rfl

end StandardSphere

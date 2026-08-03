import BauschkeLean.Chap30.Theorem_30_8

open Function

universe u v

namespace SetValuedOperator

/-- The Chapter 30 common fixed-point set of a constant `Unit`-indexed family is the fixed-point
set of its unique component. -/
@[simp] theorem commonFixedPointSet_unit_eq_fixedPoints
    {H : Type u} (T : H → H) :
    commonFixedPointSet (fun _ : Unit ↦ T) = fixedPoints T := by
  ext x
  rw [mem_commonFixedPointSet_iff, mem_fixedPoints_iff]
  constructor
  · intro hx
    exact hx ()
  · intro hx _
    exact hx

/-- The canonical `Unit`-indexed control map visits the unique index in each block of length `1`. -/
theorem visitsEveryIndexInEachBlock_unit :
    VisitsEveryIndexInEachBlock (fun _ : ℕ ↦ ()) 1 := by
  intro j n
  cases j
  exact ⟨0, rfl⟩

end SetValuedOperator

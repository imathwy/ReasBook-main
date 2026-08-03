import Mathlib
import BauschkeLean.Chap01.Text_1_0_8
import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u v

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

section

variable [AddGroup X]

/-- Text 1.0.21: The translation of a set-valued operator `A` by `y` sends `x` to the value
of `A` at `x - y`. -/
def translate (A : SetValuedOperator X Y) (y : X) : SetValuedOperator X Y :=
  fun x ↦ A (x - y)

/-- Applying the translation of `A` by `y` at `x` evaluates `A` at `x - y`. -/
@[simp] theorem translate_apply (A : SetValuedOperator X Y) (y x : X) :
    translate A y x = A (x - y) :=
  rfl

/-- Membership in the translation of a set-valued operator is equivalent to membership in the
original operator after translating the input by `-y`. -/
@[simp]
theorem mem_translate_iff (A : SetValuedOperator X Y) (y x : X) (u : Y) :
    u ∈ translate A y x ↔ u ∈ A (x - y) :=
  Iff.rfl

/-- The reversal of a set-valued operator sends `x` to the value of `A` at `-x`. -/
def reverse (A : SetValuedOperator X Y) : SetValuedOperator X Y :=
  fun x ↦ A (-x)

/- Lean cannot use the textbook ASCII surface `A^∨` here. We therefore use the postfix vee token
`Aᵛ` as the direct Lean surface for operator reversal. -/
scoped postfix:max "ᵛ" => SetValuedOperator.reverse

/-- Applying the reversal of `A` at `x` evaluates `A` at `-x`. -/
@[simp] theorem reverse_apply (A : SetValuedOperator X Y) (x : X) :
    reverse A x = A (-x) :=
  rfl

/-- Membership in the reversal of a set-valued operator is equivalent to membership in the
original operator at the negated input. -/
@[simp]
theorem mem_reverse_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    u ∈ reverse A x ↔ u ∈ A (-x) :=
  Iff.rfl

end

section

variable [Add Y]

/-- The output translation of a set-valued operator `A` by `z` is the codomain translation
obtained by composing `A` with the singleton-valued map `y ↦ z + y`. -/
def addConst (A : SetValuedOperator X Y) (z : Y) : SetValuedOperator X Y :=
  ((fun y ↦ z + y).toSetValuedOperator).comp A

/-- Applying `A.addConst z` at `x` yields the translated value set `({z} : Set Y) + A x`. -/
@[simp] theorem addConst_apply (A : SetValuedOperator X Y) (z : Y) (x : X) :
    A.addConst z x = ({z} : Set Y) + A x := by
  ext u
  rw [addConst, mem_comp, Set.mem_add]
  constructor
  · rintro ⟨y, hy, huy⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at huy
    exact ⟨z, by simp, y, hy, huy.symm⟩
  · rintro ⟨w, hw, y, hy, hwu⟩
    rw [Set.mem_singleton_iff] at hw
    subst w
    exact ⟨y, hy, by
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
      exact hwu.symm⟩

/-- Membership in the codomain translation `A.addConst z` means belonging to `A x` up to adding
the constant `z`. -/
@[simp] theorem mem_addConst_iff (A : SetValuedOperator X Y) (z : Y) (x : X) (u : Y) :
    u ∈ A.addConst z x ↔ ∃ y ∈ A x, u = z + y := by
  rw [addConst, mem_comp]
  constructor
  · rintro ⟨y, hy, huy⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at huy
    exact ⟨y, hy, huy⟩
  · rintro ⟨y, hy, hyu⟩
    exact ⟨y, hy, by
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
      exact hyu⟩

/-- The codomain translation owner `A.addConst z` is exactly the pointwise sum of `A` with the
singleton-valued constant operator `x ↦ {z}`. -/
theorem addConst_eq_const_toSetValuedOperator_add (A : SetValuedOperator X Y) (z : Y) :
    A.addConst z = (fun _ : X ↦ z).toSetValuedOperator + A := by
  ext x u
  constructor
  · intro hu
    rw [addConst_apply] at hu
    simpa [Function.toSetValuedOperator_apply, Set.mem_add] using hu
  · intro hu
    rw [addConst_apply]
    simpa [Function.toSetValuedOperator_apply, Set.mem_add] using hu

end

end SetValuedOperator

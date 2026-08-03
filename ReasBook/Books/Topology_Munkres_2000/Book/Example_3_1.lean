module

public import Mathlib.Data.Rel

public section

universe u

open scoped SetRel

namespace Kinship

variable {P : Type u}

/-- Example 3.1 (2): The blood relation consists of people having a common
ancestor. The relation `D` records when its first argument is a descendant of
its second. -/
def blood (D : SetRel P P) : SetRel P P := D ○ D.inv

/-- Membership in the blood relation is witnessed by a common ancestor. -/
@[simp] theorem mem_blood (D : SetRel P P) (x y : P) :
    x ~[blood D] y ↔ ∃ z, x ~[D] z ∧ y ~[D] z := .rfl

/-- Example 3.1 (4): The blood relation is symmetric. -/
instance blood.instIsSymm (D : SetRel P P) : SetRel.IsSymm (blood D) := by
  unfold blood
  infer_instance

/-- Example 3.1 (3): The sibling relation consists of people having exactly the
same parents. -/
def sibling (parent : SetRel P P) : SetRel P P :=
  {(x, y) | ∀ z, x ~[parent] z ↔ y ~[parent] z}

/-- Membership in the sibling relation means equality of parent sets. -/
@[simp] theorem mem_sibling (parent : SetRel P P) (x y : P) :
    x ~[sibling parent] y ↔ ∀ z, x ~[parent] z ↔ y ~[parent] z := .rfl

end Kinship

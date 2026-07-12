import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜]
variable (A : GradedObjectWithShift (1 : ℤ) 𝒜) (k : ℤ)

/- Domain-style sampling:
- primary domain: shifts of graded objects indexed by `ℤ`;
- sampled owner declarations:
  `shiftFunctor`,
  `GradedObject.hasShift`,
  `GradedObject.shiftFunctor_obj_apply`,
  `GradedObject.shiftFunctor_map_apply`.

Source/core/bridge triage:
- `core/canonical`: the `HasShift`/`shiftFunctor` owner on `GradedObjectWithShift (1 : ℤ) 𝒜`;
- `source-facing`: the shifted graded object `A⟦k⟧`;
- `bridge/view`: the component formula from `GradedObject.shiftFunctor_obj_apply`.

Primitive data are only the owner shift functor. The component formula `(A⟦k⟧) i = A (i + k)` and
the corresponding map formula are derived API, so this file should remain a canonical recall item
rather than introducing a parallel local wrapper for graded-object shifts.

Definition 12.16.4: for a graded object `A`, the `k`-shift `A[k]` is the canonical owner object
`A⟦k⟧`. -/
#check A⟦k⟧

/-- Definition 12.16.4: the textbook `k`-shift of a graded object is the canonical owner object
`A⟦k⟧`. -/
@[stacks 09MG]
abbrev gradedShift (A : GradedObjectWithShift (1 : ℤ) 𝒜) (k : ℤ) :
    GradedObjectWithShift (1 : ℤ) 𝒜 :=
  A⟦k⟧

/-- Helper for Definition 12.16.4: the degree-`i` component of the shifted graded object is the
`(k + i)`-component of the original graded object. -/
lemma graded_shift_obj (A : GradedObjectWithShift (1 : ℤ) 𝒜) (k i : ℤ) :
    gradedShift A k i = A (k + i) := by
  -- Unfold the textbook wrapper and evaluate the canonical shift functor on components.
  simpa [gradedShift, add_comm] using
    (GradedObject.shiftFunctor_obj_apply (s := (1 : ℤ)) A i k)

/- Companion recall: `GradedObject.shiftFunctor_obj_apply` computes the components of the canonical
graded-object shift, giving `(A⟦k⟧) i = A (i + k)` for grading step `1 : ℤ`. -/
recall GradedObject.shiftFunctor_obj_apply

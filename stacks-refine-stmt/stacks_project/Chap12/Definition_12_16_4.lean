import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Recall

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

/- Companion recall: `GradedObject.shiftFunctor_obj_apply` computes the components of the canonical
graded-object shift, giving `(A⟦k⟧) i = A (i + k)` for grading step `1 : ℤ`. -/
recall GradedObject.shiftFunctor_obj_apply

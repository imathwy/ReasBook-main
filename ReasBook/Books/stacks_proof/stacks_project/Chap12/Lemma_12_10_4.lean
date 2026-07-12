import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace ExactFunctor

section

open Functor (kernel)
open Limits

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ₑ B)

/- Lemma 12.10.4: for an exact functor `F : \mathcal A ⥤ₑ \mathcal B` between abelian
categories, the kernel object property `kernel F.obj` is a Serre class.

Domain-style sampling:
- primary domain: exact functors and Serre classes of object properties in abelian categories;
- sampled owner declarations: `Functor.kernel`, `ObjectProperty.IsSerreClass`, and the generic
  inverse-image instance giving `IsSerreClass (P.inverseImage F)` when `F` preserves finite limits
  and finite colimits;
- owner abstraction: `Functor.kernel` on the underlying functor `F.obj`;
- primitive data: the object property `IsZero (F.obj.obj X)`;
- derived API: the Serre-class structure on that inverse image.

Source/core/bridge triage:
- `source-facing`: the kernel of an exact functor is a Serre class;
- `core/canonical`: the owner `kernel F.obj`;
- `bridge/view`: the exact-functor bundle supplies the preservation instances needed to invoke the
  generic inverse-image Serre-class instance.
-/

/-
The helper only needs the ambient categories and the exact-functor bundle; the abelian instances
are omitted to keep the declaration warning-free.
-/
omit [Abelian A] [Abelian B] in
/-- Helper for Lemma 12.10.4: the kernel object property is definitionally the inverse image of
`IsZero` along the underlying functor. -/
lemma kernel_eq_inverseImage_isZero :
    kernel F.obj = ObjectProperty.inverseImage (IsZero : ObjectProperty B) F.obj := by
  -- The kernel owner is defined as this inverse image, so the bridge is definitional.
  rfl

/-- Lemma 12.10.4: the kernel object property of an exact functor is a Serre class. -/
@[stacks 02MQ]
theorem kernel_isSerreClass :
    (kernel F.obj).IsSerreClass := by
  -- We follow the source route: identify the kernel with the inverse image of the zero-object
  -- property, then use the generic inverse-image Serre-class instance.
  -- Route correction: make the inverse-image owner explicit instead of leaving the whole argument
  -- hidden in raw instance synthesis.
  simpa [kernel_eq_inverseImage_isZero (F := F)] using
    (inferInstance : (ObjectProperty.inverseImage (IsZero : ObjectProperty B) F.obj).IsSerreClass)

-- The synthesized instance for the textbook statement is exactly `kernel_isSerreClass`.
example : (kernel F.obj).IsSerreClass := kernel_isSerreClass (F := F)

end

end ExactFunctor

end CategoryTheory

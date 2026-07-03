import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace ExactFunctor

section

open Functor (kernel)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ₑ B)

/- Lemma 12.10.4: for an exact functor `F : \mathcal A ⥤ₑ \mathcal B` between abelian
categories, the kernel object property `kernel F.obj` is a LinearRepresentations_Serre_1977 class.

Domain-style sampling:
- primary domain: exact functors and LinearRepresentations_Serre_1977 classes of object properties in abelian categories;
- sampled owner declarations: `Functor.kernel`, `ObjectProperty.IsSerreClass`, and the generic
  inverse-image instance giving `IsSerreClass (P.inverseImage F)` when `F` preserves finite limits
  and finite colimits;
- owner abstraction: `Functor.kernel` on the underlying functor `F.obj`;
- primitive data: the object property `IsZero (F.obj.obj X)`;
- derived API: the LinearRepresentations_Serre_1977-class structure on that inverse image.

Source/core/bridge triage:
- `source-facing`: the kernel of an exact functor is a LinearRepresentations_Serre_1977 class;
- `core/canonical`: the owner `kernel F.obj`;
- `bridge/view`: the exact-functor bundle supplies the preservation instances needed to invoke the
  generic inverse-image LinearRepresentations_Serre_1977-class instance.
-/
#synth (kernel F.obj).IsSerreClass

end

end ExactFunctor

end CategoryTheory

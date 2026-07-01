import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace ExactFunctor

section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ₑ B)

/- Definition 12.10.5:
- source-facing: the kernel of an exact functor is the full subcategory of objects sent to zero
- primary domain: exact functors and full subcategories cut out by an object property
- sampled owner declarations: `Functor.kernel`, `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`
- core/canonical owner: `Functor.kernel`, specialized here to `F.obj.kernel`
- bridge/view: the associated full subcategory `F.obj.kernel.FullSubcategory`

The primitive data are the object property `IsZero (F.obj X)`; the subcategory is derived API. -/
recall Functor.kernel
#check F.obj.kernel.FullSubcategory

end

end ExactFunctor

end CategoryTheory

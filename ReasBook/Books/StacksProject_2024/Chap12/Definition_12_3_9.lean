import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)

/- Source/core/bridge triage for Definition 12.3.9:
- source-facing: the textbook kernel, cokernel, coimage, and image attached to a morphism
- core/canonical owners: `kernel f` and `cokernel f`
- bridge/view: `Abelian.coimage f` and `Abelian.image f` are the abelian source-facing owners
  obtained from those canonical kernel/cokernel constructions -/

section

variable [HasKernel f]

/-
Definition 12.3.9 (kernel): the textbook kernel construction in a preadditive category is the
canonical owner object `kernel f` with structure morphism `kernel.ι f`, characterized by the
universal property `kernelIsKernel f`; the owner API itself only needs zero morphisms.
-/
recall kernel
recall kernel.ι
recall kernel.condition
recall kernelIsKernel

end

section

variable [HasCokernel f]

/-
Definition 12.3.9 (cokernel): the textbook cokernel construction in a preadditive category is the
canonical owner object `cokernel f` with structure morphism `cokernel.π f`, characterized by the
universal property `cokernelIsCokernel f`; the owner API itself only needs zero morphisms.
-/
recall cokernel
recall cokernel.π
recall cokernel.condition
recall cokernelIsCokernel

end

section

variable [HasKernel f]
variable [HasCokernel (kernel.ι f)]

/- Definition 12.3.9 (coimage): the textbook coimage construction, stated for preadditive
categories, is the canonical owner object `Abelian.coimage f` with structure morphism
`Abelian.coimage.π f`. -/
recall Abelian.coimage
recall Abelian.coimage.π

/- Companion bridge: the source-facing coimage definition is exactly the canonical cokernel owner
applied to `kernel.ι f`, with universal property `cokernelIsCokernel (kernel.ι f)`. -/
#check cokernelIsCokernel (kernel.ι f)

end

section

variable [HasCokernel f]
variable [HasKernel (cokernel.π f)]

/- Definition 12.3.9 (image): the textbook image construction, stated for preadditive categories,
is the canonical owner object `Abelian.image f` with structure morphism `Abelian.image.ι f`. -/
recall Abelian.image
recall Abelian.image.ι

/- Companion bridge: the source-facing image definition is exactly the canonical kernel owner
applied to `cokernel.π f`, with universal property `kernelIsKernel (cokernel.π f)`. -/
#check kernelIsKernel (cokernel.π f)

end

end CategoryTheory

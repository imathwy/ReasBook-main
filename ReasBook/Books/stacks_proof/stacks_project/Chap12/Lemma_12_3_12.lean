import StacksProject_2024.Chap12.Definition_12_3_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits Abelian

local notation "coimage" => Abelian.coimage
local notation "image" => Abelian.image

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)
variable [HasKernel f] [HasCokernel f] [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)]

/-
Source/core/bridge triage for Lemma 12.3.12:
- primary domain: abelian coimage/image factorization in a category with zero morphisms
- sampled owner declarations: `coimage.π`, `image.ι`, `coimageImageComparison`, and
  `coimage_image_factorisation`
- source-facing: uniqueness of the factorization of `f` through its coimage and image
- core/canonical owner: `coimageImageComparison f`
- bridge/view: `coimage_image_factorisation f` identifies the owner morphism with the
  textbook factorization
- primitive data: the existence assumptions for the kernel, cokernel, coimage, and image of `f`
- derived API: the epi/mono instances for `coimage.π f` and `image.ι f`, and the comparison
  factorization equation
-/

/-- Lemma 12.3.12: the canonical morphism `coimageImageComparison f` is the unique
factorization of `f` through its abelian coimage and abelian image. -/
@[stacks 0107]
theorem unique_coimage_image_factorization :
    ∃! g : coimage f ⟶ image f,
      coimage.π f ≫ g ≫ image.ι f = f := by
  refine ⟨coimageImageComparison f, coimage_image_factorisation f, ?_⟩
  intro g hg
  apply (cancel_epi (coimage.π f)).1
  apply (cancel_mono (image.ι f)).1
  simpa [Category.assoc] using hg.trans (coimage_image_factorisation f).symm

end CategoryTheory

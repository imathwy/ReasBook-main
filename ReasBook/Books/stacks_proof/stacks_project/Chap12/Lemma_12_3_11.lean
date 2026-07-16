import stacks_proof.stacks_project.Chap12.Definition_12_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits Abelian

local notation "coimage" => Abelian.coimage
local notation "image" => Abelian.image

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)

/-
Source/core/bridge triage for Lemma 12.3.11:
- primary domain: kernel/cokernel/coimage/image structure morphisms in a category with zero
  morphisms
- sampled owner declarations: `kernel.ι`, `cokernel.π`, `Abelian.coimage.π`, and
  `Abelian.image.ι`
- source-facing: the canonical kernel, cokernel, coimage, and image structure morphisms are
  mono or epi as appropriate
- core/canonical owner abstraction: the owner objects are the canonical kernel/cokernel/coimage/
  image constructions, and this lemma only uses their structure morphisms
- bridge/view: Definition `12.3.9` already identifies the textbook constructions with these
  owners, while the mono/epi facts themselves are supplied canonically by the upstream
  equalizer/coequalizer instances via typeclass inference
- primitive-vs-derived split: the primitive data are the existence assumptions
  `[HasKernel f]`, `[HasCokernel f]`, `[HasCokernel (kernel.ι f)]`, and
  `[HasKernel (cokernel.π f)]`; the mono/epi assertions are entirely derived from instance
  search, so there is no local wrapper data to keep
-/

section Kernel

variable [HasKernel f]

/- Lemma 12.3.11 (1): if a kernel of `f` exists, then the canonical kernel morphism
`kernel.ι f` is a monomorphism. -/
#check (inferInstance : Mono (kernel.ι f))

end Kernel

section Cokernel

variable [HasCokernel f]

/- Lemma 12.3.11 (2): if a cokernel of `f` exists, then the canonical cokernel morphism
`cokernel.π f` is an epimorphism. -/
#check (inferInstance : Epi (cokernel.π f))

end Cokernel

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/- Lemma 12.3.11 (3): the textbook coimage projection `cokernel.π (kernel.ι f)` is the owner
morphism `coimage.π f`, and it is an epimorphism. -/
#check (inferInstance : Epi (coimage.π f))

end Coimage

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/- Lemma 12.3.11 (4): the textbook image inclusion `kernel.ι (cokernel.π f)` is the owner
morphism `image.ι f`, and it is a monomorphism. -/
#check (inferInstance : Mono (image.ι f))

end Image

end CategoryTheory

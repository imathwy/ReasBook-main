import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

open Limits

universe v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (x y : C) [HasBinaryBiproduct x y]

/- Domain-style sampling for Lemma 12.3.10:
- primary domain: kernels and cokernels arising from the canonical binary biproduct square;
- sampled canonical declarations:
  `biprod.sndKernelFork`,
  `biprod.isKernelSndKernelFork`,
  `biprod.inrCokernelCofork`,
  `biprod.isCokernelInrCokernelFork`;
- owner abstraction: `HasBinaryBiproduct x y`;
- primitive data: the binary biproduct object `x ⊞ y` with structure morphisms
  `biprod.inl`, `biprod.inr`, `biprod.fst`, and `biprod.snd`;
- derived API: the kernel fork of `biprod.snd` and the cokernel cofork of `biprod.inr`,
  together with their universal properties.

Source/core/bridge triage:
- `source-facing`: the textbook statements that, in the direct sum decomposition `x ⊞ y`,
  `biprod.inl` is the kernel of `biprod.snd` and `biprod.fst` is the cokernel of `biprod.inr`;
- `core/canonical`: the mathlib owner declarations `biprod.isKernelSndKernelFork` and
  `biprod.isCokernelInrCokernelFork`;
- `bridge/view`: none is needed here, because the source-facing statements already coincide with
  the owner declarations. -/

/- Lemma 12.3.10 (1): in the direct sum `x ⊞ y` with structure morphisms
`biprod.inl`, `biprod.inr`, `biprod.fst`, and `biprod.snd` as in Lemma `12.3.4`,
the inclusion `biprod.inl : x ⟶ x ⊞ y` is a kernel of the projection
`biprod.snd : x ⊞ y ⟶ y`. This is the canonical mathlib kernel-fork statement. -/
recall biprod.isKernelSndKernelFork

/- Lemma 12.3.10 (2): dually, in the same direct-sum decomposition, the projection
`biprod.fst : x ⊞ y ⟶ x` is a cokernel of the inclusion
`biprod.inr : y ⟶ x ⊞ y`. This is the canonical mathlib cokernel-cofork statement. -/
recall biprod.isCokernelInrCokernelFork

end

end CategoryTheory

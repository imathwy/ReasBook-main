import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.Tactic.Recall

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {W X Y Z : C} {f : W ⟶ Y} {g : W ⟶ X} {h : Y ⟶ Z} {k : X ⟶ Z}

/-
Domain-style sampling for Lemma 12.5.12:
- primary domain: kernel and cokernel comparison morphisms associated to pullback and pushout
  squares in a category with zero morphisms;
- sampled owner declarations:
  `kernel.map`,
  `cokernel.map`,
  `isIso_kernel_map_of_isPullback`,
  `isIso_cokernel_map_of_isPushout`;
- best owner abstraction: the mathlib owner theorems
  `isIso_kernel_map_of_isPullback` and `isIso_cokernel_map_of_isPushout`;
- primitive data: a pullback or pushout square together with the existing kernel or cokernel
  objects on the relevant vertical morphisms;
- derived API: the vertical comparison statements obtained canonically from those owner theorems by
  flipping the square.

Source/core/bridge triage:
- `source-facing`: the Stacks formulation comparing the kernels or cokernels of the vertical maps;
- `core/canonical`: the owner theorems for the horizontal comparison maps;
- `bridge/view`: the source-facing vertical specialization theorems below, derived from `sq.flip`.

This numbered item is therefore bridge-only: the canonical owner theorems already exist upstream,
so the refined file should recall them directly and keep only thin named companion theorems for
the vertical Stacks formulations.
-/

/- Lemma 12.5.12, core/canonical recall: in a pullback square, the canonical horizontal kernel map
is an isomorphism. -/
recall isIso_kernel_map_of_isPullback

/- Lemma 12.5.12 (1), source-facing specialization: for a cartesian square, the induced morphism
`kernel f ⟶ kernel k` between the kernels of the vertical maps is the canonical isomorphism
obtained by applying `isIso_kernel_map_of_isPullback` to the flipped square. -/
theorem isIso_kernel_map_vertical_of_isPullback [HasKernel f] [HasKernel k]
    (sq : IsPullback g f k h) :
    IsIso (kernel.map f k g h sq.w.symm) := by
  simpa using isIso_kernel_map_of_isPullback sq.flip

/- Lemma 12.5.12, core/canonical recall: in a pushout square, the canonical horizontal cokernel
map is an isomorphism. -/
recall isIso_cokernel_map_of_isPushout

/- Lemma 12.5.12 (2), source-facing specialization: for a cocartesian square, the induced
morphism `cokernel f ⟶ cokernel k` between the cokernels of the vertical maps is the canonical
isomorphism obtained by applying `isIso_cokernel_map_of_isPushout` to the flipped square. -/
theorem isIso_cokernel_map_vertical_of_isPushout [HasCokernel f] [HasCokernel k]
    (sq : IsPushout g f k h) :
    IsIso (cokernel.map f k g h sq.w.symm) := by
  simpa using isIso_cokernel_map_of_isPushout sq.flip

end CategoryTheory.Limits

import Mathlib
import stacks_project.Chap10.Definition_10_72_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

namespace Module

/-
Source/core/bridge triage:
* source-facing: `Module.CohenMacaulay R M`, the Cohen-Macaulay condition for finite modules over
  a Noetherian local ring;
* core/canonical: the same owner class, expressed directly with `supportDim` and `moduleDepth` in
  the Noetherian local setting;
* bridge/view: the projection `CohenMacaulay.supportDim_eq_moduleDepth`, which exposes the
  defining equality directly from the owner class.

Primitive data are only the finiteness assumption carried by the owner class and the defining
equality `supportDim R M = .some (moduleDepth R M)`. The inherited `Module.Finite` instance is
derived from the owner abstraction and should not be restated as a parallel local instance or a
duplicate unpacking theorem.
-/
/-- Definition 10.103.1: a finite `R`-module over a Noetherian local ring is Cohen-Macaulay when
the Krull dimension of its support equals its depth. -/
class CohenMacaulay : Prop extends Module.Finite R M where
  supportDim_eq_moduleDepth : supportDim R M = .some (moduleDepth R M)

end Module

end

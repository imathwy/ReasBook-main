import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped TensorProduct
open TensorProduct

section

variable (R : Type u) (M : Type v) (N : Type w)
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/- The finite tensor-product part of this item is the canonical mathlib instance. -/
recall Module.Finite.tensorProduct

namespace Module.FinitePresentation

/-- Lemma 10.12.14: if `M` and `N` are finitely presented `R`-modules, then the tensor
product `M ⊗[R] N` is finitely presented over `R`. -/
instance tensorProduct [Module.FinitePresentation R M]
    [Module.FinitePresentation R N] : Module.FinitePresentation R (M ⊗[R] N) := sorry

end Module.FinitePresentation

end

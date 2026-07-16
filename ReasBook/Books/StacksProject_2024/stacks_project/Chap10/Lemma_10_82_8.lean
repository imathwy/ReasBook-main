import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {N : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N]
variable {f : M →ₗ[R] M'}

-- Proof sketch: for any `R`-module `Q`, use the tensor associativity isomorphism to identify
-- `((M ⊗[R] N) ⊗[R] Q)` with `M ⊗[R] (N ⊗[R] Q)` and similarly on the target. Under these
-- identifications, `(f.rTensor N).rTensor Q` is the tensor of `f` with `N ⊗[R] Q`, so its
-- injectivity follows from the universal injectivity of `f`.
/-- Lemma 10.82.8: tensoring a universally injective `R`-linear map on the right with any
`R`-module again yields a universally injective map. -/
theorem universallyInjective_rTensor (hf : UniversallyInjective f) :
    UniversallyInjective (f.rTensor N) := sorry

end

end LinearMap

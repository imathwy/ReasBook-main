import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace LinearMap

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

-- Proof sketch: injectivity is detected by applying the universal injectivity hypothesis to the
-- kernel inclusion `ker f → M`.
/-- Lemma 10.82.14 (injective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects injectivity. -/
theorem injective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Injective (f.rTensor S)) : Function.Injective f := sorry

-- Proof sketch: surjectivity is detected from the cokernel after tensoring and the same universal
-- injectivity hypothesis applied to the canonical map `Q → Q ⊗[R] S`.
/-- Lemma 10.82.14 (surjective clause): if `R → S` is universally injective as an `R`-module map,
then tensoring an `R`-linear map with `S` reflects surjectivity. -/
theorem surjective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Surjective (f.rTensor S)) : Function.Surjective f := sorry

-- Proof sketch: bijectivity is the conjunction of injectivity and surjectivity.
/-- If tensoring with `S` makes an `R`-linear map bijective, then the original map is bijective,
provided `R → S` is universally injective as an `R`-module map. -/
theorem bijective_of_rTensor_of_universallyInjective
    (hS : UniversallyInjective (Algebra.linearMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective (f.rTensor S)) : Function.Bijective f :=
  ⟨injective_of_rTensor_of_universallyInjective hS hf.1,
    surjective_of_rTensor_of_universallyInjective hS hf.2⟩

end

end LinearMap

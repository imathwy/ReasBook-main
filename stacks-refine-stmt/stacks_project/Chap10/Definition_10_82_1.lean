import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Definition 10.82.1 (1): an `R`-linear map is universally injective if tensoring it with any
`R`-module preserves injectivity. -/
def UniversallyInjective (f : M →ₗ[R] N) : Prop :=
  ∀ (Q : Type*) (_ : AddCommGroup Q) (_ : Module R Q),
    Function.Injective (f.rTensor Q)

-- Proof sketch: for every `Q`, the tensor map of the identity is the identity on `M ⊗[R] Q`,
-- hence it is injective.
/-- The identity map of an `R`-module is universally injective. -/
theorem universallyInjective_id :
    UniversallyInjective (LinearMap.id : M →ₗ[R] M) := by
  unfold UniversallyInjective
  intro Q _ _ x y h
  simpa using h

end

end LinearMap

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- Definition 10.82.1 (2): a short exact sequence of `R`-modules is universally exact if its
first map is universally injective. -/
def UniversallyExact (S : ShortComplex (ModuleCat.{v} R)) : Prop :=
  S.ShortExact ∧ LinearMap.UniversallyInjective.{u, v, v, v} S.f.hom

namespace UniversallyExact

-- Proof sketch: this is the first projection from the defining conjunction.
/-- A universally exact short complex is short exact. -/
theorem shortExact (hS : UniversallyExact S) : S.ShortExact := hS.1

-- Proof sketch: this is the second projection from the defining conjunction.
/-- In a universally exact short complex, the first map is universally injective. -/
theorem universallyInjective_f (hS : UniversallyExact S) :
    LinearMap.UniversallyInjective.{u, v, v, v} S.f.hom := hS.2

end UniversallyExact

end

end CategoryTheory.ShortComplex

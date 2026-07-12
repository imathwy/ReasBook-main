import Mathlib.RingTheory.Ideal.Basic
import StacksProject_2024.Chap15.Lemma_15_71_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- 
Domain-style sampling:
* primary domain: module-theoretic factorization of scalar-action endomorphisms through
  projective modules;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.lsmul`,
  `Module.Projective`,
  `LinearMap.factorsThroughProjective_of_projective`;
* best owner abstraction: `LinearMap.FactorsThroughProjective` is the canonical owner for the
  pointwise factorization datum, while `Module.IsIdealProjective I M` is the source-facing
  module-level owner bundling that datum for every `a : I`;
* layer triage:
  `LinearMap.FactorsThroughProjective` is `core/canonical`,
  `Module.IsIdealProjective I M` is `source-facing`,
  and the projective-module instance below is derived API;
* primitive data: the ideal `I`, the module `M`, and for each `a : I` a projective factorization
  of the scalar-action endomorphism `LinearMap.lsmul R M (a : R)`;
* derived API: the instance saying projective modules are `I`-projective, obtained by factoring
  each scalar-action endomorphism through `M` itself.
-/

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

namespace Module

/-- Definition 15.71.4: an `R`-module `M` is `I`-projective if, for every `a : I`, the
scalar-action endomorphism `m ↦ (a : R) • m` factors through a projective `R`-module. -/
class IsIdealProjective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop where
  /-- Multiplication by each element of `I` on `M` factors through a projective `R`-module. -/
  factorsThroughProjective (a : I) :
    (LinearMap.lsmul R M a).FactorsThroughProjective

/-- Projective `R`-modules are `I`-projective for every ideal `I`. -/
instance (I : Ideal R) [Projective R M] : IsIdealProjective I M where
  factorsThroughProjective a :=
    (LinearMap.lsmul R M a).factorsThroughProjective_of_projective

end Module

end

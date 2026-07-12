import Mathlib
import StacksProject_2024.Chap05.Definition_5_10_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace PrimeSpectrum
open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsDomain R] [ValuationRing R]
variable [CommRing S] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "GenericFiber" => Ideal.Fiber (⊥ : Ideal R) S

/- Domain-style sampling:
- primary domain: fibers of finite-type algebras over valuation rings, with the special fiber
  and generic fiber both expressed by the canonical fiber owner `Ideal.Fiber`;
- sampled owner declarations:
  `Ideal.Fiber`,
  `PrimeSpectrum.preimageHomeomorphFiber`,
  `relativeDimensionAt`,
  `EquidimensionalSpace`,
  `ringKrullDim`;
- best owner abstraction: the special fiber should be written as the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, and the generic fiber should live on the same
  owner level `GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`; the tensor model
  `S ⊗[R] FractionRing R` is only a bridge presentation of `GenericFiber`, while the public
  conclusions belong on `PrimeSpectrum ClosedFiber`, `ringKrullDim ClosedFiber`, and
  `ringKrullDim GenericFiber`;
- primitive data: the valuation-ring map `R → S`, injectivity of `algebraMap R S`, the canonical
  closed fiber `ClosedFiber`, and the generic fiber `GenericFiber`;
- derived API: equidimensionality of `PrimeSpectrum ClosedFiber` and the dimension equality
  `ringKrullDim ClosedFiber = ringKrullDim GenericFiber`.

Source/core/bridge triage:
- `source-facing`: the special-fiber equidimensionality and dimension-comparison statements;
- `core/canonical`: `Ideal.Fiber`, `EquidimensionalSpace`, and `ringKrullDim`;
- `bridge/view`: the tensor-product presentations of `ClosedFiber` and `GenericFiber`.
-/

-- Proof sketch: if the special fiber is trivial then its prime spectrum is empty, hence
-- equidimensional. Otherwise apply the quasi-finite presentation from Lemma 10.125.2 near each
-- prime of the special fiber and combine it with the lower bound from Lemma 10.125.6 to identify
-- the local dimension at every prime with the common dimension of the generic fiber.
/-- Lemma 10.125.9: if `R` is a valuation ring, `S` is a finite type domain over `R`, and the
structure map `R → S` is injective, then the canonical closed fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, canonically presented by `κ(R) ⊗[R] S`, has
equidimensional prime spectrum. -/
theorem primeSpectrum_specialFiber_equidimensional_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S)) :
    EquidimensionalSpace (PrimeSpectrum ClosedFiber) := sorry

-- Proof sketch: once the special fiber spectrum is equidimensional with every irreducible
-- component having the generic-fiber dimension, the Krull dimension of the special fiber ring is
-- exactly the Krull dimension of the canonical generic fiber `GenericFiber`, which is presented
-- by the tensor model `S ⊗[R] FractionRing R`.
/-- If the special fiber of a finite type domain over a valuation ring is nontrivial, then its
Krull dimension agrees with that of the canonical generic fiber
`GenericFiber = Ideal.Fiber (⊥ : Ideal R) S`, presented by `S ⊗[R] FractionRing R`. -/
theorem ringKrullDim_specialFiber_eq_genericFiber_of_finiteType_over_valuationRing
    (hRS : Function.Injective (algebraMap R S))
    (hspecial : Nontrivial ClosedFiber) :
    ringKrullDim ClosedFiber = ringKrullDim GenericFiber := sorry

end

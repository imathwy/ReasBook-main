import Mathlib
import stacks_project.Chap05.Definition_5_10_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing TopologicalSpace

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling for formal catenarity of Noetherian local rings:
- primary domain: local commutative algebra of maximal-ideal completions, minimal primes, and
  equidimensional spectra;
- sampled owner declarations:
  `UniversallyCatenaryRing`,
  `IsCatenaryRing`,
  `EquidimensionalSpace`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner for this definition;
  the completed quotient `A^∧ / pA^∧` is only an auxiliary canonical construction and should not
  be promoted to a second public owner;
- primitive data: for each minimal prime `p` of `A`, equidimensionality of `Spec (A^∧ / pA^∧)`;
- derived API: the later bridge from formal catenarity to `UniversallyCatenaryRing`.

Source/core/bridge triage:
- `source-facing`: `IsFormallyCatenaryRing`;
- `core/canonical`: `UniversallyCatenaryRing` and `EquidimensionalSpace`;
- `bridge/view`: the quotient `ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p`.
-/

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-- Definition 15.110.1: a Noetherian local ring is formally catenary if for every minimal prime
`p` of `A`, the prime spectrum of the completion quotient `A^∧ / p A^∧` is equidimensional. -/
class IsFormallyCatenaryRing : Prop extends IsLocalRing A, IsNoetherianRing A where
  equidimensional_completion_quotient (p : minimalPrimes A) :
      EquidimensionalSpace
        (PrimeSpectrum (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1))

end

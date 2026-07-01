import Mathlib
import stacks_project.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace PrimeSpectrum

section

variable (R : Type u) [CommRing R]

/- 
Domain-style sampling:
- primary domain: local Cohen-Macaulayness on `Spec(R)` and the corresponding open locus;
- sampled owner declarations of the same kind:
  `Module.CohenMacaulay`,
  `Module.LocallyCohenMacaulay`,
  `PrimeSpectrum.normalLocus`,
  `Module.flatOverBaseLocus`;
- best owner abstraction: the source-facing point-set owner should be a named locus on
  `PrimeSpectrum R`, with pointwise membership owned by the canonical local self-module predicate
  `Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)`;
- primitive data: the prime `p : PrimeSpectrum R` and its canonical local ring
  `Localization.AtPrime p.asIdeal`;
- derived API: the named locus on `Spec(R)`, its membership lemma, and openness/density theorems
  for finite type algebras over a field.

Source/core/bridge triage:
- `source-facing`: the Cohen-Macaulay locus in `Spec(R)`;
- `core/canonical`: `Localization.AtPrime` and `Module.CohenMacaulay` on the localized
  self-module;
- `bridge/view`: none beyond the membership lemma for the named locus.
-/

/-- The Cohen-Macaulay locus of `Spec(R)`, consisting of the primes whose local rings are
Cohen-Macaulay. -/
def cohenMacaulayLocus : Set (PrimeSpectrum R) :=
  { p | Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) }

/-- Membership in `PrimeSpectrum.cohenMacaulayLocus R` means that the corresponding local ring is
Cohen-Macaulay. -/
@[simp] theorem mem_cohenMacaulayLocus (p : PrimeSpectrum R) :
    p ∈ cohenMacaulayLocus R ↔
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  Iff.rfl

end

end PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

-- Proof sketch: let `q : PrimeSpectrum S` be a point where `S_q` is Cohen-Macaulay. After
-- shrinking to a basic open neighborhood of `q`, choose a finite injective map from a polynomial
-- ring over `k` to `S` as in Lemmas `10.115.5` and `10.116.3`. Then Lemma `10.130.1` identifies
-- the Cohen--Macaulay locus near `q` with the flat locus of `S` over that polynomial ring, and
-- Theorem `10.129.4` shows that this flat locus is open.
/-- Lemma 10.130.2: for a finite type algebra `S` over a field `k`, the set of primes `q` such
that the local ring `S_q` is Cohen-Macaulay is an open subset of `Spec(S)`. -/
theorem isOpen_cohenMacaulayLocus_of_finiteType :
    IsOpen (PrimeSpectrum.cohenMacaulayLocus S) := sorry

end

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/- Domain-style sampling:
- primary domain: flatness loci of finitely presented modules over a base ring on `Spec(S)`;
- sampled owner declarations in the surrounding chapter/project:
  `GenericFlatness.goodLocus`,
  `relativeDimensionAtLELocus`,
  `Ideal.IsFlatOverBaseLocus`,
  `Module.flatOverBaseLocus`;
- best owner abstraction here: the point-set owner
  `Module.flatOverBaseLocus R S M : Set (PrimeSpectrum S)`;
- primitive data: the base ring `R`, the target algebra `S`, and the `S`-module `M` viewed over
  `R`;
- derived API: the membership lemma and the openness theorem under finite-presentation
  hypotheses.

Source/core/bridge triage:
- `source-facing`: the Stacks-theorem openness statement for the flatness locus on `Spec(S)`;
- `core/canonical`: `Module.flatOverBaseLocus`;
- `bridge/view`: downstream closed-subset reformulations such as `Ideal.IsFlatOverBaseLocus`.
-/

/-- The locus in `Spec(S)` where the localized `S`-module `M_q` is flat over the base ring `R`. -/
def flatOverBaseLocus : Set (PrimeSpectrum S) :=
  { q | Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) }

/-- Membership in `flatOverBaseLocus R S M` means that `M_q` is flat over `R`. -/
@[simp] theorem mem_flatOverBaseLocus (q : PrimeSpectrum S) :
    q ∈ flatOverBaseLocus R S M ↔
      Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) :=
  Iff.rfl

variable [Algebra.FinitePresentation R S] [Module.FinitePresentation S M]

/-- Theorem 10.129.4: for a finitely presented ring map `R → S` and a finitely presented
`S`-module `M`, the set of primes `q` of `S` such that the localization `M_q` is flat over `R`
is an open subset of `Spec(S)`. -/
-- Proof sketch: for a prime `q` where `M_q` is flat over `R`, first descend the data to a finite
-- type `ℤ`-model using Lemma `10.127.18` and recover flatness at a stage via Lemma `10.128.3`.
-- Then reduce to the Noetherian case, resolve `M` by a bounded finite free complex, show the top
-- syzygy becomes free near `q`, and apply Lemma `10.129.3` together with the flatness criterion
-- from Lemma `10.99.5` to obtain a basic open neighborhood contained in the flat locus.
theorem isOpen_flatOverBaseLocus_of_finitePresentation :
    IsOpen (flatOverBaseLocus R S M) := sorry

end

end Module

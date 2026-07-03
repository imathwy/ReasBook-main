import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open PrimeSpectrum
open scoped PrimeSpectrum

variable {A : Type u} [CommRing A]
variable (I : Ideal A) [HenselianRing A I] (p : PrimeSpectrum A)

/- Domain-style sampling:
- primary domain: commutative algebra of henselian pairs, quotient spectra, and connectedness of
  closed subsets of `Spec(A)`;
- sampled owner declarations:
  `HenselianRing`,
  `ideal_map_henselianRing_of_isIntegral`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`,
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- best owner abstraction: the source-facing theorem remains the connectedness statement for the
  closed subset `V(p + I)`, but its canonical proof/data flow is owned by the quotient-spectrum
  homeomorphism onto a zero locus, the third-isomorphism equivalence
  `DoubleQuot.quotQuotEquivQuotSup`, and the Chapter 10 connectedness criterion for spectra;
- primitive data: the prime `p`, the ideal `I`, the quotient ring `A ⧸ p.asIdeal`, and the mapped
  ideal `Ideal.map (Ideal.Quotient.mk p.asIdeal) I`;
- derived API: henselianity of the mapped pair, the double-quotient identification with
  `A ⧸ (p.asIdeal ⊔ I)`, and the idempotent-triviality criterion for connected prime spectra.

Source/core/bridge triage:
- `source-facing`: connectedness of the closed subset `V(p + I)` in `Spec(A)`;
- `core/canonical`: `HenselianRing`, `DoubleQuot.quotQuotEquivQuotSup`,
  `Ideal.primeSpectrum_quotient_homeomorph_zeroLocus`, and
  `primeSpectrum_connectedSpace_iff_idempotents_trivial`;
- `bridge/view`: passing from `V(p + I)` to the spectrum of the quotient
  `(A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I`.
-/

-- Proof sketch: by Lemma `15.11.8`, the quotient pair
-- `(A ⧸ p.asIdeal, Ideal.map (Ideal.Quotient.mk p.asIdeal) I)` is henselian. Thus it is enough to
-- prove connectedness of `Spec ((A ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) I)`.
-- Since `A ⧸ p.asIdeal` is a domain, any disconnection would give a nontrivial idempotent in this
-- quotient by Lemma `10.21.4`; Lemma `15.11.6` then lifts that idempotent to a nontrivial
-- idempotent of the domain `A ⧸ p.asIdeal`, a contradiction.
/-- Lemma 15.11.16: for a henselian pair `(A, I)` and a prime ideal `p` of `A`, the closed subset
`V(p + I)` of `Spec(A)` is connected. -/
theorem connectedSpace_zeroLocus_prime_add_of_henselianRing :
    ConnectedSpace (V(((p.asIdeal + I : Ideal A) : Set A))) := by
  sorry

end

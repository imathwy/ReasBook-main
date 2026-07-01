import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling for Lemma 10.21.1:
- primary domain: idempotents and the topology of `Spec(R)`;
- sampled owner declarations:
  `PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem`,
  `PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem`,
  `PrimeSpectrum.isClopen_iff`,
  `PrimeSpectrum.isClopen_iff_zeroLocus`;
- best owner abstraction: the canonical `PrimeSpectrum` owner lemmas describing the basic open and
  zero locus attached to an idempotent;
- primitive data: a commutative ring `R`, an element `e : R`, and the proof that `e` is
  idempotent;
- derived API: clopen descriptions of subsets of `Spec(R)` and the decomposition of `Spec(R)` by
  complementary idempotents.

Source/core/bridge triage:
- `source-facing`: the textbook identification `D(e) = V(1 - e)` and its companion
  `V(e) = D(1 - e)` for an idempotent `e`;
- `core/canonical`: the upstream owner lemmas in `PrimeSpectrum`;
- `bridge/view`: the later clopen and decomposition results that reuse these owner lemmas.

This item adds no new mathematical data, so the file should recall the owner declarations directly
instead of keeping a parallel local theorem or alias.
-/
/- Lemma 10.21.1: for an idempotent `e : R`, the standard open `D(e)` is the zero locus
`V(1 - e)`. Together with `basicOpen_eq_zeroLocus_compl`, this is exactly the
standard decomposition `Spec(R) = D(e) ⨿ D(1 - e)`. -/
recall PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem

/- Companion recall: equivalently, `V(e) = D(1 - e)` for an idempotent `e`. -/
recall PrimeSpectrum.zeroLocus_eq_basicOpen_of_isIdempotentElem

end

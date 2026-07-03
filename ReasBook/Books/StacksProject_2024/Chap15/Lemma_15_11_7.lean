import Mathlib
import StacksProject_2024.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open PrimeSpectrum

variable {A : Type u} [CommRing A]

namespace Ideal

/- Domain-style sampling:
- primary domain: henselian pairs in commutative algebra, viewed through the prime-spectrum closed
  subset `V(I)` and the Chapter 15 idempotent-lifting criterion;
- sampled owner declarations:
  `HenselianRing`,
  `Ideal.HasIntegralAlgebraIdempotentLifting`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`,
  `PrimeSpectrum.zeroLocus_eq_iff`;
- best owner abstraction: the public statement should stay on the canonical owner
  `HenselianRing A I`; the integral-idempotent lifting predicate is derived bridge API from
  Lemma `15.11.6`, and radical equality is the canonical owner-level form of the spectral
  hypothesis `V(I) = V(J)`;
- primitive data: the ideals `I`, `J`, the closed-subset equality `zeroLocus I = zeroLocus J`,
  and for auxiliary integral `A`-algebras `B`, the mapped ideals `Ideal.map (algebraMap A B) I`
  and `Ideal.map (algebraMap A B) J`;
- derived API: the quotient-induced maps on idempotents and the passage from an ideal to its
  radical quotient, which is internal proof infrastructure rather than public owner data.

Source/core/bridge triage:
- `source-facing`: the invariance of henselianity under replacing `I` by an ideal with the same
  closed subset in `Spec A`;
- `core/canonical`: `HenselianRing A I`, `Ideal.HasIntegralAlgebraIdempotentLifting`, and
  `PrimeSpectrum.zeroLocus_eq_iff`;
- `bridge/view`: the zero-locus invariance equivalence for the Chapter 15 integral-idempotent
  lifting owner, proved by passing to the common radical / reduced quotient.
-/

-- If two ideals define the same closed subset of `Spec A`, then the Chapter 15 integral
-- idempotent-lifting criterion is the same for both.
private theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    I.HasIntegralAlgebraIdempotentLifting ↔ J.HasIntegralAlgebraIdempotentLifting := by
  -- For every integral `A`-algebra `B`, the mapped ideals `IB` and `JB` have the same zero locus,
  -- hence the same radical by `PrimeSpectrum.zeroLocus_eq_iff`. Passing from `B / IB` and
  -- `B / JB` to the common reduced quotient by that radical does not change idempotents, because
  -- quotienting by a nilradical extension preserves idempotents. Thus the Chapter 15 owner
  -- `HasIntegralAlgebraIdempotentLifting` depends only on the closed subset `V(I)`.
  sorry

end Ideal

-- Proof sketch: by Lemma `15.11.6`, henselianity of `(A, I)` is equivalent to bijectivity on
-- idempotents after quotienting every integral `A`-algebra `B` by `IB`. If `V(I) = V(J)` in
-- `Spec A`, then for every integral `A`-algebra `B` the extended ideals `IB` and `JB` have the
-- same zero locus, so Lemma `10.21.3` identifies the idempotents of `B/IB` and `B/JB`. Hence the
-- idempotent-lifting criterion is the same for `I` and `J`, and the conclusion follows again from
-- Lemma `15.11.6`.
/-- Lemma 15.11.7: if two ideals `I` and `J` of a commutative ring `A` define the same closed
subset of `Spec A`, then the pair `(A, I)` is henselian if and only if the pair `(A, J)` is
henselian. -/
theorem henselianRing_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    HenselianRing A I ↔ HenselianRing A J := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [HenselianRing A K, K.HasEtaleLiftProperty, Q K, P K, K.SatisfiesGabberRootCriterion]
  have hTfaeI : List.TFAE (T I) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hI : HenselianRing A I ↔ P I := by
    simpa [T] using hTfaeI.out 0 3
  have hIJ : P I ↔ P J :=
    Ideal.hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq I J hV
  have hTfaeJ : List.TFAE (T J) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hJ : HenselianRing A J ↔ P J := by
    simpa [T] using hTfaeJ.out 0 3
  exact (hI.trans hIJ).trans hJ.symm

end

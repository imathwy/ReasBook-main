import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open PrimeSpectrum

variable {A : Type u} [CommRing A]

-- Domain-style sampling pass:
-- * primary domain: commutative algebra on `PrimeSpectrum A`
-- * core/canonical owner: `PrimeSpectrum.zeroLocus` on ideals
-- * sampled owner API:
--   - `PrimeSpectrum.zeroLocus`
--   - `PrimeSpectrum.mem_zeroLocus`
--   - `PrimeSpectrum.zeroLocus_span`
--   - `PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical`
-- Primitive data here is the principal ideal `Ideal.span {(p : A)}`. Its zero locus is the
-- canonical owner for the whole set of primes over `pA`, while an individual prime over `pA`
-- should be exposed as `P : PrimeSpectrum A` together with the containment hypothesis
-- `Ideal.span {(p : A)} ≤ P.asIdeal`.

-- Proof sketch: prime ideals containing `(p)` correspond to prime ideals of the finite quotient
-- `A ⧸ Ideal.span {(p : A)}`, so there can only be finitely many of them.
/-- Lemma 12-12.7-2 (1): there are only finitely many prime ideals of `A` containing `pA`. -/
theorem zeroLocus_span_nat_finite (p : ℕ)
    [Finite (A ⧸ Ideal.span {(p : A)})] :
    Set.Finite (zeroLocus (Ideal.span {(p : A)} : Set A)) := by
  classical
  -- Transport finiteness from `Spec (A / pA)` to the zero locus of `(p)`.
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus (R := A) (Ideal.span {(p : A)})
  letI : Finite (PrimeSpectrum.zeroLocus (R := A) (Ideal.span {(p : A)})) :=
    Finite.of_equiv (PrimeSpectrum (A ⧸ Ideal.span {(p : A)})) e.toEquiv
  exact Set.toFinite _

-- Proof sketch: if `P` contains `p`, then `A ⧸ P` is a quotient of the finite ring
-- `A ⧸ Ideal.span {(p : A)}`. A finite integral domain is a field, so `P` is maximal.
/-- Lemma 12-12.7-2 (2): any prime ideal of `A` containing `(p)` is maximal, so its quotient ring
is a field. -/
theorem isMaximal_of_span_nat_le (p : ℕ)
    [Finite (A ⧸ Ideal.span {(p : A)})]
    (P : PrimeSpectrum A) (hP : Ideal.span {(p : A)} ≤ P.asIdeal) :
    P.asIdeal.IsMaximal := by
  classical
  let I : Ideal A := Ideal.span {(p : A)}
  let e := Ideal.primeSpectrumQuotientOrderIsoZeroLocus (R := A) I
  -- View `P` as a point of the zero locus, then move it to the quotient spectrum.
  have hP_mem : P ∈ PrimeSpectrum.zeroLocus (R := A) (I : Set A) := by
    simpa [I, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hP
  let Q : PrimeSpectrum (A ⧸ I) := e.symm ⟨P, hP_mem⟩
  -- The finite quotient ring is Artinian, so every prime there is maximal.
  haveI : IsArtinianRing (A ⧸ I) := by
    rw [isArtinianRing_iff]
    exact isArtinian_of_finite (R := A ⧸ I) (M := A ⧸ I)
  have hQ_max : Q.asIdeal.IsMaximal := IsArtinianRing.isMaximal_of_isPrime Q.asIdeal
  letI : Q.asIdeal.IsMaximal := hQ_max
  -- Pull maximality back along the quotient map.
  have hcomap : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = P := by
    exact congrArg Subtype.val (e.apply_symm_apply ⟨P, hP_mem⟩)
  have hcomap_ideal : Ideal.comap (Ideal.Quotient.mk I) Q.asIdeal = P.asIdeal := by
    simpa using congrArg PrimeSpectrum.asIdeal hcomap
  simpa [hcomap_ideal] using
    (Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (K := Q.asIdeal))

-- Proof sketch: quotienting the finite ring `A ⧸ Ideal.span {(p : A)}` further by a prime ideal
-- over `p` gives a finite quotient `A ⧸ P`; since `p` maps to zero there and `p` is prime, the
-- quotient has characteristic `p`.
/-- Lemma 12-12.7-2 (3): for a prime ideal `P` of `A` containing `(p)`, the quotient `A ⧸ P` is
finite and has characteristic `p`; combined with part (2), it is a finite field. -/
theorem quotient_finite_and_charP_of_span_nat_le
    (p : ℕ) [Fact p.Prime]
    [Finite (A ⧸ Ideal.span {(p : A)})]
    (P : PrimeSpectrum A) (hP : Ideal.span {(p : A)} ≤ P.asIdeal) :
    Finite (A ⧸ P.asIdeal) ∧ CharP (A ⧸ P.asIdeal) p := by
  -- Quotienting further from `A / pA` onto `A / P` preserves finiteness.
  have hfinite : Finite (A ⧸ P.asIdeal) :=
    Finite.of_surjective (Ideal.Quotient.factor hP) (Ideal.Quotient.factor_surjective hP)
  haveI : Finite (A ⧸ P.asIdeal) := hfinite
  have hP_ne_top : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  haveI : Nontrivial (A ⧸ P.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr hP_ne_top
  -- In the quotient by `P`, the element `p` is already zero.
  have hp_zero : (p : A ⧸ P.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hP (Ideal.subset_span (Set.mem_singleton _))
  refine ⟨hfinite, ?_⟩
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 hp_zero

-- Proof sketch: in the finite ring `A ⧸ Ideal.span {(p : A)}`, the nilradical is nilpotent
-- because finite rings are Artinian. Pulling this nilpotence statement back to `A` identifies the
-- nilradical with the intersection of the prime ideals over `p`.
/-- Lemma 12-12.7-2 (4): some power of the radical of the principal ideal `pA`, equivalently the
intersection of all prime ideals of `A` containing `(p)`, is contained in `pA`. -/
theorem pow_radical_span_nat_le_span_nat (p : ℕ)
    [Finite (A ⧸ Ideal.span {(p : A)})] :
    ∃ N : ℕ, (Ideal.span {(p : A)}).radical ^ N ≤ Ideal.span {(p : A)} := by
  let I : Ideal A := Ideal.span {(p : A)}
  -- Work in the finite quotient, where the nilradical is nilpotent because the ring is Artinian.
  haveI : IsArtinianRing (A ⧸ I) := by
    rw [isArtinianRing_iff]
    exact isArtinian_of_finite (R := A ⧸ I) (M := A ⧸ I)
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A ⧸ I)
  use N
  have hnil : (Ideal.radical (⊥ : Ideal (A ⧸ I))) ^ N = ⊥ := by
    simpa [Ideal.zero_eq_bot, IsArtinianRing.jacobson_eq_radical (R := A ⧸ I)
      (⊥ : Ideal (A ⧸ I))] using hN
  -- Identify the image of `radical I` with the nilradical of the quotient.
  have hrad : Ideal.map (Ideal.Quotient.mk I) I.radical = Ideal.radical (⊥ : Ideal (A ⧸ I)) := by
    simpa [Ideal.map_bot] using
      (Ideal.map_radical_of_surjective (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (le_of_eq Ideal.mk_ker))
  have hmap_pow : Ideal.map (Ideal.Quotient.mk I) (I.radical ^ N) = ⊥ := by
    rw [Ideal.map_pow, hrad, hnil]
  -- Pull the vanishing statement back through the quotient map.
  simpa [I, Ideal.mk_ker] using
    (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk I)).mp hmap_pow

end

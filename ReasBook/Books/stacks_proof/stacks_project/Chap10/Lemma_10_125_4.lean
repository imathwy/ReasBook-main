import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: quasi-finite localizations of finite-type commutative-algebra maps and Krull
  dimension comparisons at primes;
- sampled owner declarations:
  `Algebra.QuasiFiniteAt`,
  `Ideal.under`,
  `ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver`,
  `ringKrullDim_le_of_isIntegral`;
- best owner abstraction: the primewise owner `Algebra.QuasiFiniteAt R q`, with the base prime
  recovered canonically as `q.under R`;
- primitive data: the target prime `q` and the canonical quasi-finite owner structure;
- derived API: the base prime `p` together with `[q.LiesOver p]`, which are redundant once `q` is
  fixed.

This item is therefore kept at the `source-facing` layer as the local-dimension inequality, but
its public interface is refined to the canonical owner shape indexed only by `q`.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 125 4: contraction of prime ideals is monotone on spectra. -/
private lemma primeSpectrumComap_mono {P Q : PrimeSpectrum S} (hPQ : P ≤ Q) :
    PrimeSpectrum.comap (algebraMap R S) P ≤ PrimeSpectrum.comap (algebraMap R S) Q := by
  -- The specialization order is ideal inclusion, and contraction preserves inclusions.
  simpa [PrimeSpectrum.comap_asIdeal] using
    (Ideal.comap_mono (f := algebraMap R S) hPQ)

/-- Helper for Chap10 Lemma 10 125 4: below a quasi-finite point, contraction is strictly
monotone. -/
private lemma primeSpectrumComap_iic_strictMono_of_quasiFiniteAt
    (q : PrimeSpectrum S) [Algebra.QuasiFiniteAt R q.asIdeal] :
    StrictMono (fun Q : Set.Iic q =>
      (⟨PrimeSpectrum.comap (algebraMap R S) Q.1, primeSpectrumComap_mono (R := R) Q.2⟩ :
        Set.Iic (PrimeSpectrum.comap (algebraMap R S) q))) := by
  -- Monotonicity gives the weak comparison; equal contractions contradict quasi-finiteness.
  intro P Q hPQ
  refine lt_of_le_of_ne (primeSpectrumComap_mono (R := R) hPQ.le) ?_
  intro hEq
  have hComap : PrimeSpectrum.comap (algebraMap R S) P.1 =
      PrimeSpectrum.comap (algebraMap R S) Q.1 := by
    exact congrArg Subtype.val hEq
  have hUnder : P.1.asIdeal.under R = Q.1.asIdeal.under R := by
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hComap
  have hPQIdeal : P.1.asIdeal ≤ Q.1.asIdeal := hPQ.le
  have hQq : Q.1.asIdeal ≤ q.asIdeal := Q.2
  letI : Algebra.QuasiFiniteAt R Q.1.asIdeal := Algebra.QuasiFiniteAt.of_le (R := R) hQq
  have hIdeal : P.1.asIdeal = Q.1.asIdeal := by
    exact Algebra.QuasiFiniteAt.eq_of_le_of_under_eq (R := R) hPQIdeal hUnder
  apply hPQ.ne
  exact Subtype.ext (PrimeSpectrum.ext hIdeal)

/-- Helper for Chap10 Lemma 10 125 4: quasi-finite contraction does not decrease prime height. -/
private lemma primeHeight_le_comap_primeHeight_of_quasiFiniteAt
    (q : PrimeSpectrum S) [Algebra.QuasiFiniteAt R q.asIdeal] :
    q.asIdeal.primeHeight ≤ (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.primeHeight := by
  -- Heights are Krull dimensions of lower intervals, so the strict chain map gives the inequality.
  have hdim : Order.krullDim (Set.Iic q) ≤
      Order.krullDim (Set.Iic (PrimeSpectrum.comap (algebraMap R S) q)) := by
    exact Order.krullDim_le_of_strictMono _
      (primeSpectrumComap_iic_strictMono_of_quasiFiniteAt (R := R) q)
  have hheight : ((q.asIdeal.primeHeight : ℕ∞) : WithBot ℕ∞) ≤
      (((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.primeHeight : ℕ∞) :
        WithBot ℕ∞) := by
    rw [Ideal.primeHeight, Ideal.primeHeight]
    rw [Order.height_eq_krullDim_Iic, Order.height_eq_krullDim_Iic]
    exact hdim
  exact WithBot.coe_le_coe.mp hheight

-- Route correction: avoid the dimension-addition route, which requires Noetherian hypotheses not
-- present here; quasi-finiteness instead makes contraction strictly preserve chains below `q`.
/-- Chap10 Lemma 10 125 4 (Lemma 10.125.4): for a finite type ring map `R → S`, if `q` is a prime ideal of `S` and the
map is quasi-finite at `q`, then the Krull dimension of the local ring `S_q` is at most the Krull
dimension of the local ring `R_(q ∩ R)`. -/
@[stacks 00QF]
theorem ringKrullDim_localizationAtPrime_le_of_quasiFiniteAt
    [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    ringKrullDim (Localization.AtPrime q) ≤ ringKrullDim (Localization.AtPrime (q.under R)) := by
  -- Rewrite local dimensions as heights, then apply the height comparison for contraction.
  have hheight :=
    primeHeight_le_comap_primeHeight_of_quasiFiniteAt (R := R) (S := S)
      (q := (⟨q, inferInstance⟩ : PrimeSpectrum S))
  have hheight' : q.primeHeight ≤ (q.under R).primeHeight := by
    simpa [PrimeSpectrum.comap_asIdeal, Ideal.under_def] using hheight
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R)
      (Localization.AtPrime (q.under R)),
    Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight]
  exact_mod_cast hheight'

end

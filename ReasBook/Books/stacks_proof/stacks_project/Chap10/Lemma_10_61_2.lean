import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_17_2
import stacks_proof.stacks_project.Chap10.Lemma_10_60_4
import stacks_proof.stacks_project.Chap10.Lemma_10_61_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Finite (PrimeSpectrum R)]

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.61.2: a quotient of a ring with finite prime spectrum again has finite
prime spectrum. -/
private theorem finite_primeSpectrum_quotient (I : Ideal R) :
    Finite (PrimeSpectrum (R ⧸ I)) := by
  -- Transport finiteness across the canonical order isomorphism with the zero locus `V(I)`.
  let e : PrimeSpectrum (R ⧸ I) ≃o PrimeSpectrum.zeroLocus (R := R) I :=
    Ideal.primeSpectrumQuotientOrderIsoZeroLocus I
  exact Finite.of_injective (f := e) e.injective

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.61.2: localizing at a prime ideal preserves finiteness of the prime
spectrum. -/
private theorem finite_primeSpectrum_localizationAtPrime (p : PrimeSpectrum R) :
    Finite (PrimeSpectrum (Localization.AtPrime p.asIdeal)) := by
  -- The spectrum of the localization identifies with the lower interval `Set.Iic p`.
  let e :
      PrimeSpectrum (Localization.AtPrime p.asIdeal) ≃o Set.Iic p :=
    IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p.asIdeal) p.asIdeal
  exact Finite.of_injective (f := e) e.injective

omit [IsNoetherianRing R] [Finite (PrimeSpectrum R)] in
/-- Helper for Lemma 10.61.2: the Krull dimension of a prime quotient is the coheight of the
corresponding point of the ambient spectrum. -/
private theorem ringKrullDim_quotient_eq_coheight (q : Ideal R) [q.IsPrime] :
    ringKrullDim (R ⧸ q) = Order.coheight (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
  -- Rewrite the quotient spectrum as the upper interval above `q`.
  let x : PrimeSpectrum R := ⟨q, inferInstance⟩
  rw [ringKrullDim_quotient]
  have hzero : PrimeSpectrum.zeroLocus (q : Set R) = Set.Ici x := by
    ext p
    change q ≤ p.asIdeal ↔ x ≤ p
    rfl
  rw [hzero]
  exact (Order.coheight_eq_krullDim_Ici x).symm

/-- Helper for Lemma 10.61.2: a Noetherian domain with finite prime spectrum has Krull dimension
at most `1`. -/
private theorem krullDimLE_one_of_finite_primeSpectrum_domain
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Finite (PrimeSpectrum A)] :
    Ring.KrullDimLE 1 A := by
  -- Bound the global dimension by checking every maximal localization, as in the source proof.
  refine Ring.krullDimLE_of_isLocalization_maximal
    (R := A) (Rₚ := fun P _ => Localization.AtPrime P) ?_
  intro P hP
  letI : Finite (PrimeSpectrum (Localization.AtPrime P)) :=
    finite_primeSpectrum_localizationAtPrime (R := A) ⟨P, hP.isPrime⟩
  refine Ring.krullDimLE_iff.mpr ?_
  by_contra hdim
  -- If the localized ring had dimension at least `2`, Lemma `10.61.1` would force its whole
  -- spectrum to be infinite, contradicting finiteness.
  have htwo : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime P) := by
    simpa using Order.succ_le_of_lt (lt_of_not_ge hdim)
  have huniv_ne_bot :
      (⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) ≠ ⊥ := by
    intro htop
    have hmem :
        (⊥ : PrimeSpectrum (Localization.AtPrime P)) ∈
          ((⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) :
            Set (PrimeSpectrum (Localization.AtPrime P))) := by
      simp
    simpa [htop] using hmem
  have hinfinite :
      Set.Infinite
        ((⊤ : TopologicalSpace.Opens (PrimeSpectrum (Localization.AtPrime P))) :
          Set (PrimeSpectrum (Localization.AtPrime P))) :=
    infinite_open_subset_of_local_noetherian_domain_of_two_le_ringKrullDim
      (R := Localization.AtPrime P) ⊤ huniv_ne_bot htwo
  have hfinite_univ :
      Set.Finite (Set.univ : Set (PrimeSpectrum (Localization.AtPrime P))) :=
    Set.toFinite _
  exact hfinite_univ.not_infinite (by simpa using hinfinite)

/-- Helper for Lemma 10.61.2: every prime ideal of a Noetherian ring with finite spectrum has
coheight at most `1`. -/
private theorem coheight_le_one_of_prime (p : PrimeSpectrum R) :
    Order.coheight p ≤ 1 := by
  -- Choose a minimal prime below `p` and compare coheights with the corresponding domain quotient.
  obtain ⟨q, hq, hqp⟩ :=
    Ideal.exists_minimalPrimes_le (R := R) (I := (⊥ : Ideal R)) (J := p.asIdeal) bot_le
  haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hq
  let qPoint : PrimeSpectrum R := ⟨q, inferInstance⟩
  letI : IsDomain (R ⧸ q) := (Ideal.Quotient.isDomain_iff_prime (I := q)).2 inferInstance
  letI : Finite (PrimeSpectrum (R ⧸ q)) := finite_primeSpectrum_quotient (R := R) q
  have hqdim :
      ringKrullDim (R ⧸ q) ≤ 1 := by
    exact Ring.krullDimLE_iff.mp (krullDimLE_one_of_finite_primeSpectrum_domain (A := R ⧸ q))
  have hqcoheight : Order.coheight qPoint ≤ 1 := by
    simpa [qPoint, ringKrullDim_quotient_eq_coheight (R := R) q] using hqdim
  exact le_trans (Order.coheight_anti (show qPoint ≤ p from hqp)) hqcoheight

-- Layering for this item:
-- * source-facing: a Noetherian ring with finite prime spectrum has dimension at most `1`.
-- * core/canonical owner: `Ring.KrullDimLE 1 R`.
-- * bridge/view: `ringKrullDim R ≤ 1` is recovered from the owner instance by
--   `Ring.krullDimLE_iff`.
-- Primitive data are exactly the assumptions `[IsNoetherianRing R]` and
-- `[Finite (PrimeSpectrum R)]`; the inequality theorem below is derived API from the owner
-- abstraction.

-- Proof sketch: first treat the local domain case using Lemma `10.61.1`, which rules out
-- Krull dimension at least `2` because a finite prime spectrum cannot contain an infinite nonempty
-- open subset. Then localize a domain at each maximal ideal and apply Lemma `10.60.4` to bound
-- `ringKrullDim R` by the supremum of maximal heights. For a general Noetherian ring, pass to each
-- quotient by a minimal prime and use Lemma `10.17.2` to see that every prime contains a minimal
-- prime, so all prime chains still have length at most `1`.
/-- Owner-level form of Lemma 10.61.2. The source-facing inequality
`ringKrullDim R ≤ 1` is the companion theorem below, obtained via `Ring.krullDimLE_iff`. -/
instance krullDimLE_one_of_finite_primeSpectrum : Ring.KrullDimLE 1 R := by
  -- Separate the degenerate ring from the nontrivial case before applying the primewise argument.
  cases subsingleton_or_nontrivial R with
  | inl hR =>
      letI := hR
      exact Ring.krullDimLE_iff.mpr <| by
        simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hR =>
      letI := hR
      -- Bound `ringKrullDim R` by bounding the coheight of every prime ideal by `1`.
      refine Ring.krullDimLE_iff.mpr ?_
      rw [ringKrullDim, Order.krullDim_eq_iSup_coheight]
      refine iSup_le fun p => ?_
      exact WithBot.coe_le_coe.mpr (coheight_le_one_of_prime (R := R) p)

end

section

variable {R : Type u} [CommRing R]

/-- Lemma 10.61.2, source-facing form: a Noetherian ring with finitely many prime ideals has
Krull dimension at most `1`. -/
@[stacks 0ALV]
theorem ringKrullDim_le_one_of_finite_primeSpectrum [IsNoetherianRing R] [Finite (PrimeSpectrum R)] :
    ringKrullDim R ≤ 1 :=
  Ring.krullDimLE_iff.mp inferInstance

end

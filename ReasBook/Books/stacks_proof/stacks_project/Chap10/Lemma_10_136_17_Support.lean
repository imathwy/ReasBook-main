import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_112_5
import stacks_proof.stacks_project.Chap10.Definition_10_135_1
import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_135_2
import stacks_proof.stacks_project.Chap10.Lemma_10_136_3
import stacks_proof.stacks_project.Chap10.Lemma_10_136_4
import stacks_proof.stacks_project.Chap10.Lemma_10_136_9
import stacks_proof.stacks_project.Chap10.Lemma_10_136_15

universe u

section

namespace Algebra

/-- Helper for Chap10 Lemma 10 136 17: localizing a ring at a prime does not increase Krull
dimension. -/
private theorem ringKrullDim_localizationAtPrime_le_ringKrullDim
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] :
    ringKrullDim (Localization.AtPrime I) ≤ ringKrullDim A := by
  -- Proof comment: rewrite the localized Krull dimension as the height of the prime and then
  -- apply the global height bound.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height I (Localization.AtPrime I)]
  exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'

/-- Helper for Chap10 Lemma 10 136 17: the local dimension inequality applies to a maximal ideal
once the two presentations provide the required finite-type hypotheses. -/
private theorem fieldCompPresentation_localizedHeightBound_of_isMaximal
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {n c n' c' : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (Q : Algebra.Presentation A B (Fin n') (Fin c'))
    (m : Ideal B) (hm : m.IsMaximal) :
    ringKrullDim (Localization.AtPrime m) ≤
      ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) ⟨m, hm.isPrime⟩).asIdeal) +
        ringKrullDim (fiberLocalRingAt A B ⟨m, hm.isPrime⟩) := by
  let q : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  letI : IsNoetherianRing k := IsNoetherianRing.of_finite k k
  letI : Algebra.FinitePresentation k A := P.finitePresentation_of_isFinite
  letI : Algebra.FinitePresentation A B := Q.finitePresentation_of_isFinite
  letI : Algebra.FiniteType k A := Algebra.FiniteType.of_finitePresentation
  letI : Algebra.FiniteType A B := Algebra.FiniteType.of_finitePresentation
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hm_liesOver : m.LiesOver p.asIdeal := by
    -- Proof comment: the contracted prime of `m` is exactly `p`, so the local dimension
    -- inequality applies to the pair `(p, m)`.
    simpa [p] using (Ideal.over_under (A := A) m : m.LiesOver (m.under A))
  -- Proof comment: apply the local dimension inequality at the maximal ideal `m`.
  simpa [p, q] using
    ringKrullDim_localizationAtPrime_le_ringKrullDim_localizationAtPrime_add_ringKrullDim_fiberLocalRingAt_of_liesOver
      (R := A) (S := B) p.asIdeal m hm_liesOver

/-- Helper for Chap10 Lemma 10 136 17: localizing the source presentation fiber does not exceed
the ambient presentation dimension. -/
private theorem fieldCompPresentation_localizedBaseDim_le_presentationDimension
    {A : Type*} [CommRing A]
    {k : Type*} [Field k] [Algebra k A]
    {n c : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (hP : ringKrullDim A = P.dimension)
    (p : PrimeSpectrum A) :
    ringKrullDim (Localization.AtPrime p.asIdeal) ≤ P.dimension := by
  -- Proof comment: localizing at `p` does not increase dimension, and `P` realizes the dimension
  -- of `A`.
  calc
    ringKrullDim (Localization.AtPrime p.asIdeal) ≤ ringKrullDim A :=
      ringKrullDim_localizationAtPrime_le_ringKrullDim p.asIdeal
    _ = P.dimension := hP

/-- Helper for Chap10 Lemma 10 136 17: the local fiber ring dimension is bounded by the fiber
dimension promised by the relative complete-intersection presentation. -/
private theorem fieldCompPresentation_fiberLocalDim_le_presentationDimension
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {n' c' : ℕ}
    (Q : Algebra.Presentation A B (Fin n') (Fin c'))
    (hQ : Q.IsRelativeGlobalCompleteIntersection)
    (q : PrimeSpectrum B) :
    ringKrullDim (fiberLocalRingAt A B q) ≤ Q.dimension := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  -- Proof comment: the local fiber ring is a localization of the fiber at `p`, so its
  -- dimension is bounded by the relative-GCI fiber dimension of `Q`.
  calc
    ringKrullDim (fiberLocalRingAt A B q)
        = ringKrullDim (Localization.AtPrime (fiberPrimeAt A B q).asIdeal) := by
            rfl
    _ ≤ ringKrullDim (p.asIdeal.Fiber B) :=
      ringKrullDim_localizationAtPrime_le_ringKrullDim (fiberPrimeAt A B q).asIdeal
    _ = Q.dimension := by
      exact hQ p ⟨fiberPrimeAt A B q⟩

/-- Helper for Chap10 Lemma 10 136 17: the local dimension formula gives the additive upper bound
in the field-level composition argument. -/
private theorem fieldCompPresentation_height_le_sumDimension_of_isMaximal
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {n c n' c' : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (Q : Algebra.Presentation A B (Fin n') (Fin c'))
    (hP : ringKrullDim A = P.dimension)
    (hQ : Q.IsRelativeGlobalCompleteIntersection)
    (m : Ideal B) (hm : m.IsMaximal) :
    (m.height : WithBot ℕ∞) ≤ P.dimension + Q.dimension := by
  let q : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hlocal :
      ringKrullDim (Localization.AtPrime m) ≤
        ringKrullDim (Localization.AtPrime p.asIdeal) +
          ringKrullDim (fiberLocalRingAt A B q) := by
    exact fieldCompPresentation_localizedHeightBound_of_isMaximal (P := P) (Q := Q) m hm
  have hpdim :
      ringKrullDim (Localization.AtPrime p.asIdeal) ≤ P.dimension := by
    exact fieldCompPresentation_localizedBaseDim_le_presentationDimension (P := P) hP p
  have hfiberdim :
      ringKrullDim (fiberLocalRingAt A B q) ≤ Q.dimension := by
    exact fieldCompPresentation_fiberLocalDim_le_presentationDimension (Q := Q) hQ q
  -- Proof comment: rewrite the maximal-ideal height as a local Krull dimension and combine the
  -- local bound with the two ambient dimension bounds.
  calc
    (m.height : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime m) := by
      symm
      exact IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)
    _ ≤ ringKrullDim (Localization.AtPrime p.asIdeal) + ringKrullDim (fiberLocalRingAt A B q) :=
      hlocal
    _ ≤ P.dimension + Q.dimension :=
      add_le_add hpdim hfiberdim

/-- Helper for Chap10 Lemma 10 136 17: the field-level composition argument bounds the target
Krull dimension by the sum of the two presentation dimensions. -/
private theorem fieldCompPresentation_ringKrullDim_le_sumDimension
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {n c n' c' : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (Q : Algebra.Presentation A B (Fin n') (Fin c'))
    (hP : ringKrullDim A = P.dimension)
    (hQ : Q.IsRelativeGlobalCompleteIntersection) :
    ringKrullDim B ≤ P.dimension + Q.dimension := by
  -- Proof comment: reduce the global upper bound to the maximal-ideal case handled separately.
  refine (ringKrullDim_le_iff_isMaximal_height_le (P.dimension + Q.dimension)).2 ?_
  intro m hm
  exact fieldCompPresentation_height_le_sumDimension_of_isMaximal
    (P := P) (Q := Q) hP hQ m hm

/-- Helper for Chap10 Lemma 10 136 17: the natural-number bounds in the field-level presentation
argument force the expected presentation dimension. -/
private theorem fieldCompPresentation_nat_eq_dimension
    {n c n' c' d : ℕ}
    (hupper : d ≤ (n' + n) - (c' + c))
    (hlower : n' + n ≤ d + (c' + c)) :
    d = (n' + n) - (c' + c) := by
  -- Proof comment: this is the isolated arithmetic tail of the Krull-dimension argument.
  omega

/-- Helper for Chap10 Lemma 10 136 17: a finite presentation over a field gives the standard
quotient-model lower bound on the target Krull dimension. -/
private theorem presentation_relation_bound
    {k : Type*} [Field k]
    {B : Type*} [CommRing B] [Algebra k B]
    {n c : ℕ}
    (P : Algebra.Presentation k B (Fin n) (Fin c))
    (hB : Nonempty (PrimeSpectrum B)) :
    ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B + c := by
  let _ : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp hB
  rcases presentation_relation_quotient_model P with ⟨e⟩
  letI :
      Nontrivial
        ((MvPolynomial (Fin n) k) ⧸ Ideal.span (Set.range P.relation)) :=
    e.toEquiv.nontrivial
  -- Proof comment: transport the standard polynomial-quotient inequality across the quotient
  -- model attached to the chosen presentation.
  simpa [ringKrullDim_eq_of_ringEquiv e.toRingEquiv] using
    IsGlobalCompleteIntersection.mvPolynomial_quotient_le_dim_add_relation_count
      (f := P.relation)

/-- Helper for Chap10 Lemma 10 136 17: a finite upper bound together with the quotient-model
relation bound forces a field-valued presentation to realize the target Krull dimension. -/
private theorem ringKrullDim_eq_presentationDimension_of_nonempty_of_le
    {k : Type*} [Field k]
    {B : Type*} [CommRing B] [Algebra k B]
    {n c : ℕ}
    (P : Algebra.Presentation k B (Fin n) (Fin c))
    (hupper : ringKrullDim B ≤ P.dimension)
    (hB : Nonempty (PrimeSpectrum B)) :
    ringKrullDim B = P.dimension := by
  let _ : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp hB
  have hbot : ringKrullDim B ≠ ⊥ := by
    -- Proof comment: a nontrivial ring has nonnegative Krull dimension, so `⊥` is excluded.
    intro hbot'
    simpa [hbot'] using (ringKrullDim_nonneg_of_nontrivial (R := B))
  have htop : ringKrullDim B ≠ ⊤ := by
    -- Proof comment: the explicit upper bound by a natural number shows the dimension is finite.
    exact ne_of_lt <| lt_of_le_of_lt hupper <|
      WithBot.coe_lt_coe.mpr (ENat.coe_lt_top P.dimension)
  let d : ℕ := ((ringKrullDim B).unbot hbot).toNat
  have hdim : ringKrullDim B = d := by
    -- Proof comment: replace the finite `WithBot ℕ∞` dimension by its natural-number value once.
    have hneTop : (ringKrullDim B).unbot hbot ≠ ⊤ := by
      intro h
      exact htop (by
        simpa [WithBot.coe_unbot] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) h)
    have hdim' : ((ringKrullDim B).unbot hbot : WithBot ℕ∞) = d := by
      simpa [d] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim B = (ringKrullDim B).unbot hbot := by
        exact (WithBot.coe_unbot (ringKrullDim B) hbot).symm
      _ = d := hdim'
  have hupper_nat : d ≤ P.dimension := by
    -- Proof comment: after the normalization, the upper bound becomes an ordinary nat inequality.
    simpa [hdim] using hupper
  have hrelation_nat : n ≤ d + c := by
    -- Proof comment: rewrite the quotient-model lower bound into a nat inequality.
    have hrelation :
        ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B + c :=
      presentation_relation_bound P hB
    have hle' :
        (((n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((d + c : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hdim, ← WithBot.coe_add, Nat.cast_add] using hrelation
    have hle_enat : (n : ℕ∞) ≤ (d + c : ℕ∞) := WithBot.coe_le_coe.mp hle'
    rwa [← ENat.coe_add, ENat.coe_le_coe] at hle_enat
  have hdim_nat : d = P.dimension := by
    -- Proof comment: the arithmetic helper closes the normalized dimension count.
    have hPdim : P.dimension = n - c := presentation_dimension_eq_fin_sub P
    rw [hPdim] at hupper_nat
    exact fieldCompPresentation_nat_eq_dimension hupper_nat hrelation_nat
  simpa [hdim_nat] using hdim

/-- Helper for Chap10 Lemma 10 136 17: over a field, composing a global complete-intersection
presentation with a relative global complete-intersection presentation gives the expected Krull
dimension formula on the target. -/
theorem fieldCompPresentation_ringKrullDim
    {k : Type*} [Field k]
    {A : Type*} [CommRing A] [Algebra k A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    {n c n' c' : ℕ}
    (P : Algebra.Presentation k A (Fin n) (Fin c))
    (Q : Algebra.Presentation A B (Fin n') (Fin c'))
    (hP : ringKrullDim A = P.dimension)
    (hQ : Q.IsRelativeGlobalCompleteIntersection)
    (hcompDim : P.dimension + Q.dimension = (Q.comp P).dimension)
    (hB : Nonempty (PrimeSpectrum B)) :
    ringKrullDim B = (Q.comp P).dimension := by
  -- Proof comment: the local upper bound plus the explicit dimension-compatibility hypothesis
  -- reduce the theorem to the field-level closing lemma for the composite presentation.
  have hupper : ringKrullDim B ≤ (Q.comp P).dimension := by
    calc
      ringKrullDim B ≤ P.dimension + Q.dimension :=
        fieldCompPresentation_ringKrullDim_le_sumDimension
          (P := P) (Q := Q) hP hQ
      _ = (Q.comp P).dimension := hcompDim
  exact ringKrullDim_eq_presentationDimension_of_nonempty_of_le
    (P := Q.comp P) hupper hB

end Algebra

end

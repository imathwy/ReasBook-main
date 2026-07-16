import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_135_5
import stacks_proof.stacks_project.Chap10.Lemma_10_135_4
import stacks_proof.stacks_project.Chap10.Lemma_10_126_7
import stacks_proof.stacks_project.Chap10.Lemma_10_135_2
import stacks_proof.stacks_project.Chap10.Lemma_10_135_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Algebra
open PolynomialPresentationAtPrime

universe u v

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- Helper for Chap10 Lemma 10 135 8: four propositions form a `TFAE` once the first three
clauses are all identified with the third and the third is identified with the fourth. -/
private theorem tfae_four_of_equiv
    {A B C D : Prop} (hAC : A ↔ C) (hBC : B ↔ C) (hCD : C ↔ D) :
    List.TFAE [A, B, C, D] := by
  -- Proof comment: after unfolding `TFAE`, membership in the four-element list is a finite
  -- case split and the supplied equivalences solve all cases propositionally.
  rw [List.TFAE]
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  tauto

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 8: the finite height defect of a polynomial presentation is
unchanged by replacing it with the natural number obtained by `ENat.toNat`. -/
private lemma heightSub_eq_coe_toNat_of_polynomialPresentation
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (q : PrimeSpectrum S) :
    (PolynomialPresentationAtPrime.prime π q).asIdeal.height - q.asIdeal.height =
      (ENat.toNat
        ((PolynomialPresentationAtPrime.prime π q).asIdeal.height - q.asIdeal.height) : ℕ∞) := by
  -- Proof comment: the source and presentation primes have finite height in these noetherian
  -- finite-type rings, so their `ℕ∞` difference is finite and equals its `toNat` coercion.
  classical
  have hprime_ne_top :
      (PolynomialPresentationAtPrime.prime π q).asIdeal.height ≠ ⊤ := by
    exact Ideal.height_ne_top (I := (PolynomialPresentationAtPrime.prime π q).asIdeal)
      (PolynomialPresentationAtPrime.prime π q).2.ne_top
  have hsub_ne_top :
      (PolynomialPresentationAtPrime.prime π q).asIdeal.height - q.asIdeal.height ≠ ⊤ := by
    intro htop
    exact hprime_ne_top ((ENat.sub_eq_top_iff.mp htop).1)
  exact (ENat.coe_toNat hsub_ne_top).symm

/-- Helper for Chap10 Lemma 10 135 8: a finite set whose span is the unit ideal has an element
outside any given prime ideal. -/
private lemma exists_notMem_of_span_eq_top_of_prime
    {A : Type*} [CommRing A] (s : Finset A) {p : Ideal A} [p.IsPrime]
    (hs : Ideal.span (s : Set A) = ⊤) :
    ∃ a ∈ s, a ∉ p := by
  -- Proof comment: if every cover element lay in the prime, the generated ideal would be
  -- contained in the prime, forcing the prime to be the whole ring.
  by_contra h
  push Not at h
  have hspan_le : Ideal.span (s : Set A) ≤ p := by
    exact Ideal.span_le.mpr fun x hx ↦ h x hx
  have htop_le : (⊤ : Ideal A) ≤ p := by
    rw [← hs]
    exact hspan_le
  have hone : (1 : A) ∈ p := htop_le trivial
  have htop : p = ⊤ := (Ideal.eq_top_iff_one p).mpr hone
  exact (Ideal.IsPrime.ne_top (show p.IsPrime from inferInstance)) htop

/-- Helper for Chap10 Lemma 10 135 8: a prime avoiding an away parameter has a prime in the
away localization lying over it. -/
private lemma exists_primeSpectrum_away_comap_eq_of_notMem
    {A : Type*} [CommRing A] (p : PrimeSpectrum A) {f : A} (hf : f ∉ p.asIdeal) :
    ∃ q : PrimeSpectrum (Localization.Away f),
      PrimeSpectrum.comap (algebraMap A (Localization.Away f)) q = p := by
  -- Proof comment: the image of `Spec(A_f)` is exactly the basic open `D(f)`.
  have hp_range : p ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    simpa [PrimeSpectrum.mem_basicOpen] using hf
  exact Set.mem_range.mp hp_range

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 8: an iterated away localization of a principal open is a
single principal open of the original ring, using the numerator of a chosen section. -/
private lemma single_original_awayAlgEquiv
    (g : S) (u : Localization.Away g) :
    let h : S := g * (IsLocalization.Away.sec g u).1
    Nonempty (Localization.Away u ≃ₐ[k] Localization.Away h) := by
  -- Proof comment: replace the iterated parameter by an associated numerator, then use the
  -- standard product formula for consecutive away localizations.
  let a : S := (IsLocalization.Away.sec g u).1
  let h : S := g * a
  let hassoc :
      Associated (algebraMap S (Localization.Away g) a) u :=
    IsLocalization.Away.associated_sec_fst g u
  letI :
      IsLocalization.Away u (Localization.Away (algebraMap S (Localization.Away g) a)) :=
    IsLocalization.Away.of_associated hassoc
  let eIter :
      Localization.Away u ≃ₐ[k] Localization.Away (algebraMap S (Localization.Away g) a) :=
    (Localization.algEquiv
      (Submonoid.powers u)
      (Localization.Away (algebraMap S (Localization.Away g) a))).restrictScalars k
  letI :
      IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)) := by
    simpa [h]
      using
        (inferInstance :
          IsLocalization.Away h (Localization.Away (algebraMap S (Localization.Away g) a)))
  let eSingle :
      Localization.Away (algebraMap S (Localization.Away g) a) ≃ₐ[k] Localization.Away h :=
    (Localization.algEquiv
      (Submonoid.powers h)
      (Localization.Away (algebraMap S (Localization.Away g) a))).symm.restrictScalars k
  exact ⟨eIter.trans eSingle⟩

/-- Helper for Chap10 Lemma 10 135 8: if an element of an away localization avoids a lifted
prime, then the corresponding cleared denominator avoids the original prime. -/
private lemma notMem_original_away_of_iterated_away
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal)
    {u : Localization.Away g} (qAway : PrimeSpectrum (Localization.Away g))
    (hqAway : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) qAway = q)
    (hu : u ∉ qAway.asIdeal) :
    g * (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
  -- Proof comment: membership of the section numerator would map into the lifted prime and, by
  -- associatedness with `u`, force `u` itself into that prime.
  have hsec_not_mem_away :
      algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∉ qAway.asIdeal := by
    intro hsec_mem
    have hu_mem : u ∈ qAway.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst g u)).mp hsec_mem
    exact hu hu_mem
  have hsec_not_mem :
      (IsLocalization.Away.sec g u).1 ∉ q.asIdeal := by
    intro hsec_mem
    have hqAwayIdeal :
        Ideal.comap (algebraMap S (Localization.Away g)) qAway.asIdeal = q.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
    have hmap_mem :
        algebraMap S (Localization.Away g) (IsLocalization.Away.sec g u).1 ∈
          qAway.asIdeal := by
      have :
          (IsLocalization.Away.sec g u).1 ∈
            Ideal.comap (algebraMap S (Localization.Away g)) qAway.asIdeal := by
        rw [hqAwayIdeal]
        exact hsec_mem
      simpa [Ideal.mem_comap] using this
    exact hsec_not_mem_away hmap_mem
  -- Proof comment: both factors avoid the prime, hence so does their product.
  exact q.2.mul_notMem hg hsec_not_mem

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 8: a local complete-intersection principal-open
neighbourhood can be shrunk to a global complete-intersection principal-open neighbourhood. -/
private lemma globalNearPrime_of_localCompleteIntersectionAway
    (q : PrimeSpectrum S) {g : S} (hg : g ∉ q.asIdeal)
    (hlocal : IsLocalCompleteIntersection k (Localization.Away g)) :
    isGlobalCompleteIntersectionNearPrime k q := by
  -- Route correction: instead of transporting a local-CI chart directly to the stalk, first
  -- shrink the local-CI finite cover to a global-CI basic open around the lifted prime.
  classical
  obtain ⟨qAway, hqAway⟩ := exists_primeSpectrum_away_comap_eq_of_notMem q hg
  rcases hlocal.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  obtain ⟨u, hus, hu⟩ :=
    exists_notMem_of_span_eq_top_of_prime s (p := qAway.asIdeal) hs
  refine ⟨g * (IsLocalization.Away.sec g u).1, ?_, ?_⟩
  · exact notMem_original_away_of_iterated_away q hg qAway hqAway hu
  · obtain ⟨e⟩ := single_original_awayAlgEquiv (k := k) (S := S) g u
    exact IsGlobalCompleteIntersection.of_algEquiv (hglobal u hus) e

/-- Helper for Chap10 Lemma 10 135 8: a global complete-intersection principal-open
neighbourhood makes the local ring at the prime a complete intersection over the base field. -/
private lemma isCompleteIntersectionOver_atPrime_of_globalNearPrime
    (q : PrimeSpectrum S) :
    isGlobalCompleteIntersectionNearPrime k q →
      Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: lift `q` to the chosen global-CI principal open and use Lemma 10.135.7 with
  -- that lifted at-prime localization as the global model of `S_q`.
  rintro ⟨g, hg, hglobal⟩
  obtain ⟨qAway, hqAway⟩ := exists_primeSpectrum_away_comap_eq_of_notMem q hg
  have hqAway_asIdeal :
      Ideal.comap (algebraMap S (Localization.Away g)) qAway.asIdeal = q.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hqAway
  letI : IsLocalization.AtPrime (Localization.AtPrime qAway.asIdeal) q.asIdeal := by
    simpa [hqAway_asIdeal] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers g)
        (Localization.AtPrime qAway.asIdeal)
        qAway.asIdeal)
  let eS : Localization.AtPrime q.asIdeal ≃ₐ[S] Localization.AtPrime qAway.asIdeal :=
    IsLocalization.algEquiv q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime qAway.asIdeal)
  let e : Localization.AtPrime q.asIdeal ≃ₐ[k] Localization.AtPrime qAway.asIdeal :=
    eS.restrictScalars k
  have hTFAE :=
    isCompleteIntersectionOver_tfae
      (k := k)
      (S := Localization.AtPrime q.asIdeal)
  have hmodel :
      ∃ (A : Type v) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
          (e : Localization.AtPrime q.asIdeal ≃ₐ[k] Localization.AtPrime a.asIdeal),
          IsGlobalCompleteIntersection k A :=
    ⟨Localization.Away g, inferInstance, inferInstance, qAway, e, hglobal⟩
  exact (hTFAE.out 3 0 rfl rfl).mp hmodel

/-- Helper for Chap10 Lemma 10 135 8: a local complete-intersection basic-open neighbourhood
gives a prime-local model of the local ring as a localization of a local complete intersection. -/
private lemma isCompleteIntersectionOver_atPrime_of_localNearPrime
    (q : PrimeSpectrum S) :
    isLocalCompleteIntersectionNearPrime k q →
      Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: first shrink the local complete-intersection neighbourhood to a global one,
  -- then apply the global-neighbourhood-to-stalk bridge.
  rintro ⟨g, hg, hlocal⟩
  exact isCompleteIntersectionOver_atPrime_of_globalNearPrime q
    (globalNearPrime_of_localCompleteIntersectionAway q hg hlocal)

/-- Helper for Chap10 Lemma 10 135 8: the complete-intersection condition on the stalk is
equivalent to the existence of a global complete-intersection principal-open neighbourhood. -/
private lemma isCompleteIntersectionOver_atPrime_iff_globalNearPrime
    (q : PrimeSpectrum S) :
    Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      isGlobalCompleteIntersectionNearPrime k q := by
  -- Proof comment: one direction spreads the global model supplied by Lemma 10.135.7 using
  -- Lemma 10.126.7; the other direction is the direct lifted-prime construction above.
  constructor
  · intro hci
    letI : Algebra.FinitePresentation k S :=
      (Algebra.FinitePresentation.of_finiteType (R := k) (A := S)).mp inferInstance
    have hTFAE :=
      isCompleteIntersectionOver_tfae
        (k := k)
        (S := Localization.AtPrime q.asIdeal)
    have hmodel :
        ∃ (A : Type v) (_ : CommRing A) (_ : Algebra k A) (a : PrimeSpectrum A)
            (e : Localization.AtPrime q.asIdeal ≃ₐ[k] Localization.AtPrime a.asIdeal),
            IsGlobalCompleteIntersection k A :=
      (hTFAE.out 0 3 rfl rfl).mp hci
    rcases hmodel with ⟨A, hAcomm, hAalg, a, e, hglobalA⟩
    letI : CommRing A := hAcomm
    letI : Algebra k A := hAalg
    letI : IsGlobalCompleteIntersection k A := hglobalA
    letI : Algebra.FinitePresentation k A := inferInstance
    obtain ⟨g, hg, gA, hgA, ⟨eAway⟩⟩ :=
      exists_awayAlgEquiv_of_localizationAtPrime_algEquiv
        (R := k)
        (S := S)
        (S' := A)
        q
        a
        e
    refine ⟨g, hg, ?_⟩
    have hglobalAwayA : IsGlobalCompleteIntersection k (Localization.Away gA) :=
      IsGlobalCompleteIntersection.of_isLocalizationAway gA hglobalA
    exact IsGlobalCompleteIntersection.of_algEquiv hglobalAwayA eAway.symm
  · exact isCompleteIntersectionOver_atPrime_of_globalNearPrime q

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 8: the local and global principal-open neighbourhood
conditions are equivalent at a fixed prime. -/
private lemma localNearPrime_iff_globalNearPrime
    (q : PrimeSpectrum S) :
    isLocalCompleteIntersectionNearPrime k q ↔
      isGlobalCompleteIntersectionNearPrime k q := by
  -- Proof comment: global charts are local charts by the owner instance, while local charts are
  -- shrunk to global charts by the finite-cover prime-avoidance lemma.
  constructor
  · rintro ⟨g, hg, hlocal⟩
    exact globalNearPrime_of_localCompleteIntersectionAway q hg hlocal
  · rintro ⟨g, hg, hglobal⟩
    letI : IsGlobalCompleteIntersection k (Localization.Away g) := hglobal
    exact ⟨g, hg, inferInstance⟩

/-- Helper for Chap10 Lemma 10 135 8: the global-neighbourhood condition is equivalent to the
regular-sequence condition for every finite polynomial presentation. -/
private lemma globalNearPrime_iff_regularSequencePresentation
    (q : PrimeSpectrum S) :
    isGlobalCompleteIntersectionNearPrime k q ↔
      (∀ {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (_ : Function.Surjective π),
        kernelGeneratedByRegularSequenceCondition π q
          (ENat.toNat ((prime π q).asIdeal.height - q.asIdeal.height))) := by
  -- Proof comment: use Lemma 10.135.4 for each presentation; for the reverse implication choose
  -- one finite generator presentation from finite type.
  constructor
  · intro hglobal n π hπ
    have hc := heightSub_eq_coe_toNat_of_polynomialPresentation π q
    have hTFAE := PolynomialPresentationAtPrime.tfae π hπ q hc
    exact (hTFAE.out 0 4 rfl rfl).mp hglobal
  · intro hregular
    classical
    obtain ⟨n, ⟨P⟩⟩ :=
      (Algebra.FiniteType.iff_exists_generators (R := k) (S := S)).mp inferInstance
    let π : MvPolynomial (Fin n) k →ₐ[k] S := MvPolynomial.aeval P.val
    have hπ : Function.Surjective π := P.aeval_val_surjective
    have hc := heightSub_eq_coe_toNat_of_polynomialPresentation π q
    have hTFAE := PolynomialPresentationAtPrime.tfae π hπ q hc
    exact (hTFAE.out 4 0 rfl rfl).mp (hregular π hπ)

/- Domain-style sampling pass.

Primary domain: complete intersections at a prime of a finite type algebra, compared through
localization and localized polynomial presentations.

Sampled owner declarations:
* `Algebra.IsCompleteIntersectionOver`;
* `PolynomialPresentationAtPrime.tfae`;
* `isLocalCompleteIntersectionNearPrime`;
* `isGlobalCompleteIntersectionNearPrime`.

Best owner abstraction: `Algebra.IsCompleteIntersectionOver` is the canonical owner for the local
ring condition at `q`, while the presentation-theoretic clause is derived from the existing owner
theorem `PolynomialPresentationAtPrime.tfae` rather than from a new local wrapper.

Primitive vs. derived:
* primitive data: the finite type `k`-algebra `S`, the prime `q`, and a chosen surjective
  polynomial presentation of `S`;
* derived API: the near-prime local/global complete intersection predicates and the five-condition
  `List.TFAE` for a chosen presentation.

Source/core/bridge triage:
* source-facing: the four-way `List.TFAE` below;
* core/canonical: `Algebra.IsCompleteIntersectionOver`;
* bridge/view: the basic-open neighborhood predicates and the localized polynomial-presentation
  criterion from `PolynomialPresentationAtPrime.tfae`.
-/

-- Proof sketch: apply Lemma `10.135.7` to the local ring `S_q`, whose being a complete
-- intersection over `k` is equivalent to being a localization at a prime of either a local or a
-- global complete intersection. The presentation-theoretic clause is then identified with the
-- corresponding criterion from Lemma `10.135.4`, and the finite-type hypothesis on `S` supplies
-- the essential finite-type hypothesis needed after localizing at `q`.
/-- Chap10 Lemma 10 135 8: for a finite type `k`-algebra `S` and a prime `q` of `S`, the
following are equivalent: the local ring `S_q` is a complete intersection over `k`; some basic
open neighbourhood of `q` is a local complete intersection over `k`; some basic open neighbourhood
of `q` is a global complete intersection over `k`; and for every surjective polynomial
presentation of `S`, the localized defining ideal at the prime over `q` is generated by a regular
sequence of length equal to the codimension difference. -/
@[stacks 00SG]
theorem completeIntersectionOver_atPrime_tfae
    (q : PrimeSpectrum S) :
    List.TFAE
      [ Algebra.IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal)
      , isLocalCompleteIntersectionNearPrime k q
      , isGlobalCompleteIntersectionNearPrime k q
      , (∀ {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (_ : Function.Surjective π),
            kernelGeneratedByRegularSequenceCondition π q
              (ENat.toNat ((prime π q).asIdeal.height - q.asIdeal.height)))
      ] := by
  -- Proof comment: identify the first, second, and fourth clauses with the global-neighbourhood
  -- clause, then assemble the four-term `TFAE` propositionally.
  exact
    tfae_four_of_equiv
      (isCompleteIntersectionOver_atPrime_iff_globalNearPrime q)
      (localNearPrime_iff_globalNearPrime q)
      (globalNearPrime_iff_regularSequencePresentation q)

end

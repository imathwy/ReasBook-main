import Mathlib
import StacksProject_2024.Chap10.Lemma_10_144_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: a maximal ideal of a finite algebra over a local base
contracts to the base maximal ideal. -/
private lemma maximalSpectrumComap_eq_maximalIdeal_of_finite
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [Module.Finite A B] (m : MaximalSpectrum B) :
    Ideal.comap (algebraMap A B) m.asIdeal = IsLocalRing.maximalIdeal A := by
  -- A finite algebra is integral, so contraction of a maximal ideal is maximal.
  haveI : Algebra.IsIntegral A B := inferInstance
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  have hmax : (Ideal.comap (algebraMap A B) m.asIdeal).IsMaximal := by
    exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m.asIdeal
  -- In a local ring there is only one maximal ideal.
  exact IsLocalRing.eq_maximalIdeal hmax

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: the powers of an element outside a prime ideal are
disjoint from that prime ideal. -/
private lemma disjoint_powers_of_not_mem
    {A : Type*} [CommSemiring A] {p : Ideal A} (hp : p.IsPrime)
    {f : A} (hf : f ∉ p) :
    Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (p : Set A) := by
  -- A power lying in a prime ideal forces the original element to lie there.
  rw [Set.disjoint_left]
  intro x hx hxmem
  have hx' : x ∈ Submonoid.powers f := hx
  rw [Submonoid.mem_powers_iff] at hx'
  obtain ⟨n, hn⟩ := hx'
  subst x
  exact hf (hp.mem_of_pow_mem n hxmem)

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: the image of a prime avoiding the inverted element is
prime in the corresponding away localization. -/
private lemma awayImagePrime_isPrime
    {A : Type*} [CommRing A] (p : Ideal A) (hp : p.IsPrime)
    {f : A} (hf : f ∉ p) :
    (Ideal.map (algebraMap A (Localization.Away f)) p).IsPrime := by
  -- This is the standard image-prime theorem for localizations, with the disjointness made
  -- explicit for the powers submonoid.
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
    (Localization.Away f) p hp (disjoint_powers_of_not_mem hp hf)

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: a prime avoiding the inverted element contracts back from
the corresponding away localization to itself. -/
private lemma awayImagePrime_comap_eq
    {A : Type*} [CommRing A] (p : Ideal A) (hp : p.IsPrime)
    {f : A} (hf : f ∉ p) :
    Ideal.comap (algebraMap A (Localization.Away f))
        (Ideal.map (algebraMap A (Localization.Away f)) p) = p := by
  -- The contraction statement uses the same powers-disjointness as the image-prime statement.
  exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
    (Localization.Away f) hp (disjoint_powers_of_not_mem hp hf)

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: localizing an already-localized ring at a prime gives a
localization at the contracted prime of the original ring. -/
private lemma isLocalizationAtPrime_of_comap_eq
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {M : Submonoid A} [IsLocalization M B]
    (J : Ideal B) [J.IsPrime] [IsLocalization.AtPrime C J]
    (p : Ideal A) [p.IsPrime]
    (hcomap : Ideal.comap (algebraMap A B) J = p) :
    IsLocalization.AtPrime C p := by
  -- Mathlib's localization-of-localization theorem gives the contracted prime; rewrite it to
  -- the named prime used downstream.
  have hloc : IsLocalization.AtPrime C (Ideal.comap (algebraMap A B) J) := by
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := M) C J
  simpa [hcomap] using hloc

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: if a map pulls a prime back to `q`, then elements outside
`q` become units in the at-prime localization of the target. -/
private lemma isUnit_toAtPrime_of_not_mem_comap
    {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
    [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C)
    (J : Ideal C) [J.IsPrime] (q : Ideal B)
    (hcomap : Ideal.comap φ.toRingHom J = q) {x : B} (hx : x ∉ q) :
    IsUnit (algebraMap C (Localization.AtPrime J) (φ x)) := by
  -- Being outside the pulled-back prime says precisely that the image lies in the prime
  -- complement inverted by the at-prime localization.
  have hnot : φ x ∉ J := by
    intro hmem
    exact hx (by simpa [← hcomap, Ideal.mem_comap] using hmem)
  exact IsLocalization.map_units (M := J.primeCompl) (Localization.AtPrime J) ⟨φ x, hnot⟩

omit [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 146 2: a map out of a localization of a local ring is local once
the closed point has the same contraction to the original ring. -/
private lemma isLocalHom_of_isLocalization_closedPointComap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] {M : Submonoid A} [IsLocalization M B]
    [IsLocalRing B] [IsLocalRing C] (φ : B →+* C)
    (h :
      PrimeSpectrum.comap (φ.comp (algebraMap A B)) (IsLocalRing.closedPoint C) =
        PrimeSpectrum.comap (algebraMap A B) (IsLocalRing.closedPoint B)) :
    IsLocalHom φ := by
  -- Injectivity of the spectrum map of a localization reduces locality to equality after
  -- contraction to the original ring.
  rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
  apply PrimeSpectrum.localization_comap_injective B M
  simpa using h

/-- Chap10 Lemma 10 146 2: if `R → S` is a local homomorphism of local rings and `S` is a
localization of an étale `R`-algebra, then there exists a finite, finitely presented, faithfully
flat `R`-algebra `S'` such that every maximal localization of `S'` admits a local `R`-algebra
factorization from `S`. -/
@[stacks 053K]
theorem existsFiniteFaithfullyFlatExtensionWithLocalFactorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          ∃ φ : S →ₐ[R] Localization.AtPrime m'.asIdeal,
            IsLocalHom φ.toRingHom := by
  -- Proof route: pull back the closed point of `S` to the etale algebra `T`, shrink to a
  -- standard-etale away chart, apply Lemma 10.144.5 to that chart, and then extend each
  -- chartwise away factorization across the original localization `S`.
  obtain ⟨T, hTcomm, hTalg, hTSalg, hTower, hEtale, M, hLoc⟩ := hS
  letI : CommRing T := hTcomm
  letI : Algebra R T := hTalg
  letI : Algebra T S := hTSalg
  letI : IsScalarTower R T S := hTower
  letI : Algebra.Etale R T := hEtale
  letI : IsLocalization M S := hLoc
  -- The closed point of `S` determines the prime of `T` at which the etale algebra is made
  -- standard etale.
  let qT : Ideal T := Ideal.comap (algebraMap T S) (IsLocalRing.maximalIdeal S)
  have hqT_prime : qT.IsPrime := by
    simpa [qT] using Ideal.comap_isPrime (algebraMap T S) (IsLocalRing.maximalIdeal S)
  letI : qT.IsPrime := hqT_prime
  have hqT_over :
      Ideal.comap (algebraMap R T) qT = IsLocalRing.maximalIdeal R := by
    -- Pulling the closed point all the way back to `R` is the local-hom maximal ideal.
    dsimp [qT]
    rw [Ideal.comap_comap]
    have hcomp :
        (algebraMap T S).comp (algebraMap R T) = algebraMap R S := by
      ext r
      exact (IsScalarTower.algebraMap_apply R T S r).symm
    rw [hcomp]
    exact IsLocalRing.maximalIdeal_comap (algebraMap R S)
  have hEtaleAt : Algebra.IsEtaleAt R qT := by
    -- Since `T` is etale over `R`, every prime of `T` lies in the etale locus.
    have hall : Algebra.etaleLocus R T = Set.univ :=
      (Algebra.etaleLocus_eq_univ_iff_etale (R := R) (A := T)).2 inferInstance
    have hmem : (⟨qT, hqT_prime⟩ : PrimeSpectrum T) ∈ Algebra.etaleLocus R T := by
      rw [hall]
      exact Set.mem_univ _
    simpa [Algebra.mem_etaleLocus_iff] using hmem
  obtain ⟨f, hfqT, hfstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := T) (Q := qT)
  letI : Algebra.IsStandardEtale R (Localization.Away f) := hfstd
  obtain ⟨S', hS'comm, hS'alg, hS'finite, hS'fp, hS'ff, hprimeLift⟩ :=
    Algebra.exists_finitePresentation_flat_surjective_extension_lifting_primes
      (R := R) (S := Localization.Away f)
  letI : CommRing S' := hS'comm
  letI : Algebra R S' := hS'alg
  letI : Module.Finite R S' := hS'finite
  refine ⟨S', hS'comm, hS'alg, hS'finite, hS'fp, hS'ff, ?_⟩
  intro m'
  let p : PrimeSpectrum R := IsLocalRing.closedPoint R
  have hm'_over_closed :
      m'.asIdeal ∈ p.asIdeal.primesOver S' := by
    -- The finite-extension contraction helper places every maximal ideal over the closed point
    -- of the local base.
    have hcomap :
        Ideal.comap (algebraMap R S') m'.asIdeal = IsLocalRing.maximalIdeal R :=
      maximalSpectrumComap_eq_maximalIdeal_of_finite (A := R) (B := S') m'
    haveI : m'.asIdeal.LiesOver p.asIdeal := by
      constructor
      simpa [p, IsLocalRing.closedPoint, Ideal.under_def] using hcomap.symm
    exact ⟨m'.isMaximal.isPrime, inferInstance⟩
  let qComponent : p.asIdeal.primesOver S' := ⟨m'.asIdeal, hm'_over_closed⟩
  -- Route correction: the direct transport from the away chart to `S'_{m'}` is avoided.  We first
  -- work in the at-prime localization of the image prime in the away chart, where the closed-point
  -- contraction is definitionally controlled by `Localization.AtPrime.comap_maximalIdeal`.
  let A := Localization.Away f
  let qA : Ideal A := Ideal.map (algebraMap T A) qT
  have hqA_prime : qA.IsPrime := by
    -- The chart prime is the image of `qT` in the away localization at an element outside `qT`.
    simpa [A, qA] using awayImagePrime_isPrime qT hqT_prime hfqT
  have hqA_comap_T : Ideal.comap (algebraMap T A) qA = qT := by
    -- Contraction from the away chart recovers the original prime of `T`.
    simpa [A, qA] using awayImagePrime_comap_eq qT hqT_prime hfqT
  have hqA_over_R : Ideal.comap (algebraMap R A) qA = p.asIdeal := by
    -- Pull the chart prime back through `T`; the result is the closed point of `R`.
    calc
      Ideal.comap (algebraMap R A) qA =
          Ideal.comap (algebraMap R T) (Ideal.comap (algebraMap T A) qA) := by
        rw [Ideal.comap_comap]
        congr 1
      _ = Ideal.comap (algebraMap R T) qT := by rw [hqA_comap_T]
      _ = p.asIdeal := by simpa [p, IsLocalRing.closedPoint] using hqT_over
  have hqA_over_closed : qA ∈ p.asIdeal.primesOver A := by
    -- Package the chart prime as a prime of the standard-etale chart lying over the closed point.
    haveI : qA.LiesOver p.asIdeal := by
      constructor
      simpa [Ideal.under_def] using hqA_over_R.symm
    exact ⟨hqA_prime, inferInstance⟩
  let qAway : p.asIdeal.primesOver A := ⟨qA, hqA_over_closed⟩
  obtain ⟨g', hg', ψ, hψ_comap⟩ := hprimeLift p qAway qComponent
  let C := Localization.Away g'
  let J : Ideal C := Ideal.map (algebraMap S' C) m'.asIdeal
  have hJ_prime : J.IsPrime := by
    -- The maximal ideal of `S'` also avoids `g'`, so its image in the away chart is prime.
    simpa [C, J] using
      awayImagePrime_isPrime m'.asIdeal m'.isMaximal.isPrime hg'
  have hJ_comap : Ideal.comap (algebraMap S' C) J = m'.asIdeal := by
    -- This image prime contracts to the original maximal ideal of `S'`.
    simpa [C, J] using
      awayImagePrime_comap_eq m'.asIdeal m'.isMaximal.isPrime hg'
  letI : J.IsPrime := hJ_prime
  letI : IsLocalization.AtPrime (Localization.AtPrime J) m'.asIdeal :=
    isLocalizationAtPrime_of_comap_eq (A := S') (B := C) (C := Localization.AtPrime J)
      (M := Submonoid.powers g') J m'.asIdeal hJ_comap
  let awayToJ : C →ₐ[R] Localization.AtPrime J :=
    IsScalarTower.toAlgHom R C (Localization.AtPrime J)
  let chartToJ : A →ₐ[R] Localization.AtPrime J := awayToJ.comp ψ
  let baseToJ : T →ₐ[R] Localization.AtPrime J :=
    chartToJ.comp (IsScalarTower.toAlgHom R T A)
  have hM_avoid_qT : ∀ y : M, (y : T) ∉ qT := by
    -- Elements inverted in `S` cannot land in the maximal ideal of the local ring `S`.
    intro y hy
    have hunit : IsUnit (algebraMap T S (y : T)) := IsLocalization.map_units S y
    have hnot : algebraMap T S (y : T) ∉ IsLocalRing.maximalIdeal S :=
      IsLocalRing.notMem_maximalIdeal.2 hunit
    exact hnot (by simpa [qT, Ideal.mem_comap] using hy)
  have hM_units_J : ∀ y : M, IsUnit (baseToJ (y : T)) := by
    -- The comap equality supplied by Lemma 10.144.5 moves nonmembership from the chart prime to
    -- the image prime `J`, where the at-prime localization inverts exactly the complement.
    intro y
    have hyA : algebraMap T A (y : T) ∉ qA := by
      intro hmem
      have hyComap : (y : T) ∈ Ideal.comap (algebraMap T A) qA := by
        exact hmem
      exact hM_avoid_qT y (by simpa [hqA_comap_T] using hyComap)
    have hyUnit :
        IsUnit (algebraMap C (Localization.AtPrime J) (ψ (algebraMap T A (y : T)))) :=
      isUnit_toAtPrime_of_not_mem_comap ψ J qA hψ_comap hyA
    simpa only [baseToJ, chartToJ, awayToJ, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply] using hyUnit
  let φJ : S →ₐ[R] Localization.AtPrime J :=
    IsLocalization.liftAlgHom (A := R) (R := T) (M := M) (S := S)
      (P := Localization.AtPrime J) (f := baseToJ) hM_units_J
  have hφJ_comp : φJ.toRingHom.comp (algebraMap T S) = baseToJ.toRingHom := by
    -- The lifted map from `S` agrees with the constructed chart map on elements of `T`.
    exact IsLocalization.lift_comp hM_units_J
  have hbase_closed :
      Ideal.comap baseToJ.toRingHom (IsLocalRing.maximalIdeal (Localization.AtPrime J)) = qT := by
    -- The closed point pulls back through `C`, through the chart map, and through the away chart
    -- to the original prime `qT`.
    calc
      Ideal.comap baseToJ.toRingHom (IsLocalRing.maximalIdeal (Localization.AtPrime J)) =
          Ideal.comap (algebraMap T A)
            (Ideal.comap ψ.toRingHom
              (Ideal.comap (algebraMap C (Localization.AtPrime J))
                (IsLocalRing.maximalIdeal (Localization.AtPrime J)))) := by
        rw [Ideal.comap_comap, Ideal.comap_comap]
        congr 1
      _ = Ideal.comap (algebraMap T A) (Ideal.comap ψ.toRingHom J) := by
        rw [Localization.AtPrime.comap_maximalIdeal]
      _ = Ideal.comap (algebraMap T A) qA := by rw [hψ_comap]
      _ = qT := hqA_comap_T
  have hφJ_closed :
      PrimeSpectrum.comap (φJ.toRingHom.comp (algebraMap T S))
          (IsLocalRing.closedPoint (Localization.AtPrime J)) =
        PrimeSpectrum.comap (algebraMap T S) (IsLocalRing.closedPoint S) := by
    -- Both closed points have the same contraction to `T`, so the spectrum criterion applies.
    ext t
    change (φJ.toRingHom.comp (algebraMap T S)) t ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime J) ↔
        (algebraMap T S) t ∈ IsLocalRing.maximalIdeal S
    rw [hφJ_comp]
    rw [← Ideal.mem_comap, hbase_closed]
    simpa [qT, Ideal.mem_comap]
  have hφJ_local : IsLocalHom φJ.toRingHom :=
    isLocalHom_of_isLocalization_closedPointComap (A := T) (B := S)
      (C := Localization.AtPrime J) (M := M) φJ.toRingHom hφJ_closed
  let e : Localization.AtPrime J ≃ₐ[S'] Localization.AtPrime m'.asIdeal :=
    IsLocalization.algEquiv m'.asIdeal.primeCompl (Localization.AtPrime J)
      (Localization.AtPrime m'.asIdeal)
  let φ : S →ₐ[R] Localization.AtPrime m'.asIdeal :=
    (e.restrictScalars R).toAlgHom.comp φJ
  have hφ_local : IsLocalHom φ.toRingHom := by
    -- The final localization equivalence is a local ring isomorphism, so locality is preserved by
    -- composition.
    let eR : Localization.AtPrime J →ₐ[R] Localization.AtPrime m'.asIdeal :=
      (e.restrictScalars R).toAlgHom
    have he_local : IsLocalHom eR.toRingHom := by
      have he_equiv : IsLocalHom (e.restrictScalars R).toRingEquiv :=
        isLocalHom_equiv (e.restrictScalars R).toRingEquiv
      change IsLocalHom
        ((e.restrictScalars R).toRingEquiv :
          Localization.AtPrime J →+* Localization.AtPrime m'.asIdeal)
      infer_instance
    have hcomp : IsLocalHom (eR.toRingHom.comp φJ.toRingHom) :=
      RingHom.isLocalHom_comp eR.toRingHom φJ.toRingHom
    simpa [φ, eR] using hcomp
  exact ⟨φ, hφ_local⟩

/- Domain-style sampling:
* primary domain: étale neighborhoods of local rings, prime/maximal-ideal factorization after
  finite faithfully flat extension, and localization maps to local rings;
* sampled declarations:
  `IsEtaleAt.exists_isStandardEtale`,
  `exists_finitePresentation_flat_surjective_extension_lifting_primes`,
  `AlgHom.comp_algebraMap`,
  `Localization.localRingHom`,
  `Localization.isLocalHom_localRingHom`;
* best owner abstraction:
  the primewise finite faithfully flat extension theorem from Lemma `10.144.5`, together with the
  canonical factorization owner `S →ₐ[R] Localization.AtPrime m'.asIdeal`, whose base-ring
  compatibility is already built into `AlgHom`;
* source/core/bridge triage:
  this file is `source-facing`, since it specializes the primewise owner theorem to the local-ring
  situation and extracts the factorization morphisms for maximal ideals of the auxiliary extension;
  the core/canonical layer is the primewise theorem from Lemma `10.144.5`, while the present file
  is the bridge from prime fibers to local factorizations;
* primitive-vs-derived split:
  primitive existential data are only the auxiliary `R`-algebra `S'` and its standard owner
  witnesses `Module.Finite`, `Algebra.FinitePresentation`, and
  `(algebraMap R S').FaithfullyFlat`;
  the source-facing output is the canonical factorization morphism
  `S →ₐ[R] Localization.AtPrime m'.asIdeal`, while locality of its underlying ring hom is a
  derived companion consequence.
-/

-- Proof sketch: write `S` as a localization of an étale `R`-algebra `T`. By Proposition
-- `10.144.4`, near the prime corresponding to the maximal ideal of `S`, the map `R → T` becomes
-- standard étale. Apply Lemma `10.144.5` to obtain a finite, finitely presented, faithfully flat
-- `R`-algebra `S'` with the required prime-lifting property, and then localize at each maximal
-- ideal of `S'` to induce the desired factorization morphism `S →ₐ[R] S'_{m'}`.
/-- Companion to Chap10 Lemma 10 146 2: the local factorization theorem also gives the requested
bare factorization maps after forgetting locality. -/
theorem exists_finite_finitePresentation_faithfullyFlat_extension_with_factorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          Nonempty (S →ₐ[R] Localization.AtPrime m'.asIdeal) := by
  -- The stronger local-factorization helper includes the requested maps; forget locality.
  obtain ⟨S', hS'comm, hS'alg, hS'finite, hS'fp, hS'ff, hlocal⟩ :=
    existsFiniteFaithfullyFlatExtensionWithLocalFactorizations
      (R := R) (S := S) hS
  refine ⟨S', hS'comm, hS'alg, hS'finite, hS'fp, hS'ff, ?_⟩
  intro m'
  obtain ⟨φ, _hφlocal⟩ := hlocal m'
  exact ⟨φ⟩

end

end Algebra

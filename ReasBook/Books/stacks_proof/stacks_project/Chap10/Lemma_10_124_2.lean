import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_13
import StacksProject_2024.Chap10.Lemma_10_112_6

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open Algebra.TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [Algebra.EssFiniteType R S]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/-- Helper for Chap10 Lemma 10 124 2: a localization whose target is local is also the
localization at the complement of the contracted maximal ideal. -/
private theorem isLocalizationAtComapMaximalIdeal
    {P : Type u} {T : Type v} [CommRing P] [CommRing T] [Algebra P T]
    (M : Submonoid P) [IsLocalization M T] [IsLocalRing T] :
    let q : Ideal P := Ideal.comap (algebraMap P T) (maximalIdeal T)
    q.IsPrime ∧ IsLocalization q.primeCompl T := by
  let q : Ideal P := Ideal.comap (algebraMap P T) (maximalIdeal T)
  have hq_prime : q.IsPrime := by
    -- The contraction of the maximal ideal of the local target is prime.
    simpa [q] using Ideal.comap_isPrime (algebraMap P T) (maximalIdeal T)
  letI : q.IsPrime := hq_prime
  have h_targetUnits : (maximalIdeal T).primeCompl ≤ IsUnit.submonoid T := by
    intro x hx
    -- In a local ring, being outside the maximal ideal is the same as being a unit.
    simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_primeCompl_iff,
      Classical.not_not] using hx
  letI : IsLocalization (maximalIdeal T).primeCompl T := IsLocalization.self h_targetUnits
  have h_unitOutsideMaximal : ∀ x : T, IsUnit x → x ∈ (maximalIdeal T).primeCompl := by
    intro x hx
    -- Units in a local ring lie outside the maximal ideal.
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hx
  have hloc :
      IsLocalization (((maximalIdeal T).primeCompl).comap (algebraMap P T)) T := by
    -- The second localization inverts only units, so it collapses back to the same target.
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units
      (M := M) (N := (maximalIdeal T).primeCompl) (T := T) h_unitOutsideMaximal
  have hprime_compl :
      ((maximalIdeal T).primeCompl).comap (algebraMap P T) = q.primeCompl := by
    -- Pulling back the complement is the complement of the pulled-back prime.
    ext x
    simp [q, Ideal.mem_primeCompl_iff]
  constructor
  · exact hq_prime
  · simpa [hprime_compl] using hloc

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 124 2: Zariski's main theorem gives a finite subalgebra and a
basic-open comparison at a quasi-finite prime. -/
private theorem existsFgFiniteSubalgebraAwayMapBijectiveAtPrime
    {T : Type v} [CommRing T] [Algebra R T] [Algebra.FiniteType R T]
    (q : Ideal T) [q.IsPrime] [Algebra.QuasiFiniteAt R q] :
    ∃ A : Subalgebra R T,
      A.toSubmodule.FG ∧ Module.Finite R A ∧ ∃ r : A,
        r.1 ∉ q ∧ Function.Bijective (Localization.awayMap A.val.toRingHom r) := by
  -- Zariski's main theorem supplies finite-generation plus a bijective away comparison.
  obtain ⟨A, hAfg, r, hrq, haway⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := R) (S := T) q
  have hAfinite : Module.Finite R A := by
    -- Convert finite generation of the underlying submodule into `Module.Finite`.
    exact ⟨(Subalgebra.toSubmodule A).fg_top.mpr hAfg⟩
  exact ⟨A, hAfg, hAfinite, r, hrq, haway⟩

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.EssFiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 2: the image of a finitely generated subalgebra of the
finite-type presentation remains finite over the base. -/
private theorem moduleFinite_map_subalgebra_of_fg
    (B : Subalgebra R S) (A₀ : Subalgebra R B) (hA₀fg : A₀.toSubmodule.FG) :
    Module.Finite R (A₀.map B.val) := by
  have hAfg : (A₀.map B.val).toSubmodule.FG := by
    -- Push the finite generating set through the inclusion into `S`.
    rw [Subalgebra.map_toSubmodule]
    exact hA₀fg.map B.val.toLinearMap
  exact ⟨(Subalgebra.toSubmodule (A₀.map B.val)).fg_top.mpr hAfg⟩

/-- Helper for Chap10 Lemma 10 124 2: powers of an element outside a prime stay outside. -/
private theorem pow_notMem_of_notMem_prime {A : Type*} [CommSemiring A]
    {q : Ideal A} [q.IsPrime] {x : A} (hx : x ∉ q) (n : ℕ) : x ^ n ∉ q := by
  -- Prime ideals are radical, so membership of a power would force membership of the element.
  intro hmem
  exact hx ((show q.IsPrime from inferInstance).mem_of_pow_mem n hmem)

/-- Helper for Chap10 Lemma 10 124 2: a product of two elements outside a prime stays outside. -/
private theorem mul_notMem_of_notMem_prime {A : Type*} [CommSemiring A]
    {q : Ideal A} [q.IsPrime] {x y : A} (hx : x ∉ q) (hy : y ∉ q) : x * y ∉ q := by
  -- If the product lay in the prime ideal, one of the factors would lie in it.
  intro hmem
  exact ((show q.IsPrime from inferInstance).mem_or_mem hmem).elim hx hy

omit [Algebra.EssFiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 2: the prime of a finite-type subalgebra contracted from
the closed point of the local target lies over the closed point of the local source. -/
private theorem subalgebraClosedPoint_under_eq_maximalIdeal
    (B : Subalgebra R S) (q : Ideal B)
    (hq : q = Ideal.comap (algebraMap B S) (maximalIdeal S)) :
    q.under R = maximalIdeal R := by
  -- Rewrite the two-step contraction through `B` as contraction along the local map `R → S`.
  rw [Ideal.under_def, hq, Ideal.comap_comap]
  rw [← IsScalarTower.algebraMap_eq R B S]
  -- The map `R → S` is local, so it contracts the closed point of `S` to that of `R`.
  exact IsLocalRing.maximalIdeal_comap (algebraMap R S)

/-- Helper for Chap10 Lemma 10 124 2: finite residue field over the base field makes a finite
type fiber point closed. -/
private theorem isClosed_singleton_of_moduleFinite_residueField
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (q : PrimeSpectrum A) (hfin : Module.Finite k q.asIdeal.ResidueField) :
    IsClosed ({q} : Set (PrimeSpectrum A)) := by
  -- Proof comment: finiteness makes the residue field integral over `k`, hence integral over
  -- the finite-type algebra; the kernel defining the residue field is therefore maximal.
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
  letI : Module.Finite k q.asIdeal.ResidueField := hfin
  letI : Algebra.IsIntegral k q.asIdeal.ResidueField :=
    Algebra.IsIntegral.of_finite k q.asIdeal.ResidueField
  letI : Algebra.IsIntegral A q.asIdeal.ResidueField :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := k) x).tower_top⟩
  have hmax : (RingHom.ker (algebraMap A q.asIdeal.ResidueField)).IsMaximal := by
    exact Algebra.ker_algebraMap_isMaximal_of_isIntegral A q.asIdeal.ResidueField
  rwa [Ideal.ker_algebraMap_residueField] at hmax

omit [IsLocalRing R] in
/-- Helper for Chap10 Lemma 10 124 2: a point whose residue field is finite over a base ring is
closed in any algebra over that base. -/
private theorem isClosed_singleton_of_moduleFinite_residueField_over_base
    {A : Type v} [CommRing A] [Algebra R A]
    (q : PrimeSpectrum A) (hfin : Module.Finite R q.asIdeal.ResidueField) :
    IsClosed ({q} : Set (PrimeSpectrum A)) := by
  -- Proof comment: finite generation over the base makes the residue field integral over the
  -- base, hence integral over the algebra by scalar extension.
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr
  letI : Module.Finite R q.asIdeal.ResidueField := hfin
  letI : Algebra.IsIntegral R q.asIdeal.ResidueField :=
    Algebra.IsIntegral.of_finite R q.asIdeal.ResidueField
  letI : Algebra.IsIntegral A q.asIdeal.ResidueField :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  have hmax : (RingHom.ker (algebraMap A q.asIdeal.ResidueField)).IsMaximal := by
    exact Algebra.ker_algebraMap_isMaximal_of_isIntegral A q.asIdeal.ResidueField
  rwa [Ideal.ker_algebraMap_residueField] at hmax

/-- Helper for Chap10 Lemma 10 124 2: the localization at a prime has Krull dimension zero
exactly when the prime is minimal. -/
private theorem ringKrullDim_localizationAtPrime_eq_zero_iff_mem_minimalPrimes
    {A : Type v} [CommRing A] (q : PrimeSpectrum A) :
    ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ↔ q.asIdeal ∈ minimalPrimes A := by
  -- Proof comment: translate local dimension to height, then use the standard zero-height
  -- characterization of minimal primes.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (Localization.AtPrime q.asIdeal)]
  rw [Ideal.height_eq_primeHeight q.asIdeal]
  rw [WithBot.coe_eq_zero]
  exact Ideal.primeHeight_eq_zero_iff

/-- Helper for Chap10 Lemma 10 124 2: a closed finite-type field-algebra point with
zero-dimensional local ring is open. -/
private theorem isOpen_singleton_of_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero
    (k : Type u) {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (q : PrimeSpectrum A)
    (hclosed : IsClosed ({q} : Set (PrimeSpectrum A)))
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    IsOpen ({q} : Set (PrimeSpectrum A)) := by
  -- Proof comment: the Noetherian Jacobson singleton criterion turns closedness plus
  -- generization-stability into openness; zero local dimension supplies minimality.
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
    0 2 rfl rfl]
  refine ⟨hclosed, ?_⟩
  rw [PrimeSpectrum.stableUnderGeneralization_singleton]
  exact (ringKrullDim_localizationAtPrime_eq_zero_iff_mem_minimalPrimes q).mp hdim

/-- Helper for Chap10 Lemma 10 124 2: finite residue field and zero local dimension imply
quasi-finiteness at a point of a finite-type algebra over a field. -/
private theorem quasiFiniteAt_of_finiteResidueField_and_ringKrullDim
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (q : PrimeSpectrum A)
    (hfinite : Module.Finite k q.asIdeal.ResidueField)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    Algebra.QuasiFiniteAt k q.asIdeal := by
  -- Proof comment: finite residue gives closedness, and the zero-dimensional local ring makes the
  -- closed singleton isolated; mathlib's owner theorem converts isolatedness to quasi-finiteness.
  have hclosed : IsClosed ({q} : Set (PrimeSpectrum A)) :=
    isClosed_singleton_of_moduleFinite_residueField q hfinite
  have hopen : IsOpen ({q} : Set (PrimeSpectrum A)) :=
    isOpen_singleton_of_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero
      k q hclosed hdim
  exact Algebra.QuasiFiniteAt.of_isOpen_singleton q hopen

/-- Helper for Chap10 Lemma 10 124 2: the prime of a fiber corresponding to a point over the
base prime contracts back to the original prime. -/
private theorem fiberPrime_asIdeal_comap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap A B) q = p) :
    Ideal.comap includeRight.toRingHom
      (PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩).asIdeal = q.asIdeal := by
  -- Proof comment: move the fiber point back through the defining equivalence and project to
  -- the underlying ideal of the original point.
  change
    ((PrimeSpectrum.preimageEquivFiber A B p).symm
      (PrimeSpectrum.preimageEquivFiber A B p ⟨q, hq⟩)).1.asIdeal = q.asIdeal
  exact congrArg
    (fun x : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} ↦ x.1.asIdeal)
    ((PrimeSpectrum.preimageEquivFiber A B p).symm_apply_apply ⟨q, hq⟩)

omit [Algebra.EssFiniteType R S] in
/-- Chap10 Lemma 10 124 2: the finite closed-fiber hypotheses make the contracted closed point
on a finite-type subalgebra quasi-finite. -/
private theorem quasiFiniteAtSubalgebraComapMaximal_of_closedFiber_dimZero
    (B : Subalgebra R S) [Algebra.FiniteType R B]
    (q : Ideal B) [q.IsPrime] [IsLocalization q.primeCompl S]
    (hq : q = Ideal.comap (algebraMap B S) (maximalIdeal S))
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    Algebra.QuasiFiniteAt R q := by
  have hq_under : q.under R = maximalIdeal R :=
    subalgebraClosedPoint_under_eq_maximalIdeal B q hq
  let qPoint : PrimeSpectrum B := ⟨q, inferInstance⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) qPoint
  have hp_closed : p.asIdeal = maximalIdeal R := by
    -- Proof comment: the prime of the finite-type subalgebra lies over the closed point of `R`.
    simpa [p, qPoint] using hq_under
  let qbar : PrimeSpectrum (p.asIdeal.Fiber B) := fiberPrimeAt R B qPoint
  have hq_lies : q.LiesOver p.asIdeal := by
    -- Proof comment: `p` was defined as the contraction of `q`, so the lies-over witness is
    -- definitionally the contraction identity.
    exact ⟨by rfl⟩
  letI : q.LiesOver p.asIdeal := hq_lies
  have hqbar_comap :
      Ideal.comap includeRight.toRingHom qbar.asIdeal = q := by
    -- Proof comment: the chosen fiber point is the canonical point over `q`.
    simpa [qbar, qPoint, fiberPrimeAt] using fiberPrime_asIdeal_comap (A := R) (B := B) p qPoint rfl
  have hqbar_qf : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qbar.asIdeal := by
    -- Proof comment: after the closed-fiber localization and residue-field comparisons are named,
    -- the field-algebra point is quasi-finite by the closed/residue finite plus zero local
    -- dimension criterion proved above.
    have hSfiniteR_local : Module.Finite R (ResidueField S) :=
      Module.Finite.trans (ResidueField R) (ResidueField S)
    letI : IsScalarTower R (ResidueField S) (maximalIdeal S).ResidueField :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have hmaxBij :
        Function.Bijective (algebraMap (ResidueField S) (maximalIdeal S).ResidueField) :=
      Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal S)
    let eMax : ResidueField S ≃ₐ[R] (maximalIdeal S).ResidueField :=
      AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom R (ResidueField S) (maximalIdeal S).ResidueField) hmaxBij
    have hSfiniteR : Module.Finite R (maximalIdeal S).ResidueField :=
      (Module.Finite.equiv_iff eMax.toLinearEquiv).mp hSfiniteR_local
    have hbijq :
        Function.Bijective (Ideal.ResidueField.map q (maximalIdeal S) (algebraMap B S) hq) :=
      (RingHom.surjectiveOnStalks_of_isLocalization q.primeCompl S).residueFieldMap_bijective
        q (maximalIdeal S) hq
    let eqS : q.ResidueField ≃ₐ[R] (maximalIdeal S).ResidueField :=
      AlgEquiv.ofBijective
        (Ideal.ResidueField.mapₐ q (maximalIdeal S) (IsScalarTower.toAlgHom R B S) hq)
        hbijq
    have hqfiniteR : Module.Finite R q.ResidueField :=
      (Module.Finite.equiv_iff eqS.toLinearEquiv).mpr hSfiniteR
    have hbijbar :
        Function.Bijective
          (Ideal.ResidueField.map q qbar.asIdeal includeRight.toRingHom hqbar_comap.symm) := by
      -- The map from `B` to the fiber is a base change of the residue-field map at `p`.
      simpa using
        ((@RingHom.SurjectiveOnStalks.baseChange' R _ p.asIdeal.ResidueField _ B _ _ _
          (Ideal.surjectiveOnStalks_residueField p.asIdeal)).residueFieldMap_bijective
            q qbar.asIdeal hqbar_comap.symm)
    let eqbar : q.ResidueField ≃ₐ[R] qbar.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (Ideal.ResidueField.mapₐ q qbar.asIdeal
          (Algebra.TensorProduct.includeRight (R := R) (A := p.asIdeal.ResidueField) (B := B))
          hqbar_comap.symm)
        hbijbar
    have hqbarfiniteR : Module.Finite R qbar.asIdeal.ResidueField :=
      (Module.Finite.equiv_iff eqbar.toLinearEquiv).mp hqfiniteR
    let eLoc : Localization.AtPrime q ≃+* S :=
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S).toRingEquiv
    let ILoc : Ideal (Localization.AtPrime q) :=
      Ideal.map (algebraMap R (Localization.AtPrime q)) p.asIdeal
    let IS : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
    have hmapI0 : Ideal.map eLoc.toRingHom ILoc = Ideal.map (algebraMap R S) p.asIdeal := by
      -- The localization equivalence is `B`-linear, hence also respects the maps from `R`.
      change Ideal.map eLoc.toRingHom
          (Ideal.map (algebraMap R (Localization.AtPrime q)) p.asIdeal) =
        Ideal.map (algebraMap R S) p.asIdeal
      rw [Ideal.map_map]
      congr 1
      ext r
      calc
        (eLoc.toRingHom.comp (algebraMap R (Localization.AtPrime q))) r =
            (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S)
              (algebraMap B (Localization.AtPrime q) (algebraMap R B r)) := by
                rw [RingHom.comp_apply,
                  IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)]
                rfl
        _ = algebraMap B S (algebraMap R B r) := by
                exact
                  (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S).commutes
                    (algebraMap R B r)
        _ = algebraMap R S r := by
                rw [IsScalarTower.algebraMap_apply R B S]
    have hmapI : IS = Ideal.map eLoc.toRingHom ILoc := by
      -- The source prime is the closed point, so the transported quotient ideal is the closed
      -- fiber ideal in `S`.
      change Ideal.map (algebraMap R S) (maximalIdeal R) = Ideal.map eLoc.toRingHom ILoc
      rw [hmapI0]
      simp [p, qPoint, hq_under]
    let eQuot : (Localization.AtPrime q ⧸ ILoc) ≃+* (S ⧸ IS) :=
      Ideal.quotientEquiv ILoc IS eLoc hmapI
    have hdimSQuot : ringKrullDim (S ⧸ IS) = 0 := by
      -- The quotient by the closed-point ideal is the closed fiber.
      change ringKrullDim (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) = 0
      exact
        (ringKrullDim_eq_of_ringEquiv
          (closedFiber_quotient_equiv (A := R) (B := S)).toRingEquiv).trans hdim
    have hdimLocQuot : ringKrullDim (Localization.AtPrime q ⧸ ILoc) = 0 :=
      (ringKrullDim_eq_of_ringEquiv eQuot).trans hdimSQuot
    have hdimLocal : ringKrullDim (Localization.AtPrime qbar.asIdeal) = 0 := by
      -- The quotient-local model is exactly the chapter owner `fiberLocalRingAt`.
      have hfiber :
          ringKrullDim (fiberLocalRingAt R B qPoint) = 0 :=
        (ringKrullDim_quotient_localizationAtPrime_eq_ringKrullDim_fiberLocalRingAt
          (R := R) (S := B) qPoint).symm.trans hdimLocQuot
      simpa [qbar] using hfiber
    have hclosed : IsClosed ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber B))) :=
      isClosed_singleton_of_moduleFinite_residueField_over_base qbar hqbarfiniteR
    have hopen : IsOpen ({qbar} : Set (PrimeSpectrum (p.asIdeal.Fiber B))) :=
      isOpen_singleton_of_isClosed_and_ringKrullDim_localizationAtPrime_eq_zero
        p.asIdeal.ResidueField qbar hclosed hdimLocal
    exact Algebra.QuasiFiniteAt.of_isOpen_singleton qbar hopen
  letI : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qbar.asIdeal := hqbar_qf
  exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
    p.asIdeal q qbar.asIdeal hqbar_comap

omit [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Algebra.EssFiniteType R S] in
/-- Helper for Chap10 Lemma 10 124 2: a Zariski-main away isomorphism and a prime localization
make the image finite subalgebra a localization source for the local target. -/
private theorem isLocalizationMappedSubalgebraOfAwayMapBijectiveAtPrime
    (B : Subalgebra R S) (q : Ideal B) [q.IsPrime] [IsLocalization q.primeCompl S]
    (A₀ : Subalgebra R B) (r : A₀) (hrq : r.1 ∉ q)
    (haway : Function.Bijective (Localization.awayMap A₀.val.toRingHom r)) :
    IsLocalization
      ((IsUnit.submonoid S).comap (algebraMap (A₀.map B.val) S)) S := by
  -- Route correction: instead of transporting a tower of localizations through equivalences,
  -- prove the localization axioms directly for the image subalgebra in `S`.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    -- Elements of the chosen submonoid are units by definition.
    exact x.2
  · intro z
    -- Write `z` as a `q`-local fraction in `B`.
    obtain ⟨⟨b, d⟩, hz⟩ := IsLocalization.surj q.primeCompl z
    have hsurjAway :
        ∀ b : B, ∃ a : A₀, ∃ n : ℕ,
          A₀.val.toRingHom a = A₀.val.toRingHom r ^ n * b := by
      -- The surjective half of the Zariski-main away comparison clears powers of `r`.
      exact (Localization.awayMap_surjective_iff (f := A₀.val.toRingHom) (r := r)).mp haway.2
    obtain ⟨a, n, ha⟩ := hsurjAway b
    obtain ⟨c, m, hc⟩ := hsurjAway d
    let e : A₀ ≃ₐ[R] A₀.map B.val :=
      Subalgebra.equivMapOfInjective A₀ B.val Subtype.val_injective
    have hden_notMem : (A₀.val.toRingHom (c * r ^ n)) ∉ q := by
      -- The denominator is a product of the original denominator and powers of `r`, both outside
      -- the contracted prime.
      have hr : A₀.val.toRingHom r ∉ q := hrq
      have hd : (d : B) ∉ q := d.2
      have hleft : A₀.val.toRingHom r ^ m * d ∉ q :=
        mul_notMem_of_notMem_prime (pow_notMem_of_notMem_prime hr m) hd
      have hcleared :
          (A₀.val.toRingHom r ^ m * d) * A₀.val.toRingHom r ^ n ∉ q :=
        mul_notMem_of_notMem_prime hleft (pow_notMem_of_notMem_prime hr n)
      rwa [map_mul, map_pow, hc]
    have hunit_den :
        IsUnit (algebraMap (A₀.map B.val) S (e (c * r ^ n))) := by
      -- Since the image denominator maps outside `q`, its image is a unit in the localization `S`.
      have hunit_B : IsUnit (algebraMap B S (A₀.val.toRingHom (c * r ^ n))) := by
        exact IsLocalization.map_units (M := q.primeCompl) S
          ⟨A₀.val.toRingHom (c * r ^ n), hden_notMem⟩
      simpa using hunit_B
    refine ⟨⟨e (a * r ^ m), ⟨e (c * r ^ n), hunit_den⟩⟩, ?_⟩
    have hnum_eq :
        A₀.val.toRingHom (a * r ^ m) =
          A₀.val.toRingHom r ^ m * b * A₀.val.toRingHom r ^ n := by
      -- The numerator is the original numerator, with the denominator-clearing power included.
      rw [map_mul, map_pow, ha]
      ring
    have hden_eq :
        A₀.val.toRingHom (c * r ^ n) =
          A₀.val.toRingHom r ^ m * d * A₀.val.toRingHom r ^ n := by
      -- The denominator clears both the `q`-local denominator and the away-localized numerator.
      rw [map_mul, map_pow, hc]
    -- The two cleared identities reduce the target equality to the original `q`-local fraction
    -- equality `z * d = b`.
    have hden_coe :
        algebraMap (A₀.map B.val) S (e (c * r ^ n)) =
          algebraMap B S (A₀.val.toRingHom (c * r ^ n)) := by
      rfl
    have hnum_coe :
        algebraMap (A₀.map B.val) S (e (a * r ^ m)) =
          algebraMap B S (A₀.val.toRingHom (a * r ^ m)) := by
      rfl
    calc
      z * algebraMap (A₀.map B.val) S (e (c * r ^ n)) =
          z * algebraMap B S (A₀.val.toRingHom (c * r ^ n)) := by
            rw [hden_coe]
      _ = z * algebraMap B S
            (A₀.val.toRingHom r ^ m * d * A₀.val.toRingHom r ^ n) := by
            rw [hden_eq]
      _ = (algebraMap B S (A₀.val.toRingHom r ^ m) *
            (z * algebraMap B S d)) *
            algebraMap B S (A₀.val.toRingHom r ^ n) := by
            simp [map_mul]
            ring
      _ = (algebraMap B S (A₀.val.toRingHom r ^ m) *
            algebraMap B S b) *
            algebraMap B S (A₀.val.toRingHom r ^ n) := by
            rw [hz]
      _ = algebraMap B S
            (A₀.val.toRingHom r ^ m * b * A₀.val.toRingHom r ^ n) := by
            simp [map_mul]
      _ = algebraMap B S (A₀.val.toRingHom (a * r ^ m)) := by
            rw [hnum_eq]
      _ = algebraMap (A₀.map B.val) S (e (a * r ^ m)) := by
            rw [hnum_coe]
  · intro x y hxy
    -- The image subalgebra is literally a subalgebra of `S`, so equality after applying the
    -- structure map is already equality in the source.
    refine ⟨⟨1, isUnit_one⟩, ?_⟩
    have hxyA : x = y := Subtype.ext hxy
    simpa [hxyA]

/-
Domain-style sampling:
- primary domain: local quasi-finite algebra maps and Zariski-main finiteness over local rings;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.EssFiniteType`,
  `Algebra.EssFiniteType.essFiniteType_iff_exists_subalgebra`,
  `exists_finite_subalgebra_of_integralClosure_with_zariskiMain_properties`;
- best owner abstraction: the closed fiber is the canonical owner `Ideal.Fiber`, and the decisive
  local finiteness condition is the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`,
  while the source-facing finite-localization conclusion is organized through `Subalgebra R S`
  together with `IsLocalization`;
- source/core/bridge triage:
  `source-facing`: the existence of a finite `R`-subalgebra of `S` whose localization is `S`;
  `core/canonical`: `Ideal.Fiber`, `Algebra.QuasiFiniteAt`, `Algebra.EssFiniteType`,
    `Subalgebra R S`, and `IsLocalization`;
  `bridge/view`: the local closed-fiber hypotheses imply the canonical quasi-finite owner at
  `maximalIdeal S`, which then feeds the Zariski-main finite-localization argument;
- primitive data: the local map, the essentially finite type owner, the finite residue-field
  extension `ResidueField R → ResidueField S`, and the canonical closed fiber `ClosedFiber`;
- derived API: quasi-finiteness at `maximalIdeal S` and the resulting finite-subalgebra
  localization witness.
-/

/-- The local source hypotheses, including the finite residue-field extension
`ResidueField R → ResidueField S`, make `R → S` quasi-finite at the maximal ideal of `S`. -/
-- Proof sketch: write `S` as a localization of the canonical finite-type subalgebra supplied by
-- `Algebra.EssFiniteType`. Because `ClosedFiber` is a finite-type `ResidueField R`-algebra,
-- the hypothesis `hκ` and `ringKrullDim ClosedFiber = 0` match clause `(6)` of the isolated-point
-- criterion from Lemmas `10.122.1` and `10.122.4` for the unique point of the local closed fiber,
-- which is exactly the owner predicate `Algebra.QuasiFiniteAt R (maximalIdeal S)`.
theorem quasiFiniteAt_maximalIdeal_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    Algebra.QuasiFiniteAt R (maximalIdeal S) := by
  let B : Subalgebra R S := Algebra.EssFiniteType.subalgebra R S
  let M : Submonoid B := Algebra.EssFiniteType.submonoid R S
  let q : Ideal B := Ideal.comap (algebraMap B S) (maximalIdeal S)
  have hq_loc : q.IsPrime ∧ IsLocalization q.primeCompl S := by
    -- Normalize the essential finite type presentation to the localization at the closed point.
    simpa [B, M, q] using
      isLocalizationAtComapMaximalIdeal (P := B) (T := S) M
  have hqf_q : Algebra.QuasiFiniteAt R q := by
    letI : q.IsPrime := hq_loc.1
    letI : IsLocalization q.primeCompl S := hq_loc.2
    -- The dedicated bridge proves quasi-finiteness on the finite-type owner subalgebra.
    exact quasiFiniteAtSubalgebraComapMaximal_of_closedFiber_dimZero B q rfl hκ hdim
  letI : q.IsPrime := hq_loc.1
  letI : IsLocalization q.primeCompl S := hq_loc.2
  letI : Algebra.QuasiFiniteAt R q := hqf_q
  have hstalks : (algebraMap B S).SurjectiveOnStalks := by
    -- A localization map is surjective on all stalks, so quasi-finiteness descends to `S`.
    exact RingHom.surjectiveOnStalks_of_isLocalization q.primeCompl S
  have hcomap :
      q = Ideal.comap (algebraMap B S) (maximalIdeal S) := by
    -- The contracted prime was chosen to be the pullback of the closed point of `S`.
    rfl
  exact Algebra.QuasiFiniteAt.of_surjectiveOnStalks
    q (IsScalarTower.toAlgHom R B S) hstalks (maximalIdeal S) hcomap

omit [IsLocalRing R] [IsLocalHom (algebraMap R S)] in
/-- Helper for Chap10 Lemma 10 124 2: a local essentially finite type algebra that is
quasi-finite at its closed point is a localization of a finite subalgebra. -/
private theorem existsFiniteSubalgebraLocalization_of_quasiFiniteAt_maximalIdeal
    (hqf : Algebra.QuasiFiniteAt R (maximalIdeal S)) :
    ∃ (A : Subalgebra R S) (M : Submonoid A),
      Module.Finite R A ∧ IsLocalization M S := by
  let B : Subalgebra R S := Algebra.EssFiniteType.subalgebra R S
  let M₀ : Submonoid B := Algebra.EssFiniteType.submonoid R S
  let q : Ideal B := Ideal.comap (algebraMap B S) (maximalIdeal S)
  have hq_loc : q.IsPrime ∧ IsLocalization q.primeCompl S := by
    -- The finite-type subalgebra localizes to `S` at the prime contracted from the closed point.
    simpa [B, M₀, q] using
      isLocalizationAtComapMaximalIdeal (P := B) (T := S) M₀
  have hqf_q : Algebra.QuasiFiniteAt R q := by
    letI : q.IsPrime := hq_loc.1
    letI : IsLocalization q.primeCompl S := hq_loc.2
    have h_targetUnits : (maximalIdeal S).primeCompl ≤ IsUnit.submonoid S := by
      intro x hx
      -- Localizing a local ring at the complement of its maximal ideal does not change it.
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_primeCompl_iff,
        Classical.not_not] using hx
    letI : IsLocalization (maximalIdeal S).primeCompl S :=
      IsLocalization.self h_targetUnits
    have hq_to_S : Algebra.QuasiFiniteAt R q ↔ Algebra.QuasiFinite R S := by
      -- Compare the `q`-localization of `B` with the already-local ring `S`.
      exact Algebra.QuasiFinite.iff_of_algEquiv
        ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S).restrictScalars R)
    have hm_to_S :
        Algebra.QuasiFiniteAt R (maximalIdeal S) ↔ Algebra.QuasiFinite R S := by
      -- Compare the maximal localization of `S` with `S` itself.
      exact Algebra.QuasiFinite.iff_of_algEquiv
        ((IsLocalization.algEquiv (maximalIdeal S).primeCompl
          (Localization.AtPrime (maximalIdeal S)) S).restrictScalars R)
    exact hq_to_S.mpr (hm_to_S.mp hqf)
  letI : q.IsPrime := hq_loc.1
  letI : IsLocalization q.primeCompl S := hq_loc.2
  letI : Algebra.QuasiFiniteAt R q := hqf_q
  obtain ⟨A₀, hA₀fg, hA₀finite, r, hrq, haway⟩ :=
    existsFgFiniteSubalgebraAwayMapBijectiveAtPrime (R := R) (T := B) q
  let A : Subalgebra R S := A₀.map B.val
  have hAfinite : Module.Finite R A := by
    -- The image of the finite Zariski-main subalgebra remains finite over `R`.
    simpa [A] using moduleFinite_map_subalgebra_of_fg B A₀ hA₀fg
  let M : Submonoid A := (IsUnit.submonoid S).comap (algebraMap A S)
  refine ⟨A, M, hAfinite, ?_⟩
  -- The remaining localization-composition helper turns the Zariski-main away isomorphism into
  -- the required localization presentation of `S` from the finite image subalgebra.
  simpa [A, M] using
    isLocalizationMappedSubalgebraOfAwayMapBijectiveAtPrime B q A₀ r hrq haway

/-- Consequence of Chap10 Lemma 10 124 2: if `R → S` is a local homomorphism of local rings, `S` is
essentially of finite type over `R`, and the canonical closed fiber
`ClosedFiber = κ(R) ⊗[R] S`, equivalently `S ⧸ maximalIdeal R • S`, has Krull dimension zero,
and the induced residue-field extension `ResidueField R → ResidueField S` is finite, then `S`
is the localization of a finite
`R`-subalgebra of `S`. -/
-- Proof sketch: first apply the previous theorem to obtain the canonical owner
-- `Algebra.QuasiFiniteAt R (maximalIdeal S)`. Present `S` by the canonical finite-type
-- subalgebra coming from `Algebra.EssFiniteType`, use Lemma `10.123.13` to shrink to a basic open
-- neighborhood on which the map is quasi-finite, and then apply Lemma `10.123.14` to replace
-- that neighborhood by the localization of a finite `R`-subalgebra of `S`.
@[stacks 052V]
theorem exists_finite_algebra_localization_of_essFiniteType_of_closedFiber_dimZero
    (hκ : Module.Finite (ResidueField R) (ResidueField S))
    (hdim : ringKrullDim ClosedFiber = 0) :
    ∃ (A : Subalgebra R S) (M : Submonoid A),
      Module.Finite R A ∧ IsLocalization M S := by
  -- The closed-fiber criterion supplies quasi-finiteness at the closed point; the remaining
  -- Zariski-main helper turns that owner predicate into the finite-subalgebra localization.
  exact existsFiniteSubalgebraLocalization_of_quasiFiniteAt_maximalIdeal
    (quasiFiniteAt_maximalIdeal_of_closedFiber_dimZero hκ hdim)

end

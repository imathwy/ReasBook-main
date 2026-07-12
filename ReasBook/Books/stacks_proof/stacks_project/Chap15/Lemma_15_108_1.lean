import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum Ideal

/- Domain triage:
* primary domain: commutative algebra on fibers of `Spec B → Spec A`;
* sampled owner abstractions: `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, the quasi-finite fiber theorem
  `Algebra.QuasiFinite.eq_of_le_of_under_eq`, `Ideal.primesOver`, and the Chapter 10 bridge
  `ringHom_injective_tfae_of_image_contains_dense_set`;
* source-facing layer: the theorem `ideal_comap_ne_bot_of_cases`, whose hypothesis is the direct
  seven-way disjunction from Stacks Lemma `15.108.1`, expressed on the owner predicates for
  intermediate algebras together with the fiberwise specialization condition on
  `p.asIdeal.primesOver B` and the proposition-valued unique generic-fiber condition
  `Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B)`;
* core/canonical layer: the owner predicates `Algebra.Etale`, `Algebra.Unramified`,
  `Algebra.QuasiFinite`, `Algebra.IsIntegral`, and the owner fiber sets `p.asIdeal.primesOver B`.

Primitive data vs. derived API:
* primitive data in the localization clauses: an intermediate `A`-algebra `C`, a localization
  `C → B`, and one of the canonical owner predicates on `C`;
* derived API: the fiberwise antisymmetry consequence of quasi-finiteness and the generic-point
  image criterion over `Spec A`.
-/

variable {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
variable [Algebra A B]

/-- Helper for Lemma 15.108.1: in an integral extension, two distinct primes with the same image
in the base are incomparable. -/
lemma primes_over_same_prime_are_incomparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (q q' : PrimeSpectrum S) (hqq' : q ≠ q')
    (himage : PrimeSpectrum.comap (algebraMap R S) q = PrimeSpectrum.comap (algebraMap R S) q') :
    ¬ q ≤ q' ∧ ¬ q' ≤ q := by
  -- Compare strict containments after contracting along the integral map.
  have hnot_le :
      ∀ ⦃x y : PrimeSpectrum S⦄,
        x ≠ y →
        PrimeSpectrum.comap (algebraMap R S) x = PrimeSpectrum.comap (algebraMap R S) y →
        ¬ x ≤ y := by
    intro x y hxy hxy_image hxy_le
    have hlt : x.asIdeal < y.asIdeal := by
      refine lt_of_le_of_ne hxy_le ?_
      intro hEq
      exact hxy (PrimeSpectrum.ext hEq)
    obtain ⟨hle, z, hzy, hzx⟩ := SetLike.lt_iff_le_and_exists.mp hlt
    have hcomap :
        Ideal.comap (algebraMap R S) x.asIdeal = Ideal.comap (algebraMap R S) y.asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hxy_image
    exact
      (Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hzy, hzx⟩
        (Algebra.IsIntegral.isIntegral z)).ne hcomap
  exact ⟨hnot_le hqq' himage, hnot_le hqq'.symm himage.symm⟩

/-- Helper for Lemma 15.108.1: over a domain, a flat target module is torsion free, so the
structural algebra map is injective. -/
lemma algebraMap_injective_of_flat_domain_target [Module.Flat A B] :
    Function.Injective (algebraMap A B) := by
  -- Torsion-freeness rules out a nonzero scalar killing `1`.
  let _ : Module.IsTorsionFree A B :=
    (Submodule.isTorsionFree_iff_torsion_eq_bot).2 Module.Flat.torsion_eq_bot
  intro a b hab
  have hmap : algebraMap A B (a - b) = 0 := by
    simpa [map_sub] using sub_eq_zero.mpr hab
  have hsmul : (a - b) • (1 : B) = 0 := by
    simpa [Algebra.smul_def, hmap]
  have hzero_or : a - b = 0 ∨ (1 : B) = 0 := (smul_eq_zero.mp hsmul)
  exact sub_eq_zero.mp (hzero_or.resolve_right one_ne_zero)

/-- Helper for Lemma 15.108.1: injectivity of `A → B` is equivalent to `(0 : Ideal B)` lying
over `(0 : Ideal A)`. -/
lemma under_bot_eq_bot_of_injective
    (hinj : Function.Injective (algebraMap A B)) :
    Ideal.under A (⊥ : Ideal B) = ⊥ := by
  -- Contracting the zero ideal is exactly the kernel of the structural map.
  simpa [Ideal.under_def] using
    (RingHom.injective_iff_ker_eq_bot (algebraMap A B)).mp hinj

/-- Helper for Lemma 15.108.1: if the generic fiber over `(0)` is nonempty, then the algebra map
`A → B` is injective. -/
lemma algebraMap_injective_of_nonempty_generic_fiber
    (hgeneric : Nonempty ((⊥ : Ideal A).primesOver B)) :
    Function.Injective (algebraMap A B) := by
  rcases hgeneric with ⟨q⟩
  -- Any prime in the generic fiber contracts to `(0)`, so the kernel is forced to vanish.
  have hq_comap : Ideal.comap (algebraMap A B) q.1 = (⊥ : Ideal A) := by
    simpa [Ideal.under_def] using q.2.2.over.symm
  rw [RingHom.injective_iff_ker_eq_bot]
  refine le_antisymm ?_ bot_le
  simpa [RingHom.ker, hq_comap] using
    (Ideal.comap_mono (f := algebraMap A B) (show (⊥ : Ideal B) ≤ q.1 from bot_le :
      (⊥ : Ideal B) ≤ q.1))

/-- Helper for Lemma 15.108.1: once `A → B` is injective, the zero ideal of `B` is a point of the
generic fiber over `(0)`. -/
lemma bot_lies_over_bot_of_injective
    (hinj : Function.Injective (algebraMap A B)) :
    (⊥ : Ideal B).LiesOver (⊥ : Ideal A) := by
  -- The zero ideal of `B` contracts to the zero ideal of `A`.
  exact (Ideal.liesOver_iff (⊥ : Ideal B) (⊥ : Ideal A)).2 <|
    (under_bot_eq_bot_of_injective hinj).symm

/-- Helper for Lemma 15.108.1: injectivity places the zero ideal of `B` in the generic fiber
over `(0)`. -/
lemma nonempty_generic_fiber_of_injective
    (hinj : Function.Injective (algebraMap A B)) :
    Nonempty ((⊥ : Ideal A).primesOver B) := by
  letI : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) := bot_lies_over_bot_of_injective hinj
  -- The zero prime of the domain `B` is therefore a point of the generic fiber.
  exact ⟨Ideal.primesOver.mk (⊥ : Ideal A) (⊥ : Ideal B)⟩

/-- Helper for Lemma 15.108.1: if the generic fiber over `(0)` is a subsingleton, then every
prime over `(0)` is the zero ideal. -/
lemma generic_fiber_prime_eq_bot
    (hgeneric : Nonempty ((⊥ : Ideal A).primesOver B))
    (hsub : Subsingleton ((⊥ : Ideal A).primesOver B))
    {Q : Ideal B} [Q.IsPrime] (hQ : Q.LiesOver (⊥ : Ideal A)) :
    Q = ⊥ := by
  letI : Q.LiesOver (⊥ : Ideal A) := hQ
  let qQ : ((⊥ : Ideal A).primesOver B) := Ideal.primesOver.mk (⊥ : Ideal A) Q
  let hinj : Function.Injective (algebraMap A B) :=
    algebraMap_injective_of_nonempty_generic_fiber hgeneric
  letI : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) := bot_lies_over_bot_of_injective hinj
  let q0 : ((⊥ : Ideal A).primesOver B) := Ideal.primesOver.mk (⊥ : Ideal A) (⊥ : Ideal B)
  -- The subsingleton generic fiber identifies every prime over `(0)` with the zero prime.
  exact congrArg Subtype.val (Subsingleton.elim qQ q0)

/-- Helper for Lemma 15.108.1: if `(0 : Ideal B)` lies over `(0 : Ideal A)` and there are no
nontrivial specializations inside fibers, then the generic fiber is a subsingleton. -/
lemma generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations
    (hzero : Ideal.under A (⊥ : Ideal B) = ⊥)
    (hnospec :
      ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q') :
    Subsingleton ((⊥ : Ideal A).primesOver B) := by
  let p0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  letI : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) :=
    (Ideal.liesOver_iff (⊥ : Ideal B) (⊥ : Ideal A)).2 hzero.symm
  let q0 : p0.asIdeal.primesOver B := Ideal.primesOver.mk p0.asIdeal (⊥ : Ideal B)
  refine ⟨fun q q' ↦ ?_⟩
  -- The zero prime is the distinguished generic-fiber point, and every point specializes to it.
  have hq0q : q0 = q := hnospec p0 q0 q (show q0.1 ≤ q.1 from bot_le)
  have hq0q' : q0 = q' := hnospec p0 q0 q' (show q0.1 ≤ q'.1 from bot_le)
  exact hq0q.symm.trans hq0q'

/-- Helper for Lemma 15.108.1: a localization of a quasi-finite algebra has no nontrivial
specializations inside fibers. -/
lemma fiberwise_no_specializations_of_localized_quasi_finite
    (hloc :
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.QuasiFinite A C ∧ IsLocalization M B) :
    ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q' := by
  rcases hloc with ⟨C, _, _, _, _, M, hqf, hlocB⟩
  letI : Algebra.QuasiFinite A C := hqf
  letI : IsLocalization M B := hlocB
  intro p q q' hqq'
  let e := IsLocalization.orderIsoOfPrime M B
  let r : Ideal C := (e ⟨q.1, q.2.1⟩).1
  let r' : Ideal C := (e ⟨q'.1, q'.2.1⟩).1
  letI : r.IsPrime := (e ⟨q.1, q.2.1⟩).2.1
  letI : r'.IsPrime := (e ⟨q'.1, q'.2.1⟩).2.1
  -- Lift the specialization inside the fiber to the intermediate quasi-finite algebra.
  have hrr' : r ≤ r' := e.monotone hqq'
  have hr_under : Ideal.under A r = p.asIdeal := by
    simpa [r, e, Ideal.under_def, Ideal.comap_comap, IsScalarTower.algebraMap_eq A C B] using
      q.2.2.over.symm
  have hr'_under : Ideal.under A r' = p.asIdeal := by
    simpa [r', e, Ideal.under_def, Ideal.comap_comap, IsScalarTower.algebraMap_eq A C B] using
      q'.2.2.over.symm
  have hrr_eq : r = r' :=
    Algebra.QuasiFinite.eq_of_le_of_under_eq r r' hrr' (hr_under.trans hr'_under.symm)
  -- Then descend the equality back through the localization/order correspondence.
  have hdomain :
      (⟨q.1, q.2.1⟩ : { P : Ideal B // P.IsPrime }) =
        ⟨q'.1, q'.2.1⟩ := e.injective <| Subtype.ext hrr_eq
  apply Subtype.ext
  exact congrArg (fun x : { P : Ideal B // P.IsPrime } ↦ x.1) hdomain

/-- Helper for Lemma 15.108.1: a localization of an étale algebra has no nontrivial
specializations inside fibers. -/
lemma fiberwise_no_specializations_of_localized_etale
    (hloc :
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.Etale A C ∧ IsLocalization M B) :
    ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q' := by
  rcases hloc with ⟨C, _, _, _, _, M, hEtale, hlocB⟩
  letI : Algebra.Etale A C := hEtale
  have hqf : Algebra.QuasiFinite A C := inferInstance
  -- Repackage the same localization witness through the canonical quasi-finite owner.
  exact fiberwise_no_specializations_of_localized_quasi_finite
    ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, M, hqf, hlocB⟩

/-- Helper for Lemma 15.108.1: a localization of an integral algebra has no nontrivial
specializations inside fibers. -/
lemma fiberwise_no_specializations_of_localized_integral
    (hloc :
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.IsIntegral A C ∧ IsLocalization M B) :
    ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q' := by
  rcases hloc with ⟨C, _, _, _, _, M, hint, hlocB⟩
  letI : Algebra.IsIntegral A C := hint
  letI : IsLocalization M B := hlocB
  intro p q q' hqq'
  let e := IsLocalization.orderIsoOfPrime M B
  let r : Ideal C := (e ⟨q.1, q.2.1⟩).1
  let r' : Ideal C := (e ⟨q'.1, q'.2.1⟩).1
  letI : r.IsPrime := (e ⟨q.1, q.2.1⟩).2.1
  letI : r'.IsPrime := (e ⟨q'.1, q'.2.1⟩).2.1
  -- Lift the specialization to the integral source algebra and rule out a strict inequality there.
  have hrr' : r ≤ r' := e.monotone hqq'
  have hr_under : Ideal.under A r = p.asIdeal := by
    simpa [r, e, Ideal.under_def, Ideal.comap_comap, IsScalarTower.algebraMap_eq A C B] using
      q.2.2.over.symm
  have hr'_under : Ideal.under A r' = p.asIdeal := by
    simpa [r', e, Ideal.under_def, Ideal.comap_comap, IsScalarTower.algebraMap_eq A C B] using
      q'.2.2.over.symm
  have hrr_eq : r = r' := by
    by_contra hne
    let rq : PrimeSpectrum C := ⟨r, inferInstance⟩
    let rq' : PrimeSpectrum C := ⟨r', inferInstance⟩
    have himage :
        PrimeSpectrum.comap (algebraMap A C) rq =
          PrimeSpectrum.comap (algebraMap A C) rq' := by
      apply PrimeSpectrum.ext
      simpa [PrimeSpectrum.comap_asIdeal] using hr_under.trans hr'_under.symm
    exact (primes_over_same_prime_are_incomparable rq rq' (by simpa [rq, rq'] using hne) himage).1
      hrr'
  -- Descend the equality of lifted primes back to the localization.
  have hdomain :
      (⟨q.1, q.2.1⟩ : { P : Ideal B // P.IsPrime }) =
        ⟨q'.1, q'.2.1⟩ := e.injective <| Subtype.ext hrr_eq
  apply Subtype.ext
  exact congrArg (fun x : { P : Ideal B // P.IsPrime } ↦ x.1) hdomain

/-- Helper for Lemma 15.108.1: a localization of an unramified algebra has no nontrivial
specializations inside fibers. -/
lemma fiberwise_no_specializations_of_localized_unramified
    (hloc :
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
        (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.Unramified A C ∧ IsLocalization M B) :
    ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q' := by
  rcases hloc with ⟨C, _, _, _, _, M, hunram, hlocB⟩
  letI : Algebra.Unramified A C := hunram
  have hqf : Algebra.QuasiFinite A C := inferInstance
  -- Mathlib packages global unramifiedness as a quasi-finite algebra, so the same localization
  -- comparison used in the quasi-finite branch applies unchanged.
  exact fiberwise_no_specializations_of_localized_quasi_finite
    ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, M, hqf, hlocB⟩

/-- Helper for Lemma 15.108.1: once the generic fiber over `(0)` is nonempty and a singleton,
every nonzero ideal of `B` has nonzero contraction to `A`. -/
lemma ideal_comap_ne_bot_of_unique_generic_fiber
    (hgeneric : Nonempty ((⊥ : Ideal A).primesOver B))
    (hsub : Subsingleton ((⊥ : Ideal A).primesOver B))
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := by
  classical
  intro hcomap
  let S : Submonoid B := ((⊥ : Ideal A).primeCompl).map (algebraMap A B)
  have hdisj : Disjoint (J : Set B) S := by
    rw [Set.disjoint_left]
    intro y hyJ hyS
    rcases hyS with ⟨a, ha, rfl⟩
    have haJ : a ∈ J.comap (algebraMap A B) := hyJ
    have ha0 : a ∈ (⊥ : Ideal A) := by simpa [hcomap] using haJ
    exact ha ha0
  -- A prime over `J` disjoint from the image of the nonzero elements of `A`
  -- is precisely a point in the generic fiber.
  obtain ⟨Q, hQprime, hJQ, hQdisj⟩ := Ideal.exists_le_prime_disjoint J S hdisj
  letI : Q.IsPrime := hQprime
  have hQunder : Ideal.under A Q = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro a haQ
    by_contra ha0
    have haS : algebraMap A B a ∈ S := by
      exact ⟨a, by simpa [Ideal.primeCompl] using ha0, rfl⟩
    exact (Set.disjoint_left.mp hQdisj) haQ haS
  have hQover : Q.LiesOver (⊥ : Ideal A) :=
    (Ideal.liesOver_iff Q (⊥ : Ideal A)).2 hQunder.symm
  have hQbot : Q = ⊥ := generic_fiber_prime_eq_bot hgeneric hsub hQover
  have hJle_bot : J ≤ ⊥ := by
    simpa [hQbot] using hJQ
  have hJbot : J = ⊥ := le_antisymm hJle_bot bot_le
  exact hJ hJbot

-- Proof sketch: reduce cases (1) through (6) to the unique-generic-fiber case as in the Stacks
-- proof. In that case a nonzero element of `J` becomes a unit after inverting the nonzero
-- elements of `A`, and clearing denominators returns a nonzero element of `A ∩ J`.
/-- Lemma 15.108.1: under any of the seven stated hypotheses on the domain map `A → B`, every
nonzero ideal of `B` has nonzero contraction to `A`. -/
@[stacks 0GS5]
theorem ideal_comap_ne_bot_of_cases
    (hAB :
      (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
          (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Etale A C ∧ IsLocalization M B) ∨
        (Module.Flat A B ∧
          ((∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.Unramified A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.QuasiFinite A C ∧ IsLocalization M B) ∨
            (∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
              (_ : IsScalarTower A C B) (M : Submonoid C),
              Algebra.IsIntegral A C ∧ IsLocalization M B) ∨
            ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q')) ∨
        (Nonempty ((⊥ : Ideal A).primesOver B) ∧
          ∀ (p : PrimeSpectrum A) (q q' : p.asIdeal.primesOver B), q ≤ q' → q = q') ∨
      Nonempty ((⊥ : Ideal A).primesOver B) ∧ Subsingleton ((⊥ : Ideal A).primesOver B))
    (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap (algebraMap A B) ≠ ⊥ := by
  rcases hAB with hEtale | hRest
  · rcases hEtale with ⟨C, _, _, _, _, M, hEtale, hlocB⟩
    letI : Algebra.Etale A C := hEtale
    letI : IsLocalization M B := hlocB
    have hflatC : Module.Flat A C := by
      rw [← RingHom.flat_algebraMap_iff]
      exact
        (RingHom.Etale.iff_flat_and_formallyUnramified (f := algebraMap A C)).mp
          ((RingHom.etale_algebraMap (R := A) (S := C)).mpr hEtale) |>.1
    letI : Module.Flat A C := hflatC
    have hflatCB : Module.Flat C B := IsLocalization.flat B M
    letI : Module.Flat A B := Module.Flat.trans A C B
    -- Étale maps are flat, so the generic point lies in the fiber and the étale adapter gives
    -- fiberwise antisymmetry exactly as in the quasi-finite branch.
    have hinj : Function.Injective (algebraMap A B) :=
      algebraMap_injective_of_flat_domain_target
    have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
      under_bot_eq_bot_of_injective hinj
    have hsub :
        Subsingleton ((⊥ : Ideal A).primesOver B) :=
      generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero
        (fiberwise_no_specializations_of_localized_etale
          ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, M, hEtale, hlocB⟩)
    exact ideal_comap_ne_bot_of_unique_generic_fiber
      (nonempty_generic_fiber_of_injective hinj) hsub J hJ
  rcases hRest with ⟨hflat, hcases⟩ | hgeneric | hunique
  · rcases hcases with hunram | hquasi | hint | hnospec
    · -- Flatness again places `(0)` in the generic fiber, and the unramified adapter reduces the
      -- branch to the same fiberwise antisymmetry statement used for quasi-finite maps.
      letI : Module.Flat A B := hflat
      have hinj : Function.Injective (algebraMap A B) :=
        algebraMap_injective_of_flat_domain_target
      have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
        under_bot_eq_bot_of_injective hinj
      have hsub :
          Subsingleton ((⊥ : Ideal A).primesOver B) :=
        generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero
          (fiberwise_no_specializations_of_localized_unramified hunram)
      exact ideal_comap_ne_bot_of_unique_generic_fiber
        (nonempty_generic_fiber_of_injective hinj) hsub J hJ
    · -- Flatness gives `(0)` in the generic fiber, and quasi-finiteness makes that fiber a singleton.
      letI : Module.Flat A B := hflat
      have hinj : Function.Injective (algebraMap A B) :=
        algebraMap_injective_of_flat_domain_target
      have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
        under_bot_eq_bot_of_injective hinj
      have hsub :
          Subsingleton ((⊥ : Ideal A).primesOver B) :=
        generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero
          (fiberwise_no_specializations_of_localized_quasi_finite hquasi)
      exact ideal_comap_ne_bot_of_unique_generic_fiber
        (nonempty_generic_fiber_of_injective hinj) hsub J hJ
    · -- Flatness again gives `(0)` in the generic fiber, while integrality kills strict
      -- specializations inside fibers after lifting through the localization.
      letI : Module.Flat A B := hflat
      have hinj : Function.Injective (algebraMap A B) :=
        algebraMap_injective_of_flat_domain_target
      have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
        under_bot_eq_bot_of_injective hinj
      have hsub :
          Subsingleton ((⊥ : Ideal A).primesOver B) :=
        generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero
          (fiberwise_no_specializations_of_localized_integral hint)
      exact ideal_comap_ne_bot_of_unique_generic_fiber
        (nonempty_generic_fiber_of_injective hinj) hsub J hJ
    · -- The source already gives the no-specialization condition on fibers.
      letI : Module.Flat A B := hflat
      have hinj : Function.Injective (algebraMap A B) :=
        algebraMap_injective_of_flat_domain_target
      have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
        under_bot_eq_bot_of_injective hinj
      have hsub :
          Subsingleton ((⊥ : Ideal A).primesOver B) :=
        generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero hnospec
      exact ideal_comap_ne_bot_of_unique_generic_fiber
        (nonempty_generic_fiber_of_injective hinj) hsub J hJ
  · -- Here the generic point is already known to be in the image, and the fiberwise condition
    -- collapses that generic fiber to a singleton.
    rcases hgeneric with ⟨hnonempty, hnospec⟩
    let hinj : Function.Injective (algebraMap A B) :=
      algebraMap_injective_of_nonempty_generic_fiber hnonempty
    have hzero : Ideal.under A (⊥ : Ideal B) = (⊥ : Ideal A) :=
      under_bot_eq_bot_of_injective hinj
    have hsub :
        Subsingleton ((⊥ : Ideal A).primesOver B) :=
      generic_fiber_subsingleton_of_zero_lies_over_and_no_specializations hzero hnospec
    exact ideal_comap_ne_bot_of_unique_generic_fiber hnonempty hsub J hJ
  · -- This is exactly the unique-generic-fiber endgame.
    rcases hunique with ⟨hnonempty, hsub⟩
    exact ideal_comap_ne_bot_of_unique_generic_fiber hnonempty hsub J hJ

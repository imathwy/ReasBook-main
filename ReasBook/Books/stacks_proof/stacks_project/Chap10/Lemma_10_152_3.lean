import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_145_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
* primary domain: étale-local product decompositions for unramified finite-type algebra maps, with
  fiber primes tracked over a chosen base prime;
* sampled owner declarations:
  `exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder`,
  `exists_etale_baseChange_prod_of_isUnramifiedAt`,
  `Ideal.primesOver`,
  `Algebra.isUnramifiedAt_iff_map_eq`;
* best owner abstraction:
  the chapter-local decomposition theorem
  `exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder`,
  with factor primes recorded in the canonical owner fibers `p'.primesOver (A i)`;
* source/core/bridge triage:
  - `source-facing`: the present theorem, which keeps the finite product decomposition and upgrades
    the factor conclusions to surjectivity in the unramified case;
  - `core/canonical`: `Ideal.primesOver` for the distinguished factor primes;
  - `bridge/view`: the atomic identification of each distinguished prime with the extended ideal
    `Ideal.map (algebraMap R' (A i)) p'`;
* primitive data:
  an unramified `R`-algebra `S` and a prime `p ⊂ R`;
* derived API:
  the étale neighborhood, the finite family of factors, the distinguished primes over `p'`, the
  surjectivity of `R' → Aᵢ`, and the absence of primes of the remainder over `p'`.
-/

/-- Helper for Chap10 Lemma 10 152 3: a surjective image of an unramified algebra is
unramified over the same base. -/
private lemma unramified_of_surjective_algHom
    {R₀ : Type u} {T : Type (max u v)} {A : Type (max u v)}
    [CommRing R₀] [CommRing T] [CommRing A] [Algebra R₀ T] [Algebra R₀ A]
    [Algebra.Unramified R₀ T] (f : T →ₐ[R₀] A) (hf : Function.Surjective f) :
    Algebra.Unramified R₀ A := by
  -- Formal unramifiedness and finite type both descend through a surjective algebra map.
  exact ⟨Algebra.FormallyUnramified.of_surjective f hf, Algebra.FiniteType.of_surjective f hf⟩

/-- Helper for Chap10 Lemma 10 152 3: a factor in a product decomposition of an unramified
algebra is unramified over the base. -/
private lemma unramified_factor_of_algEquiv
    {R₀ : Type u} {T : Type (max u v)} {ι : Type (max u v)}
    {A : ι → Type (max u v)} {B : Type (max u v)}
    [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [∀ i, CommRing (A i)] [∀ i, Algebra R₀ (A i)] [CommRing B] [Algebra R₀ B]
    [Algebra.Unramified R₀ T]
    (e : T ≃ₐ[R₀] ((i : ι) → A i) × B) (i : ι) :
    Algebra.Unramified R₀ (A i) := by
  -- Project the product decomposition to the chosen factor and descend unramifiedness.
  let φ : T →ₐ[R₀] A i :=
    (Pi.evalAlgHom R₀ A i).comp ((AlgHom.fst R₀ ((j : ι) → A j) B).comp e.toAlgHom)
  have hφ : Function.Surjective φ :=
    (Function.surjective_eval i).comp (Prod.fst_surjective.comp e.surjective)
  exact unramified_of_surjective_algHom φ hφ

/-- Helper for Chap10 Lemma 10 152 3: the remainder in a product decomposition of an
unramified algebra is unramified over the base. -/
private lemma unramified_remainder_of_algEquiv
    {R₀ : Type u} {T : Type (max u v)} {ι : Type (max u v)}
    {A : ι → Type (max u v)} {B : Type (max u v)}
    [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [∀ i, CommRing (A i)] [∀ i, Algebra R₀ (A i)] [CommRing B] [Algebra R₀ B]
    [Algebra.Unramified R₀ T]
    (e : T ≃ₐ[R₀] ((i : ι) → A i) × B) :
    Algebra.Unramified R₀ B := by
  -- Project the product decomposition to the remainder and descend unramifiedness.
  let φ : T →ₐ[R₀] B := (AlgHom.snd R₀ ((j : ι) → A j) B).comp e.toAlgHom
  have hφ : Function.Surjective φ := Prod.snd_surjective.comp e.surjective
  exact unramified_of_surjective_algHom φ hφ

/-- Helper for Chap10 Lemma 10 152 3: a globally unramified algebra is quasi-finite at every
prime. -/
private lemma quasiFiniteAt_of_unramified
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A] [Algebra.Unramified R₀ A]
    (q : Ideal A) [q.IsPrime] :
    Algebra.QuasiFiniteAt R₀ q := by
  -- The canonical local quasi-finiteness instance is available from global unramifiedness.
  exact (inferInstance : Algebra.QuasiFiniteAt R₀ q)

/-- Helper for Chap10 Lemma 10 152 3: a purely inseparable residue-field extension attached to
an unramified prime is surjective. -/
private lemma residueFieldMap_surjective_of_unramified_purelyInseparable
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A] [Algebra.EssFiniteType R₀ A]
    (p₀ : Ideal R₀) [p₀.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p₀]
    [Algebra.IsUnramifiedAt R₀ q] [IsPurelyInseparable p₀.ResidueField q.ResidueField] :
    Function.Surjective (algebraMap p₀.ResidueField q.ResidueField) := by
  -- Unramifiedness gives separability, and separable plus purely inseparable forces equality.
  exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable p₀.ResidueField q.ResidueField

/-- Helper for Chap10 Lemma 10 152 3: the distinguished residue-field maps in a pure product
decomposition are surjective in the unramified case. -/
private lemma residueFieldMaps_surjective_of_unramified_decomposition
    {R₀ : Type u} {T : Type (max u v)} {ι : Type (max u v)}
    {A : ι → Type (max u v)} {B : Type (max u v)}
    [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [∀ i, CommRing (A i)] [∀ i, Algebra R₀ (A i)] [CommRing B] [Algebra R₀ B]
    [Algebra.Unramified R₀ T]
    (p₀ : Ideal R₀) [p₀.IsPrime]
    (e : T ≃ₐ[R₀] ((i : ι) → A i) × B)
    (r : ∀ i, p₀.primesOver (A i))
    (hres : ∀ i, FiniteDimensional p₀.ResidueField (r i).1.ResidueField ∧
      IsPurelyInseparable p₀.ResidueField (r i).1.ResidueField) :
    ∀ i, Function.Surjective (algebraMap p₀.ResidueField (r i).1.ResidueField) := by
  intro i
  -- Transfer unramifiedness to the selected finite factor before reading the residue extension.
  have hAi : Algebra.Unramified R₀ (A i) := unramified_factor_of_algEquiv e i
  letI : IsPurelyInseparable p₀.ResidueField (r i).1.ResidueField := (hres i).2
  exact residueFieldMap_surjective_of_unramified_purelyInseparable p₀ (r i).1

/-- Helper for Chap10 Lemma 10 152 3: an unramified remainder cannot have a prime over the
chosen base prime if the product decomposition says every such prime is not quasi-finite. -/
private lemma noPrimesOver_remainder_of_unramified_decomposition
    {R₀ : Type u} {T : Type (max u v)} {ι : Type (max u v)}
    {A : ι → Type (max u v)} {B : Type (max u v)}
    [CommRing R₀] [CommRing T] [Algebra R₀ T]
    [∀ i, CommRing (A i)] [∀ i, Algebra R₀ (A i)] [CommRing B] [Algebra R₀ B]
    [Algebra.Unramified R₀ T]
    (p₀ : Ideal R₀) [p₀.IsPrime]
    (e : T ≃ₐ[R₀] ((i : ι) → A i) × B)
    (hnonQuasiFinite : ∀ q : p₀.primesOver B, ¬ Algebra.QuasiFiniteAt R₀ q.1) :
    ∀ _ : p₀.primesOver B, False := by
  -- The remainder inherits unramifiedness, hence quasi-finiteness at every prime.
  have hB : Algebra.Unramified R₀ B := unramified_remainder_of_algEquiv e
  intro q
  exact hnonQuasiFinite q (quasiFiniteAt_of_unramified q.1)

/-- Helper for Chap10 Lemma 10 152 3: a nonempty subsingleton fiber of primes over `p` is the
singleton consisting of its distinguished prime. -/
private lemma primesOver_eq_singleton_of_subsingleton
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p₀ : Ideal R₀) [p₀.IsPrime] (r : p₀.primesOver A)
    [Subsingleton (p₀.primesOver A)] :
    p₀.primesOver A = {r.1} := by
  -- Reduce the set equality to uniqueness in the canonical `primesOver` subtype.
  ext q
  constructor
  · intro hq
    let qOver : p₀.primesOver A := ⟨q, hq⟩
    have hqr : qOver = r := Subsingleton.elim qOver r
    simpa [qOver] using congrArg Subtype.val hqr
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    rw [hq]
    exact r.2

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap10 Lemma 10 152 3: surjectivity on the local rings at the unique prime over
`p` implies surjectivity after inverting one element outside `p`. -/
private lemma exists_awayMap_surjective_of_localRingHom_surjective
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p₀ : Ideal R₀) [p₀.IsPrime] (q : Ideal A) [q.IsPrime]
    [Module.Finite R₀ A] [q.LiesOver p₀]
    (hunique : p₀.primesOver A = {q})
    (H : Function.Surjective
      (Localization.localRingHom p₀ q (algebraMap R₀ A) (q.over_def p₀))) :
    ∃ s ∉ p₀, ∀ t, s ∣ t →
      Function.Surjective (Localization.awayMap (algebraMap R₀ A) t) := by
  classical
  -- First clear denominators for every element of `A` using surjectivity on the local rings.
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R₀) (A := A)
  have hclear (x : A) : ∃ a, ∃ b ∉ p₀, algebraMap R₀ A a = x * algebraMap R₀ A b := by
    have hx :=
      (IsLocalization.mk'_surjective p₀.primeCompl).exists.mp (H (algebraMap _ _ x))
    simp only [Localization.localRingHom_mk', Prod.exists, Subtype.exists,
      Ideal.mem_primeCompl_iff, IsLocalization.mk'_eq_iff_eq_mul, exists_prop, ← map_mul,
      IsLocalization.eq_iff_exists q.primeCompl] at hx
    obtain ⟨a, b, hbp, c, hcq, hc⟩ := hx
    obtain ⟨d, hd, _, hdvd⟩ :=
      Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hunique _ hcq
    exact ⟨d * a, d * b, ‹p₀.IsPrime›.mul_notMem hd hbp, by grind⟩
  choose a b hbp heq using hclear
  have hprod : ∏ i ∈ s, b i ∈ p₀.primeCompl :=
    prod_mem fun i _ ↦ (show b i ∈ p₀.primeCompl from hbp i)
  refine ⟨∏ i ∈ s, b i, ?_, ?_⟩
  · simpa [Ideal.mem_primeCompl_iff] using hprod
  intro t ht
  -- The finite generator equations put every element of `A` in the range of the away map.
  have hrange :
      (IsScalarTower.toAlgHom R₀ A _).range ≤
        (Localization.awayMapₐ (Algebra.ofId R₀ A) t).range := by
    rw [← Algebra.map_top, Subalgebra.map_le, ← hs, Algebra.adjoin_le_iff]
    intro x hxs
    obtain ⟨t', ht'⟩ := ht
    refine ⟨IsLocalization.mk' (M := .powers t) _
      (t' * (∏ i ∈ s.erase x, b i) * a x) ⟨_, 1, rfl⟩, ?_⟩
    dsimp [Localization.awayMapₐ, IsLocalization.Away.map]
    simp only [pow_one, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul,
      ← map_mul (algebraMap A _), map_mul (algebraMap R₀ _), heq]
    congr 1
    rw [ht', ← Finset.prod_erase_mul s b hxs, map_mul, map_mul]
    ring_nf
  -- Finally pass from elements of `A` to arbitrary fractions in the localized target.
  intro x
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (.powers (algebraMap R₀ A t)) x
  obtain ⟨y, hy : Localization.awayMap _ _ _ = _⟩ := hrange ⟨x, rfl⟩
  dsimp at hy
  refine ⟨y * Localization.Away.invSelf _ ^ n, ?_⟩
  simp only [map_mul, hy]
  simp [Localization.Away.invSelf, Localization.mk_eq_mk', Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_mk', ← Algebra.smul_def,
    IsLocalization.smul_mk', ← IsLocalization.mk'_pow]

/-- Helper for Chap10 Lemma 10 152 3: local surjectivity at the unique prime over `p` spreads
to surjectivity after inverting one element outside `p`. -/
private lemma exists_awayMap_surjective_of_residueField_surjective
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p₀ : Ideal R₀) [p₀.IsPrime] (q : Ideal A) [q.IsPrime]
    [Module.Finite R₀ A] [q.LiesOver p₀] [Algebra.IsUnramifiedAt R₀ q]
    (hunique : p₀.primesOver A = {q})
    (hres : Function.Surjective (algebraMap p₀.ResidueField q.ResidueField)) :
    ∃ s ∉ p₀, ∀ t, s ∣ t →
      Function.Surjective (Localization.awayMap (algebraMap R₀ A) t) := by
  -- Convert residue-field surjectivity into local-ring surjectivity, then clear one finite set of
  -- denominators to get surjectivity on a basic open.
  exact exists_awayMap_surjective_of_localRingHom_surjective p₀ q hunique
    (Localization.localRingHom_surjective_of_primesOver_eq_singleton hunique hres)

/-- Helper for Chap10 Lemma 10 152 3: a prime ideal avoids all powers of an element outside
the prime. -/
private lemma disjoint_powers_of_notMem_prime
    {R₀ : Type u} [CommRing R₀] {p₀ : Ideal R₀} [p₀.IsPrime] {s : R₀}
    (hs : s ∉ p₀) :
    Disjoint (Submonoid.powers s : Set R₀) (p₀ : Set R₀) := by
  -- This is the standard radical criterion specialized to prime ideals.
  simpa using
    (Ideal.disjoint_powers_iff_notMem s ((inferInstance : p₀.IsPrime).isRadical)).2 hs

/-- Helper for Chap10 Lemma 10 152 3: the canonical algebra map to the map-submonoid
localization is surjective exactly when the corresponding `awayMap` is surjective. -/
private lemma algebraMap_localization_surjective_of_awayMap_surjective
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A] (s : R₀)
    (H : Function.Surjective (Localization.awayMap (algebraMap R₀ A) s)) :
    Function.Surjective
      (algebraMap (Localization (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) := by
  -- Put the target localization into the same `Away` normal form used by `Localization.awayMap`.
  letI : IsLocalization.Away (algebraMap R₀ A s)
      (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s))) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  rw [Localization.awayMap, IsLocalization.Away.map_surjective_iff] at H
  rw [localizationAlgebraMap_def]
  change Function.Surjective (IsLocalization.Away.map (Localization.Away s)
    (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))
    (algebraMap R₀ A) s)
  rw [IsLocalization.Away.map_surjective_iff]
  exact H

/-- Helper for Chap10 Lemma 10 152 3: a product decomposition remains a product decomposition
after localizing the base at one denominator. -/
private noncomputable def baseChange_localizedProductDecomposition
    {R₀ : Type u} {ι : Type (max u v)}
    {A : ι → Type (max u v)} {B : Type (max u v)}
    [CommRing R₀] [Algebra R R₀]
    [∀ i, CommRing (A i)] [∀ i, Algebra R₀ (A i)] [CommRing B] [Algebra R₀ B]
    [Fintype ι] [DecidableEq ι]
    (s : R₀) (e : R₀ ⊗[R] S ≃ₐ[R₀] ((i : ι) → A i) × B) :
    Localization (Submonoid.powers s) ⊗[R] S ≃ₐ[Localization (Submonoid.powers s)]
      ((i : ι) → Localization (Algebra.algebraMapSubmonoid (A i) (Submonoid.powers s))) ×
        Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers s)) :=
  (Algebra.TensorProduct.cancelBaseChange R R₀ (Localization (Submonoid.powers s))
      (Localization (Submonoid.powers s)) S).symm.trans <|
  (Algebra.TensorProduct.congr .refl e).trans <|
  (Algebra.TensorProduct.prodRight R₀ (Localization (Submonoid.powers s))
    (Localization (Submonoid.powers s)) ((i : ι) → A i) B).trans <|
  AlgEquiv.prodCongr
    ((Algebra.TensorProduct.piRight R₀ (Localization (Submonoid.powers s))
      (Localization (Submonoid.powers s)) A).trans <|
      AlgEquiv.piCongrRight fun i ↦
        Localization.tensorRightAlgEquiv (Submonoid.powers s) (A i))
    (Localization.tensorRightAlgEquiv (Submonoid.powers s) B)

/-- Helper for Chap10 Lemma 10 152 3: after localizing at a denominator outside the base
prime, the localized distinguished prime is the extension of the localized base prime. -/
private lemma localizedPrime_eq_map_of_surjective
    {R₀ : Type u} {A : Type (max u v)}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    (p₀ : Ideal R₀) [p₀.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p₀]
    {s : R₀} (hs : s ∉ p₀)
    (hsurj : Function.Surjective
      (algebraMap (Localization (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s))))) :
    let pLoc : Ideal (Localization (Submonoid.powers s)) :=
      Ideal.map (algebraMap R₀ (Localization (Submonoid.powers s))) p₀
    let qLoc : Ideal (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s))) :=
      Ideal.map (algebraMap A (Localization (Algebra.algebraMapSubmonoid A
        (Submonoid.powers s)))) q
    qLoc.IsPrime ∧ qLoc.LiesOver pLoc ∧
      qLoc = Ideal.map
        (algebraMap (Localization (Submonoid.powers s))
          (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) pLoc := by
  intro pLoc qLoc
  -- The old prime over `p₀` avoids the image of the denominator because `s ∉ p₀`.
  have hqAvoid :
      Disjoint (Algebra.algebraMapSubmonoid A (Submonoid.powers s) : Set A) (q : Set A) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    apply disjoint_powers_of_notMem_prime
    intro hsq
    exact hs (by
      rw [Ideal.over_def q p₀, Ideal.under_def]
      exact hsq)
  have hqLocPrime : qLoc.IsPrime := by
    simpa [qLoc] using
      IsLocalization.isPrime_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid A (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s))) q
        (inferInstance : q.IsPrime) hqAvoid
  have hpAvoid : Disjoint (Submonoid.powers s : Set R₀) (p₀ : Set R₀) :=
    disjoint_powers_of_notMem_prime hs
  have hqComap :
      Ideal.comap (algebraMap A (Localization (Algebra.algebraMapSubmonoid A
        (Submonoid.powers s)))) qLoc = q := by
    simpa [qLoc] using
      IsLocalization.comap_map_of_isPrime_disjoint
        (Algebra.algebraMapSubmonoid A (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))
        (inferInstance : q.IsPrime) hqAvoid
  have hbaseComap :
      Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s)))
        (Ideal.comap
          (algebraMap (Localization (Submonoid.powers s))
            (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) qLoc) =
        p₀ := by
    rw [Ideal.comap_comap]
    trans Ideal.comap (algebraMap R₀ A)
        (Ideal.comap (algebraMap A
          (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) qLoc)
    · rw [Ideal.comap_comap]
      rw [← IsScalarTower.algebraMap_eq R₀ (Localization (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))]
      rw [← IsScalarTower.algebraMap_eq R₀ A
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))]
    · rw [hqComap]
      rw [Ideal.over_def q p₀, Ideal.under_def]
  have hlies : qLoc.LiesOver pLoc := by
    refine Ideal.LiesOver.mk ?_
    rw [Ideal.under_def]
    symm
    calc
      Ideal.comap
          (algebraMap (Localization (Submonoid.powers s))
            (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) qLoc
          = Ideal.map (algebraMap R₀ (Localization (Submonoid.powers s)))
              (Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s)))
                (Ideal.comap
                  (algebraMap (Localization (Submonoid.powers s))
                    (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) qLoc)) := by
            rw [IsLocalization.map_comap (Submonoid.powers s)
              (Localization (Submonoid.powers s))]
      _ = pLoc := by
            rw [hbaseComap]
  have hcomapEq :
      Ideal.comap
        (algebraMap (Localization (Submonoid.powers s))
          (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) qLoc =
        pLoc := by
    simpa [Ideal.under_def] using hlies.over.symm
  have heq : qLoc = Ideal.map
        (algebraMap (Localization (Submonoid.powers s))
          (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) pLoc := by
    rw [← Ideal.map_comap_of_surjective
      (algebraMap (Localization (Submonoid.powers s))
        (Localization (Algebra.algebraMapSubmonoid A (Submonoid.powers s)))) hsurj qLoc]
    rw [hcomapEq]
  exact ⟨hqLocPrime, hlies, heq⟩

/-- Helper for Chap10 Lemma 10 152 3: if the old remainder has no prime over `p₀`, then its
localization has no prime over the localized base prime. -/
private lemma noPrimesOver_localization_of_noPrimesOver
    {R₀ : Type u} {B : Type (max u v)}
    [CommRing R₀] [CommRing B] [Algebra R₀ B]
    (p₀ : Ideal R₀) [p₀.IsPrime] {s : R₀} (hs : s ∉ p₀)
    (hno : ∀ _ : p₀.primesOver B, False) :
    let pLoc : Ideal (Localization (Submonoid.powers s)) :=
      Ideal.map (algebraMap R₀ (Localization (Submonoid.powers s))) p₀
    ∀ _ : pLoc.primesOver
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers s))), False := by
  intro pLoc Q
  let Bloc := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers s))
  let J : Ideal B := Ideal.comap (algebraMap B Bloc) Q.1
  -- Contract a hypothetical localized prime back to the old remainder.
  have hJPrime : J.IsPrime := by
    dsimp [J]
    exact Ideal.comap_isPrime (algebraMap B Bloc) Q.1
  have hpAvoid : Disjoint (Submonoid.powers s : Set R₀) (p₀ : Set R₀) :=
    disjoint_powers_of_notMem_prime hs
  have hpComap :
      Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s))) pLoc = p₀ := by
    simpa [pLoc] using
      IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers s)
        (Localization (Submonoid.powers s)) (inferInstance : p₀.IsPrime) hpAvoid
  have hQover : pLoc =
      Ideal.comap (algebraMap (Localization (Submonoid.powers s)) Bloc) Q.1 := by
    simpa [Ideal.under_def, Bloc] using Q.2.2.over
  have hJLies : J.LiesOver p₀ := by
    refine Ideal.LiesOver.mk ?_
    rw [Ideal.under_def]
    calc
      p₀ = Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s))) pLoc :=
        hpComap.symm
      _ = Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s)))
            (Ideal.comap (algebraMap (Localization (Submonoid.powers s)) Bloc) Q.1) := by
            exact congrArg (Ideal.comap (algebraMap R₀ (Localization (Submonoid.powers s))))
              hQover
      _ = Ideal.comap (algebraMap R₀ B) J := by
            dsimp [J]
            rw [Ideal.comap_comap]
            rw [Ideal.comap_comap]
            rw [← IsScalarTower.algebraMap_eq R₀ (Localization (Submonoid.powers s)) Bloc]
            rw [← IsScalarTower.algebraMap_eq R₀ B Bloc]
  exact hno ⟨J, hJPrime, hJLies⟩

/-- Helper for Chap10 Lemma 10 152 3: after one further étale shrinking, a pure finite product
decomposition of a globally unramified algebra can be upgraded so that all finite factor maps are
surjective and the distinguished factor primes are extended from the base. -/
private lemma upgradePureProductDecompositionAfterEtaleShrink
    [Algebra.Unramified R S] (p : Ideal R) [p.IsPrime]
    (hdecomp :
      ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
        (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
        ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
          (instAComm : ∀ i, CommRing (A i)) (instAAlg : ∀ i, Algebra R' (A i))
          (B : Type (max u v)) (instBComm : CommRing B) (instBAlg : Algebra R' B),
        letI : ∀ i, CommRing (A i) := instAComm
        letI : ∀ i, Algebra R' (A i) := instAAlg
        letI : CommRing B := instBComm
        letI : Algebra R' B := instBAlg
        ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
        ∃ _ : ∀ i, Module.Finite R' (A i),
        ∃ r : ∀ i, p'.primesOver (A i),
        ∃ _ : ∀ i, Subsingleton (p'.primesOver (A i)),
        ∃ _ :
          ∀ i,
            FiniteDimensional p'.ResidueField (r i).1.ResidueField ∧
              IsPurelyInseparable p'.ResidueField (r i).1.ResidueField,
        ∀ q : p'.primesOver B, ¬ Algebra.QuasiFiniteAt R' q.1) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R' (A i)) (B : Type (max u v)) (instBComm : CommRing B)
        (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ r : ∀ i, p'.primesOver (A i),
      (∀ i, Function.Surjective (algebraMap R' (A i))) ∧
        (∀ i, (r i).1 = Ideal.map (algebraMap R' (A i)) p') ∧
        (∀ _ : p'.primesOver B, False) := by
  classical
  -- Unpack the pure product decomposition supplied by the previous lemma.
  obtain ⟨R', instR', instAlgRR', instEtaleRR', p', instPrimep', instLiesp', ι,
      instFintypeι, A, instAComm, instAAlg, B, instBComm, instBAlg, e, hfinite, r,
      hsubsingleton, hres, hnonQuasiFinite⟩ := hdecomp
  letI : CommRing R' := instR'
  letI : Algebra R R' := instAlgRR'
  letI : Algebra.Etale R R' := instEtaleRR'
  letI : p'.IsPrime := instPrimep'
  letI : p'.LiesOver p := instLiesp'
  letI : Fintype ι := instFintypeι
  letI : ∀ i, CommRing (A i) := instAComm
  letI : ∀ i, Algebra R' (A i) := instAAlg
  letI : CommRing B := instBComm
  letI : Algebra R' B := instBAlg
  have hTensorUnramified : Algebra.Unramified R' (R' ⊗[R] S) := by
    infer_instance
  -- The unramified product decomposition makes each distinguished residue-field map surjective.
  have hresSurj :
      ∀ i, Function.Surjective (algebraMap p'.ResidueField (r i).1.ResidueField) := by
    letI : Algebra.Unramified R' (R' ⊗[R] S) := hTensorUnramified
    exact residueFieldMaps_surjective_of_unramified_decomposition p' e r hres
  -- The same unramifiedness also turns the non-quasi-finite remainder condition into emptiness.
  have hnoPrimesOld : ∀ q : p'.primesOver B, False := by
    letI : Algebra.Unramified R' (R' ⊗[R] S) := hTensorUnramified
    exact noPrimesOver_remainder_of_unramified_decomposition p' e hnonQuasiFinite
  -- For every finite factor, clear denominators on a basic open around `p'`.
  have hfactorShrink :
      ∀ i, ∃ s ∉ p', ∀ t, s ∣ t →
        Function.Surjective (Localization.awayMap (algebraMap R' (A i)) t) := by
    intro i
    letI : Module.Finite R' (A i) := hfinite i
    letI : Subsingleton (p'.primesOver (A i)) := hsubsingleton i
    have hAi : Algebra.Unramified R' (A i) := by
      letI : Algebra.Unramified R' (R' ⊗[R] S) := hTensorUnramified
      exact unramified_factor_of_algEquiv e i
    letI : Algebra.Unramified R' (A i) := hAi
    have hunique : p'.primesOver (A i) = {(r i).1} :=
      primesOver_eq_singleton_of_subsingleton p' (r i)
    exact exists_awayMap_surjective_of_residueField_surjective p' (r i).1 hunique
      (hresSurj i)
  -- A finite product of the factor denominators gives one common étale shrink.
  have hcommonShrink :
      ∃ s ∉ p', ∀ i,
        Function.Surjective (Localization.awayMap (algebraMap R' (A i)) s) := by
    choose s hs hsurj using hfactorShrink
    have hprod : ∏ i, s i ∈ p'.primeCompl :=
      prod_mem fun i _ ↦ (show s i ∈ p'.primeCompl from hs i)
    refine ⟨∏ i, s i, ?_, ?_⟩
    · simpa [Ideal.mem_primeCompl_iff] using hprod
    intro i
    exact hsurj i (∏ j, s j)
      (Finset.dvd_prod_of_mem (fun j ↦ s j) (Finset.mem_univ i))
  -- TODO: localize the base and all product factors at the common denominator from
  -- `hcommonShrink`, transport `e` through tensor-product/product localization, and identify the
  -- localized distinguished primes as the extended ideals using the factor surjectivity.
  obtain ⟨s, hs, hsurjFactor⟩ := hcommonShrink
  let Rloc := Localization (Submonoid.powers s)
  let pLoc : Ideal Rloc := Ideal.map (algebraMap R' Rloc) p'
  let Aloc : ι → Type (max u v) :=
    fun i ↦ Localization (Algebra.algebraMapSubmonoid (A i) (Submonoid.powers s))
  let Bloc : Type (max u v) :=
    Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers s))
  have hpAvoid : Disjoint (Submonoid.powers s : Set R') (p' : Set R') :=
    disjoint_powers_of_notMem_prime hs
  have hpLocPrime : pLoc.IsPrime := by
    simpa [pLoc, Rloc] using
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) Rloc p'
        (inferInstance : p'.IsPrime) hpAvoid
  have hpLocComap : Ideal.comap (algebraMap R' Rloc) pLoc = p' := by
    simpa [pLoc, Rloc] using
      IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers s) Rloc
        (inferInstance : p'.IsPrime) hpAvoid
  have hpLocLies : pLoc.LiesOver p := by
    refine Ideal.LiesOver.mk ?_
    rw [Ideal.under_def]
    calc
      p = Ideal.comap (algebraMap R R') p' := by
        rw [Ideal.over_def p' p, Ideal.under_def]
      _ = Ideal.comap (algebraMap R Rloc) pLoc := by
        rw [← hpLocComap, Ideal.comap_comap]
        rw [← IsScalarTower.algebraMap_eq R R' Rloc]
  have hsurjLoc : ∀ i, Function.Surjective (algebraMap Rloc (Aloc i)) := by
    intro i
    exact algebraMap_localization_surjective_of_awayMap_surjective s (hsurjFactor i)
  have hprimeData :
      ∀ i,
        let qLoc : Ideal (Aloc i) := Ideal.map (algebraMap (A i) (Aloc i)) (r i).1
        qLoc.IsPrime ∧ qLoc.LiesOver pLoc ∧
          qLoc = Ideal.map (algebraMap Rloc (Aloc i)) pLoc := by
    intro i
    exact localizedPrime_eq_map_of_surjective p' (r i).1 hs (hsurjLoc i)
  let rLoc : ∀ i, pLoc.primesOver (Aloc i) := fun i ↦
    let qLoc : Ideal (Aloc i) := Ideal.map (algebraMap (A i) (Aloc i)) (r i).1
    ⟨qLoc, (hprimeData i).1, (hprimeData i).2.1⟩
  let instAlocComm : ∀ i, CommRing (Aloc i) := fun _ ↦ inferInstance
  let instAlocAlg : ∀ i, Algebra Rloc (Aloc i) := fun _ ↦ inferInstance
  let instBlocComm : CommRing Bloc := inferInstance
  let instBlocAlg : Algebra Rloc Bloc := inferInstance
  refine ⟨Rloc, inferInstance, inferInstance, inferInstance, pLoc, hpLocPrime, hpLocLies,
    ι, instFintypeι, Aloc, instAlocComm, instAlocAlg, Bloc, instBlocComm, instBlocAlg, ?_,
    rLoc, ?_, ?_, ?_⟩
  · -- The old product decomposition transports through the common localization.
    exact baseChange_localizedProductDecomposition (R := R) (S := S) s e
  · -- Each localized factor map is surjective by the common-shrink construction.
    exact hsurjLoc
  · -- The localized distinguished primes are exactly the extensions of the localized base prime.
    intro i
    exact (hprimeData i).2.2
  · -- Any localized remainder prime contracts to an old remainder prime, contradicting `hnoPrimesOld`.
    exact noPrimesOver_localization_of_noPrimesOver p' hs hnoPrimesOld

-- Proof sketch: start from the étale product decomposition of Lemma `10.145.4` applied to the
-- unramified finite type map `R → S`. For each finite factor `Aᵢ`, the unique prime over `p'`
-- has residue field both purely inseparable and separable over `κ(p')`, hence equal to `κ(p')`;
-- the local map `R'_{p'} → (Aᵢ)_{p'Aᵢ}` is therefore surjective by the unramified local
-- criterion. Finite generation lets one shrink the étale neighborhood so that each global map
-- `R' → Aᵢ` becomes surjective, and quasi-finiteness of unramified maps removes every prime of
-- the remainder `B` above `p'`.
/-- Chap10 Lemma 10 152 3: if `R → S` is unramified and `p ⊂ R` is prime, then after an étale base
change `R → R'` with a prime `p'` over `p`, the algebra `R' ⊗[R] S` decomposes as a finite
product `A₁ × ... × Aₙ × B` such that each map `R' → Aᵢ` is surjective, the extended ideal
`p'Aᵢ` is a prime of `Aᵢ` lying over `p'`, and there is no prime of `B` lying over `p'`. -/
@[stacks 00UY]
theorem exists_surjective_factor_decomposition_of_pure_decomposition
    [Algebra.Unramified R S] (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p),
      ∃ (ι : Type (max u v)) (_ : Fintype ι) (A : ι → Type (max u v))
        (instAComm : ∀ i, CommRing (A i))
        (instAAlg : ∀ i, Algebra R' (A i)) (B : Type (max u v)) (instBComm : CommRing B)
        (instBAlg : Algebra R' B),
      letI : ∀ i, CommRing (A i) := instAComm
      letI : ∀ i, Algebra R' (A i) := instAAlg
      letI : CommRing B := instBComm
      letI : Algebra R' B := instBAlg
      ∃ _ : R' ⊗[R] S ≃ₐ[R'] ((i : ι) → A i) × B,
      ∃ r : ∀ i, p'.primesOver (A i),
      (∀ i, Function.Surjective (algebraMap R' (A i))) ∧
        (∀ i, (r i).1 = Ideal.map (algebraMap R' (A i)) p') ∧
        (∀ _ : p'.primesOver B, False) := by
  -- Start from Lemma 10.145.4, then hand the finite shrink/base-change upgrade to the
  -- dedicated structural helper above.
  have hfiniteType : Algebra.FiniteType R S := Algebra.Unramified.finiteType
  exact upgradePureProductDecompositionAfterEtaleShrink p
    (exists_etale_finite_product_decomposition_with_purelyInseparable_residueFields_and_nonQuasiFinite_remainder
      (R := R) (S := S) p)

end

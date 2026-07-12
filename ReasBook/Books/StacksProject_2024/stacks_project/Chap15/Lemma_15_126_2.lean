import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import StacksProject_2024.Chap10.Lemma_10_62_3
import StacksProject_2024.Chap10.Lemma_10_62_4
import StacksProject_2024.Chap10.Lemma_10_79_1
import StacksProject_2024.Chap15.Lemma_15_126_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped nonZeroDivisors

section

/- Domain triage:
* primary domain: one-dimensional local commutative algebra, comparing minimal-prime counts with
  principal-ideal quotient length;
* sampled owner API: `Ring.ord`, `minimalPrimes.finite_of_isNoetherianRing`,
  `Ring.KrullDimLE 1`, and the chapter-level principal-ideal length theorem
  `ord_pow_le_nsmul_ord`;
* source/core/bridge triage:
  `source-facing`: the Stacks bound on the number of minimal primes of a one-dimensional local
  ring cut by an element of the maximal ideal avoiding all minimal primes;
* `core/canonical`: the owner for `Module.length R (R ⧸ Ideal.span {x})` is `Ring.ord R x`;
* `bridge/view`: the textbook quotient length is already canonically owned by `Ring.ord`, so no
  parallel local length wrapper belongs in this file.

Primitive-vs-derived split:
* primitive data: the local Noetherian ring, the distinguished element `x : maximalIdeal R`, and
  the canonical membership-style minimal-prime avoidance predicate
  `∀ p ∈ minimalPrimes R, (x : R) ∉ p`;
* derived API: the quotient-length bound, expressed canonically through `Ring.ord`.
-/

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 15.126.2: the intersection of the minimal primes is the nilradical. -/
private theorem sInf_minimalPrimes_eq_nilradical :
    (⨅ p : minimalPrimes R, p.1) = nilradical R := by
  -- Rewrite the minimal-prime intersection as the radical of `(0)`.
  have hsInf : sInf (minimalPrimes R) = nilradical R := by
    have hsInf' : sInf ((⊥ : Ideal R).minimalPrimes) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes
    simpa [minimalPrimes, nilradical, Ideal.zero_eq_bot] using hsInf'
  rw [sInf_eq_iInf] at hsInf
  simpa [iInf_subtype'] using hsInf

/-- Helper for Lemma 15.126.2: the reduced quotient maps diagonally to the product of the
minimal-prime quotients. -/
private noncomputable def reducedDiagonalMap :
    (R ⧸ nilradical R) →+* ∀ p : minimalPrimes R, R ⧸ p.1 :=
  (Ideal.quotientInfToPiQuotient fun p : minimalPrimes R ↦ p.1).comp
    (Ideal.quotEquivOfEq (sInf_minimalPrimes_eq_nilradical (R := R)).symm).toRingHom

/-- Helper for Lemma 15.126.2: the reduced diagonal map is injective. -/
private theorem reduced_diagonal_map_injective :
    Function.Injective (reducedDiagonalMap (R := R)) := by
  -- Transport the canonical injective quotient-to-product map along
  -- `⨅ minimalPrimes = nilradical`.
  simpa [reducedDiagonalMap] using
    (Ideal.quotientInfToPiQuotient_inj fun p : minimalPrimes R ↦ p.1).comp
      (Ideal.quotEquivOfEq (sInf_minimalPrimes_eq_nilradical (R := R)).symm).injective

/-- Helper for Lemma 15.126.2: a prime avoiding an element of the maximal ideal is a minimal
prime in Krull dimension at most one. -/
private theorem prime_not_mem_x_mem_minimalPrimes
    (x : maximalIdeal R) (q : PrimeSpectrum R) (hxq : (x : R) ∉ q.asIdeal) :
    q.asIdeal ∈ minimalPrimes R := by
  -- Because `x` belongs to the maximal ideal, a prime avoiding `x` cannot be the maximal ideal.
  have hq_ne_max : q.asIdeal ≠ maximalIdeal R := by
    intro hqmax
    have hxmax : (x : R) ∈ maximalIdeal R := x.2
    have hxq' : (x : R) ∈ q.asIdeal := by
      simp [hqmax] at hxmax ⊢
    exact hxq hxq'
  have hq_lt_max : q.asIdeal < maximalIdeal R := by
    -- Every prime ideal in a local ring lies under the maximal ideal.
    exact lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal) hq_ne_max
  have hdim : ringKrullDim R ≤ 1 := (Ring.krullDimLE_iff (R := R)).mp inferInstance
  have hmax_primeHeight_le_one : (maximalIdeal R).primeHeight ≤ 1 := by
    -- Rewrite the closed-point prime height as the ambient Krull dimension.
    have hmax_primeHeight_le_one' : ((maximalIdeal R).primeHeight : WithBot ℕ∞) ≤ 1 := by
      simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
    exact_mod_cast hmax_primeHeight_le_one'
  have hq_add_one_le_one : q.asIdeal.primeHeight + 1 ≤ 1 := by
    -- The strict inclusion `q < m` forces the prime height of `q` to drop by at least one.
    calc
      q.asIdeal.primeHeight + 1 ≤ (maximalIdeal R).primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt hq_lt_max
      _ ≤ 1 := hmax_primeHeight_le_one
  have hq_primeHeight_ne_top : q.asIdeal.primeHeight ≠ ⊤ := by
    intro htop
    simp [htop] at hq_add_one_le_one
  have hq_primeHeight_lt_one : q.asIdeal.primeHeight < 1 := by
    exact (ENat.add_one_le_iff hq_primeHeight_ne_top).mp hq_add_one_le_one
  have hq_primeHeight_zero : q.asIdeal.primeHeight = 0 :=
    ENat.lt_one_iff_eq_zero.mp hq_primeHeight_lt_one
  -- Height zero is exactly the minimal-prime condition for a prime ideal.
  exact (Ideal.primeHeight_eq_zero_iff (I := q.asIdeal)).mp hq_primeHeight_zero

/-- Helper for Lemma 15.126.2: in a one-dimensional local ring, every nonmaximal prime is
minimal. -/
private theorem nonmaximal_prime_mem_minimalPrimes
    (q : PrimeSpectrum R) (hq : q.asIdeal ≠ maximalIdeal R) :
    q.asIdeal ∈ minimalPrimes R := by
  -- A nonmaximal prime sits strictly below the maximal ideal in a local ring.
  have hq_lt_max : q.asIdeal < maximalIdeal R := by
    exact lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime q.asIdeal) hq
  have hdim : ringKrullDim R ≤ 1 := (Ring.krullDimLE_iff (R := R)).mp inferInstance
  have hmax_primeHeight_le_one : (maximalIdeal R).primeHeight ≤ 1 := by
    have hmax_primeHeight_le_one' : ((maximalIdeal R).primeHeight : WithBot ℕ∞) ≤ 1 := by
      simpa [IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] using hdim
    exact_mod_cast hmax_primeHeight_le_one'
  have hq_add_one_le_one : q.asIdeal.primeHeight + 1 ≤ 1 := by
    -- Strict containment below the maximal ideal forces the prime height to drop by at least one.
    calc
      q.asIdeal.primeHeight + 1 ≤ (maximalIdeal R).primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt hq_lt_max
      _ ≤ 1 := hmax_primeHeight_le_one
  have hq_primeHeight_ne_top : q.asIdeal.primeHeight ≠ ⊤ := by
    intro htop
    simp [htop] at hq_add_one_le_one
  have hq_primeHeight_lt_one : q.asIdeal.primeHeight < 1 := by
    exact (ENat.add_one_le_iff hq_primeHeight_ne_top).mp hq_add_one_le_one
  have hq_primeHeight_zero : q.asIdeal.primeHeight = 0 :=
    ENat.lt_one_iff_eq_zero.mp hq_primeHeight_lt_one
  -- Height-zero prime ideals are exactly the minimal primes.
  exact (Ideal.primeHeight_eq_zero_iff (I := q.asIdeal)).mp hq_primeHeight_zero

/-- Helper for Lemma 15.126.2: localizing the quotient by one minimal prime at a different minimal
prime kills that factor. -/
private theorem localized_quotient_subsingleton_of_ne_minimalPrime
    (p q : minimalPrimes R) (hpq : p ≠ q) :
    Subsingleton (LocalizedModule.AtPrime q.1 (R ⧸ p.1)) := by
  have hp_min : Minimal Ideal.IsPrime p.1 := by
    simpa [minimalPrimes_eq_minimals] using p.2
  have hq_min : Minimal Ideal.IsPrime q.1 := by
    simpa [minimalPrimes_eq_minimals] using q.2
  have hp_not_le_q : ¬ p.1 ≤ q.1 := by
    -- Distinct minimal primes are incomparable, so `p` cannot sit inside `q`.
    intro hp_le_q
    have hq_le_p : q.1 ≤ p.1 := hq_min.2 hp_min.1 hp_le_q
    exact hpq (Subtype.ext (le_antisymm hp_le_q hq_le_p))
  rcases SetLike.not_le_iff_exists.mp hp_not_le_q with ⟨s, hs_mem_p, hs_not_mem_q⟩
  rw [LocalizedModule.subsingleton_iff (S := q.1.primeCompl) (M := R ⧸ p.1)]
  intro y
  refine ⟨s, hs_not_mem_q, ?_⟩
  -- The chosen separator already vanishes in `R ⧸ p`, so it annihilates every quotient class.
  refine Quotient.inductionOn' y ?_
  intro a
  change Ideal.Quotient.mk p.1 (s * a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact p.1.mul_mem_right a hs_mem_p

/-- Helper for Lemma 15.126.2: the quotient by a minimal prime of a local ring is again a local
domain. -/
private theorem minimalPrimeQuotient_isLocalDomain (p : minimalPrimes R) :
    let S := R ⧸ p.1
    IsLocalRing S ∧ IsDomain S := by
  let S := R ⧸ p.1
  have hp_ne_top : p.1 ≠ ⊤ := Ideal.IsPrime.ne_top (show p.1.IsPrime from inferInstance)
  let _ : Nontrivial S := (Ideal.Quotient.nontrivial_iff.2 hp_ne_top)
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p.1) Ideal.Quotient.mk_surjective
  letI : IsDomain S := Ideal.Quotient.isDomain p.1
  exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.126.2: if `x` avoids the minimal prime `p`, then its image in `R ⧸ p`
is a nonzerodivisor and has positive order of vanishing. -/
private theorem one_le_ord_image_of_not_mem_minimalPrime
    (x : maximalIdeal R) (p : minimalPrimes R) (hx : (x : R) ∉ p.1) :
    1 ≤ Ring.ord (R ⧸ p.1) ((Ideal.Quotient.mk p.1) (x : R)) := by
  let S := R ⧸ p.1
  let π : R →+* S := Ideal.Quotient.mk p.1
  have hlocalDomain := minimalPrimeQuotient_isLocalDomain (R := R) p
  let _ : IsLocalRing S := hlocalDomain.1
  let _ : IsDomain S := hlocalDomain.2
  have hx0 : π (x : R) ≠ 0 := by
    intro hzero
    exact hx ((Ideal.Quotient.eq_zero_iff_mem).mp hzero)
  have hx_nz : π (x : R) ∈ nonZeroDivisors S := by
    exact (mem_nonZeroDivisors_iff_ne_zero).2 hx0
  have hx_max : π (x : R) ∈ maximalIdeal S := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem π x.property
  have hspan_ne_top : Ideal.span ({π (x : R)} : Set S) ≠ ⊤ := by
    intro htop
    have hunit : IsUnit (π (x : R)) := (Ideal.span_singleton_eq_top).mp htop
    exact (IsLocalRing.notMem_maximalIdeal.mpr hunit) hx_max
  let _ : Nontrivial (S ⧸ Ideal.span ({π (x : R)} : Set S)) :=
    (Ideal.Quotient.nontrivial_iff.2 hspan_ne_top)
  have hpos :
      0 < Module.length S (S ⧸ Ideal.span ({π (x : R)} : Set S)) := by
    simpa using
      (Module.length_pos_iff (R := S) (M := S ⧸ Ideal.span ({π (x : R)} : Set S))).2 inferInstance
  have hord_pos : 0 < Ring.ord S (π (x : R)) := by
    simpa [Ring.ord] using hpos
  exact ENat.one_le_iff_ne_zero.mpr hord_pos.ne'

/-- Helper for Lemma 15.126.2: in each minimal-prime quotient, the `n`-th power of the image of
`x` has order of vanishing at least `n`. -/
private theorem exponent_le_ord_pow_image_of_not_mem_minimalPrime
    (x : maximalIdeal R) (p : minimalPrimes R) {n : ℕ}
    (hx : (x : R) ∉ p.1) :
    n ≤ Ring.ord (R ⧸ p.1) (((Ideal.Quotient.mk p.1) (x : R)) ^ n) := by
  let S := R ⧸ p.1
  let π : R →+* S := Ideal.Quotient.mk p.1
  have hlocalDomain := minimalPrimeQuotient_isLocalDomain (R := R) p
  let _ : IsLocalRing S := hlocalDomain.1
  let _ : IsDomain S := hlocalDomain.2
  have hx0 : π (x : R) ≠ 0 := by
    intro hzero
    exact hx ((Ideal.Quotient.eq_zero_iff_mem).mp hzero)
  have hx_nz : π (x : R) ∈ nonZeroDivisors S := by
    exact (mem_nonZeroDivisors_iff_ne_zero).2 hx0
  have hord_one : 1 ≤ Ring.ord S (π (x : R)) :=
    one_le_ord_image_of_not_mem_minimalPrime (R := R) x p hx
  -- Apply Lemma `15.126.1` in the domain quotient and use that the first power already
  -- contributes at least one to the order of vanishing.
  calc
    n = n • (1 : ℕ∞) := by simp
    _ ≤ n • Ring.ord S (π (x : R)) := by
      exact nsmul_le_nsmul_right hord_one n
    _ = Ring.ord S ((π (x : R)) ^ n) := by
      symm
      simpa [S, π] using
        ord_pow_eq_nsmul_ord_of_mem_nonZeroDivisors (R := S) hx_nz n

/-- Helper for Lemma 15.126.2: package the owner localization equivalence between the localized
product of minimal-prime quotients and the product of the localized factors. -/
private noncomputable def localized_minimalPrimeProduct_equiv
    (q : minimalPrimes R) :
    LocalizedModule.AtPrime q.1 (∀ p : minimalPrimes R, R ⧸ p.1) ≃ₗ[R]
      ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) :=
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  -- Use the canonical componentwise localization map, then invoke the owner comparison theorem
  -- `IsLocalizedModule.linearEquiv` rather than proving a bespoke product-localization theorem.
  let βq :
      (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R]
        ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) :=
    LinearMap.pi fun p : minimalPrimes R ↦
      (LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1)) ∘ₗ LinearMap.proj p
  let _ : IsLocalizedModule q.1.primeCompl βq :=
    IsLocalizedModule.pi q.1.primeCompl
      (fun p : minimalPrimes R ↦ LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1))
  IsLocalizedModule.linearEquiv q.1.primeCompl
    (LocalizedModule.mkLinearMap q.1.primeCompl (∀ p : minimalPrimes R, R ⧸ p.1)) βq

/-- Helper for Lemma 15.126.2: the reduced diagonal is `R`-linear, so it can be localized by the
owner API `LocalizedModule.map`. -/
private noncomputable def reducedDiagonalLinearMap :
    (R ⧸ nilradical R) →ₗ[R] ∀ p : minimalPrimes R, R ⧸ p.1 where
  toFun := reducedDiagonalMap (R := R)
  map_add' := (reducedDiagonalMap (R := R)).map_add
  map_smul' r a := by
    -- Rewrite scalar multiplication in both quotients as multiplication by the image of `r`.
    ext p
    change
      (reducedDiagonalMap (R := R)) (((algebraMap R (R ⧸ nilradical R)) r) * a) p =
        (algebraMap R (R ⧸ p.1) r) * ((reducedDiagonalMap (R := R)) a p)
    rw [map_mul]
    rfl

/-- Helper for Lemma 15.126.2: under the product-localization equivalence, the localized reduced
diagonal is computed coordinatewise on localization generators. -/
private theorem localized_minimalPrimeProduct_equiv_reduced_diagonal_mk_apply
    (q : minimalPrimes R) (a : R ⧸ nilradical R) :
    localized_minimalPrimeProduct_equiv (R := R) q
      (LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))
        (LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ nilradical R) a)) =
      fun p => LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1)
        ((reducedDiagonalMap (R := R) a) p) := by
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let βq :
      (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R]
        ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) :=
    LinearMap.pi fun p : minimalPrimes R ↦
      (LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1)) ∘ₗ LinearMap.proj p
  letI : IsLocalizedModule q.1.primeCompl βq :=
    IsLocalizedModule.pi q.1.primeCompl
      (fun p : minimalPrimes R ↦ LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1))
  -- Evaluate the owner localization equivalence on the generator represented by `a`.
  ext p
  simpa [reducedDiagonalLinearMap, localized_minimalPrimeProduct_equiv, βq,
      LinearMap.pi_apply, LocalizedModule.map_mk] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply q.1.primeCompl
        (LocalizedModule.mkLinearMap q.1.primeCompl (∀ p : minimalPrimes R, R ⧸ p.1))
        βq
        ((reducedDiagonalLinearMap (R := R)) a))
      p

/-- Helper for Lemma 15.126.2: after localizing the product of minimal-prime quotients at a
minimal prime `q`, every off-diagonal factor disappears, so projection to the surviving
`q`-coordinate is bijective. -/
private theorem localized_product_proj_bijective_at_minimalPrime
    (q : minimalPrimes R) :
    Function.Bijective
      (LinearMap.proj q :
        (∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1)) →ₗ[Localization.AtPrime q.1]
          LocalizedModule.AtPrime q.1 (R ⧸ q.1)) := by
  constructor
  · intro y z hyz
    -- Two localized tuples agree at `q` by hypothesis, and away from `q` all factors are
    -- subsingleton by the already-closed off-diagonal vanishing lemma.
    ext p
    by_cases hpq : p = q
    · subst hpq
      simpa using hyz
    · letI : Subsingleton (LocalizedModule.AtPrime q.1 (R ⧸ p.1)) :=
        localized_quotient_subsingleton_of_ne_minimalPrime (R := R) p q hpq
      exact Subsingleton.elim _ _
  · intro z
    -- Build the localized tuple with prescribed `q`-coordinate and zero elsewhere.
    refine ⟨fun p ↦ if hpq : p = q then ?_ else 0, ?_⟩
    · subst hpq
      exact z
    · simp

/-- Helper for Lemma 15.126.2: on quotient generators, the `q`-coordinate of the reduced diagonal
is exactly the canonical quotient map to `R ⧸ q`. -/
private theorem reduced_coordinate_apply_mk
    (q : minimalPrimes R) (r : R) :
    ((reducedDiagonalMap (R := R)) ((Ideal.Quotient.mk (nilradical R)) r)) q =
      (Ideal.Quotient.mk q.1) r := by
  -- Expand the reduced diagonal through the canonical identification
  -- `R ⧸ nilradical R ≃ R ⧸ ⨅ p, p` and evaluate the owner map on a quotient generator.
  change
    ((Ideal.quotientInfToPiQuotient fun p : minimalPrimes R ↦ p.1)
      ((Ideal.quotEquivOfEq (sInf_minimalPrimes_eq_nilradical (R := R)).symm)
        ((Ideal.Quotient.mk (nilradical R)) r))) q =
      (Ideal.Quotient.mk q.1) r
  rw [Ideal.quotEquivOfEq_mk, Ideal.quotientInfToPiQuotient_mk]

/-- Helper for Lemma 15.126.2: the kernel of the surviving `q`-coordinate on the reduced quotient
is precisely the image of `q` in `R ⧸ nilradical R`. -/
private theorem reduced_coordinate_ker_eq_map_minimalPrime
    (q : minimalPrimes R) :
    RingHom.ker
        ((Pi.evalRingHom (fun p : minimalPrimes R ↦ R ⧸ p.1) q).comp
          (reducedDiagonalMap (R := R))) =
      Ideal.map (Ideal.Quotient.mk (nilradical R)) q.1 := by
  -- Compare both ideals on quotient generators and reduce to the defining equation
  -- of the quotient by `q`.
  ext a
  refine Quotient.inductionOn' a ?_
  intro r
  change
    (((Pi.evalRingHom (fun p : minimalPrimes R ↦ R ⧸ p.1) q).comp
        (reducedDiagonalMap (R := R))) ((Ideal.Quotient.mk (nilradical R)) r) = 0) ↔
      (Ideal.Quotient.mk (nilradical R)) r ∈ Ideal.map (Ideal.Quotient.mk (nilradical R)) q.1
  -- Unfold the composed coordinate map before applying the generator formula.
  simp only [RingHom.comp_apply, Pi.evalRingHom_apply]
  rw [reduced_coordinate_apply_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change r ∈ q.1 ↔ r ∈ Ideal.comap (Ideal.Quotient.mk (nilradical R))
    (Ideal.map (Ideal.Quotient.mk (nilradical R)) q.1)
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker]
  have hnil_le_q : nilradical R ≤ q.1 := nilradical_le_prime q.1
  simpa [sup_eq_left.mpr hnil_le_q]

/-- Helper for Lemma 15.126.2: the surviving `q`-coordinate of the reduced diagonal is
surjective. -/
private theorem reduced_coordinate_surjective
    (q : minimalPrimes R) :
    Function.Surjective
      ((Pi.evalRingHom (fun p : minimalPrimes R ↦ R ⧸ p.1) q).comp
        (reducedDiagonalMap (R := R))) := by
  intro y
  refine Quotient.inductionOn' y ?_
  intro r
  refine ⟨(Ideal.Quotient.mk (nilradical R)) r, ?_⟩
  -- The coordinate formula on quotient generators gives the required preimage.
  exact reduced_coordinate_apply_mk (R := R) q r

/-- Helper for Lemma 15.126.2: after localizing the product of minimal-prime quotients at `q`,
the surviving coordinate is the projection to the localized `q`-factor transported across the
owner product-localization equivalence. -/
private noncomputable def localized_survivingCoordinateMap
    (q : minimalPrimes R) :
    LocalizedModule.AtPrime q.1 (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R]
      LocalizedModule.AtPrime q.1 (R ⧸ q.1) :=
  ((LinearMap.proj q :
      (∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1)) →ₗ[
        Localization.AtPrime q.1] LocalizedModule.AtPrime q.1 (R ⧸ q.1)).restrictScalars R).comp
    (localized_minimalPrimeProduct_equiv (R := R) q).toLinearMap

/-- Helper for Lemma 15.126.2: localizing the `q`-coordinate of the reduced diagonal gives the
canonical localized map from the reduced quotient to the localized `q`-factor. -/
private noncomputable def reducedLocalizedCoordinateMap
    (q : minimalPrimes R) :
    LocalizedModule.AtPrime q.1 (R ⧸ nilradical R) →ₗ[R]
      LocalizedModule.AtPrime q.1 (R ⧸ q.1) :=
  LocalizedModule.map q.1.primeCompl
    ((LinearMap.proj q : (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R] R ⧸ q.1) ∘ₗ
      (reducedDiagonalLinearMap (R := R)))

/-- Helper for Lemma 15.126.2: after transporting the localized reduced diagonal through the
product-localization equivalence, projecting to the surviving `q`-coordinate is exactly the
localized `q`-coordinate map. -/
private theorem localized_surviving_coordinate_transport
    (q : minimalPrimes R) :
    (localized_survivingCoordinateMap (R := R) q).comp
        ((LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))).restrictScalars R) =
      reducedLocalizedCoordinateMap (R := R) q := by
  -- Compare the two localized maps after precomposing with the localization generator map.
  apply IsLocalizedModule.linearMap_ext (S := q.1.primeCompl)
    (LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ nilradical R))
    (LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ q.1))
  apply LinearMap.ext
  intro a
  -- On generators, the product-localization equivalence computes coordinatewise.
  simpa [localized_survivingCoordinateMap, reducedLocalizedCoordinateMap,
      LinearMap.comp_apply, LocalizedModule.map_mk] using
    congrArg
      (fun z :
        ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) ↦ z q)
      (localized_minimalPrimeProduct_equiv_reduced_diagonal_mk_apply (R := R) q a)

/-- Helper for Lemma 15.126.2: after localizing at a minimal prime, the reduced diagonal map is
surjective. -/
private theorem localized_reduced_diagonal_surjective_at_minimalPrime
    (q : minimalPrimes R) :
    Function.Surjective
      (LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))) := by
  let k := localized_survivingCoordinateMap (R := R) q
  have hk_bij : Function.Bijective k := by
    -- The localized product equivalence is bijective, and projection is bijective because all
    -- off-diagonal localized factors vanish.
    exact
      (localized_product_proj_bijective_at_minimalPrime (R := R) q).comp
        (localized_minimalPrimeProduct_equiv (R := R) q).bijective
  have hcoord_surj :
      Function.Surjective (reducedLocalizedCoordinateMap (R := R) q) := by
    have hbase_surj :
        Function.Surjective
          (((LinearMap.proj q : (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R] R ⧸ q.1) ∘ₗ
            (reducedDiagonalLinearMap (R := R)))) := by
      intro y
      obtain ⟨a, ha⟩ := reduced_coordinate_surjective (R := R) q y
      refine ⟨a, ?_⟩
      -- Forgetting the ring-hom packaging leaves exactly the same coordinate map.
      simpa [reducedDiagonalLinearMap, LinearMap.comp_apply] using ha
    -- Localization preserves surjectivity of the coordinate map.
    simpa [reducedLocalizedCoordinateMap] using
      (LocalizedModule.map_surjective q.1.primeCompl
        ((LinearMap.proj q : (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R] R ⧸ q.1) ∘ₗ
          (reducedDiagonalLinearMap (R := R))) hbase_surj)
  intro z
  obtain ⟨y, hy⟩ := hcoord_surj (k z)
  refine ⟨y, ?_⟩
  -- Apply injectivity of `k` after rewriting the left-hand side via the transport lemma.
  apply hk_bij.1
  have htransport :=
    congrArg
      (fun f :
        LocalizedModule.AtPrime q.1 (R ⧸ nilradical R) →ₗ[R]
          LocalizedModule.AtPrime q.1 (R ⧸ q.1) ↦ f y)
      (localized_surviving_coordinate_transport (R := R) q)
  have hkfy :
      k (((LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))) y)) =
        reducedLocalizedCoordinateMap (R := R) q y := by
    simpa [k, LinearMap.comp_apply] using htransport
  exact hkfy.trans hy

/-- Helper for Lemma 15.126.2: the cokernel of the reduced diagonal is supported inside the basic
closed set cut out by `x`. -/
private theorem reduced_diagonal_cokernel_support_subset_zeroLocus
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    Module.support R
        ((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R))) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span ({(x : R)} : Set R)) := by
  intro q hq
  rw [PrimeSpectrum.mem_zeroLocus]
  by_contra hxq
  have hxq' : (x : R) ∉ q.asIdeal := by
    intro hxmem
    have hspan : Ideal.span ({(x : R)} : Set R) ≤ q.asIdeal := by
      simpa using (Ideal.span_singleton_le_iff_mem (I := q.asIdeal) (x := (x : R))).2 hxmem
    exact hxq hspan
  have hqmin : q.asIdeal ∈ minimalPrimes R :=
    prime_not_mem_x_mem_minimalPrimes (R := R) x q hxq'
  let qmin : minimalPrimes R := ⟨q.asIdeal, hqmin⟩
  have hsurj :
      Function.Surjective
        (LocalizedModule.map q.asIdeal.primeCompl (reducedDiagonalLinearMap (R := R))) := by
    simpa [qmin] using
      localized_reduced_diagonal_surjective_at_minimalPrime (R := R) qmin
  have hq_not_mem :
      q ∉ Module.support R
        ((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R))) :=
    (localized_surjective_iff_not_mem_support_cokernel
      (reducedDiagonalLinearMap (R := R)) q).mp hsurj
  exact hq_not_mem hq

/-- Helper for Lemma 15.126.2: some positive power of `(x)` annihilates the cokernel of the
reduced diagonal. -/
private theorem exists_pos_pow_span_singleton_le_annihilator_reduced_diagonal_cokernel
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    ∃ N : ℕ,
      0 < N ∧
        ((Ideal.span ({(x : R)} : Set R)) ^ N ≤
          Module.annihilator R
            ((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
              LinearMap.range (reducedDiagonalLinearMap (R := R)))) := by
  let C :=
    ((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
      LinearMap.range (reducedDiagonalLinearMap (R := R)))
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let _ : Module.Finite R (∀ p : minimalPrimes R, R ⧸ p.1) := by infer_instance
  let _ : Module.Finite R C := Module.Finite.quotient R _
  have hsupport :
      Module.support R C ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({(x : R)} : Set R)) := by
    simpa [C] using
      reduced_diagonal_cokernel_support_subset_zeroLocus (R := R) x hmin
  obtain ⟨n, hn⟩ :=
    (Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus
      (M := C) (Ideal.span ({(x : R)} : Set R))
      (Ideal.fg_of_isNoetherianRing (Ideal.span ({(x : R)} : Set R)))).mpr hsupport
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn

/-- Helper for Lemma 15.126.2: multiplication by a power of `x` is injective both on the reduced
quotient and on the product of the minimal-prime quotients. -/
private theorem pow_image_injective_on_reduced_and_minimalPrime_product
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) (N : ℕ) :
    Function.Injective (fun a : R ⧸ nilradical R ↦ ((x : R) ^ N) • a) ∧
      Function.Injective (fun b : ∀ p : minimalPrimes R, R ⧸ p.1 ↦ ((x : R) ^ N) • b) := by
  have hprod_inj :
      Function.Injective (fun b : ∀ p : minimalPrimes R, R ⧸ p.1 ↦ ((x : R) ^ N) • b) := by
    intro b₁ b₂ hmul
    ext p
    have hlocalDomain := minimalPrimeQuotient_isLocalDomain (R := R) p
    let _ : IsLocalRing (R ⧸ p.1) := hlocalDomain.1
    let _ : IsDomain (R ⧸ p.1) := hlocalDomain.2
    have hxpow_ne_zero : (Ideal.Quotient.mk p.1 ((x : R) ^ N)) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero N fun hxbar ↦
        hmin p p.2 ((Ideal.Quotient.eq_zero_iff_mem).mp hxbar)
    have hp := congrFun hmul p
    change (Ideal.Quotient.mk p.1 ((x : R) ^ N)) * b₁ p =
        (Ideal.Quotient.mk p.1 ((x : R) ^ N)) * b₂ p at hp
    exact mul_left_cancel₀ hxpow_ne_zero hp
  have hred_inj :
      Function.Injective (fun a : R ⧸ nilradical R ↦ ((x : R) ^ N) • a) := by
    intro a₁ a₂ hmul
    apply reduced_diagonal_map_injective (R := R)
    apply hprod_inj
    ext p
    -- Apply the reduced diagonal to the scaled equality and rewrite each coordinate.
    simpa [Algebra.smul_def, map_pow] using
      congrArg (fun a : R ⧸ nilradical R ↦ (reducedDiagonalMap (R := R) a) p) hmul
  exact ⟨hred_inj, hprod_inj⟩

/-- Helper for Lemma 15.126.2: quotienting the reduced ring by `(x^N)` is no longer than the
corresponding quotient of `R`, so Lemma `15.126.1` gives the canonical upper bound. -/
private theorem reduced_pow_quotient_length_le_nsmul_ord
    (x : maximalIdeal R) (N : ℕ) :
    Module.length R
        ((R ⧸ nilradical R) ⧸
          ((Ideal.span ({(x : R)} : Set R)) ^ N •
            (⊤ : Submodule R (R ⧸ nilradical R)))) ≤
      N • Ring.ord R x := by
  let A := R ⧸ nilradical R
  let I : Ideal R := (Ideal.span ({(x : R)} : Set R)) ^ N
  let π : R →ₗ[R] A := (Ideal.Quotient.mkₐ R (nilradical R)).toLinearMap
  let πI : (R ⧸ (I • (⊤ : Submodule R R))) →ₗ[R] (A ⧸ (I • (⊤ : Submodule R A))) :=
    (I • (⊤ : Submodule R R)).mapQ (I • (⊤ : Submodule R A)) π
      (Submodule.smul_top_le_comap_smul_top I π)
  have hπIsurj : Function.Surjective πI := by
    intro y
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R A)) y
    obtain ⟨r, rfl⟩ := (Ideal.Quotient.mk_surjective :
      Function.Surjective (Ideal.Quotient.mk (nilradical R))) a
    -- The quotient map induced by `R → R_red` is still surjective on quotient representatives.
    refine ⟨(I • (⊤ : Submodule R R)).mkQ r, ?_⟩
    simpa [π, πI] using
      DFunLike.congr_fun
        (Submodule.mapQ_mkQ (I • (⊤ : Submodule R R)) (I • (⊤ : Submodule R A)) π) r
  calc
    Module.length R (A ⧸ (I • (⊤ : Submodule R A))) ≤
        Module.length R (R ⧸ (I • (⊤ : Submodule R R))) := by
          exact Module.length_le_of_surjective πI hπIsurj
    _ = Module.length R (R ⧸ I) := by
          rw [Ideal.smul_eq_mul, Ideal.mul_top]
    _ = Ring.ord R ((x : R) ^ N) := by
          -- Rewrite the principal power to the owner quotient-length formula `Ring.ord`.
          rw [show I = Ideal.span ({((x : R) ^ N)} : Set R) by
            simpa [I] using (Ideal.span_singleton_pow (x : R) N), Ring.ord]
    _ ≤ N • Ring.ord R x := by
          simpa using ord_pow_le_nsmul_ord (R := R) (x := (x : R)) N

/-- Helper for Lemma 15.126.2: every minimal-prime factor contributes at least `N` to the
quotient by `(x^N)` because the image of `x` has order of vanishing at least `1`. -/
private theorem minimalPrime_factor_pow_quotient_length_lower_bound
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p)
    (p : minimalPrimes R) (N : ℕ) :
    (N : ℕ∞) ≤
      Module.length R
        ((R ⧸ p.1) ⧸
          ((Ideal.span ({(x : R)} : Set R)) ^ N •
            (⊤ : Submodule R (R ⧸ p.1)))) := by
  let S := R ⧸ p.1
  have hsurj : Function.Surjective (algebraMap R S) := by
    simpa [S, Ideal.Quotient.algebraMap_eq] using
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk p.1))
  have hmap_pow :
      Ideal.map (algebraMap R S) ((Ideal.span ({(x : R)} : Set R)) ^ N) =
        Ideal.span ({((algebraMap R S) (x : R)) ^ N} : Set S) := by
    -- Push the principal power through the quotient map before reading it as an order.
    calc
      Ideal.map (algebraMap R S) ((Ideal.span ({(x : R)} : Set R)) ^ N) =
          (Ideal.map (algebraMap R S) (Ideal.span ({(x : R)} : Set R))) ^ N := by
            rw [Ideal.map_pow]
      _ = (Ideal.span ({(algebraMap R S (x : R))} : Set S)) ^ N := by
            rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span ({((algebraMap R S) (x : R)) ^ N} : Set S) := by
            exact Ideal.span_singleton_pow ((algebraMap R S) (x : R)) N
  calc
    (N : ℕ∞) ≤ Ring.ord S (((algebraMap R S) (x : R)) ^ N) := by
      simpa [S, Ideal.Quotient.algebraMap_eq] using
        exponent_le_ord_pow_image_of_not_mem_minimalPrime
          (R := R) x p (n := N) (hmin p p.2)
    _ = Module.length S
          (S ⧸ Ideal.map (algebraMap R S) ((Ideal.span ({(x : R)} : Set R)) ^ N)) := by
            rw [Ring.ord, hmap_pow]
    _ = Module.length R
          (S ⧸ Ideal.map (algebraMap R S) ((Ideal.span ({(x : R)} : Set R)) ^ N)) := by
            symm
            rw [Module.length_eq_of_surjective hsurj]
    _ = Module.length R
          (S ⧸ Submodule.restrictScalars R
            (Ideal.map (algebraMap R S) ((Ideal.span ({(x : R)} : Set R)) ^ N))) := by
            rfl
    _ = Module.length R
          (S ⧸ (((Ideal.span ({(x : R)} : Set R)) ^ N) • (⊤ : Submodule R S))) := by
            rw [Ideal.smul_top_eq_map]

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: for nested submodules `K ≤ L`, the quotient `L / K` identifies with
the image of `L` inside `M / K`. -/
private noncomputable def quotient_submoduleOf_equiv_image
    {M : Type*} [AddCommGroup M] [Module R M]
    (K L : Submodule R M) :
    (L ⧸ K.submoduleOf L) ≃ₗ[R] L.map K.mkQ :=
  let f : L →ₗ[R] M ⧸ K := K.mkQ.comp L.subtype
  let hk : f.ker = K.submoduleOf L := by
    -- The elements of `L` mapping to zero mod `K` are exactly those already lying in `K`.
    ext x
    simp [f, Submodule.submoduleOf]
  let hr : f.range = L.map K.mkQ := by
    -- The image of the induced map is exactly the visible image of `L` in the ambient quotient.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: if `K ≤ L`, then the quotient `M / K` splits into the outer quotient
`M / L` and the intermediate subquotient `L / K`. -/
private theorem length_quotient_eq_add_length_subquotient
    {M : Type*} [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L) :
    Module.length R (M ⧸ K) =
      Module.length R (M ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) := by
  let π : M ⧸ K →ₗ[R] M ⧸ L := Submodule.mapQ K L (LinearMap.id) hKL
  have hπsurj : Function.Surjective π := by
    -- Every class modulo `L` is still represented by the same element modulo `K`.
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hker : π.ker = L.map K.mkQ := by
    -- The kernel is exactly the image of `L` inside `M / K`.
    ext y
    refine Quotient.inductionOn' y ?_
    intro x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hxL : x ∈ L := by
        simpa [π] using (Submodule.Quotient.mk_eq_zero L).1 hx
      exact ⟨x, hxL, rfl⟩
    · rintro ⟨z, hzL, hz⟩
      rw [LinearMap.mem_ker]
      rw [← hz]
      exact (Submodule.Quotient.mk_eq_zero L).2 hzL
  have hkerLength :
      Module.length R π.ker = Module.length R (L ⧸ K.submoduleOf L) := by
    -- Replace the kernel model by the standard subquotient `L / K`.
    rw [hker]
    symm
    exact (quotient_submoduleOf_equiv_image (R := R) K L).length_eq
  have hlen :
      Module.length R (M ⧸ K) = Module.length R π.ker + Module.length R (M ⧸ L) := by
    -- Apply additivity of length to `0 → ker π → M / K → M / L → 0`.
    simpa using
      (Module.length_eq_add_of_exact
        (π.ker.subtype)
        π
        (Submodule.subtype_injective _)
        hπsurj
        (LinearMap.exact_subtype_ker_map π))
  calc
    Module.length R (M ⧸ K) = Module.length R π.ker + Module.length R (M ⧸ L) := hlen
    _ = Module.length R (L ⧸ K.submoduleOf L) + Module.length R (M ⧸ L) := by
      rw [hkerLength]
    _ = Module.length R (M ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) := by
      rw [add_comm]

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: quotient maps induced by ambient linear maps send a quotient
generator to the class of its image. -/
private theorem quotientByIdealTopMap_apply_mk
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N)
    (hφ : I • (⊤ : Submodule R M) ≤ Submodule.comap φ (I • (⊤ : Submodule R N)))
    (x : M) :
    (Submodule.mapQ
        (I • (⊤ : Submodule R M))
        (I • (⊤ : Submodule R N))
        φ hφ)
        (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (φ x) :
        N ⧸ I • (⊤ : Submodule R N)) := by
  -- The induced quotient map acts on representatives by the underlying linear map.
  simpa using
    DFunLike.congr_fun
      (Submodule.mapQ_mkQ
        (I • (⊤ : Submodule R M))
        (I • (⊤ : Submodule R N))
        φ)
      x

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: the quotient map induced by an ambient linear map modulo `I • ⊤`. -/
private noncomputable def quotientByIdealTopMap
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
  Submodule.mapQ
    (I • (⊤ : Submodule R M))
    (I • (⊤ : Submodule R N))
    φ
    (Submodule.smul_top_le_comap_smul_top I φ)

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: the local quotient map `quotientByIdealTopMap` acts on generators
by the underlying linear map. -/
private theorem quotientByIdealTopMap_mk
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (x : M) :
    quotientByIdealTopMap (R := R) I φ (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (φ x) : N ⧸ I • (⊤ : Submodule R N)) := by
  -- Expand the local quotient map definition and use the owner `mapQ_mkQ` computation rule.
  exact quotientByIdealTopMap_apply_mk (R := R) I φ (Submodule.smul_top_le_comap_smul_top I φ) x

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: quotienting by `I • ⊤` preserves surjectivity of a linear map. -/
private theorem quotientByIdealTopMap_surjective
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (hφ : Function.Surjective φ) :
    Function.Surjective (quotientByIdealTopMap (R := R) I φ) := by
  intro y
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) y
  obtain ⟨m, rfl⟩ := hφ n
  -- The descended quotient map sends the chosen representative to the required quotient class.
  refine ⟨Submodule.Quotient.mk m, ?_⟩
  exact quotientByIdealTopMap_mk (R := R) I φ m

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: quotienting by `I • ⊤` preserves exactness of a surjective pair. -/
private theorem quotientMapByIdeal_exact
    (I : Ideal R)
    {N P Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (quotientByIdealTopMap (R := R) I f) (quotientByIdealTopMap (R := R) I g) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x :=
      -- Lift the `I • ⊤` witness from the quotient target back through surjectivity of `g`.
      Submodule.smul_induction_on hx'
        (fun r hr z _ ↦ by
          obtain ⟨y, rfl⟩ := hg z
          refine ⟨r • y, ?_, by simp⟩
          exact Submodule.smul_mem_smul hr (by simp))
        (fun y z hy hz ↦ by
          rcases hy with ⟨y', hy', rfl⟩
          rcases hz with ⟨z', hz', rfl⟩
          exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩)
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    have hyzero : ((I • (⊤ : Submodule R P)).mkQ y : P ⧸ I • (⊤ : Submodule R P)) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hyI
    calc
      (I • (⊤ : Submodule R P)).mkQ (f n) = (I • (⊤ : Submodule R P)).mkQ (x - y) := by
        rw [hn]
      _ = (I • (⊤ : Submodule R P)).mkQ x := by
        rw [LinearMap.map_sub, hyzero, sub_zero]
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: a linear equivalence transports quotients by `I • ⊤` across the
ambient module equivalence. -/
private noncomputable def quotientByIdealTopLinearEquiv
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
  let hForward :
      I • (⊤ : Submodule R M) ≤
        Submodule.comap e.toLinearMap (I • (⊤ : Submodule R N)) := by
    -- Transport visible `I`-multiples forward across the linear equivalence.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e y ∈ (⊤ : Submodule R N) by simp))
  let hBackward :
      I • (⊤ : Submodule R N) ≤
        Submodule.comap e.symm.toLinearMap (I • (⊤ : Submodule R M)) := by
    -- The inverse equivalence gives the reverse quotient transport.
    rw [Submodule.smul_le]
    intro r hr y hy
    simpa using
      (Submodule.smul_mem_smul hr (show e.symm y ∈ (⊤ : Submodule R M) by simp))
  let f :
      (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule R M))
      (I • (⊤ : Submodule R N))
      e.toLinearMap
      hForward
  let g :
      (N ⧸ I • (⊤ : Submodule R N)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
    Submodule.mapQ
      (I • (⊤ : Submodule R N))
      (I • (⊤ : Submodule R M))
      e.symm.toLinearMap
      hBackward
  -- Check both composites on quotient generators and use that `e` and `e.symm` are inverses.
  LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change f (g (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      rw [quotientByIdealTopMap_apply_mk (R := R) I e.symm.toLinearMap hBackward]
      rw [quotientByIdealTopMap_apply_mk (R := R) I e.toLinearMap hForward]
      simp)
    (by
      apply LinearMap.ext
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change g (f (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
      rw [quotientByIdealTopMap_apply_mk (R := R) I e.toLinearMap hForward]
      rw [quotientByIdealTopMap_apply_mk (R := R) I e.symm.toLinearMap hBackward]
      simp)

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: the `Option`-splitting equivalence already transports the quotient
by `I • ⊤` from a finite product family to the corresponding binary product. -/
private noncomputable def quotient_piOptionEquivProd_transport
    (I : Ideal R) {ι : Type*} {M : Option ι → Type*}
    [(i : Option ι) → AddCommGroup (M i)] [(i : Option ι) → Module R (M i)] :
    ((((i : Option ι) → M i) ⧸ I • (⊤ : Submodule R ((i : Option ι) → M i))) ≃ₗ[R]
      ((M none × ((i : ι) → M (some i))) ⧸
        I • (⊤ : Submodule R (M none × ((i : ι) → M (some i)))))) :=
  quotientByIdealTopLinearEquiv (R := R) I (LinearEquiv.piOptionEquivProd R)

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: quotienting a binary product by `I • ⊤` has length equal to the
sum of the two quotient lengths. -/
private theorem length_quotientByIdealTop_prod_eq_add
    (I : Ideal R) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (((M × N) ⧸ I • (⊤ : Submodule R (M × N)))) =
      Module.length R (M ⧸ I • (⊤ : Submodule R M)) +
        Module.length R (N ⧸ I • (⊤ : Submodule R N)) := by
  let inlbar :
      (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R]
        ((M × N) ⧸ I • (⊤ : Submodule R (M × N))) :=
    quotientByIdealTopMap (R := R) I (LinearMap.inl R M N)
  let sndbar :
      ((M × N) ⧸ I • (⊤ : Submodule R (M × N))) →ₗ[R]
        (N ⧸ I • (⊤ : Submodule R N)) :=
    quotientByIdealTopMap (R := R) I (LinearMap.snd R M N)
  let fstbar :
      ((M × N) ⧸ I • (⊤ : Submodule R (M × N))) →ₗ[R]
        (M ⧸ I • (⊤ : Submodule R M)) :=
    quotientByIdealTopMap (R := R) I (LinearMap.fst R M N)
  have hleft : Function.LeftInverse fstbar inlbar := by
    -- The quotient of `fst` is a left inverse to the quotient of `inl` on generators.
    intro q
    refine Quotient.inductionOn' q ?_
    intro m
    change fstbar (inlbar (Submodule.Quotient.mk m)) = Submodule.Quotient.mk m
    rw [quotientByIdealTopMap_mk (R := R) I (LinearMap.inl R M N)]
    rw [quotientByIdealTopMap_mk (R := R) I (LinearMap.fst R M N)]
    rfl
  have hinj : Function.Injective inlbar := hleft.injective
  have hsurj : Function.Surjective sndbar := by
    -- Every quotient class in the right factor comes from the class of `(0, n)`.
    intro q
    refine Quotient.inductionOn' q ?_
    intro n
    refine ⟨Submodule.Quotient.mk (0, n), ?_⟩
    change sndbar (Submodule.Quotient.mk (0, n)) = Submodule.Quotient.mk n
    rw [quotientByIdealTopMap_mk (R := R) I (LinearMap.snd R M N)]
    rfl
  have hexact : Function.Exact inlbar sndbar := by
    -- Route correction: only the descended exact sequence is needed here, not a full quotient
    -- product equivalence.
    simpa [inlbar, sndbar] using
      (quotientMapByIdeal_exact (R := R) (I := I) (LinearMap.inl R M N) (LinearMap.snd R M N)
        (Function.Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N))
        LinearMap.snd_surjective)
  -- Apply additivity of length to the reduced split exact sequence.
  simpa [inlbar, sndbar] using
    (Module.length_eq_add_of_exact inlbar sndbar hinj hsurj hexact)

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: length is additive on binary products. -/
private theorem length_prod_eq_add
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (M × N) = Module.length R M + Module.length R N := by
  -- Apply additivity of length to the split short exact sequence `0 → M → M × N → N → 0`.
  simpa using
    (Module.length_eq_add_of_exact
      (LinearMap.inl R M N)
      (LinearMap.snd R M N)
      LinearMap.inl_injective
      LinearMap.snd_surjective
      (Function.Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N)))

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: the quotient by `I • ⊤` on an `Option`-indexed finite product has
length equal to the sum of the lengths of the two quotient factors. -/
private theorem length_quotient_piOption_eq_add
    (I : Ideal R) {ι : Type*} {M : Option ι → Type*}
    [(i : Option ι) → AddCommGroup (M i)] [(i : Option ι) → Module R (M i)] :
    Module.length R (((i : Option ι) → M i) ⧸ I • (⊤ : Submodule R ((i : Option ι) → M i))) =
      Module.length R (M none ⧸ I • (⊤ : Submodule R (M none))) +
        Module.length R ((((i : ι) → M (some i)) ⧸
          I • (⊤ : Submodule R ((i : ι) → M (some i))))) := by
  -- Transport to the binary product quotient and apply the direct binary length formula.
  calc
    Module.length R (((i : Option ι) → M i) ⧸ I • (⊤ : Submodule R ((i : Option ι) → M i))) =
        Module.length R
          (((M none × ((i : ι) → M (some i))) ⧸
            I • (⊤ : Submodule R (M none × ((i : ι) → M (some i)))))) := by
      exact (quotient_piOptionEquivProd_transport (R := R) I).length_eq
    _ =
        Module.length R (M none ⧸ I • (⊤ : Submodule R (M none))) +
          Module.length R ((((i : ι) → M (some i)) ⧸
            I • (⊤ : Submodule R ((i : ι) → M (some i))))) := by
      simpa using
        (length_quotientByIdealTop_prod_eq_add (R := R) I
          (M := M none) (N := ((i : ι) → M (some i))))

omit [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R] in
/-- Helper for Lemma 15.126.2: for a finite product, a uniform lower bound on each quotient
factor adds to the corresponding lower bound on the quotient of the whole product. -/
private theorem finite_pi_quotient_length_lower_bound
    (I : Ideal R) (N : ℕ) {ι : Type u} [Fintype ι] {M : ι → Type u}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)]
    (hfactor :
      ∀ i, (N : ℕ∞) ≤ Module.length R (M i ⧸ I • (⊤ : Submodule R (M i)))) :
    (N : ℕ∞) * Fintype.card ι ≤
      Module.length R (((i : ι) → M i) ⧸ I • (⊤ : Submodule R ((i : ι) → M i))) := by
  classical
  let P : ∀ (κ : Type u) [Fintype κ], Prop := fun κ _ =>
    ∀ (M : κ → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ i, (N : ℕ∞) ≤ Module.length R (M i ⧸ I • (⊤ : Submodule R (M i)))) →
        (N : ℕ∞) * Fintype.card κ ≤
          Module.length R (((i : κ) → M i) ⧸ I • (⊤ : Submodule R ((i : κ) → M i)))
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e hα
      letI : Fintype α := Fintype.ofEquiv β e.symm
      intro M hAdd hMod hβ
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module R (M i) := hMod
      have hαbound :
          (N : ℕ∞) * Fintype.card α ≤
            Module.length R
              (((i : α) → M (e i)) ⧸ I • (⊤ : Submodule R ((i : α) → M (e i)))) :=
        hα (fun i ↦ M (e i)) (fun i ↦ hβ (e i))
      -- Reindex the finite family along `e` and transport the quotient length across the
      -- induced product equivalence.
      calc
        (N : ℕ∞) * Fintype.card β = (N : ℕ∞) * Fintype.card α := by
          simpa using congrArg (fun n : ℕ ↦ ((N : ℕ∞) * n)) (Fintype.card_congr e).symm
        _ ≤ Module.length R
              (((i : α) → M (e i)) ⧸ I • (⊤ : Submodule R ((i : α) → M (e i)))) :=
          hαbound
        _ = Module.length R (((i : β) → M i) ⧸ I • (⊤ : Submodule R ((i : β) → M i))) := by
          simpa using
            (quotientByIdealTopLinearEquiv (R := R) I
              (LinearEquiv.piCongrLeft R (fun i : β ↦ M i) e)).length_eq
    · intro M hAdd hMod hEmpty
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module R (M i) := hMod
      letI :
          Subsingleton
            (((i : PEmpty) → M i) ⧸ I • (⊤ : Submodule R ((i : PEmpty) → M i))) := by
        infer_instance
      -- The empty product is the zero module, so both sides are zero.
      simp [Module.length_eq_zero]
    · intro α _ hα
      intro M hAdd hMod hOption
      letI : ∀ i, AddCommGroup (M i) := hAdd
      letI : ∀ i, Module R (M i) := hMod
      letI : ∀ i : α, AddCommGroup (M (some i)) := fun i ↦ hAdd (some i)
      letI : ∀ i : α, Module R (M (some i)) := fun i ↦ hMod (some i)
      have htail :
          (N : ℕ∞) * Fintype.card α ≤
            Module.length R
              (((i : α) → M (some i)) ⧸ I • (⊤ : Submodule R ((i : α) → M (some i)))) :=
        hα (fun i ↦ M (some i)) (fun i ↦ hOption (some i))
      -- Split off the `none` factor and add the induction hypothesis to the first-coordinate
      -- lower bound.
      calc
        (N : ℕ∞) * Fintype.card (Option α) = (N : ℕ∞) + (N : ℕ∞) * Fintype.card α := by
          rw [Fintype.card_option, Nat.add_comm, Nat.cast_add, mul_add]
          simp
        _ ≤ Module.length R (M none ⧸ I • (⊤ : Submodule R (M none))) +
              Module.length R
                (((i : α) → M (some i)) ⧸ I • (⊤ : Submodule R ((i : α) → M (some i)))) := by
          exact add_le_add (hOption none) htail
        _ = Module.length R
              (((i : Option α) → M i) ⧸ I • (⊤ : Submodule R ((i : Option α) → M i))) := by
          symm
          exact length_quotient_piOption_eq_add (R := R) I (M := M)
  exact hP M hfactor

/-- Helper for Lemma 15.126.2: summing the factorwise lower bounds gives the expected lower bound
for the quotient of the minimal-prime product. -/
private theorem minimalPrime_product_pow_quotient_length_lower_bound
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) (N : ℕ) :
    (N : ℕ∞) * (minimalPrimes R).encard ≤
      Module.length R
        (((p : minimalPrimes R) → R ⧸ p.1) ⧸
          ((Ideal.span ({(x : R)} : Set R)) ^ N •
            (⊤ : Submodule R (((p : minimalPrimes R) → R ⧸ p.1))))) := by
  classical
  let I : Ideal R := (Ideal.span ({(x : R)} : Set R)) ^ N
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  have hprod :
      (N : ℕ∞) * Fintype.card (minimalPrimes R) ≤
        Module.length R
          (((p : minimalPrimes R) → R ⧸ p.1) ⧸
            (I • (⊤ : Submodule R (((p : minimalPrimes R) → R ⧸ p.1))))) := by
    -- Apply the generic finite-product estimate with the one-factor bounds proved above.
    refine finite_pi_quotient_length_lower_bound (R := R) I N ?_
    intro p
    simpa [I] using
      minimalPrime_factor_pow_quotient_length_lower_bound (R := R) x hmin p N
  -- Convert the finite-cardinality model of `minimalPrimes R` back to the source-facing `encard`.
  calc
    (N : ℕ∞) * (minimalPrimes R).encard = (N : ℕ∞) * Fintype.card (minimalPrimes R) := by
      rw [(Set.coe_fintypeCard (minimalPrimes R)).symm]
    _ ≤ Module.length R
          (((p : minimalPrimes R) → R ⧸ p.1) ⧸
            (I • (⊤ : Submodule R (((p : minimalPrimes R) → R ⧸ p.1))))) := hprod
    _ = Module.length R
          (((p : minimalPrimes R) → R ⧸ p.1) ⧸
            (((Ideal.span ({(x : R)} : Set R)) ^ N) •
              (⊤ : Submodule R (((p : minimalPrimes R) → R ⧸ p.1))))) := by
      rfl

/-- Helper for Lemma 15.126.2: the cokernel of the reduced diagonal is supported only at the
closed point, hence has finite length. -/
private theorem reduced_diagonal_cokernel_isFiniteLength
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    IsFiniteLength R
      (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
        LinearMap.range (reducedDiagonalLinearMap (R := R)))) := by
  let C :=
    (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
      LinearMap.range (reducedDiagonalLinearMap (R := R))))
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  let _ : Module.Finite R (∀ p : minimalPrimes R, R ⧸ p.1) := by infer_instance
  let _ : Module.Finite R C := Module.Finite.quotient R _
  have hsupport_closed :
      Module.support R C ⊆ ({closedPoint R} : Set (PrimeSpectrum R)) := by
    intro q hq
    have hxq : (x : R) ∈ q.asIdeal := by
      have hzeroLocus :
          q ∈ PrimeSpectrum.zeroLocus (Ideal.span ({(x : R)} : Set R)) := by
        exact reduced_diagonal_cokernel_support_subset_zeroLocus (R := R) x hmin hq
      rw [PrimeSpectrum.mem_zeroLocus] at hzeroLocus
      exact (Ideal.span_singleton_le_iff_mem (I := q.asIdeal) (x := (x : R))).mp hzeroLocus
    by_cases hqmax : q.asIdeal = maximalIdeal R
    · exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext hqmax)
    · have hqmin : q.asIdeal ∈ minimalPrimes R :=
        nonmaximal_prime_mem_minimalPrimes (R := R) q hqmax
      exact False.elim (hmin q.asIdeal hqmin hxq)
  by_cases hC : Nontrivial C
  · letI := hC
    have hclosed_mem : closedPoint R ∈ Module.support R C :=
      IsLocalRing.closedPoint_mem_support R C
    have hsupport_eq :
        Module.support R C = ({closedPoint R} : Set (PrimeSpectrum R)) := by
      exact Set.Subset.antisymm hsupport_closed (Set.singleton_subset_iff.mpr hclosed_mem)
    exact (support_eq_singleton_closedPoint_iff_isFiniteLength (R := R) (M := C)).mp hsupport_eq
  · haveI : Subsingleton C := not_nontrivial_iff_subsingleton.mp hC
    have hlen_zero : Module.length R C = 0 := by
      simp [Module.length_eq_zero]
    exact (Module.length_ne_top_iff.mp <| by rw [hlen_zero]; simp)

/-- Helper for Lemma 15.126.2: after quotienting by an ideal that already annihilates the cokernel
of the reduced diagonal, the product quotient is no longer than the reduced quotient plus that
fixed cokernel. -/
private theorem minimalPrime_product_quotient_length_le_reduced_quotient_length_add_cokernel
    (I : Ideal R)
    (hIann :
      I ≤ Module.annihilator R
        (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          LinearMap.range (reducedDiagonalLinearMap (R := R))))) :
    Module.length R
        (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
          I • (⊤ : Submodule R (∀ p : minimalPrimes R, R ⧸ p.1)))) ≤
      Module.length R
          (((R ⧸ nilradical R) ⧸
            I • (⊤ : Submodule R (R ⧸ nilradical R)))) +
        Module.length R
          (((∀ p : minimalPrimes R, R ⧸ p.1) ⧸
            LinearMap.range (reducedDiagonalLinearMap (R := R)))) := by
  let A := R ⧸ nilradical R
  let B := ∀ p : minimalPrimes R, R ⧸ p.1
  let φ : A →ₗ[R] B := reducedDiagonalLinearMap (R := R)
  let C := B ⧸ LinearMap.range φ
  let _ : AddCommGroup C := inferInstance
  let _ : Module R C := inferInstance
  let g : B →ₗ[R] C := Submodule.mkQ (LinearMap.range φ)
  let fbar : (A ⧸ I • (⊤ : Submodule R A)) →ₗ[R] (B ⧸ I • (⊤ : Submodule R B)) :=
    quotientByIdealTopMap (R := R) I φ
  let gbar :
      (B ⧸ I • (⊤ : Submodule R B)) →ₗ[R] (C ⧸ I • (⊤ : Submodule R C)) :=
    quotientByIdealTopMap (R := R) I g
  have hExactφg : Function.Exact φ g := by
    -- The quotient by the range of `φ` gives the canonical exact cokernel row.
    rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  have hExactBar : Function.Exact fbar gbar := by
    exact quotientMapByIdeal_exact (R := R) (I := I) φ g hExactφg (Submodule.mkQ_surjective _)
  have hgbar_surj : Function.Surjective gbar := by
    exact quotientByIdealTopMap_surjective (R := R) I g (Submodule.mkQ_surjective _)
  have hker :
      LinearMap.ker gbar = LinearMap.range fbar := by
    rw [LinearMap.exact_iff] at hExactBar
    exact hExactBar
  have hrange_le :
      Module.length R (LinearMap.range fbar) ≤
        Module.length R (A ⧸ I • (⊤ : Submodule R A)) := by
    -- The domain surjects onto the range of the descended reduced diagonal.
    exact Module.length_le_of_surjective fbar.rangeRestrict fbar.surjective_rangeRestrict
  have hIbot : I • (⊤ : Submodule R C) = ⊥ := by
    -- The quotient by `I • ⊤` on the cokernel is trivial because `I` already annihilates `C`.
    simpa [Submodule.annihilator_top] using
      (Submodule.le_annihilator_iff.mp <| by
        simpa [Submodule.annihilator_top] using hIann :
          I • (⊤ : Submodule R C) = ⊥)
  have hCquot :
      Module.length R (C ⧸ I • (⊤ : Submodule R C)) = Module.length R C := by
    -- Once `I • ⊤ = ⊥`, the quotient of `C` is canonically equivalent to `C` itself.
    rw [hIbot]
    simpa using ((⊥ : Submodule R C).quotEquivOfEqBot rfl).length_eq
  have hlen :
      Module.length R (B ⧸ I • (⊤ : Submodule R B)) =
        Module.length R (LinearMap.ker gbar) +
          Module.length R (C ⧸ I • (⊤ : Submodule R C)) := by
    -- Apply additivity of length to the descended exact sequence.
    simpa using
      (Module.length_eq_add_of_exact
        (LinearMap.ker gbar).subtype
        gbar
        (Submodule.subtype_injective _)
        hgbar_surj
        (LinearMap.exact_subtype_ker_map gbar))
  calc
    Module.length R (B ⧸ I • (⊤ : Submodule R B)) =
        Module.length R (LinearMap.ker gbar) +
          Module.length R (C ⧸ I • (⊤ : Submodule R C)) := hlen
    _ = Module.length R (LinearMap.range fbar) +
          Module.length R C := by
      rw [hker, hCquot]
    _ ≤ Module.length R (A ⧸ I • (⊤ : Submodule R A)) +
          Module.length R C := by
      exact add_le_add hrange_le le_rfl

-- Proof sketch: pass to the reduced quotient to preserve the number of minimal primes while only
-- decreasing the quotient length. Embed the reduced ring into the product of its minimal-prime
-- quotients, show the cokernel has finite length and is killed by a power of `x`, and then compare
-- lengths after multiplication by `x^n`. Apply Lemma `15.126.1` to the one-dimensional reduced
-- quotients to conclude that each minimal prime contributes at least `1` to the total length.
/-- Lemma 15.126.2: let `(R, 𝔪)` be a Noetherian local ring of dimension `1`, and let
`x : maximalIdeal R` avoid every minimal prime of `R`. Then the number of minimal prime ideals of
`R`, written as `(minimalPrimes R).encard`, is at most the order of vanishing `Ring.ord R x`,
which is canonically `Module.length R (R ⧸ Ideal.span {x})`. The explicit equality
`ringKrullDim R = 1` from the source is replaced by the owner hypothesis `[Ring.KrullDimLE 1 R]`;
the maximal-ideal condition is absorbed into the input type `x : maximalIdeal R`. -/
theorem encard_minimalPrimes_le_ord
    (x : maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, (x : R) ∉ p) :
    (minimalPrimes R).encard ≤ Ring.ord R x := by
  classical
  have hfinite : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let _ : Fintype (minimalPrimes R) := hfinite.fintype
  by_cases hord_top : Ring.ord R x = ⊤
  · simpa [hord_top]
  let A := R ⧸ nilradical R
  let B := ∀ p : minimalPrimes R, R ⧸ p.1
  let φ : A →+* B := reducedDiagonalMap (R := R)
  have hφinj : Function.Injective φ := reduced_diagonal_map_injective (R := R)
  -- Route correction: the old attempt stopped before the reduced diagonal was even formalized.
  -- The verified skeleton now starts with the canonical injective map
  -- `R_red → ∏ p, R ⧸ p`, matching the source proof.
  have hminimal_off_Dx :
      ∀ q : PrimeSpectrum R, (x : R) ∉ q.asIdeal → q.asIdeal ∈ minimalPrimes R :=
    prime_not_mem_x_mem_minimalPrimes (R := R) x
  let _ := hminimal_off_Dx
  have hprod_equiv :
      ∀ q : minimalPrimes R,
        LocalizedModule.AtPrime q.1 B ≃ₗ[R]
          ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) :=
    localized_minimalPrimeProduct_equiv (R := R)
  have hdiag_mk_apply :
      ∀ q : minimalPrimes R, ∀ a : A,
        localized_minimalPrimeProduct_equiv (R := R) q
          (LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))
            (LocalizedModule.mkLinearMap q.1.primeCompl A a)) =
          fun p => LocalizedModule.mkLinearMap q.1.primeCompl (R ⧸ p.1)
            ((reducedDiagonalMap (R := R) a) p) :=
    localized_minimalPrimeProduct_equiv_reduced_diagonal_mk_apply (R := R)
  have hproj_bij :
      ∀ q : minimalPrimes R,
        Function.Bijective
          (LinearMap.proj q :
            (∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1)) →ₗ[
              Localization.AtPrime q.1] LocalizedModule.AtPrime q.1 (R ⧸ q.1)) :=
    localized_product_proj_bijective_at_minimalPrime (R := R)
  -- The transport layer is now packaged by `localized_minimalPrimeProduct_equiv`, and the
  -- localized product also collapses to the surviving `q`-coordinate.
  -- Route correction: the previous attempts stalled on a monolithic localized-map equality.
  -- The verified frontier now includes the generator-level rewrite `hdiag_mk_apply`; the
  -- remaining blocker is only the identification of the surviving `q`-coordinate with the
  -- localized quotient-by-`q̄` map.
  -- TODO: show that after localizing away from `x`, the map `φ` is bijective; this gives
  -- `support (coker φ) ⊆ V(x)`, hence some power of `x` kills the cokernel by Lemma `10.62.4`.
  -- Then compare `A / x^n A` and `B / x^n B` via the snake-lemma exact sequence, and sum the
  -- factorwise lower bounds already proved above.
  let _ := hfinite
  let _ := hord_top
  let _ := hmin
  let _ := hφinj
  let _ := hprod_equiv
  let _ := hdiag_mk_apply
  let _ := hproj_bij
  let C := B ⧸ LinearMap.range (reducedDiagonalLinearMap (R := R))
  have hsupportC :
      Module.support R C ⊆ PrimeSpectrum.zeroLocus (Ideal.span ({(x : R)} : Set R)) := by
    simpa [B, C] using
      reduced_diagonal_cokernel_support_subset_zeroLocus (R := R) x hmin
  have hpowC :
      ∃ N : ℕ,
        0 < N ∧
          ((Ideal.span ({(x : R)} : Set R)) ^ N ≤ Module.annihilator R C) := by
    simpa [B, C] using
      exists_pos_pow_span_singleton_le_annihilator_reduced_diagonal_cokernel
        (R := R) x hmin
  rcases hpowC with ⟨N, hNpos, hNann⟩
  have hinjPow :
      Function.Injective (fun a : A ↦ ((x : R) ^ N) • a) ∧
        Function.Injective (fun b : B ↦ ((x : R) ^ N) • b) := by
    simpa [A, B] using
      pow_image_injective_on_reduced_and_minimalPrime_product (R := R) x hmin N
  have hAupper :
      Module.length R
          (A ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ N • (⊤ : Submodule R A))) ≤
        N • Ring.ord R x := by
    -- This is the ring-side estimate from the source proof, now closed inside the reduced model.
    simpa [A] using reduced_pow_quotient_length_le_nsmul_ord (R := R) x N
  have hfactorLower :
      ∀ p : minimalPrimes R,
        (N : ℕ∞) ≤
          Module.length R
            ((R ⧸ p.1) ⧸
              ((Ideal.span ({(x : R)} : Set R)) ^ N •
                (⊤ : Submodule R (R ⧸ p.1)))) := by
    intro p
    -- Each factor lower bound is already reduced to Lemma `15.126.1` in the domain quotient.
    exact minimalPrime_factor_pow_quotient_length_lower_bound (R := R) x hmin p N
  let _ := hsupportC
  let _ := hNpos
  let _ := hNann
  let _ := hinjPow
  let _ := hAupper
  let _ := hfactorLower
  have hBlower :
      (N : ℕ∞) * (minimalPrimes R).encard ≤
        Module.length R
          (B ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ N • (⊤ : Submodule R B))) := by
    -- The finite-product aggregation now matches the source step that each minimal prime
    -- contributes at least `N` after passing to the product quotient.
    simpa [B] using
      minimalPrime_product_pow_quotient_length_lower_bound (R := R) x hmin N
  let _ := hBlower
  have hCfinite : IsFiniteLength R C := by
    -- Upgrade the support control for the cokernel to finite length at the closed point.
    simpa [B, C] using reduced_diagonal_cokernel_isFiniteLength (R := R) x hmin
  have hCneTop : Module.length R C ≠ ⊤ :=
    (Module.length_ne_top_iff.mpr hCfinite)
  let c : ℕ := (Module.length R C).toNat
  let n : ℕ := (c + 1) * N
  have hNle : N ≤ n := by
    -- Replacing `N` by a larger multiple keeps the cokernel annihilated.
    dsimp [n]
    calc
      N = 1 * N := by simp
      _ ≤ (c + 1) * N := by
        exact Nat.mul_le_mul_right N (Nat.succ_le_succ (Nat.zero_le c))
  have hn_ann :
      ((Ideal.span ({(x : R)} : Set R)) ^ n ≤ Module.annihilator R C) := by
    exact (Ideal.pow_le_pow_right hNle).trans hNann
  have hCompare :
      Module.length R
          (B ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ n • (⊤ : Submodule R B))) ≤
        Module.length R
            (A ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ n • (⊤ : Submodule R A))) +
          Module.length R C := by
    -- Descend the reduced diagonal modulo the larger annihilating power and keep the cokernel as
    -- a fixed additive error term.
    simpa [A, B, C, n] using
      minimalPrime_product_quotient_length_le_reduced_quotient_length_add_cokernel
        (R := R)
        (I := (Ideal.span ({(x : R)} : Set R)) ^ n)
        hn_ann
  have hBlower_n :
      (n : ℕ∞) * (minimalPrimes R).encard ≤
        Module.length R
          (B ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ n • (⊤ : Submodule R B))) := by
    -- The product lower bound holds uniformly for every exponent.
    simpa [B, n] using
      minimalPrime_product_pow_quotient_length_lower_bound (R := R) x hmin n
  have hAupper_n :
      Module.length R
          (A ⧸ ((Ideal.span ({(x : R)} : Set R)) ^ n • (⊤ : Submodule R A))) ≤
        n • Ring.ord R x := by
    -- The reduced quotient still satisfies the same linear upper bound at the larger exponent.
    simpa [A, n] using reduced_pow_quotient_length_le_nsmul_ord (R := R) x n
  have hmain :
      (n : ℕ∞) * (minimalPrimes R).encard ≤
        n • Ring.ord R x + Module.length R C := by
    -- Combine the product lower bound, the descended exact comparison, and the reduced upper
    -- bound into a single linear inequality.
    exact le_trans hBlower_n <| le_trans hCompare <| add_le_add hAupper_n le_rfl
  have hmain_nat :
      n * Fintype.card (minimalPrimes R) ≤ n * (Ring.ord R x).toNat + c := by
    have hmain' :
        ((n * Fintype.card (minimalPrimes R) : ℕ) : ℕ∞) ≤
          ((n * (Ring.ord R x).toNat + c : ℕ) : ℕ∞) := by
      simpa [c, n, Set.coe_fintypeCard, ENat.coe_toNat hord_top, ENat.coe_toNat hCneTop,
        nsmul_eq_mul] using hmain
    exact ENat.coe_le_coe.mp hmain'
  have hc_lt_n : c < n := by
    -- The multiplier `c + 1` makes the fixed cokernel length strictly smaller than `n`.
    dsimp [n]
    calc
      c < c + 1 := Nat.lt_succ_self c
      _ ≤ (c + 1) * N := by
        have hNone : 1 ≤ N := Nat.succ_le_of_lt hNpos
        simpa [Nat.one_mul] using Nat.mul_le_mul_left (c + 1) hNone
  have hcard_le_ord :
      Fintype.card (minimalPrimes R) ≤ (Ring.ord R x).toNat := by
    -- Absorb the fixed error term `c` into the larger multiple `n = (c + 1) * N`.
    by_contra hcard_gt
    have hsucc_le :
        (Ring.ord R x).toNat + 1 ≤ Fintype.card (minimalPrimes R) := by
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hcard_gt)
    have hmul_le :
        n * ((Ring.ord R x).toNat + 1) ≤ n * Fintype.card (minimalPrimes R) := by
      exact Nat.mul_le_mul_left n hsucc_le
    have hlt :
        n * (Ring.ord R x).toNat + c < n * ((Ring.ord R x).toNat + 1) := by
      calc
        n * (Ring.ord R x).toNat + c < n * (Ring.ord R x).toNat + n := by
          exact Nat.add_lt_add_left hc_lt_n _
        _ = n * ((Ring.ord R x).toNat + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
    exact (Nat.not_le_of_lt hlt) (le_trans hmul_le hmain_nat)
  calc
    (minimalPrimes R).encard = (Fintype.card (minimalPrimes R) : ℕ∞) := by
      rw [Set.coe_fintypeCard]
    _ ≤ ((Ring.ord R x).toNat : ℕ∞) := ENat.coe_le_coe.mpr hcard_le_ord
    _ = Ring.ord R x := ENat.coe_toNat hord_top

end

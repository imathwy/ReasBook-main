import Mathlib

-- Shared reduced-diagonal API extracted for `Lemma_15_126_8`.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Lemma 15.126.8: the intersection of the minimal primes is the nilradical. -/
private theorem sInf_minimalPrimes_eq_nilradical :
    (⨅ p : minimalPrimes R, p.1) = nilradical R := by
  -- Rewrite the minimal-prime intersection as the radical of `(0)`.
  have hsInf : sInf (minimalPrimes R) = nilradical R := by
    have hsInf' : sInf ((⊥ : Ideal R).minimalPrimes) = (⊥ : Ideal R).radical :=
      Ideal.sInf_minimalPrimes
    simpa [minimalPrimes, nilradical, Ideal.zero_eq_bot] using hsInf'
  rw [sInf_eq_iInf] at hsInf
  simpa [iInf_subtype'] using hsInf

/-- Helper for Lemma 15.126.8: the reduced quotient maps diagonally to the product of the
minimal-prime quotients. -/
noncomputable def reducedDiagonalMap :
    (R ⧸ nilradical R) →+* ∀ p : minimalPrimes R, R ⧸ p.1 :=
  (Ideal.quotientInfToPiQuotient fun p : minimalPrimes R ↦ p.1).comp
    (Ideal.quotEquivOfEq (sInf_minimalPrimes_eq_nilradical (R := R)).symm).toRingHom

/-- Helper for Lemma 15.126.8: the reduced diagonal map is injective. -/
theorem reduced_diagonal_map_injective :
    Function.Injective (reducedDiagonalMap (R := R)) := by
  -- Transport the canonical injective quotient-to-product map along
  -- `⨅ minimalPrimes = nilradical`.
  simpa [reducedDiagonalMap] using
    (Ideal.quotientInfToPiQuotient_inj fun p : minimalPrimes R ↦ p.1).comp
      (Ideal.quotEquivOfEq (sInf_minimalPrimes_eq_nilradical (R := R)).symm).injective

/-- Helper for Lemma 15.126.8: localizing the quotient by one minimal prime at a different minimal
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

/-- Helper for Lemma 15.126.8: package the owner localization equivalence between the localized
product of minimal-prime quotients and the product of the localized factors. -/
private noncomputable def localized_minimalPrimeProduct_equiv
    (q : minimalPrimes R) :
    LocalizedModule.AtPrime q.1 (∀ p : minimalPrimes R, R ⧸ p.1) ≃ₗ[R]
      ∀ p : minimalPrimes R, LocalizedModule.AtPrime q.1 (R ⧸ p.1) :=
  let _ : Fintype (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).fintype
  -- Use the canonical componentwise localization map, then invoke the owner comparison theorem.
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

/-- Helper for Lemma 15.126.8: the reduced diagonal is `R`-linear, so it can be localized by the
owner API `LocalizedModule.map`. -/
noncomputable def reducedDiagonalLinearMap :
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

/-- Helper for Lemma 15.126.8: under the product-localization equivalence, the localized reduced
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

/-- Helper for Lemma 15.126.8: after localizing the product of minimal-prime quotients at a
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
    -- Two localized tuples agree at `q`; away from `q` the factors are subsingletons.
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

/-- Helper for Lemma 15.126.8: on quotient generators, the `q`-coordinate of the reduced diagonal
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

/-- Helper for Lemma 15.126.8: the surviving `q`-coordinate of the reduced diagonal is
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

/-- Helper for Lemma 15.126.8: after localizing the product of minimal-prime quotients at `q`,
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

/-- Helper for Lemma 15.126.8: localizing the `q`-coordinate of the reduced diagonal gives the
canonical localized map from the reduced quotient to the localized `q`-factor. -/
private noncomputable def reducedLocalizedCoordinateMap
    (q : minimalPrimes R) :
    LocalizedModule.AtPrime q.1 (R ⧸ nilradical R) →ₗ[R]
      LocalizedModule.AtPrime q.1 (R ⧸ q.1) :=
  LocalizedModule.map q.1.primeCompl
    ((LinearMap.proj q : (∀ p : minimalPrimes R, R ⧸ p.1) →ₗ[R] R ⧸ q.1) ∘ₗ
      (reducedDiagonalLinearMap (R := R)))

/-- Helper for Lemma 15.126.8: after transporting the localized reduced diagonal through the
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

/-- Helper for Lemma 15.126.8: after localizing at a minimal prime, the reduced diagonal map is
surjective. -/
theorem localized_reduced_diagonal_surjective_at_minimalPrime
    (q : minimalPrimes R) :
    Function.Surjective
      (LocalizedModule.map q.1.primeCompl (reducedDiagonalLinearMap (R := R))) := by
  let k := localized_survivingCoordinateMap (R := R) q
  have hk_bij : Function.Bijective k := by
    -- The product-localization equivalence is bijective, and projection is bijective because all
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

end

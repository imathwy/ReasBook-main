import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_162_11 (from Chap10) -/
universe u

/-
Domain triage:
- primary domain: analytically unramified prime quotients of Noetherian local rings, associated
  primes of the completed quotient, and discrete valuation ring localizations;
- sampled owner-style declarations: `PrimeSpectrum.IsAnalyticallyUnramified`,
  `IsAssociatedPrime`, and the canonical owner `IsDiscreteValuationRing`;
- core/canonical owners already present in the chapter/mathlib:
  `PrimeSpectrum.IsAnalyticallyUnramified` for the analytic hypothesis and
  `IsAssociatedPrime` for the associated-prime hypothesis and
  `IsDiscreteValuationRing` for the DVR structure;
- source-facing data here are the two prime points `p` and `q`; the corresponding localizations
  are better stated using the canonical owner objects `Localization.AtPrime p.asIdeal` and
  `Localization.AtPrime q.asIdeal` than by arbitrary carrier types.

The reducedness of `R^∧ / pR^∧` is derived API of the owner predicate
`PrimeSpectrum.IsAnalyticallyUnramified p`, so the public statement should use that owner rather
than restating its completion-quotient model as a parallel primitive hypothesis. Likewise, since
`q` is already fixed, the atomic owner predicate `IsAssociatedPrime q.asIdeal (...)` is more
canonical than phrasing the same input via membership in the derived set `associatedPrimes`. The
DVR clause is source-facing theorem-level packaging over the canonical owner
`IsDiscreteValuationRing`, so the theorem uses the direct existential statement instead of a
parallel wrapper predicate.
-/

section

open IsLocalRing
open scoped TensorProduct

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

local notation "RCompletion" => AdicCompletion (maximalIdeal R) R

/-- Helper for Lemma 10.162.11: the maximal ideal of the prime quotient `R ⧸ p` is the image of
the maximal ideal of `R`. -/
lemma primeQuotient_map_maximalIdeal_eq (p : PrimeSpectrum R) :
    Ideal.map (Ideal.Quotient.mk p.asIdeal) (maximalIdeal R) =
      maximalIdeal (R ⧸ p.asIdeal) := by
  -- The quotient map is surjective, so locality identifies the target maximal ideal with the image
  -- of the source maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p.asIdeal)
    Ideal.Quotient.mk_surjective

/-- Helper for Lemma 10.162.11: powers of the maximal ideal descend to the corresponding powers
in the prime quotient. -/
lemma prime_quotient_map_maximalIdeal_pow_eq (p : PrimeSpectrum R) (n : ℕ) :
    Ideal.map (Ideal.Quotient.mk p.asIdeal) ((maximalIdeal R) ^ n) =
      (maximalIdeal (R ⧸ p.asIdeal)) ^ n := by
  -- First move powers through the quotient map, then rewrite the image of the maximal ideal.
  rw [Ideal.map_pow, primeQuotient_map_maximalIdeal_eq]

/-- Helper for Lemma 10.162.11: quotienting `R ⧸ p` by the image of the maximal ideal recovers the
residue field of `R`. -/
noncomputable def prime_quotient_residueField_ringEquiv (p : PrimeSpectrum R) :
    ((R ⧸ p.asIdeal) ⧸ Ideal.map (Ideal.Quotient.mk p.asIdeal) (maximalIdeal R)) ≃+*
      R ⧸ maximalIdeal R :=
  DoubleQuot.quotQuotEquivQuotOfLE
    (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)

/-- Helper for Lemma 10.162.11: the quotient map `R → R ⧸ p` is a local ring homomorphism. -/
lemma prime_quotient_isLocalHom (p : PrimeSpectrum R) :
    IsLocalHom (algebraMap R (R ⧸ p.asIdeal)) := by
  -- Surjective maps out of a local ring are local homomorphisms.
  simpa using IsLocalHom.of_surjective (Ideal.Quotient.mk p.asIdeal)
    Ideal.Quotient.mk_surjective

attribute [local instance] prime_quotient_isLocalHom

/-- Helper for Lemma 10.162.11: the prime quotient of a local ring is again local. -/
local instance prime_quotient_isLocalRing (p : PrimeSpectrum R) :
    IsLocalRing (R ⧸ p.asIdeal) :=
  primeSpectrum_quotient_isLocalRing p

/-- Helper for Lemma 10.162.11: if the completed quotient `R^∧ / pR^∧` is reduced, then every
associated prime of that quotient is a minimal prime over `pR^∧`. -/
lemma associatedPrime_completionQuotient_mem_minimalPrimes
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion)
    (hred : IsReduced (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal))
    (hq :
      IsAssociatedPrime q.asIdeal
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal)) :
    q.asIdeal ∈ (Ideal.map (algebraMap R RCompletion) p.asIdeal).minimalPrimes := by
  let I : Ideal RCompletion := Ideal.map (algebraMap R RCompletion) p.asIdeal
  letI : IsReduced (RCompletion ⧸ I) := hred
  letI : Module (RCompletion ⧸ I) (RCompletion ⧸ I) := Semiring.toModule
  letI : IsScalarTower RCompletion (RCompletion ⧸ I) (RCompletion ⧸ I) := IsScalarTower.right
  letI : Module.Finite RCompletion (RCompletion ⧸ I) := inferInstance
  -- Move the weakly associated prime to the quotient ring itself via the finite quotient map.
  have hq_weak : q.asIdeal ∈ weaklyAssociatedPrimes RCompletion (RCompletion ⧸ I) := by
    simpa [mem_weaklyAssociatedPrimes_iff] using hq.isWeaklyAssociatedToModule
  rw [← weaklyAssociatedPrimes.restrictScalars_eq_image_comap_of_finite
      (R := RCompletion) (S := RCompletion ⧸ I) (M := RCompletion ⧸ I)] at hq_weak
  rcases hq_weak with ⟨qbar, hqbar_weak_mem, hqbar_comap⟩
  -- Over the reduced quotient ring, weakly associated primes are exactly the minimal primes.
  have hqbar_weak :
      Ideal.IsWeaklyAssociatedToModule (RCompletion ⧸ I) (RCompletion ⧸ I) qbar :=
    ((mem_weaklyAssociatedPrimes_iff (R := RCompletion ⧸ I) (M := RCompletion ⧸ I) qbar).mp
      hqbar_weak_mem)
  have hqbar_min : qbar ∈ minimalPrimes (RCompletion ⧸ I) := by
    rw [← weaklyAssociatedPrimes_ring_eq_minimalPrimes, mem_weaklyAssociatedPrimes_iff]
    exact hqbar_weak
  -- Transport that minimal prime back across the quotient map to recover minimality over `I`.
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨qbar, hqbar_min, hqbar_comap⟩

/-- Helper for Lemma 10.162.11: a minimal prime of `pR^∧` contracts back to `p`. -/
lemma minimalPrime_completionQuotient_under_eq
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion)
    (hff : RingHom.FaithfullyFlat (algebraMap R RCompletion))
    (hq :
      q.asIdeal ∈ (Ideal.map (algebraMap R RCompletion) p.asIdeal).minimalPrimes) :
    q.asIdeal.under R = p.asIdeal := by
  let I : Ideal RCompletion := Ideal.map (algebraMap R RCompletion) p.asIdeal
  haveI : Module.Flat R RCompletion :=
    (RingHom.flat_algebraMap_iff).mp hff.flat
  -- First note that `q` lies over some prime containing `p`.
  have hp_le_under : p.asIdeal ≤ q.asIdeal.under R := by
    rw [← Ideal.map_le_iff_le_comap]
    simpa [I] using hq.1.2
  -- Going down produces a prime below `q` lying exactly over `p`.
  obtain ⟨Q, hQle, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := R) (S := RCompletion)
      (p := p.asIdeal) (q := q.asIdeal.under R) q.asIdeal hp_le_under
  have hI_le_Q : I ≤ Q := by
    change Ideal.map (algebraMap R RCompletion) p.asIdeal ≤ Q
    exact Ideal.map_le_iff_le_comap.mpr <| by
      rw [hQover.over]
  -- Minimality of `q` over `pR^∧` forces that lower prime to coincide with `q`.
  have hQ_eq_q : Q = q.asIdeal := by
    apply le_antisymm hQle
    exact hq.2 ⟨hQprime, hI_le_Q⟩ hQle
  simpa [hQ_eq_q] using hQover.over.symm

/-- Helper for Lemma 10.162.11: if `q` is minimal over `I` and the localized quotient is reduced,
then the localized image of `I` is already the maximal ideal. -/
lemma localized_ideal_eq_maximalIdeal_of_mem_minimalPrimes_of_reduced_quotient
    {A : Type u} [CommRing A] (I : Ideal A) (q : Ideal A) [q.IsPrime]
    (hq : q ∈ I.minimalPrimes)
    (hred :
      IsReduced
        ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap A (Localization.AtPrime q)) I)) :
    Ideal.map (algebraMap A (Localization.AtPrime q)) I =
      maximalIdeal (Localization.AtPrime q) := by
  let J : Ideal (Localization.AtPrime q) := Ideal.map (algebraMap A (Localization.AtPrime q)) I
  have hJ_radical : J.radical = maximalIdeal (Localization.AtPrime q) := by
    -- Minimality of `q` over `I` says that after localizing at `q`, the radical of `I` becomes the
    -- unique maximal ideal.
    simpa [J, Localization.AtPrime.map_eq_maximalIdeal] using
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q I hq
  have hJ_isRadical : J.IsRadical := by
    -- Reducedness of the localized quotient is exactly the owner criterion for `J` to be radical.
    exact (Ideal.isRadical_iff_quotient_reduced J).2 hred
  -- A radical ideal with radical equal to the maximal ideal must itself be that maximal ideal.
  calc
    J = J.radical := by
      exact hJ_isRadical.radical.symm
    _ = maximalIdeal (Localization.AtPrime q) := hJ_radical

/-- Helper for Lemma 10.162.11: reducedness of `A ⧸ I` localizes to reducedness of the quotient by
the localized ideal in `A_q`. -/
lemma localized_completionQuotient_isReduced_of_isReduced
    {A : Type u} [CommRing A] (I q : Ideal A) [q.IsPrime]
    (hred : IsReduced (A ⧸ I)) :
    IsReduced
      ((Localization.AtPrime q) ⧸ Ideal.map (algebraMap A (Localization.AtPrime q)) I) := by
  let J : Ideal (Localization.AtPrime q) := Ideal.map (algebraMap A (Localization.AtPrime q)) I
  have hIrad : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).2 hred
  have hJrad : J.IsRadical := by
    -- Localizing a radical ideal stays radical, so the localized quotient remains reduced.
    rw [show J = J.radical by
      calc
        J = Ideal.map (algebraMap A (Localization.AtPrime q)) I := rfl
        _ = Ideal.map (algebraMap A (Localization.AtPrime q)) I.radical := by
          rw [hIrad.radical]
        _ = J.radical := by
          exact IsLocalization.map_radical q.primeCompl (Localization.AtPrime q) I]
    exact Ideal.radical_isRadical J
  exact (Ideal.isRadical_iff_quotient_reduced J).1 hJrad

/-- Helper for Lemma 10.162.11: quotienting `R^∧` by the extended prime `pR^∧` is the same as
tensoring `R^∧` with the prime quotient `R ⧸ p`. -/
noncomputable def prime_quotient_completionQuotient_tensorQuotient_algEquiv
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) ≃ₐ[RCompletion]
      RCompletion ⊗[R] (R ⧸ p.asIdeal) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R) (B := RCompletion) p.asIdeal

/-- Helper for Lemma 10.162.11: the `maximalIdeal R`-adic completion of the prime quotient, viewed
as an `R`-module, is the same as tensoring the prime quotient with `R^∧`. -/
noncomputable def prime_quotient_tensor_moduleCompletion_linearEquiv
    (p : PrimeSpectrum R) :
    RCompletion ⊗[R] (R ⧸ p.asIdeal) ≃ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) :=
  AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := maximalIdeal R)
    (M := R ⧸ p.asIdeal)

/-- Helper for Lemma 10.162.11: the quotient `R^∧ / pR^∧` matches the `maximalIdeal R`-adic
completion of `R ⧸ p` as an `R^∧`-module. -/
noncomputable def prime_quotient_completionQuotient_moduleCompletion_linearEquiv
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) ≃ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) :=
  (prime_quotient_completionQuotient_tensorQuotient_algEquiv p).toLinearEquiv.trans
    (prime_quotient_tensor_moduleCompletion_linearEquiv p)

/-- Helper for Lemma 10.162.11: on a quotient representative from `R^∧`, the comparison linear
equivalence is the expected pure-tensor image in the module completion. -/
lemma prime_quotient_completionQuotient_moduleCompletion_linearEquiv_mk
    (p : PrimeSpectrum R) (b : RCompletion) :
    prime_quotient_completionQuotient_moduleCompletion_linearEquiv p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b) =
      b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1 := by
  -- Compute the tensor/quotient bridge on representatives and rewrite the resulting scalar action.
  rw [prime_quotient_completionQuotient_moduleCompletion_linearEquiv, LinearEquiv.trans_apply]
  change
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) (R ⧸ p.asIdeal)
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (RCompletion) p.asIdeal)
          (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b)) =
      b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul]

/-- Helper for Lemma 10.162.11: the canonical tensor-product comparison lands in the
`maximalIdeal R`-adic completion of the prime quotient as an `RCompletion`-linear map. -/
noncomputable def prime_quotient_tensor_moduleCompletion_algHom
    (p : PrimeSpectrum R) :
    RCompletion ⊗[R] (R ⧸ p.asIdeal) →ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) :=
  prime_quotient_tensor_moduleCompletion_linearEquiv p

/-- Helper for Lemma 10.162.11: the tensor-product ring map is the same as the standard linear
comparison from tensor product to the completed quotient. -/
lemma prime_quotient_tensor_moduleCompletion_algHom_eq_linearEquiv
    (p : PrimeSpectrum R) :
    prime_quotient_tensor_moduleCompletion_algHom p =
      prime_quotient_tensor_moduleCompletion_linearEquiv p := by
  -- This helper is now just the linear comparison itself.
  rfl

/-- Helper for Lemma 10.162.11: the quotient `R^∧ / pR^∧` maps canonically to the
`maximalIdeal R`-adic completion of `R ⧸ p` as an `RCompletion`-linear map. -/
noncomputable def prime_quotient_completionQuotient_moduleCompletion_algHom
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) →ₗ[RCompletion]
      AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) :=
  prime_quotient_completionQuotient_moduleCompletion_linearEquiv p

/-- Helper for Lemma 10.162.11: the canonical map from `R^∧ / pR^∧` to the completed quotient is
injective because it agrees with the established linear equivalence. -/
lemma prime_quotient_completionQuotient_moduleCompletion_algHom_injective
    (p : PrimeSpectrum R) :
    Function.Injective (prime_quotient_completionQuotient_moduleCompletion_algHom p) := by
  -- The quotient comparison is itself a linear equivalence.
  exact (prime_quotient_completionQuotient_moduleCompletion_linearEquiv p).injective

/-- Helper for Lemma 10.162.11: every denominator coming from the closed point of the base local
ring is already a unit in the prime quotient. -/
lemma prime_quotient_closedPoint_isLocalization (p : PrimeSpectrum R) :
    IsLocalization
      (Algebra.algebraMapSubmonoid (R ⧸ p.asIdeal) (maximalIdeal R).primeCompl)
      (R ⧸ p.asIdeal) := by
  -- In a local ring, elements outside the maximal ideal are units, and quotient maps preserve
  -- those units.
  refine IsLocalization.at_units _ ?_
  intro y hy
  rcases
      (show
        ∃ x ∈ (maximalIdeal R).primeCompl,
          algebraMap R (R ⧸ p.asIdeal) x = y from by
        simpa [Algebra.algebraMapSubmonoid, Submonoid.mem_map] using hy) with
    ⟨x, hx, rfl⟩
  exact IsUnit.map (algebraMap R (R ⧸ p.asIdeal))
    ((IsLocalRing.notMem_maximalIdeal).mp hx)

/-- Helper for Lemma 10.162.11: localizing the prime quotient at the closed point of the base
local ring gives back the quotient ring itself. -/
noncomputable def prime_quotient_closedPoint_localization_algEquiv
    (p : PrimeSpectrum R) :
    Localization
        (Algebra.algebraMapSubmonoid (R ⧸ p.asIdeal) (maximalIdeal R).primeCompl) ≃ₐ[R ⧸ p.asIdeal]
      (R ⧸ p.asIdeal) :=
  letI := prime_quotient_closedPoint_isLocalization p
  IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid (R ⧸ p.asIdeal) (maximalIdeal R).primeCompl)
    (Localization
      (Algebra.algebraMapSubmonoid (R ⧸ p.asIdeal) (maximalIdeal R).primeCompl))
    (R ⧸ p.asIdeal)

/-- Helper for Lemma 10.162.11: the image of the maximal ideal in the prime quotient is finitely
generated, so the corresponding adic completion is a ring. -/
instance prime_quotient_map_maximalIdeal_fg
    (p : PrimeSpectrum R) :
    (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)).FG := by
  -- The source maximal ideal is finitely generated in a Noetherian local ring, and finite
  -- generation is preserved by ideal maps.
  simpa using ((maximalIdeal R).fg_of_isNoetherianRing.map (algebraMap R (R ⧸ p.asIdeal)))

/-- Helper for Lemma 10.162.11: the closed-point quotient of `R ⧸ p` is finite over the residue
field of `R`. -/
lemma prime_quotient_closedPoint_quotient_finite
    (p : PrimeSpectrum R) :
    Module.Finite (R ⧸ maximalIdeal R)
      ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) := by
  let eResidue := prime_quotient_residueField_ringEquiv p
  letI : Module.Finite (R ⧸ maximalIdeal R) (R ⧸ maximalIdeal R) := by
    infer_instance
  have halg :
      algebraMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) =
        eResidue.symm.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    -- Both maps agree on the source ring `R`, where they are the canonical double-quotient map.
    ext r
    rw [show
        (algebraMap (R ⧸ maximalIdeal R)
            ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))).comp
          (Ideal.Quotient.mk (maximalIdeal R)) =
            DoubleQuot.quotQuotMk p.asIdeal (maximalIdeal R) by
          rfl]
    exact congrFun
      (congrArg DFunLike.coe <| by
          simpa [prime_quotient_residueField_ringEquiv] using
            (DoubleQuot.quotQuotEquivQuotOfLE_symm_comp_mk
              (R := R) (I := p.asIdeal) (J := maximalIdeal R)
              (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)).symm)
      r
  -- Transport the obvious finite self-module structure on the residue field across the canonical
  -- residue-field equivalence for the prime quotient.
  have hsurj :
      Function.Surjective
        (Algebra.linearMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))) := by
    intro y
    refine ⟨eResidue y, ?_⟩
    change
      algebraMap (R ⧸ maximalIdeal R)
          ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (eResidue y) = y
    rw [halg]
    exact eResidue.symm_apply_apply y
  exact Module.Finite.of_surjective
    (Algebra.linearMap (R ⧸ maximalIdeal R)
      ((R ⧸ p.asIdeal) ⧸ Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)))
    hsurj

/-- Helper for Lemma 10.162.11: analytically unramified prime quotients give reduced completed
quotients `R^∧ / pR^∧`. -/
lemma completionQuotient_isReduced_of_prime_isAnalyticallyUnramified
    (p : PrimeSpectrum R) (h_analytic : PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsReduced (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
  letI : IsLocalRing (R ⧸ p.asIdeal) := primeSpectrum_quotient_isLocalRing p
  letI : IsLocalHom (algebraMap R (R ⧸ p.asIdeal)) := prime_quotient_isLocalHom p
  -- Route correction: the source-faithful next step is to compare `R^∧ / pR^∧` with the genuine
  -- ring completion of `R ⧸ p`, not only with the existing module-completion bridge.
  -- TODO: import or reconstruct a public ring-level comparison
  -- `(RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) →+*`
  -- `AdicCompletion (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) (R ⧸ p.asIdeal)`,
  -- prove it injective, and descend reducedness from the analytically unramified completion.
  sorry

/-- Helper for Lemma 10.162.11: a DVR localization at `p` admits a source element of `R` whose
image generates the maximal ideal of `R_p` and is nonzero there. -/
lemma exists_source_generator_of_maximalIdeal_localizationAtPrime
    (p : PrimeSpectrum R)
    (hp : ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)) :
    ∃ x : R,
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R)) =
        maximalIdeal (Localization.AtPrime p.asIdeal) ∧
      algebraMap R (Localization.AtPrime p.asIdeal) x ≠ 0 := by
  rcases hp with ⟨_, hDVR⟩
  let Rp := Localization.AtPrime p.asIdeal
  letI : IsDiscreteValuationRing Rp := hDVR
  -- Choose a uniformizer in `R_p`, then clear its denominator to get a source element `x : R`.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  obtain ⟨x, s, hπ⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl π
  have hsunit : IsUnit (IsLocalization.mk' Rp (1 : R) s) := by
    simpa using
      (IsLocalization.AtPrime.isUnit_mk'_iff Rp p.asIdeal (1 : R) s).2
        p.asIdeal.primeCompl.one_mem
  have hassoc : Associated π (algebraMap R Rp x) := by
    rw [← hπ, IsLocalization.mk'_eq_mul_mk'_one]
    simpa [IsLocalization.mk'_one] using
      (associated_mul_unit_right (algebraMap R Rp x)
        (IsLocalization.mk' Rp (1 : R) s) hsunit).symm
  have hmax_span :
      maximalIdeal Rp = Ideal.span ({algebraMap R Rp x} : Set Rp) := by
    calc
      maximalIdeal Rp = Ideal.span ({π} : Set Rp) := hπirr.maximalIdeal_eq
      _ = Ideal.span ({algebraMap R Rp x} : Set Rp) :=
        Ideal.span_singleton_eq_span_singleton.mpr hassoc
  refine ⟨x, ?_, ?_⟩
  · -- Rewrite the chosen source element as the principal generator of the maximal ideal in `R_p`.
    calc
      Ideal.map (algebraMap R Rp) (Ideal.span ({x} : Set R)) =
          Ideal.span ({algebraMap R Rp x} : Set Rp) := by
            rw [Ideal.map_span]
            simp
      _ = maximalIdeal Rp := hmax_span.symm
  · -- A generator of the nonzero maximal ideal in a DVR localization cannot vanish.
    intro hxzero
    exact IsDiscreteValuationRing.not_a_field Rp <| by
      rw [hmax_span, hxzero, Ideal.span_singleton_eq_bot]

/-- Helper for Lemma 10.162.11: once the source element `x : R` generates the maximal ideal of
`R_p`, its image also generates the maximal ideal of `(R^∧)_q`. -/
lemma source_generator_maps_to_target_maximalIdeal
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion) {x : R}
    (hx :
      Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R)) =
        maximalIdeal (Localization.AtPrime p.asIdeal))
    (hunder : q.asIdeal.under R = p.asIdeal)
    (hImax :
      Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
        (Ideal.map (algebraMap R RCompletion) p.asIdeal) =
          maximalIdeal (Localization.AtPrime q.asIdeal)) :
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) =
      maximalIdeal (Localization.AtPrime q.asIdeal) := by
  let f : Localization.AtPrime p.asIdeal →+* Localization.AtPrime q.asIdeal :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R RCompletion) hunder.symm
  have hfcomp :
      f.comp (algebraMap R (Localization.AtPrime p.asIdeal)) =
        algebraMap R (Localization.AtPrime q.asIdeal) := by
    ext r
    change f (algebraMap R (Localization.AtPrime p.asIdeal) r) =
      algebraMap R (Localization.AtPrime q.asIdeal) r
    rw [Localization.localRingHom_to_map
      (I := p.asIdeal) (J := q.asIdeal) (algebraMap R RCompletion) hunder.symm]
    rfl
  have hp_to_target :
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal =
        Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
          (Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    symm
    simpa using
      (Ideal.map_map (f := algebraMap R RCompletion)
        (g := algebraMap RCompletion (Localization.AtPrime q.asIdeal))
        (I := p.asIdeal))
  have hspan_to_target :
      Ideal.map f
        (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R))) =
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) := by
    simpa [hfcomp] using
      (Ideal.map_map (f := algebraMap R (Localization.AtPrime p.asIdeal))
        (g := f) (I := Ideal.span ({x} : Set R)))
  have hp_to_target' :
      Ideal.map f (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) =
        Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
    simpa [hfcomp] using
      (Ideal.map_map (f := algebraMap R (Localization.AtPrime p.asIdeal))
        (g := f) (I := p.asIdeal))
  -- Push the principal ideal through the local map and rewrite it through the localized image of
  -- `pR^∧`.
  calc
    Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) =
        Ideal.map f
          (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) (Ideal.span ({x} : Set R))) := by
            simpa using hspan_to_target.symm
    _ = Ideal.map f (maximalIdeal (Localization.AtPrime p.asIdeal)) := by rw [hx]
    _ = Ideal.map f (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) p.asIdeal) := by
          rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    _ = Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) p.asIdeal := by
          simpa using hp_to_target'
    _ = Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal))
          (Ideal.map (algebraMap R RCompletion) p.asIdeal) := hp_to_target
    _ = maximalIdeal (Localization.AtPrime q.asIdeal) := hImax

/-- Helper for Lemma 10.162.11: the source generator stays regular after passing from `R_p` to
`(R^∧)_q` along the flat local map. -/
lemma source_generator_isSMulRegular_in_target
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion)
    (hp : ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    {x : R}
    (hx : algebraMap R (Localization.AtPrime p.asIdeal) x ≠ 0)
    (hunder : q.asIdeal.under R = p.asIdeal) :
    IsSMulRegular (Localization.AtPrime q.asIdeal)
      (algebraMap R (Localization.AtPrime q.asIdeal) x) := by
  rcases hp with ⟨_, hDVR⟩
  let Rp := Localization.AtPrime p.asIdeal
  let Rq := Localization.AtPrime q.asIdeal
  letI : IsDiscreteValuationRing Rp := hDVR
  let f : Rp →+* Rq :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R RCompletion) hunder.symm
  letI : Algebra Rp Rq := f.toAlgebra
  have hflat : f.Flat := by
    exact RingHom.Flat.localRingHom
      (f := algebraMap R RCompletion)
      (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R).flat
      q.asIdeal p.asIdeal hunder.symm
  letI : Module.Flat Rp Rq := hflat
  have hxreg_target :
      IsSMulRegular Rq ((algebraMap Rp Rq) (algebraMap R Rp x)) := by
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := Rq)
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  have hmap_x :
      (algebraMap Rp Rq) (algebraMap R Rp x) = algebraMap R Rq x := by
    change f (algebraMap R Rp x) = algebraMap R Rq x
    rw [Localization.localRingHom_to_map
      (I := p.asIdeal) (J := q.asIdeal) (algebraMap R RCompletion) hunder.symm]
    rfl
  -- Flatness of `R_p → (R^∧)_q` makes the same source element regular on the target localization.
  exact hmap_x ▸ hxreg_target

/-- Helper for Lemma 10.162.11: in a Noetherian local ring, if the maximal ideal is generated by a
single regular element, then the ring is a discrete valuation ring. -/
lemma discreteValuationRing_of_span_maximalIdeal_of_isSMulRegular
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
    (hmax : maximalIdeal A = Ideal.span ({x} : Set A)) (hreg : IsSMulRegular A x) :
    ∃ (_ : IsDomain A), IsDiscreteValuationRing A := by
  have hxmem : x ∈ maximalIdeal A := by
    -- The chosen generator lies in the maximal ideal because it spans that ideal.
    rw [hmax]
    simpa using (Submodule.mem_span_singleton_self x : x ∈ Ideal.span ({x} : Set A))
  have hquot_dim : ringKrullDim (A ⧸ Ideal.span ({x} : Set A)) = 0 := by
    -- Quotienting by the generator is quotienting by the maximal ideal, hence gives the residue
    -- field and so has Krull dimension zero.
    let e : A ⧸ Ideal.span ({x} : Set A) ≃+* A ⧸ maximalIdeal A :=
      Ideal.quotEquivOfEq hmax.symm
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
    calc
      ringKrullDim (A ⧸ Ideal.span ({x} : Set A)) = ringKrullDim (A ⧸ maximalIdeal A) :=
        ringKrullDim_eq_of_ringEquiv e
      _ = 0 := ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
  have hdim : ringKrullDim A = 1 := by
    -- A regular element in the maximal ideal drops the quotient dimension by exactly one.
    have hsucc :
        ringKrullDim (A ⧸ Ideal.span ({x} : Set A)) + 1 = ringKrullDim A :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hxmem
    simpa [hquot_dim] using hsucc.symm
  have hspan_le_one : ((maximalIdeal A).spanFinrank : WithBot ℕ∞) ≤ 1 := by
    -- A principal maximal ideal needs only one generator.
    rw [hmax]
    simpa only [Nat.cast_le_one, ← Set.ncard_singleton x] using
      (Submodule.spanFinrank_span_le_ncard_of_finite (R := A) (M := A)
        (Set.finite_singleton x))
  have hregular : IsRegularLocalRing A := by
    -- The principal-generator bound matches the already computed dimension one.
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := A)
    simpa [hdim] using hspan_le_one
  -- Convert the regular-local dimension-one package to the canonical DVR owner theorem.
  exact (discreteValuationRing_iff_regularLocalRing_dim_one (A := A)).2 ⟨hregular, hdim⟩

/-- Helper for Lemma 10.162.11: the completion of a Noetherian local ring is Noetherian. -/
lemma completion_isNoetherianRing :
    IsNoetherianRing RCompletion := by
  -- TODO: recover this from the chapter-level adic-completion noetherianity route without relying
  -- on the currently broken import chain through `Lemma_10_97_6`.
  sorry

/-- Lemma 10.162.11: if `R` is a Noetherian local ring, `p` is an analytically unramified prime
of `R` such that `R_p` is a discrete valuation ring, then for every associated prime `q` of the
completed quotient `R^∧ / pR^∧` the localization `(R^∧)_q` is a discrete valuation ring. -/
-- Proof sketch: analytically unramified means precisely that the quotient `R / p` has reduced
-- completion, equivalently that `R^∧ / pR^∧` is reduced. Therefore any associated prime `q` of
-- this quotient is
-- minimal over `pR^∧`, so the maximal ideal of `(R^∧)_q` is generated by the image of `p`. Choose
-- an element of `R` generating `pR_p`; its image then generates the maximal ideal after passing to
-- `(R^∧)_q`. Faithful flatness of `R → R^∧` makes that generator a nonzerodivisor, so the local
-- ring `(R^∧)_q` is a one-dimensional local domain with principal maximal ideal, hence a DVR.
theorem completion_localizationAt_associatedPrime_isDiscreteValuationRing
    (p : PrimeSpectrum R) (q : PrimeSpectrum RCompletion)
    (hp : ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    (h_analytic : PrimeSpectrum.IsAnalyticallyUnramified p)
    (hq :
      IsAssociatedPrime q.asIdeal
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal)) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let I : Ideal RCompletion := Ideal.map (algebraMap R RCompletion) p.asIdeal
  have hff :
      RingHom.FaithfullyFlat (algebraMap R RCompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R
  have hred : IsReduced (RCompletion ⧸ I) :=
    completionQuotient_isReduced_of_prime_isAnalyticallyUnramified p h_analytic
  have hqMin :
      q.asIdeal ∈ I.minimalPrimes := by
    -- Once the reducedness bridge is in place, the quotient-theoretic minimal-prime step is done.
    exact associatedPrime_completionQuotient_mem_minimalPrimes p q hred hq
  have hunder : q.asIdeal.under R = p.asIdeal :=
    minimalPrime_completionQuotient_under_eq p q hff hqMin
  have hredLoc :
      IsReduced
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal)) I) := by
    -- The reduced completion quotient from the source proof stays reduced after localizing at `q`.
    exact localized_completionQuotient_isReduced_of_isReduced I q.asIdeal hred
  have hImax :
      Ideal.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal)) I =
        maximalIdeal (Localization.AtPrime q.asIdeal) := by
    -- Minimality of `q` over `I` identifies the localized image of `I` with the unique maximal
    -- ideal once the localized quotient is reduced.
    exact localized_ideal_eq_maximalIdeal_of_mem_minimalPrimes_of_reduced_quotient I q.asIdeal
      hqMin hredLoc
  obtain ⟨x, hx_source, hx_nonzero⟩ :=
    exists_source_generator_of_maximalIdeal_localizationAtPrime p hp
  have hx_target :
      Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) =
        maximalIdeal (Localization.AtPrime q.asIdeal) :=
    source_generator_maps_to_target_maximalIdeal p q hx_source hunder hImax
  have hx_regular :
      IsSMulRegular (Localization.AtPrime q.asIdeal)
        (algebraMap R (Localization.AtPrime q.asIdeal) x) :=
    source_generator_isSMulRegular_in_target p q hp hx_nonzero hunder
  letI : IsNoetherianRing RCompletion := completion_isNoetherianRing
  letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) inferInstance
  have hx_maximal :
      maximalIdeal (Localization.AtPrime q.asIdeal) =
        Ideal.span ({algebraMap R (Localization.AtPrime q.asIdeal) x} :
          Set (Localization.AtPrime q.asIdeal)) := by
    -- The same source element `x` now generates the target maximal ideal.
    calc
      maximalIdeal (Localization.AtPrime q.asIdeal) =
          Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (Ideal.span ({x} : Set R)) :=
            hx_target.symm
      _ = Ideal.span ({algebraMap R (Localization.AtPrime q.asIdeal) x} :
            Set (Localization.AtPrime q.asIdeal)) := by
            rw [Ideal.map_span]
            simp
  -- The source-faithful endgame is now exactly the principal-maximal-ideal plus regularity
  -- criterion for DVRs.
  exact discreteValuationRing_of_span_maximalIdeal_of_isSMulRegular hx_maximal hx_regular

end

/-! ### Lemma_10_162_12 (from Chap10) -/
universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

open IsLocalRing
open scoped TensorProduct

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
variable {x : R}

local notation "A" => R ⧸ Ideal.span (Set.singleton x)
local notation "RCompletion" => AdicCompletion (maximalIdeal R) R
local notation "J" =>
  Ideal.map (algebraMap R RCompletion) (Ideal.span (Set.singleton x))

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local domains, associated primes of
  principal quotients, and the no-embedded-primes condition on that quotient;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `embeddedAssociatedPrimes`,
  and `IsAssociatedPrime`;
- best owner abstraction: the theorem itself remains `source-facing`, but the quotient hypotheses
  should be expressed via the existing owner predicates `embeddedAssociatedPrimes R A = ∅` and
  `IsAssociatedPrime p.asIdeal A` rather than a parallel minimality condition and raw membership
  tests;
- primitive data vs. derived API: the primitive source data are the nonzero element `x` in the
  maximal ideal and the owner-level hypotheses on the quotient `A = R / xR`; the old “every
  associated prime is minimal” clause is derived bridge API for `embeddedAssociatedPrimes R A = ∅`.
-/

-- Proof sketch: let `R^∧` be the maximal-ideal completion of `R`. To prove it is reduced, take
-- `y : R^∧` with `y ^ 2 = 0`. Since `R / xR` has no embedded primes, the associated primes of
-- `R^∧ / xR^∧` are exactly the associated primes lying over the associated primes of `R / xR`.
-- For each such prime `q`, the corresponding localization `(R^∧)_q` is regular by Lemma
-- `10.162.11`, hence a domain by Lemma `10.106.2`, so `y` vanishes in every such localization.
-- Lemma `10.63.19` then shows `y = x y'`. Because `x` is a nonzerodivisor on the completion,
-- `y'` is again nilpotent; iterating and applying Krull intersection gives `y = 0`.
omit [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: the support of `R / xR` is exactly the zero locus of `(x)`. -/
lemma support_quotient_span_singleton_le_iff
    (p : PrimeSpectrum R) :
    p ∈ Module.support R A ↔ Ideal.span ({x} : Set R) ≤ p.asIdeal := by
  -- Rewrite the support of the quotient through its annihilator and identify that annihilator.
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus]
  exact Iff.rfl

omit [IsLocalRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: if an associated prime of `R / xR` is minimal among the
associated primes of the quotient, then it is a minimal prime over `(x)`. -/
lemma associatedPrime_quotient_mem_minimalPrimes_span_singleton
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (p : PrimeSpectrum R) (hp : IsAssociatedPrime p.asIdeal A) :
    p.asIdeal ∈ (Ideal.span ({x} : Set R)).minimalPrimes :=
by
  have hp_assoc : p.asIdeal ∈ associatedPrimes R A := by
    simpa using hp
  -- Route correction: first convert the no-embedded-primes hypothesis into minimality inside
  -- `associatedPrimes R A`, then descend to minimality over the principal ideal `(x)`.
  have hp_min_assoc : Minimal (· ∈ associatedPrimes R A) p.asIdeal :=
    (embeddedAssociatedPrimes_eq_empty_iff (R := R) (M := A)).1 hno_embedded p.asIdeal hp_assoc
  have hp_support : p ∈ Module.support R A := by
    simpa using IsAssociatedPrime.mem_support hp
  have hx_le : Ideal.span ({x} : Set R) ≤ p.asIdeal :=
    (support_quotient_span_singleton_le_iff (R := R) (x := x) p).1 hp_support
  refine ⟨⟨hp.isPrime, hx_le⟩, ?_⟩
  intro q hq hqp
  -- Any prime between `(x)` and `p` contains a minimal prime over `(x)`, and that minimal prime is
  -- associated to `R / xR`; minimality among associated primes then forces equality with `p`.
  have hq_min_exists :
      ∃ r ∈ (Ideal.span ({x} : Set R)).minimalPrimes, r ≤ q := by
    letI : q.IsPrime := hq.1
    exact Ideal.exists_minimalPrimes_le hq.2
  obtain ⟨r, hr_min, hrq⟩ := hq_min_exists
  have hr_assoc : r ∈ associatedPrimes R A := by
    have hr_ann : r ∈ (Module.annihilator R A).minimalPrimes := by
      simpa [Ideal.annihilator_quotient] using hr_min
    simpa using
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        (R := R) (M := A) hr_ann)
  have hp_le_r : p.asIdeal ≤ r :=
    hp_min_assoc.2 hr_assoc (hrq.trans hqp)
  exact hp_le_r.trans hrq

omit [IsLocalRing R] in
/-- Helper for Lemma 10.162.12: each associated prime of `R / xR` yields a DVR localization of
`R`. -/
lemma associatedPrime_quotient_localization_isDiscreteValuationRing
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (p : PrimeSpectrum R) (hp : IsAssociatedPrime p.asIdeal A) :
    ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
by
  have hp_min :
      p.asIdeal ∈ (Ideal.span ({x} : Set R)).minimalPrimes :=
    associatedPrime_quotient_mem_minimalPrimes_span_singleton
      (R := R) (x := x) hno_embedded p hp
  have hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 1 := by
    -- The localization at a height-one prime over a nonzero principal ideal has Krull dimension
    -- one.
    have hheight : p.asIdeal.primeHeight = 1 :=
      primeHeight_eq_one_of_mem_minimalPrimes_span_singleton_of_nonzero
      (x := x) hx0 p.asIdeal hp_min
    have hheight' : p.asIdeal.height = 1 := by
      simpa [Ideal.height_eq_primeHeight] using hheight
    exact
      (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
        (Localization.AtPrime p.asIdeal)).trans <| by
          simpa using hheight'
  -- A one-dimensional regular local ring is a discrete valuation ring.
  simpa using
    (show
        (∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
            IsDiscreteValuationRing (Localization.AtPrime p.asIdeal)) ↔
          IsRegularLocalRing (Localization.AtPrime p.asIdeal) ∧
            ringKrullDim (Localization.AtPrime p.asIdeal) = 1 from
        discreteValuationRing_iff_regularLocalRing_dim_one).2
      ⟨hregular p hp, hdim⟩

omit [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: localizing a quotient class and then identifying it with the
quotient of the localized ring sends a class `[y]` to the class of the localized numerator. -/
lemma localizedQuotientEquiv_symm_apply_mk
    (I : Ideal RCompletion) (S : Submonoid RCompletion) (y : RCompletion) :
    (localizedQuotientEquiv S (I : Submodule RCompletion RCompletion)).symm
      (LocalizedModule.mkLinearMap S (RCompletion ⧸ I) (Ideal.Quotient.mk I y)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S RCompletion y) :=
by
  -- The canonical localization equivalence is characterized by its action on quotient generators.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := S)
      (f := (I : Submodule RCompletion RCompletion).toLocalizedQuotient S)
      (g := LocalizedModule.mkLinearMap S (RCompletion ⧸ I))
      (x := Ideal.Quotient.mk I y))

/-- Helper for Lemma 10.162.12: quotienting the completion by `x R^∧` agrees with tensoring the
completion with `R / xR`. -/
noncomputable def completion_quotient_tensorQuotient_algEquiv :
    (RCompletion ⧸ J) ≃ₐ[RCompletion] (RCompletion ⊗[R] A) :=
  Algebra.TensorProduct.quotIdealMapEquivTensorQuot RCompletion
    (Ideal.span ({x} : Set R))

omit [IsDomain R] in
/-- Helper for Lemma 10.162.12: an associated prime of `R^∧ / xR^∧` contracts to an associated
prime of `R / xR`. -/
lemma completionQuotient_associatedPrime_under
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J)) :
    IsAssociatedPrime (PrimeSpectrum.comap (algebraMap R RCompletion) q).asIdeal A := by
  letI : Module.Flat R RCompletion := inferInstance
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hq_quot :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⧸ J) := by
    have hq_assoc : q.asIdeal ∈ associatedPrimes RCompletion (RCompletion ⧸ J) := by
      simpa using hq
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_assoc
  have htransport :
      associatedPrimesOfModule RCompletion (RCompletion ⧸ J) =
        associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := RCompletion ⧸ J) (M' := RCompletion ⊗[R] A)
        (completion_quotient_tensorQuotient_algEquiv (R := R) (x := x)).toLinearEquiv)
  have hq_tensor :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    -- Transport the associated-prime witness across the quotient/tensor comparison first.
    exact htransport ▸ hq_quot
  have hq_fiber :
      q ∈ relativeAssassin R RCompletion RCompletion ∩
        { q : PrimeSpectrum RCompletion | q.asIdeal.under R ∈ associatedPrimesOfModule R A } := by
    rw [← associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
      (R := R) (S := RCompletion) (M := A) (N := RCompletion)]
    exact hq_tensor
  -- The contraction component of the flat-base-change theorem is the source associated prime.
  have hp_assoc_module : Ideal.IsAssociatedToModule R A p.asIdeal := by
    simpa [p, mem_associatedPrimesOfModule_iff] using hq_fiber.2
  exact (Ideal.isAssociatedToModule_iff_isAssociatedPrime R A p.asIdeal).mp hp_assoc_module

omit [IsDomain R] in
/-- Helper for Lemma 10.162.12: an associated prime of `R^∧ / xR^∧` lies on the branch over its
contracted source associated prime. -/
lemma completionQuotient_associatedPrime_branch
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J)) :
    IsAssociatedPrime q.asIdeal
      (RCompletion ⧸
        Ideal.map (algebraMap R RCompletion)
          (PrimeSpectrum.comap (algebraMap R RCompletion) q).asIdeal) := by
  letI : Module.Flat R RCompletion := inferInstance
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hq_quot :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⧸ J) := by
    have hq_assoc : q.asIdeal ∈ associatedPrimes RCompletion (RCompletion ⧸ J) := by
      simpa using hq
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_assoc
  have htransport :
      associatedPrimesOfModule RCompletion (RCompletion ⧸ J) =
        associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := RCompletion ⧸ J) (M' := RCompletion ⊗[R] A)
        (completion_quotient_tensorQuotient_algEquiv (R := R) (x := x)).toLinearEquiv)
  have hq_tensor :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion (RCompletion ⊗[R] A) := by
    -- Reuse the quotient/tensor comparison before applying the fiberwise associated-prime theorem.
    exact htransport ▸ hq_quot
  have hq_fiber :
      q ∈ relativeAssassin R RCompletion RCompletion ∩
        { q : PrimeSpectrum RCompletion | q.asIdeal.under R ∈ associatedPrimesOfModule R A } := by
    rw [← associatedPrimesOfModule_tensorProduct_eq_fiberAssociatedPrimes_of_isNoetherianRing
      (R := R) (S := RCompletion) (M := A) (N := RCompletion)]
    exact hq_tensor
  have hq_afin : q ∈ relativeAssassinAfin R RCompletion RCompletion := by
    -- Route correction: rewrite the fiber witness to `A_fin` first, then transport the quotient.
    rw [← relativeAssassinA_eq_relativeAssassinAfin_of_flat
      (R := R) (S := RCompletion) (N := RCompletion)]
    exact hq_fiber.1
  have hq_source_branch :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion
        (relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal) := by
    simpa [mem_relativeAssassinAfin_iff, p] using hq_afin
  let e :
      relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal ≃ₗ[RCompletion]
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) :=
    Submodule.quotEquivOfEq _ _ (by
      calc
        Ideal.map (algebraMap R RCompletion) p.asIdeal • (⊤ : Submodule RCompletion RCompletion) =
            ((Ideal.map (algebraMap R RCompletion) p.asIdeal) * ⊤ : Ideal RCompletion) := by
              exact Ideal.smul_eq_mul _ _
        _ = Ideal.map (algebraMap R RCompletion) p.asIdeal := Ideal.mul_top _)
  have hbranch_transport :
      associatedPrimesOfModule RCompletion
          (relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal) =
        associatedPrimesOfModule RCompletion
          (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    simpa using
      (LinearEquiv.associatedPrimesOfModule_eq (R := RCompletion)
        (M := relativeAssassinPrimeQuotient R RCompletion RCompletion p.asIdeal)
        (M' := RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) e)
  have hq_branch :
      q.asIdeal ∈ associatedPrimesOfModule RCompletion
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
    -- The relative-assassin quotient is literally the completion quotient by the extended ideal.
    exact hbranch_transport ▸ hq_source_branch
  have hq_assoc_module :
      Ideal.IsAssociatedToModule RCompletion
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) q.asIdeal := by
    simpa [mem_associatedPrimesOfModule_iff] using hq_branch
  exact
    (Ideal.isAssociatedToModule_iff_isAssociatedPrime RCompletion
      (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) q.asIdeal).mp
      hq_assoc_module

omit [IsNoetherianRing R] [IsDomain R] in
/-- Helper for Lemma 10.162.12: a nilpotent element of the completion vanishes after localizing at
an associated prime once the localized ring is known to be a domain. -/
lemma localized_completion_nilpotent_eq_zero
    (q : PrimeSpectrum RCompletion)
    [IsDomain (Localization.AtPrime q.asIdeal)]
    {y : RCompletion} (hy : IsNilpotent y) :
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y = 0 := by
  -- Compare module localization with the actual ring localization, then kill the transported
  -- nilpotent element inside the localized domain.
  have hy_zero :
      Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y = 0 := by
    exact IsNilpotent.eq_zero (hy.map (algebraMap RCompletion (Localization.AtPrime q.asIdeal)))
  have hloc :
      (IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y) =
      (IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm 0 := by
    exact congrArg
      ((IsLocalizedModule.iso q.asIdeal.primeCompl
        (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm) hy_zero
  calc
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y =
        (IsLocalizedModule.iso q.asIdeal.primeCompl
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal) y) := by
            symm
            exact IsLocalizedModule.iso_symm_apply q.asIdeal.primeCompl
              (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal)) y
    _ =
        (IsLocalizedModule.iso q.asIdeal.primeCompl
          (Algebra.linearMap RCompletion (Localization.AtPrime q.asIdeal))).symm 0 := hloc
    _ = 0 := by
          rw [map_zero]

/-- Helper for Lemma 10.162.12: the localized class of a nilpotent completion element vanishes at
every associated prime of `R^∧ / xR^∧`. -/
lemma localized_nilpotent_quotientClass_zero_of_associatedPrime
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    (q : PrimeSpectrum RCompletion)
    (hq : IsAssociatedPrime q.asIdeal (RCompletion ⧸ J))
    {y : RCompletion} (hy : IsNilpotent y) :
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
      (Ideal.Quotient.mk J y) = 0 :=
by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R RCompletion) q
  have hp_assoc : IsAssociatedPrime p.asIdeal A :=
    completionQuotient_associatedPrime_under (R := R) (x := x) q hq
  have hp_dvr :
      ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
    associatedPrime_quotient_localization_isDiscreteValuationRing
      (R := R) (x := x) hx0 hno_embedded hregular p hp_assoc
  have hq_branch :
      IsAssociatedPrime q.asIdeal
        (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) :=
    completionQuotient_associatedPrime_branch (R := R) (x := x) q hq
  obtain ⟨hq_domain, _hq_dvr⟩ :=
    completion_localizationAt_associatedPrime_isDiscreteValuationRing
      (R := R) p q hp_dvr (h_analytic p hp_assoc) hq_branch
  letI : IsDomain (Localization.AtPrime q.asIdeal) := hq_domain
  -- Route correction: rewrite the localized quotient generator through the canonical quotient
  -- comparison, then reduce to vanishing of the localized numerator in a domain.
  let e :=
    localizedQuotientEquiv q.asIdeal.primeCompl
      (J : Submodule RCompletion RCompletion)
  have hzero' :
      e.symm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y)) = 0 := by
    rw [localizedQuotientEquiv_symm_apply_mk]
    have hmem :
        LocalizedModule.mkLinearMap q.asIdeal.primeCompl RCompletion y ∈
          Submodule.localized q.asIdeal.primeCompl (J : Submodule RCompletion RCompletion) := by
      rw [localized_completion_nilpotent_eq_zero (R := R) q hy]
      exact Submodule.zero_mem
        (Submodule.localized q.asIdeal.primeCompl
          (J : Submodule RCompletion RCompletion))
    exact (Submodule.Quotient.mk_eq_zero _).2 hmem
  calc
    LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y) =
      e (e.symm (LocalizedModule.mkLinearMap q.asIdeal.primeCompl (RCompletion ⧸ J)
        (Ideal.Quotient.mk J y))) := by
          rw [LinearEquiv.apply_symm_apply]
    _ = e 0 := by rw [hzero']
    _ = 0 := e.map_zero

/-- Helper for Lemma 10.162.12: every nilpotent element of the completion already lies in the
extended ideal `x R^∧`. -/
lemma completion_nilpotent_mem_quotientIdeal
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    y ∈ J :=
by
  letI : IsNoetherianRing RCompletion :=
    completion_isNoetherianRing (R := R)
  have hquot_zero : Ideal.Quotient.mk J y = 0 := by
    have hf_injective := 
      to_pi_localization_at_associated_primes_injective
        (R := RCompletion) (M := RCompletion ⧸ J)
    apply hf_injective
    funext q
    let qSpec : PrimeSpectrum RCompletion := ⟨q.1, q.2.1⟩
    have hq_assoc : IsAssociatedPrime qSpec.asIdeal (RCompletion ⧸ J) := by
      exact q.2
    -- Evaluate the associated-prime localization map on the quotient class and use the pointwise
    -- localized vanishing already established above.
    simpa [qSpec] using
      localized_nilpotent_quotientClass_zero_of_associatedPrime
        (R := R) (x := x) hx0 hno_embedded hregular h_analytic qSpec hq_assoc hy
  exact Ideal.Quotient.eq_zero_iff_mem.mp hquot_zero

/-- Helper for Lemma 10.162.12: a nilpotent element of the completion lies in every power of the
extended principal ideal `x R^∧`. -/
lemma completion_nilpotent_mem_all_powers_quotientIdeal
    (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    ∀ n : ℕ, y ∈ J ^ n := by
  let xhat : RCompletion := algebraMap R RCompletion x
  have hJ_span : J = Ideal.span ({xhat} : Set RCompletion) := by
    -- Normalize the extended ideal of `x` to the principal ideal generated by its image.
    rw [show J = Ideal.map (algebraMap R RCompletion) (Ideal.span ({x} : Set R)) by rfl]
    rw [Ideal.map_span]
    simp [xhat]
  have hflat : Module.Flat R RCompletion := by
    -- The maximal-ideal completion is faithfully flat over the source local ring.
    exact (RingHom.flat_algebraMap_iff).mp
      (maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R).flat
  have hx_regular : IsSMulRegular RCompletion x := by
    -- Since `R` is a domain and `x ≠ 0`, flatness keeps multiplication by `x` injective on
    -- the completion.
    exact Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := RCompletion) (mem_nonZeroDivisors_iff_ne_zero.mpr hx0)
  intro n
  induction n generalizing y with
  | zero =>
      -- The zeroth power is the unit ideal.
      simp
  | succ n ih =>
      have hy_mem_J : y ∈ J :=
        completion_nilpotent_mem_quotientIdeal
          (R := R) (x := x) hx0 hno_embedded hregular h_analytic hy
      rw [hJ_span] at hy_mem_J
      obtain ⟨y1, hy_eq⟩ := Ideal.mem_span_singleton'.mp hy_mem_J
      have hy_eq' : xhat * y1 = y := by
        simpa [xhat, mul_comm] using hy_eq
      have hy1_nilpotent : IsNilpotent y1 := by
        rcases hy with ⟨m, hm⟩
        refine ⟨m, ?_⟩
        -- Cancel the regular factor `x^m` from the nilpotence equation `(x̂ * y1)^m = 0`.
        have hsmul_zero : (x ^ m) • y1 ^ m = (x ^ m) • (0 : RCompletion) := by
          calc
            (x ^ m) • y1 ^ m = algebraMap R RCompletion (x ^ m) * y1 ^ m := by
              rfl
            _ = xhat ^ m * y1 ^ m := by
              simp [xhat, map_pow]
            _ = (xhat * y1) ^ m := by
              simp [mul_pow, mul_comm]
            _ = y ^ m := by
              simpa using congrArg (fun z : RCompletion ↦ z ^ m) hy_eq'
            _ = 0 := hm
            _ = (x ^ m) • (0 : RCompletion) := by
              simp
        exact (hx_regular.pow m) hsmul_zero
      have hy1_mem : y1 ∈ J ^ n := ih hy1_nilpotent
      have hxhat_mem : xhat ∈ J := by
        rw [hJ_span]
        exact Ideal.subset_span (by simp [xhat])
      -- Reinsert one factor of `x̂` to climb from `J^n` to `J^(n + 1)`.
      have hy_mul_mem : xhat * y1 ∈ J * J ^ n :=
        Ideal.mul_mem_mul hxhat_mem hy1_mem
      simpa [pow_succ'] using (hy_eq'.symm ▸ hy_mul_mem)

/-- Helper for Lemma 10.162.12: every nilpotent element of the completion vanishes. -/
lemma completion_nilpotent_eq_zero
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p)
    {y : RCompletion} (hy : IsNilpotent y) :
    y = 0 :=
by
  letI : IsAdicComplete (maximalIdeal R) RCompletion :=
    AdicCompletion.isAdicComplete (I := maximalIdeal R) (M := R)
      (maximalIdeal R).fg_of_isNoetherianRing
  have hy_mem_pow :
      ∀ n : ℕ, y ∈ J ^ n :=
    completion_nilpotent_mem_all_powers_quotientIdeal
      (R := R) (x := x) hx0 hno_embedded hregular h_analytic hy
  have hJ_le_max :
      J ≤ Ideal.map (algebraMap R RCompletion) (maximalIdeal R) := by
    -- The extended principal ideal generated by `x` lies inside the extended maximal ideal.
    exact Ideal.map_mono
      ((Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx)
  have hy_mod_zero :
      ∀ n : ℕ, y ≡ 0 [SMOD (maximalIdeal R ^ n • (⊤ : Submodule R RCompletion))] := by
    intro n
    rw [SModEq.zero]
    have hy_map :
        y ∈ Ideal.map (algebraMap R RCompletion) (maximalIdeal R ^ n) := by
      exact (by
        simpa [Ideal.map_pow] using
          (Ideal.pow_right_mono hJ_le_max n) (hy_mem_pow n))
    -- Rewrite the extended ideal as the corresponding `R`-submodule of the completion.
    simpa [Ideal.smul_top_eq_map, Ideal.map_pow] using hy_map
  -- Route correction: instead of forcing a local-ring structure on the completion, use that the
  -- maximal-ideal completion is Hausdorff for the source maximal ideal and kill `y` directly.
  exact IsHausdorff.haus (I := maximalIdeal R) (M := RCompletion) inferInstance y hy_mod_zero

/-- Lemma 10.162.12: if `(R, 𝔪)` is a Noetherian local domain, `x ∈ 𝔪` is nonzero, `R / xR` has
no embedded primes, and every associated prime of `R / xR` is regular and analytically
unramified, then `R` is analytically unramified. -/
theorem isAnalyticallyUnramified_of_nonzero_in_maximalIdeal_of_associatedPrimes_quotient_regular
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hno_embedded : embeddedAssociatedPrimes R A = ∅)
    (hregular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal A →
          PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsAnalyticallyUnramified R := by
  rw [isAnalyticallyUnramified_iff]
  -- It is enough to show that every nilpotent element of the maximal-ideal completion vanishes.
  refine ⟨fun y hy ↦ ?_⟩
  exact completion_nilpotent_eq_zero
    (R := R) (x := x) hx hx0 hno_embedded hregular h_analytic hy

end

/-! ### Lemma_10_162_13 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R] [NagataRing R]

/- Domain-style sampling:
- primary domain: local Nagata domains and analytically unramified maximal-ideal completions;
- sampled owner declarations:
  `NagataRing`,
  `IsAnalyticallyUnramified`,
  `isAnalyticallyUnramified_iff`,
  and `PrimeSpectrum.IsAnalyticallyUnramified`;
- best owner abstraction: `IsAnalyticallyUnramified` is the core/canonical owner for the target
  conclusion, so this file should expose the result directly in that owner language rather than
  through a parallel completion-reducedness wrapper;
- primitive data vs. derived API: the primitive data are the ambient hypotheses
  `[IsLocalRing R] [IsDomain R] [NagataRing R]`, while reducedness of the completion is derived
  bridge API coming from `isAnalyticallyUnramified_iff`.
-/

-- Proof sketch: let `S` be the integral closure of `R` in `FractionRing R`. Since `R` is Nagata,
-- `S` is module-finite over `R`; localize at the finitely many maximal ideals of `S` over the
-- maximal ideal of `R` and use completion to reduce to the normal case. Then apply Lemma
-- `10.162.12` to a nonzero element of the maximal ideal, using the height-one regularity of the
-- associated primes of `R / xR` and induction on dimension for the quotient domains.
/-- Lemma 10.162.13: a local Nagata domain is analytically unramified. -/
instance isAnalyticallyUnramified_of_nagataRing : IsAnalyticallyUnramified R := sorry

end

/-! ### Lemma_10_162_14 (from Chap10) -/
universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: Noetherian local Nagata rings and analytic unramifiedness for finite domain
  extensions;
- sampled owner declarations in the same chapter/project:
  `NagataRing`,
  `IsAnalyticallyUnramified`,
  `localization_nagataRing`,
  `isAnalyticallyUnramified_of_nagataRing`,
  `isN1Ring_of_forall_maximal_isAnalyticallyUnramified`;
- best owner abstraction: the source-facing owner for clause `(1)` is `NagataRing`, while the
  analytic condition in clauses `(2)` and `(3)` should be stated directly with the canonical owner
  `IsAnalyticallyUnramified`, not via a parallel reduced-completion wrapper;
- primitive data vs. derived API: the primitive data are the Noetherian local base ring `R` and,
  for each extension `S`, the finite/domain/local algebra structure. Localization at a maximal
  ideal and analytic unramifiedness are derived owner-level views, so the TFAE should use
  `Localization.AtPrime m.asIdeal` and `IsAnalyticallyUnramified` directly rather than introducing
  any new package or wrapper.

Source/core/bridge triage:
- `source-facing`: the TFAE relating the Nagata condition to analytically unramified finite domain
  extensions;
- `core/canonical`: `NagataRing`, `IsAnalyticallyUnramified`, `Localization.AtPrime`,
  `localization_nagataRing`, and `isAnalyticallyUnramified_of_nagataRing`;
- `bridge/view`: clause `(2)` passes from a finite domain algebra to its maximal localizations,
  while clause `(3)` is the local special case used to recover the owner `NagataRing`.
-/

-- Proof sketch: `(1) → (2)` by applying Nagata stability under finite extensions
-- (`Lemma 10.162.5`), then localizing (`Lemma 10.162.6`), and finally using that a local Nagata
-- domain is analytically unramified (`Lemma 10.162.13`). `(2) → (3)` is the special case obtained
-- by localizing a finite local domain algebra at its maximal ideal. For `(3) → (1)`, to prove
-- that `R` is Nagata one tests the `N-2` condition on each prime quotient by a finite field
-- extension, builds the corresponding finite local domain algebra, applies `(3)`, and then uses
-- `Lemma 10.162.10 (4)` to deduce finiteness of the integral closure.
/-- Lemma 10.162.14: for a Noetherian local ring `R`, the Nagata condition is equivalent to saying
that every localization `S_{m'}` of a finite domain `R`-algebra is analytically unramified, and is
also equivalent to saying that every finite local domain `R`-algebra is analytically unramified. -/
theorem nagataRing_tfae_analyticallyUnramified_finite_domain_extensions :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S],
          ∀ m : MaximalSpectrum S, IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal),
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
          [IsLocalRing S] [IsLocalHom (algebraMap R S)],
          IsAnalyticallyUnramified S ] := sorry

end

/-! ### Proposition_10_162_15_Nagata (from Chap10) -/
universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of the source-facing Nagata and universally Japanese
  conditions on commutative rings;
- sampled owner declarations of the same kind in the chapter/project:
  `IsN1Ring`,
  `IsN2Ring`,
  `UniversallyJapaneseRing`,
  `NagataRing`.
- best owner abstraction:
  `NagataRing` and `UniversallyJapaneseRing` are the source-facing owners;
  the theorem below is therefore a `bridge/view` TFAE comparing the owner `NagataRing` with its
  finite-type stability clause and the canonical `UniversallyJapaneseRing ∧ IsNoetherianRing`
  description.
- primitive data vs. derived API:
  the public clauses of the proposition are the source-facing content;
  extracted consequences such as `NagataRing R → UniversallyJapaneseRing R` are derived owner API
  and should be named once here, then reused downstream instead of re-extracting `List.TFAE` data.

Source/core/bridge triage:
- `source-facing`: the `List.TFAE` proposition itself;
- `core/canonical`: the owner classes `NagataRing`, `UniversallyJapaneseRing`, `IsN2Ring`,
  and the canonical Noetherian owner `IsNoetherianRing`;
- `bridge/view`: the named bridge theorem and instance extracted from the TFAE below.
-/

-- Proof sketch: `(1) → (2)` is the finite-type stability of Nagata rings proved by reducing to
-- the one-generator case and then to the domain case. `(2) → (3)` follows by applying clause
-- `(2)` to the identity algebra `R` to get Noetherianity, and then to finite type domain
-- `R`-algebras to obtain the universally Japanese property. `(3) → (1)` combines the Noetherian
-- hypothesis with the universally Japanese condition applied to the quotient domains `R ⧸ p`.
/-- Proposition 10.162.15 (Nagata): for a commutative ring `R`, the following are equivalent:
`R` is a Nagata ring, every finite type `R`-algebra is a Nagata ring, and `R` is universally
Japanese and Noetherian. -/
theorem nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], NagataRing S,
        UniversallyJapaneseRing R ∧ IsNoetherianRing R ] := sorry

/-- The Nagata condition is equivalent to being universally Japanese and Noetherian. -/
theorem nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing :
    NagataRing R ↔ UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R := by
  have htfae :
      List.TFAE
        [ NagataRing R,
          ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S], NagataRing S,
          UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R ] :=
    nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian
  exact htfae.out 0 2

end

section

variable (R : Type u) [CommRing R] [NagataRing R]

/-- Every Nagata ring is universally Japanese. -/
instance nagataRing_toUniversallyJapaneseRing : UniversallyJapaneseRing.{u, v} R :=
  (nagataRing_iff_universallyJapaneseRing_and_isNoetherianRing.1 inferInstance).1

end

/-! ### Proposition_10_162_16 (from Chap10) -/
universe u v

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings and universally Japanese rings, together
  with the standard source-facing permanence and example classes listed in Proposition 10.162.16;
- sampled owner declarations in the same chapter:
  `NagataRing`,
  `UniversallyJapaneseRing`,
  `nagataRing_of_noetherian_completeLocalRing`,
  `nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian`.
- best owner abstraction: `NagataRing` is the source-facing owner for the proposition, while
  `UniversallyJapaneseRing` is the canonical downstream bridge owner derived from it.
- primitive data vs. derived API:
  the primitive data here are only the source-faithful hypotheses for the field, complete-local,
  Dedekind-domain, and integer examples;
  the finite-type stability theorem and the `NagataRing → UniversallyJapaneseRing` bridge are
  derived owner API and should be reused from the chapter TFAE proposition rather than rebuilt as
  parallel local proof packages.

Source/core/bridge triage:
- `source-facing`: the example instances and the named finite-type closure theorem recorded in this
  proposition;
- `core/canonical`: the owner classes `NagataRing` and `UniversallyJapaneseRing`, plus the
  complete-local criterion `nagataRing_of_noetherian_completeLocalRing`;
- `bridge/view`: extracting the finite-type closure and universally-Japanese consequences from the
  earlier owner theorem
  `nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian`.
-/

section

variable (K : Type u) [Field K]

/-- Fields are Nagata rings. -/
-- Proof sketch: a field is Noetherian, and its only prime ideal is `(0)`, so every prime quotient
-- is again a field; fields are `N-2`.
instance : NagataRing K := sorry

end

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Noetherian complete local rings are Nagata rings. This is the source-facing owner from
`Lemma_10_162_8`, reused directly here instead of keeping a second parallel instance. -/
recall nagataRing_of_noetherian_completeLocalRing

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Dedekind domains whose fraction field has characteristic zero are Nagata rings. -/
-- Proof sketch: a Dedekind domain is Noetherian. For a prime ideal `p`, either `p = ⊥`, in which
-- case `R ⧸ p = R` is `N-2` by Lemma `10.161.11`, or `p` is maximal, in which case `R ⧸ p` is a
-- field and hence `N-2`.
instance nagataRing_of_isDedekindDomain_of_fractionRing_charZero : NagataRing R := sorry

end

section

/- The ring of integers is a Nagata ring. This is the direct specialization of the canonical
Dedekind-domain characteristic-zero owner instance above, so no separate `ℤ`-specific instance is
kept here. -/
#check (inferInstance : NagataRing ℤ)

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras over a Noetherian ring are Noetherian. For a prime ideal
-- `q` of `S`, the quotient `S ⧸ q` is a finite type domain over `R ⧸ (q.comap (algebraMap R S))`,
-- and the latter is `N-2` because `R` is Nagata. Thus `S ⧸ q` is `N-2`, giving the Nagata
-- property for `S`.
/-- Proposition 10.162.16: finite type ring extensions of Nagata rings are Nagata. Together with
the field, complete-local, `ℤ`, and Dedekind-domain cases, this yields the full list of Nagata
rings in the proposition. -/
theorem nagataRing_of_finiteType (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [NagataRing R] [Algebra.FiniteType R S] : NagataRing S := by
  let hR : NagataRing R := inferInstance
  have htfae :
      List.TFAE
        [ NagataRing R,
          ∀ (T : Type v) [CommRing T] [Algebra R T] [Algebra.FiniteType R T], NagataRing T,
          UniversallyJapaneseRing.{u, v} R ∧ IsNoetherianRing R ] :=
    nagataRing_tfae_finiteType_algebra_nagata_universallyJapanese_noetherian
  let hFiniteType := (htfae.out 0 1).1 hR
  exact hFiniteType S

end

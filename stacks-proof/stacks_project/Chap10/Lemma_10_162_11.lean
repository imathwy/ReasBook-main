import Mathlib
import stacks_project.Chap10.Definition_10_162_9
import stacks_project.Chap10.Lemma_10_66_3
import stacks_project.Chap10.Lemma_10_66_6
import stacks_project.Chap10.Lemma_10_66_13
import stacks_project.Chap10.Lemma_10_66_11
import stacks_project.Chap10.Lemma_10_119_7
import stacks_project.Chap10.Lemma_10_97_3

-- Declarations for this item will be appended below by the statement pipeline.

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

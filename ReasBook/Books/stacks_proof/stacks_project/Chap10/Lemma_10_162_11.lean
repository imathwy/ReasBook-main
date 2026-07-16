import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_162_9
import stacks_proof.stacks_project.Chap10.Lemma_10_66_3
import stacks_proof.stacks_project.Chap10.Lemma_10_66_6
import stacks_proof.stacks_project.Chap10.Lemma_10_66_13
import stacks_proof.stacks_project.Chap10.Lemma_10_66_11
import stacks_proof.stacks_project.Chap10.Lemma_10_97_3
import stacks_proof.stacks_project.Chap10.Lemma_10_97_6
import stacks_proof.stacks_project.Chap10.Lemma_10_97_7
import stacks_proof.stacks_project.Chap10.Lemma_10_162_11.Index

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

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.162.11: the maximal ideal of the prime quotient `R ⧸ p` is the image of
the maximal ideal of `R`. -/
lemma primeQuotient_map_maximalIdeal_eq (p : PrimeSpectrum R) :
    Ideal.map (Ideal.Quotient.mk p.asIdeal) (maximalIdeal R) =
      maximalIdeal (R ⧸ p.asIdeal) := by
  -- The quotient map is surjective, so locality identifies the target maximal ideal with the image
  -- of the source maximal ideal.
  exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p.asIdeal)
    Ideal.Quotient.mk_surjective

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
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

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the `maximalIdeal R`-power stage on the prime quotient as
an `R`-module is the same as the corresponding power of the mapped maximal ideal. -/
private theorem primeQuotient_stage_smul_top_eq_stage_map
    (p : PrimeSpectrum R) (n : ℕ) :
    (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal))) =
      Submodule.restrictScalars R
        ((((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n :
            Ideal (R ⧸ p.asIdeal)) : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))) := by
  -- Proof comment: rewrite the scalar-power stage as the image ideal and then identify that image
  -- with the corresponding power of the maximal ideal in the quotient ring.
  simpa [Ideal.map_pow, primeQuotient_map_maximalIdeal_eq] using
    (Ideal.smul_top_eq_map (R := R) (S := R ⧸ p.asIdeal) (I := maximalIdeal R ^ n))

/-- Helper for Chap10 Lemma 10 162 11: the mapped-maximal-ideal completion of `R ⧸ p` carries
the canonical completion ring structure. -/
noncomputable local instance primeQuotient_mapMaximalIdeal_adicCompletion_commRing
    (p : PrimeSpectrum R) :
    CommRing
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal)) :=
  AdicCompletion.instCommRing
    (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 11: the mapped-maximal-ideal completion of `R ⧸ p` is an
`R ⧸ p`-algebra. -/
noncomputable local instance primeQuotient_mapMaximalIdeal_adicCompletion_quotientAlgebra
    (p : PrimeSpectrum R) :
    Algebra (R ⧸ p.asIdeal)
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal)) :=
  AdicCompletion.instAlgebra
    (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 11: the mapped-maximal-ideal completion of `R ⧸ p` is an
`R`-algebra through the quotient map. -/
noncomputable local instance primeQuotient_mapMaximalIdeal_adicCompletion_baseAlgebra
    (p : PrimeSpectrum R) :
    Algebra R
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal)) :=
  AdicCompletion.instAlgebra
    (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))

/-- Helper for Chap10 Lemma 10 162 11: the maximal-ideal completion of `R ⧸ p` carries the
canonical completion ring structure. -/
noncomputable local instance primeQuotient_maximalIdeal_adicCompletion_commRing
    (p : PrimeSpectrum R) :
    CommRing (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal)) :=
  AdicCompletion.instCommRing (maximalIdeal (R ⧸ p.asIdeal))

/-- Helper for Chap10 Lemma 10 162 11: the maximal-ideal completion of `R ⧸ p` is an
`R ⧸ p`-algebra. -/
noncomputable local instance primeQuotient_maximalIdeal_adicCompletion_quotientAlgebra
    (p : PrimeSpectrum R) :
    Algebra (R ⧸ p.asIdeal)
      (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal)) :=
  AdicCompletion.instAlgebra (maximalIdeal (R ⧸ p.asIdeal))

/-- Helper for Chap10 Lemma 10 162 11: the maximal-ideal completion of `R ⧸ p` is an `R`-algebra
through the quotient map. -/
noncomputable local instance primeQuotient_maximalIdeal_adicCompletion_baseAlgebra
    (p : PrimeSpectrum R) :
    Algebra R (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal)) :=
  AdicCompletion.instAlgebra (maximalIdeal (R ⧸ p.asIdeal))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: after restricting scalars from `R ⧸ p` to `R`, the stage
submodule of the mapped-maximal-ideal completion is the usual `maximalIdeal R`-adic stage. -/
private theorem primeQuotient_ring_stage_restrictScalars_eq_module_stage
    (p : PrimeSpectrum R) (n : ℕ) :
    (((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))).restrictScalars R :
        Submodule R (R ⧸ p.asIdeal)) =
      (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal))) := by
  -- Proof comment: convert the ring-linear stage back to the ideal-as-submodule spelling and then
  -- apply the previous quotient-stage identification.
  calc
    (((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))).restrictScalars R :
        Submodule R (R ⧸ p.asIdeal)) =
        Submodule.restrictScalars R
          ((((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n :
              Ideal (R ⧸ p.asIdeal)) : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))) := by
          ext x
          simp
    _ = (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal))) := by
          symm
          exact primeQuotient_stage_smul_top_eq_stage_map p n

/-- Helper for Chap10 Lemma 10 162 11: the stage quotient of the mapped-maximal-ideal ring
completion of `R ⧸ p` is canonically the stage quotient used by the `maximalIdeal R`-adic module
completion. -/
private noncomputable def primeQuotient_ringCompletionStageLinearEquivModuleStage
    (p : PrimeSpectrum R) (n : ℕ) :
    ((R ⧸ p.asIdeal) ⧸
        (((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
            (⊤ : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))))) ≃ₗ[R]
      ((R ⧸ p.asIdeal) ⧸
        (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal)))) :=
  ((Submodule.Quotient.restrictScalarsEquiv R
      ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
        (⊤ : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal)))).symm).trans
    (Submodule.quotEquivOfEq _ _
      (primeQuotient_ring_stage_restrictScalars_eq_module_stage p n))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the stage comparison between the two completion models
fixes the class of a concrete quotient element. -/
private theorem primeQuotient_ringCompletionStageLinearEquivModuleStage_mk
    (p : PrimeSpectrum R) (n : ℕ) (x : R ⧸ p.asIdeal) :
    primeQuotient_ringCompletionStageLinearEquivModuleStage p n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- Proof comment: both quotient transports are induced by the identity on representatives.
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the inverse stage comparison also fixes concrete quotient
classes. -/
private theorem primeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk
    (p : PrimeSpectrum R) (n : ℕ) (x : R ⧸ p.asIdeal) :
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  -- Proof comment: apply the forward comparison to reduce the inverse computation to the
  -- representative computation.
  apply (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).injective
  rw [LinearEquiv.apply_symm_apply,
    primeQuotient_ringCompletionStageLinearEquivModuleStage_mk]

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the finite-stage comparison commutes with transition maps. -/
private theorem primeQuotient_ringCompletionStageLinearEquivModuleStage_factor
    (p : PrimeSpectrum R) {m n : ℕ} (h : m ≤ n)
    (z :
      (R ⧸ p.asIdeal) ⧸
        (((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
          (⊤ : Submodule (R ⧸ p.asIdeal) (R ⧸ p.asIdeal))))) :
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.asIdeal) h
        (primeQuotient_ringCompletionStageLinearEquivModuleStage p n z) =
      primeQuotient_ringCompletionStageLinearEquivModuleStage p m
        (AdicCompletion.transitionMap
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal) h z) := by
  -- Proof comment: transition-map naturality is checked on quotient representatives, where both
  -- comparison maps are the identity.
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the inverse finite-stage comparison commutes with
transition maps. -/
private theorem primeQuotient_ringCompletionStageLinearEquivModuleStage_symm_factor
    (p : PrimeSpectrum R) {m n : ℕ} (h : m ≤ n)
    (z :
      (R ⧸ p.asIdeal) ⧸
        (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal)))) :
    AdicCompletion.transitionMap
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) h
        ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm z) =
      (primeQuotient_ringCompletionStageLinearEquivModuleStage p m).symm
        (AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.asIdeal) h z) := by
  -- Proof comment: this is the same representative-wise identity for the inverse comparisons.
  refine Quotient.inductionOn' z ?_
  intro x
  rfl

/-- Helper for Chap10 Lemma 10 162 11: the mapped-maximal-ideal ring completion of `R ⧸ p` is
also complete for the ambient `maximalIdeal R`-adic `R`-module topology. -/
private theorem primeQuotient_ringCompletion_isAdicComplete_as_module
    (p : PrimeSpectrum R) :
    IsAdicComplete (maximalIdeal R)
      (AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal)) := by
  have hcomplete_map :
      IsAdicComplete
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal)) :=
    AdicCompletion.isAdicComplete (prime_quotient_map_maximalIdeal_fg p)
  -- Proof comment: transport completeness across the quotient algebra map `R → R ⧸ p`.
  exact (IsAdicComplete.map_algebraMap_iff
    (R := R) (S := R ⧸ p.asIdeal)
    (I := maximalIdeal R)
    (M := AdicCompletion
      (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
      (R ⧸ p.asIdeal))).mp hcomplete_map

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: coordinatewise inverse finite-stage comparison gives a
compatible point in the mapped-maximal-ideal completion. -/
private theorem primeQuotient_moduleCompletion_to_ringCompletionFun_compatible
    (p : PrimeSpectrum R)
    (x : AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal)) :
    ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal) h
          ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
            (x.val n)) =
        (primeQuotient_ringCompletionStageLinearEquivModuleStage p m).symm
          (x.val m) := by
  -- Proof comment: move the transition map through the inverse stage comparison, then use the
  -- source completion's own compatibility.
  intro m n h
  rw [primeQuotient_ringCompletionStageLinearEquivModuleStage_symm_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 162 11: the coordinatewise comparison from the `maximalIdeal R`
module completion to the mapped-maximal-ideal ring completion. -/
private noncomputable def primeQuotient_moduleCompletion_to_ringCompletionFun
    (p : PrimeSpectrum R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) →
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  fun x ↦
    ⟨fun n ↦
        (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
          (x.val n),
      primeQuotient_moduleCompletion_to_ringCompletionFun_compatible p x⟩

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the forward coordinatewise comparison preserves
addition. -/
private theorem primeQuotient_moduleCompletion_to_ringCompletionFun_map_add
    (p : PrimeSpectrum R)
    (x y : AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal)) :
    primeQuotient_moduleCompletion_to_ringCompletionFun p (x + y) =
      primeQuotient_moduleCompletion_to_ringCompletionFun p x +
        primeQuotient_moduleCompletion_to_ringCompletionFun p y := by
  -- Proof comment: equality of completion points is checked at each coordinate, where the
  -- finite-stage comparison is linear.
  ext n
  exact map_add
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
    (x.val n) (y.val n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the forward coordinatewise comparison preserves source
scalar multiplication. -/
private theorem primeQuotient_moduleCompletion_to_ringCompletionFun_map_smul
    (p : PrimeSpectrum R) (r : R)
    (x : AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal)) :
    primeQuotient_moduleCompletion_to_ringCompletionFun p (r • x) =
      r • primeQuotient_moduleCompletion_to_ringCompletionFun p x := by
  -- Proof comment: the stage comparison is `R`-linear, so scalar compatibility holds
  -- coordinatewise.
  ext n
  exact map_smul
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
    r (x.val n)

/-- Helper for Chap10 Lemma 10 162 11: the `maximalIdeal R`-adic module completion of `R ⧸ p`
maps to its mapped-maximal-ideal ring completion. -/
private noncomputable def primeQuotient_moduleCompletion_to_ringCompletion
    (p : PrimeSpectrum R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) →ₗ[R]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  { toFun := primeQuotient_moduleCompletion_to_ringCompletionFun p
    map_add' := primeQuotient_moduleCompletion_to_ringCompletionFun_map_add p
    map_smul' := primeQuotient_moduleCompletion_to_ringCompletionFun_map_smul p }

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the forward comparison sends dense elements to the same
completed quotient element. -/
private theorem primeQuotient_moduleCompletion_to_ringCompletion_of
    (p : PrimeSpectrum R) (x : R ⧸ p.asIdeal) :
    primeQuotient_moduleCompletion_to_ringCompletion p
        (AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) x) =
      AdicCompletion.of
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) x := by
  -- Proof comment: the inverse finite-stage comparison fixes representatives at every level.
  ext n
  exact primeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk p n x

/-- Helper for Chap10 Lemma 10 162 11: the `n`th finite-stage map used to lift the reverse
comparison. -/
private noncomputable def primeQuotient_ringCompletion_to_moduleCompletionStageMap
    (p : PrimeSpectrum R) (n : ℕ) :
    AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) →ₗ[R]
      (R ⧸ p.asIdeal) ⧸ (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ p.asIdeal))) :=
  (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).toLinearMap.comp
    ((AdicCompletion.eval
      (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
      (R ⧸ p.asIdeal) n).restrictScalars R)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the finite-stage maps defining the reverse comparison are
compatible with the `maximalIdeal R`-adic transition maps. -/
private theorem primeQuotient_ringCompletion_to_moduleCompletion_compatible_apply
    (p : PrimeSpectrum R) {m n : ℕ} (h : m ≤ n)
    (y :
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal)) :
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.asIdeal) h
        (primeQuotient_ringCompletion_to_moduleCompletionStageMap p n y) =
      primeQuotient_ringCompletion_to_moduleCompletionStageMap p m y := by
  -- Proof comment: commute the stage comparison past the transition map and then use the
  -- compatibility of the mapped-completion coordinates.
  rw [primeQuotient_ringCompletion_to_moduleCompletionStageMap]
  rw [primeQuotient_ringCompletion_to_moduleCompletionStageMap]
  change
    AdicCompletion.transitionMap (maximalIdeal R) (R ⧸ p.asIdeal) h
        (primeQuotient_ringCompletionStageLinearEquivModuleStage p n (y.val n)) =
      primeQuotient_ringCompletionStageLinearEquivModuleStage p m (y.val m)
  rw [primeQuotient_ringCompletionStageLinearEquivModuleStage_factor,
    AdicCompletion.transitionMap_comp_eval_apply]

/-- Helper for Chap10 Lemma 10 162 11: the mapped-maximal-ideal ring completion maps back to the
`maximalIdeal R`-adic module completion. -/
private noncomputable def primeQuotient_ringCompletion_to_moduleCompletion
    (p : PrimeSpectrum R) :
    AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) →ₗ[R]
      AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) :=
  AdicCompletion.lift (maximalIdeal R)
    (primeQuotient_ringCompletion_to_moduleCompletionStageMap p)
    (fun h ↦ LinearMap.ext (primeQuotient_ringCompletion_to_moduleCompletion_compatible_apply p h))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the reverse comparison fixes dense quotient elements. -/
private theorem primeQuotient_ringCompletion_to_moduleCompletion_of
    (p : PrimeSpectrum R) (x : R ⧸ p.asIdeal) :
    primeQuotient_ringCompletion_to_moduleCompletion p
        (AdicCompletion.of
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal) x) =
      AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) x := by
  -- Proof comment: evaluate the lifted reverse comparison at every finite stage.
  ext n
  rw [primeQuotient_ringCompletion_to_moduleCompletion]
  change
    primeQuotient_ringCompletion_to_moduleCompletionStageMap p n
        (AdicCompletion.of
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal) x) =
      Submodule.Quotient.mk x
  simpa [primeQuotient_ringCompletion_to_moduleCompletionStageMap] using
    primeQuotient_ringCompletionStageLinearEquivModuleStage_mk p n x

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the two completion comparisons are inverse on the
`maximalIdeal R`-adic module completion. -/
private theorem primeQuotient_completionComparison_left_inv
    (p : PrimeSpectrum R) :
    Function.LeftInverse
      (primeQuotient_ringCompletion_to_moduleCompletion p)
      (primeQuotient_moduleCompletion_to_ringCompletion p) := by
  -- Proof comment: after evaluation at a finite stage the composite is `Eₙ (Eₙ.symm _)`.
  intro x
  ext n
  rw [primeQuotient_ringCompletion_to_moduleCompletion]
  change
    primeQuotient_ringCompletion_to_moduleCompletionStageMap p n
        (primeQuotient_moduleCompletion_to_ringCompletion p x) =
      x.val n
  rw [primeQuotient_ringCompletion_to_moduleCompletionStageMap,
    primeQuotient_moduleCompletion_to_ringCompletion]
  change
    primeQuotient_ringCompletionStageLinearEquivModuleStage p n
        ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
          (x.val n)) =
      x.val n
  exact (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).apply_symm_apply
    (x.val n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the two completion comparisons are inverse on the
mapped-maximal-ideal ring completion. -/
private theorem primeQuotient_completionComparison_right_inv
    (p : PrimeSpectrum R) :
    Function.RightInverse
      (primeQuotient_ringCompletion_to_moduleCompletion p)
      (primeQuotient_moduleCompletion_to_ringCompletion p) := by
  -- Proof comment: the other composite has coordinate `Eₙ.symm (Eₙ _)`.
  intro y
  ext n
  change
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
        ((primeQuotient_ringCompletion_to_moduleCompletion p y).val n) =
      y.val n
  rw [primeQuotient_ringCompletion_to_moduleCompletion]
  change
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
        (primeQuotient_ringCompletion_to_moduleCompletionStageMap p n y) =
      y.val n
  rw [primeQuotient_ringCompletion_to_moduleCompletionStageMap]
  exact (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm_apply_apply
    (y.val n)

/-- Helper for Chap10 Lemma 10 162 11: the module completion of `R ⧸ p` canonically identifies
with its mapped-maximal-ideal ring completion. -/
private noncomputable def primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv
    (p : PrimeSpectrum R) :
    AdicCompletion (maximalIdeal R) (R ⧸ p.asIdeal) ≃ₗ[R]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  { primeQuotient_moduleCompletion_to_ringCompletion p with
    invFun := primeQuotient_ringCompletion_to_moduleCompletion p
    left_inv := primeQuotient_completionComparison_left_inv p
    right_inv := primeQuotient_completionComparison_right_inv p }

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the module-to-mapped-completion equivalence fixes dense
quotient elements. -/
private theorem primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv_of
    (p : PrimeSpectrum R) (x : R ⧸ p.asIdeal) :
    primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv p
        (AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) x) =
      AdicCompletion.of
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) x := by
  -- Proof comment: this is the dense-element computation for the forward comparison.
  exact primeQuotient_moduleCompletion_to_ringCompletion_of p x

/-- Helper for Chap10 Lemma 10 162 11: the genuine maximal-ideal completion of `R ⧸ p` is the
same as its completion for the image of `maximalIdeal R`. -/
private noncomputable def primeQuotient_maximalIdealCompletionAlgEquivMadicCompletion
    (p : PrimeSpectrum R) :
    AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal) ≃ₐ[R ⧸ p.asIdeal]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  maximalIdealCompletionAlgEquivMadicCompletion
    ((maximalIdeal R).fg_of_isNoetherianRing)
    (prime_quotient_closedPoint_quotient_finite p)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the completed quotient map kills the extended prime
`pR^∧`. -/
lemma completionQuotient_toPrimeQuotientCompletion_ker
    (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R RCompletion) p.asIdeal ≤
      RingHom.ker (maximalIdealCompletionMap (algebraMap R (R ⧸ p.asIdeal))) := by
  -- Proof comment: reduce an element of the extended prime to a source element of `p`, then use
  -- functoriality of maximal-ideal completion for the quotient map.
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hcomp :=
    DFunLike.congr_fun (maximalIdealCompletionMap_comp (algebraMap R (R ⧸ p.asIdeal))) x
  rw [RingHom.comp_apply, RingHom.comp_apply] at hcomp
  rw [Ideal.mem_comap, RingHom.mem_ker]
  rw [hcomp]
  change
    algebraMap (R ⧸ p.asIdeal)
        (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal))
        (Ideal.Quotient.mk p.asIdeal x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- Helper for Chap10 Lemma 10 162 11: the completed quotient map factors through
`R^∧ / pR^∧`. -/
noncomputable def completionQuotient_toPrimeQuotientCompletion
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) →+*
      AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal) :=
  Ideal.Quotient.lift
    (Ideal.map (algebraMap R RCompletion) p.asIdeal)
    (maximalIdealCompletionMap (algebraMap R (R ⧸ p.asIdeal)))
    (completionQuotient_toPrimeQuotientCompletion_ker p)

/-- Helper for Chap10 Lemma 10 162 11: the completed quotient identifies linearly with the
mapped-maximal-ideal completion of the prime quotient. -/
private noncomputable def primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) ≃ₗ[R]
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  (LinearEquiv.restrictScalars R
    (prime_quotient_completionQuotient_moduleCompletion_linearEquiv p)).trans
      (primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv p)

/-- Helper for Chap10 Lemma 10 162 11: the quotient-to-completion map followed by the
maximal-vs-mapped comparison. -/
private noncomputable def completionQuotient_toMappedPrimeQuotientCompletion
    (p : PrimeSpectrum R) :
    (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) →+*
      AdicCompletion
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
        (R ⧸ p.asIdeal) :=
  ((primeQuotient_maximalIdealCompletionAlgEquivMadicCompletion p).toRingHom).comp
    (completionQuotient_toPrimeQuotientCompletion p)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: powers of `maximalIdeal R` map into the corresponding
powers of its image in the prime quotient. -/
private theorem primeQuotient_pow_maximalIdeal_le_comap_pow_map
    (p : PrimeSpectrum R) (n : ℕ) :
    maximalIdeal R ^ n ≤
      Ideal.comap (algebraMap R (R ⧸ p.asIdeal))
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n) :=
  (Ideal.pow_right_mono
    (Ideal.le_comap_map :
      maximalIdeal R ≤
        Ideal.comap (algebraMap R (R ⧸ p.asIdeal))
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))) n).trans
    (Ideal.le_comap_pow (algebraMap R (R ⧸ p.asIdeal)) n)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: finite-stage scalar multiplication by a source quotient
class on the completed class of `1` is represented by the same source element modulo `p`. -/
private theorem primeQuotient_stage_smulOne_mk
    (p : PrimeSpectrum R) (n : ℕ) (x : R) :
    (primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
        ((Ideal.Quotient.mk (maximalIdeal R ^ n) x) •
          Submodule.Quotient.mk (1 : R ⧸ p.asIdeal)) =
      Submodule.Quotient.mk (Ideal.Quotient.mk p.asIdeal x) := by
  -- Proof comment: both sides are represented by the image of `x` in `R ⧸ p`; the finite-stage
  -- comparison is identity on representatives.
  rw [Module.Quotient.mk_smul_mk]
  simpa [Algebra.smul_def] using
    primeQuotient_ringCompletionStageLinearEquivModuleStage_symm_mk p n
      (Ideal.Quotient.mk p.asIdeal x)

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: after converting the finite mapped stage from a submodule
quotient to an ideal quotient, scalar multiplication by a source quotient class agrees with the
finite-stage quotient map. -/
private theorem primeQuotient_stage_factor_smulOne_eq_quotientMap
    (p : PrimeSpectrum R) (n : ℕ) (q : R ⧸ maximalIdeal R ^ n) :
    Ideal.Quotient.factor
        (show
          ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
              (⊤ : Ideal (R ⧸ p.asIdeal))) ≤
            (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n by
          simp)
        ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
          (q • Submodule.Quotient.mk (1 : R ⧸ p.asIdeal))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        q := by
  -- Proof comment: quotient induction reduces the factor statement to the representative
  -- computation above, where both sides are the ideal-quotient class of `x mod p`.
  refine Quotient.inductionOn' q ?_
  intro x
  let hstage :
      ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
          (⊤ : Ideal (R ⧸ p.asIdeal))) ≤
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n := by
    simp
  change
    Ideal.Quotient.factor hstage
        ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
          ((Ideal.Quotient.mk (maximalIdeal R ^ n) x) •
            Submodule.Quotient.mk (1 : R ⧸ p.asIdeal))) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        (Ideal.Quotient.mk (maximalIdeal R ^ n) x)
  rw [primeQuotient_stage_smulOne_mk]
  rfl

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the coordinate of `b • of 1` in the module completion is
the finite quotient action of the coordinate of `b` on the class of `1`. -/
private theorem primeQuotient_moduleCompletion_smul_one_val
    (p : PrimeSpectrum R) (n : ℕ) (b : RCompletion) :
    (b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1).val n =
      (AdicCompletion.evalₐ (maximalIdeal R) n b) •
        Submodule.Quotient.mk (1 : R ⧸ p.asIdeal) := by
  -- Proof comment: scalar evaluation is coordinatewise; `evalₐ` is the ideal-quotient spelling of
  -- that same coordinate action.
  rw [AdicCompletion.smul_eval]
  exact AdicCompletion.val_smul_eq_evalₐ_smul (maximalIdeal R) n b
    (Submodule.Quotient.mk (1 : R ⧸ p.asIdeal))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 162 11: the module-to-mapped-completion comparison sends
`b • of 1` to the finite-stage quotient image of `b`. -/
private theorem primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv_smul_one_eval
    (p : PrimeSpectrum R) (n : ℕ) (b : RCompletion) :
    AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) n
        (primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv p
          (b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1)) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        (AdicCompletion.evalₐ (maximalIdeal R) n b) := by
  -- Proof comment: reduce the mapped-completion coordinate to the inverse finite-stage comparison,
  -- then compute scalar multiplication by the stage image of `b` on the class of `1`.
  rw [primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv]
  change
    AdicCompletion.evalₐ
        (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) n
        (primeQuotient_moduleCompletion_to_ringCompletion p
          (b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1)) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  rw [AdicCompletion.evalₐ]
  change
    Ideal.Quotient.factor
        (show
          ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
              (⊤ : Ideal (R ⧸ p.asIdeal))) ≤
            (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n by
          simp)
        ((primeQuotient_moduleCompletion_to_ringCompletion p
          (b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1)).val n) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  change
    Ideal.Quotient.factor
        (show
          ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n •
              (⊤ : Ideal (R ⧸ p.asIdeal))) ≤
            (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n by
          simp)
        ((primeQuotient_ringCompletionStageLinearEquivModuleStage p n).symm
          ((b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1).val n)) =
      (Ideal.quotientMapₐ
        ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
        (Algebra.ofId R (R ⧸ p.asIdeal))
        (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
        (AdicCompletion.evalₐ (maximalIdeal R) n b)
  rw [primeQuotient_moduleCompletion_smul_one_val]
  exact primeQuotient_stage_factor_smulOne_eq_quotientMap p n
    (AdicCompletion.evalₐ (maximalIdeal R) n b)

/-- Helper for Chap10 Lemma 10 162 11: after the maximal-vs-mapped comparison, the completed
quotient map agrees with the tensor/module completion comparison on representatives. -/
private theorem completionQuotient_toMappedPrimeQuotientCompletion_mk
    (p : PrimeSpectrum R) (b : RCompletion) :
    completionQuotient_toMappedPrimeQuotientCompletion p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b) =
      primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv p
        (b • AdicCompletion.of (maximalIdeal R) (R ⧸ p.asIdeal) 1) := by
  -- Proof comment: compare both sides at each mapped-maximal-ideal finite quotient stage.
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [completionQuotient_toMappedPrimeQuotientCompletion, RingHom.comp_apply,
    completionQuotient_toPrimeQuotientCompletion, Ideal.Quotient.lift_mk]
  have hleft :
      AdicCompletion.evalₐ
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) n
          ((primeQuotient_maximalIdealCompletionAlgEquivMadicCompletion p).toRingEquiv.toRingHom
            (maximalIdealCompletionMap (algebraMap R (R ⧸ p.asIdeal)) b)) =
        (Ideal.quotientMapₐ
          ((Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R)) ^ n)
          (Algebra.ofId R (R ⧸ p.asIdeal))
          (primeQuotient_pow_maximalIdeal_le_comap_pow_map p n))
          (AdicCompletion.evalₐ (maximalIdeal R) n b) := by
        simpa [primeQuotient_maximalIdealCompletionAlgEquivMadicCompletion] using
          maximalIdealCompletionAlgEquivMadicCompletion_eval_base
            (R := R) (S := R ⧸ p.asIdeal)
            ((maximalIdeal R).fg_of_isNoetherianRing)
            (prime_quotient_closedPoint_quotient_finite p) n b
  exact hleft.trans
    (primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv_smul_one_eval
      p n b).symm

/-- Helper for Chap10 Lemma 10 162 11: the multiplicative quotient-to-mapped-completion map has
the same underlying function as the canonical linear equivalence. -/
private theorem completionQuotient_toMappedPrimeQuotientCompletion_eq_linearEquiv
    (p : PrimeSpectrum R) :
    (completionQuotient_toMappedPrimeQuotientCompletion p :
      (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) →
        AdicCompletion
          (Ideal.map (algebraMap R (R ⧸ p.asIdeal)) (maximalIdeal R))
          (R ⧸ p.asIdeal)) =
      primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv p := by
  -- Proof comment: both maps out of the quotient are determined by representatives from
  -- `RCompletion`; the representative computation has already normalized both finite-stage
  -- coordinates.
  funext x
  refine Quotient.inductionOn' x ?_
  intro b
  change
    completionQuotient_toMappedPrimeQuotientCompletion p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b) =
      primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b)
  rw [completionQuotient_toMappedPrimeQuotientCompletion_mk,
    primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv,
    LinearEquiv.trans_apply]
  exact congrArg (primeQuotient_moduleCompletion_mappedMaximalCompletion_linearEquiv p)
    (prime_quotient_completionQuotient_moduleCompletion_linearEquiv_mk p b).symm

/-- Helper for Chap10 Lemma 10 162 11: every element killed by the completed quotient map lies in
the extended prime `pR^∧`. -/
lemma maximalIdealCompletionMap_primeQuotient_ker_le
    (p : PrimeSpectrum R) :
    RingHom.ker (maximalIdealCompletionMap (algebraMap R (R ⧸ p.asIdeal))) ≤
      Ideal.map (algebraMap R RCompletion) p.asIdeal := by
  -- Proof comment: instead of using adic exactness directly, pass to the quotient and compose with
  -- the mapped-completion comparison, which is injective because it is the linear equivalence above.
  intro b hb
  have hbzero :
      maximalIdealCompletionMap (algebraMap R (R ⧸ p.asIdeal)) b = 0 := by
    simpa [RingHom.mem_ker] using hb
  have hmap_zero :
      completionQuotient_toMappedPrimeQuotientCompletion p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b) = 0 := by
    rw [completionQuotient_toMappedPrimeQuotientCompletion, RingHom.comp_apply,
      completionQuotient_toPrimeQuotientCompletion, Ideal.Quotient.lift_mk]
    exact (congrArg
      (primeQuotient_maximalIdealCompletionAlgEquivMadicCompletion p).toRingEquiv.toRingHom
      hbzero).trans (map_zero _)
  have hlin_zero :
      primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv p
        (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b) = 0 := by
    rw [← congrFun (completionQuotient_toMappedPrimeQuotientCompletion_eq_linearEquiv p)
      (Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b)]
    exact hmap_zero
  have hquot_zero :
      Ideal.Quotient.mk (Ideal.map (algebraMap R RCompletion) p.asIdeal) b = 0 := by
    exact
      (primeQuotient_completionQuotient_mappedMaximalCompletion_linearEquiv p).map_eq_zero_iff.mp
        hlin_zero
  exact (Ideal.Quotient.eq_zero_iff_mem).mp hquot_zero

/-- Helper for Chap10 Lemma 10 162 11: the factor map from `R^∧ / pR^∧` to the completion of
`R ⧸ p` is injective. -/
lemma completionQuotient_toPrimeQuotientCompletion_injective
    (p : PrimeSpectrum R) :
    Function.Injective (completionQuotient_toPrimeQuotientCompletion p) := by
  -- Proof comment: the quotient map is injective exactly because the completed quotient map has
  -- kernel `pR^∧`.
  exact RingHom.lift_injective_of_ker_le_ideal
    (Ideal.map (algebraMap R RCompletion) p.asIdeal)
    (completionQuotient_toPrimeQuotientCompletion_ker p)
    (maximalIdealCompletionMap_primeQuotient_ker_le p)

/-- Helper for Chap10 Lemma 10 162 11: the extended prime `pR^∧` remains a proper ideal. -/
lemma completionQuotient_ideal_ne_top (p : PrimeSpectrum R) :
    Ideal.map (algebraMap R RCompletion) p.asIdeal ≠ ⊤ := by
  -- Proof comment: faithful flatness sends proper ideals to proper extended submodules, so a
  -- proper prime ideal cannot extend to the unit ideal in `R^∧`.
  have hff : RingHom.FaithfullyFlat (algebraMap R RCompletion) :=
    maximalIdeal_adicCompletion_algebraMap_faithfullyFlat R
  have hffmod : Module.FaithfullyFlat R RCompletion :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hff
  intro htop
  have hsmul : p.asIdeal • (⊤ : Submodule R RCompletion) = ⊤ := by
    rw [Ideal.smul_top_eq_map (R := R) (S := RCompletion) (I := p.asIdeal), htop]
    rfl
  have hsource_top : p.asIdeal = ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R RCompletion).1 hffmod).2
      p.asIdeal hsmul
  exact p.isPrime.ne_top hsource_top

/-- Helper for Chap10 Lemma 10 162 11: the maximal-ideal completion of a Noetherian local ring is
complete local. -/
lemma completion_isCompleteLocalRing_local :
    IsCompleteLocalRing RCompletion := by
  -- Route correction: the previous proof relied on the unavailable owner theorem
  -- `maximalIdealCompletion_isCompleteLocalRing`; rebuild the same complete-local structure here
  -- from the evaluation-kernel maximality argument and adic completeness of the completion.
  -- Proof comment: first show the extended maximal ideal is maximal by identifying it with the
  -- kernel of the first evaluation map on the completion.
  have hmax :
      Ideal.IsMaximal (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) := by
    letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
    letI : Field (R ⧸ (maximalIdeal R) ^ 1) := by
      let e : R ⧸ (maximalIdeal R) ^ 1 ≃+* R ⧸ maximalIdeal R :=
        Ideal.quotEquivOfEq (pow_one (maximalIdeal R))
      exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
    have hker :
        Ideal.map (algebraMap R RCompletion) (maximalIdeal R) =
          RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1) := by
      simpa [pow_one] using
        completionIdeal_pow_eq_ker_evalₐ (maximalIdeal R)
          (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) 1
    simpa [hker] using
      (RingHom.ker_isMaximal_of_surjective
        (AdicCompletion.evalₐ (maximalIdeal R) 1)
        (AdicCompletion.surjective_evalₐ (maximalIdeal R) 1) :
          Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal R) 1)))
  let hcomplete :
      IsAdicComplete (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) RCompletion :=
    (adicCompletion_isNoetherian_and_isAdicComplete (maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))).2
  letI : IsLocalRing RCompletion := by
    -- Proof comment: a ring complete for a maximal ideal of definition is local.
    exact @isLocalRing_of_isAdicComplete_maximal RCompletion _
      (Ideal.map (algebraMap R RCompletion) (maximalIdeal R)) hmax hcomplete
  have hmap :
      Ideal.map (algebraMap R RCompletion) (maximalIdeal R) = maximalIdeal RCompletion := by
    -- Proof comment: once locality is installed, the maximal ideal is unique.
    exact IsLocalRing.eq_maximalIdeal hmax
  have hintrinsic :
      IsAdicComplete (maximalIdeal RCompletion) RCompletion := by
    -- Proof comment: rewrite adic completeness from the extended maximal ideal to the intrinsic
    -- maximal ideal of the completion.
    rw [← hmap]
    exact hcomplete
  exact { toIsAdicComplete := hintrinsic }

/-- Helper for Chap10 Lemma 10 162 11: the quotient `R^∧ / pR^∧` is a complete local ring. -/
lemma completionQuotient_isCompleteLocalRing (p : PrimeSpectrum R) :
    IsCompleteLocalRing (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
  -- Proof comment: `R^∧` is already complete local, and the earlier quotient theorem preserves
  -- that owner structure across proper quotients.
  letI : IsNoetherianRing RCompletion :=
    adicCompletion_isNoetherianRing (R := R) (I := maximalIdeal R)
  letI : IsCompleteLocalRing RCompletion :=
    completion_isCompleteLocalRing_local (R := R)
  exact
    completeLocalQuotient_isCompleteLocalRing
      (R := RCompletion)
      (Ideal.map (algebraMap R RCompletion) p.asIdeal)
      (completionQuotient_ideal_ne_top p)

/-- Chap10 Lemma 10 162 11: analytically unramified prime quotients give reduced completed
quotients `R^∧ / pR^∧`. -/
lemma completionQuotient_isReduced_of_prime_isAnalyticallyUnramified
    (p : PrimeSpectrum R) (h_analytic : PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsReduced (RCompletion ⧸ Ideal.map (algebraMap R RCompletion) p.asIdeal) := by
  -- Proof comment: analytic unramifiedness gives reducedness of the genuine completion of
  -- `R ⧸ p`; the factor map transfers that reducedness back to `R^∧ / pR^∧`.
  letI : IsAnalyticallyUnramified (R ⧸ p.asIdeal) := by
    simpa [PrimeSpectrum.IsAnalyticallyUnramified] using h_analytic
  have hredTarget :
      IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal)) :=
    (IsAnalyticallyUnramified.completion_isReduced :
      IsReduced (AdicCompletion (maximalIdeal (R ⧸ p.asIdeal)) (R ⧸ p.asIdeal)))
  exact @isReduced_of_injective _ _ _ _ _ _ _
    (completionQuotient_toPrimeQuotientCompletion p)
    (completionQuotient_toPrimeQuotientCompletion_injective p)
    hredTarget

/-- Helper for Lemma 10.162.11: the completion of a Noetherian local ring is Noetherian. -/
lemma completion_isNoetherianRing :
    IsNoetherianRing RCompletion := by
  -- Proof comment: this is exactly the chapter-level noetherianity theorem for adic completions,
  -- specialized to the maximal ideal of the local ring `R`.
  exact adicCompletion_isNoetherianRing (R := R) (I := maximalIdeal R)

/-- Consequence of Chap10 Lemma 10 162 11: if `R` is a Noetherian local ring, `p` is an analytically
unramified prime
of `R` such that `R_p` is a discrete valuation ring, then for every associated prime `q` of the
completed quotient `R^∧ / pR^∧` the localization `(R^∧)_q` is a discrete valuation ring. -/
-- Proof sketch: analytically unramified means precisely that the quotient `R / p` has reduced
-- completion, equivalently that `R^∧ / pR^∧` is reduced. Therefore any associated prime `q` of
-- this quotient is
-- minimal over `pR^∧`, so the maximal ideal of `(R^∧)_q` is generated by the image of `p`. Choose
-- an element of `R` generating `pR_p`; its image then generates the maximal ideal after passing to
-- `(R^∧)_q`. Faithful flatness of `R → R^∧` makes that generator a nonzerodivisor, so the local
-- ring `(R^∧)_q` is a one-dimensional local domain with principal maximal ideal, hence a DVR.
@[stacks 032Z]
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

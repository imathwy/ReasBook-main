import Mathlib
import stacks_proof.stacks_project.Chap09.Lemma_9_26_11
import stacks_proof.stacks_project.Chap10.Lemma_10_25_2
import stacks_proof.stacks_project.Chap10.Proposition_10_162_15_Nagata

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open IntermediateField

/-
Domain triage: this file is in the commutative algebra of Nagata and universally Japanese rings,
with the target construction the integral closure of a reduced essentially finite type algebra.

Sampled owner API in this domain:
- `NagataRing`, the source-facing owner from `Definition_10_162_1`;
- `UniversallyJapaneseRing`, the core owner abstraction already present upstream in the chapter;
- `UniversallyJapaneseRing.finiteType_algebra_isN2Ring`, the owner-side `N-2` API for finite type
  domains;
- `IsN2Ring.integralClosure_finite`, the canonical finite-normalization field for finite
  fraction-field extensions;
- the project instance `[NagataRing R] → [UniversallyJapaneseRing R]` from
  `Proposition_10_162_15_Nagata`, which supplies the source-to-owner bridge for the theorem below.

Source/core/bridge triage for the declarations below:
- `integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced` is `source-facing`, since
  Lemma 10.162.2 is stated for Nagata rings;
- `UniversallyJapaneseRing`, `IsN2Ring`, and `integralClosure` are the `core/canonical` owners;
- the owner-level bridge is the existing instance `[NagataRing R] → [UniversallyJapaneseRing R]`,
  reused directly inside the theorem rather than through a parallel local wrapper.

Primitive data: the rings `R`, `S`, the `R`-algebra structure on `S`, and the hypotheses
`Algebra.EssFiniteType R S` and `IsReduced S`.
Derived API: finiteness of `integralClosure R S`.
-/

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.EssFiniteType R S] [IsReduced S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

local instance (q : minimalPrimes S) : q.1.IsPrime := Ideal.minimalPrimes_isPrime q.2

/-- Helper for Lemma 10.162.2: the kernel quotient `R / ker(R → S_q)` maps canonically to the
minimal-prime localization `S_q`. -/
noncomputable abbrev kernelQuotientToLocalizationAtPrime (q : minimalPrimes S) :
    R ⧸ RingHom.ker (algebraMap R (Localization.AtPrime q.1)) →+* Localization.AtPrime q.1 :=
  RingHom.kerLift (algebraMap R (Localization.AtPrime q.1))

/-- Helper for Chap10 Lemma 10 162 2: the minimal-prime localization carries the canonical algebra
structure over the quotient by the kernel of `R → S_q`. -/
noncomputable instance kernelQuotientToLocalizationAtPrimeAlgebra (q : minimalPrimes S) :
    Algebra
      (R ⧸ RingHom.ker (algebraMap R (Localization.AtPrime q.1)))
      (Localization.AtPrime q.1) :=
  (kernelQuotientToLocalizationAtPrime (R := R) (S := S) q).toAlgebra

omit [Algebra.EssFiniteType R S] [IsReduced S] in
/-- Helper for Lemma 10.162.2: on quotient representatives, the kernel-quotient map to the factor
field is just the localization map. -/
@[simp]
lemma kernelQuotientToLocalizationAtPrime_mk (q : minimalPrimes S) (x : R) :
    kernelQuotientToLocalizationAtPrime (R := R) (S := S) q
        (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.AtPrime q.1))) x) =
      algebraMap R (Localization.AtPrime q.1) x := by
  exact RingHom.kerLift_mk (f := algebraMap R (Localization.AtPrime q.1)) x

/-- Helper for Lemma 10.162.2: if an `R`-algebra map factors through its kernel quotient, then an
element integral over `R` is integral over that quotient as well. -/
lemma integral_over_ker_quotient
    {A : Type*} [CommRing A] [Algebra R A]
    [Algebra (R ⧸ RingHom.ker (algebraMap R A)) A]
    (hcomp :
      (algebraMap (R ⧸ RingHom.ker (algebraMap R A)) A).comp
          (Ideal.Quotient.mk (RingHom.ker (algebraMap R A))) =
        algebraMap R A)
    (x : integralClosure R A) :
    IsIntegral (R ⧸ RingHom.ker (algebraMap R A)) (x : A) := by
  -- Transport the original integrality witness across the factorization through the kernel
  -- quotient.
  simpa using
    (IsIntegral.map_of_comp_eq
      (φ := Ideal.Quotient.mk (RingHom.ker (algebraMap R A)))
      (ψ := RingHom.id A) hcomp x.2)

/-- Helper for Lemma 10.162.2: over a domain, an element integral over the domain lies in the
relative algebraic closure over its fraction field. -/
lemma isIntegral_mem_algebraicClosure_fractionRing
    {A : Type*} {K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [FaithfulSMul A K] [Algebra (FractionRing A) K]
    [IsScalarTower A (FractionRing A) K] {x : K} (hx : IsIntegral A x) :
    x ∈ algebraicClosure (FractionRing A) K := by
  have hx_alg_A : IsAlgebraic A x := hx.isAlgebraic
  have hx_alg_frac : IsAlgebraic (FractionRing A) x := by
    exact (IsFractionRing.isAlgebraic_iff A (FractionRing A) K).mp hx_alg_A
  -- Membership in the relative algebraic closure is exactly algebraicity over the fraction field.
  exact mem_algebraicClosure_iff.mpr hx_alg_frac

/-- Helper for Lemma 10.162.2: integrality in the ambient field and in an intermediate field agree
for the same element. -/
lemma intermediateField_mem_integralClosure_of_isIntegral
    {A : Type*} {F : Type*} {K : Type*}
    [CommRing A] [Field F] [Field K] [Algebra A F] [Algebra A K] [Algebra F K]
    [IsScalarTower A F K]
    (L : IntermediateField F K) {x : L} (hx : IsIntegral A (x : K)) :
    x ∈ integralClosure A L := by
  -- Reinterpret the ambient-field integrality statement on the same element of `L`.
  change IsIntegral A x
  exact (IntermediateField.coe_isIntegral_iff (R := A) (K := F) (L := K) (S := L)).mp hx

/-- Helper for Lemma 10.162.2: a named finite intermediate field over the fraction field of an
`N-2` domain has finite integral closure over the domain. -/
lemma isN2Ring_integralClosure_finite_of_finiteDimensional_intermediateField
    {A : Type u} [CommRing A] [IsDomain A]
    {K : Type v} [Field K] [Algebra A K] [Algebra (FractionRing A) K]
    [IsScalarTower A (FractionRing A) K] [IsN2Ring A]
    (T : IntermediateField (FractionRing A) K)
    [FiniteDimensional (FractionRing A) T] :
    Module.Finite A (integralClosure A T) := by
  -- The owner theorem already handles arbitrary finite extensions once the intermediate field is
  -- used as the ambient carrier.
  exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := A) (L := T)

/-- Helper for Chap10 Lemma 10 162 2: codrestrict the ambient inclusion of `integralClosure A K`
to the intermediate field `T` when every integral element already lies in `T`. -/
noncomputable def integralClosureToIntermediateField
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T) :
    integralClosure A K →ₐ[A] T where
  toRingHom := RingHom.codRestrict ((integralClosure A K).val : integralClosure A K →+* K) T hmem
  commutes' r := by
    apply Subtype.ext
    change ((integralClosure A K).val : integralClosure A K →+* K) (algebraMap A (integralClosure A K) r) =
      algebraMap A K r
    simp

/-- Helper for Chap10 Lemma 10 162 2: the codrestricted map to `T` does not change the underlying
element of `K`. -/
@[simp]
lemma integralClosureToIntermediateField_coe
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T)
    (x : integralClosure A K) :
    ((integralClosureToIntermediateField (A := A) (K := K) T hmem x : T) : K) = (x : K) := by
  simpa [integralClosureToIntermediateField]
    using RingHom.codRestrict_apply
      (((integralClosure A K).val : integralClosure A K →+* K)) T hmem x

/-- Helper for Chap10 Lemma 10 162 2: the same codrestricted inclusion lands in the integral
closure inside `T`. -/
noncomputable def integralClosureToIntegralClosureIntermediateField
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T) :
    integralClosure A K →ₐ[A] integralClosure A T where
  toRingHom := RingHom.codRestrict
    ((integralClosureToIntermediateField (A := A) (K := K) T hmem).toRingHom)
    (integralClosure A T) fun y ↦ by
      -- The codrestricted element has the same underlying value in `K`, so its original
      -- integrality witness packages it into `integralClosure A T`.
      have hy :
          ((integralClosureToIntermediateField (A := A) (K := K) T hmem y : T) : K) = (y : K) :=
        integralClosureToIntermediateField_coe (A := A) (K := K) T hmem y
      exact intermediateField_mem_integralClosure_of_isIntegral (A := A) (F := FractionRing A)
        (K := K) T (x := integralClosureToIntermediateField (A := A) (K := K) T hmem y) <| by
          exact hy ▸ y.2
  commutes' r := by
    apply Subtype.ext
    simpa using
      (integralClosureToIntermediateField (A := A) (K := K) T hmem).commutes r

/-- Helper for Chap10 Lemma 10 162 2: the codrestricted map to `integralClosure A T` still has the
same underlying element of `K`. -/
@[simp]
lemma integralClosureToIntegralClosureIntermediateField_coe
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T)
    (x : integralClosure A K) :
    (((integralClosureToIntegralClosureIntermediateField (A := A) (K := K) T hmem x :
        integralClosure A T) : T) : K) = (x : K) := by
  simp [integralClosureToIntegralClosureIntermediateField,
    integralClosureToIntermediateField_coe (A := A) (K := K) T hmem x]

/-- Helper for Chap10 Lemma 10 162 2: the codrestricted map into `integralClosure A T` is
injective because it is the identity on the underlying elements of `K`. -/
lemma integralClosureToIntegralClosureIntermediateField_injective
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T) :
    Function.Injective
      (integralClosureToIntegralClosureIntermediateField (A := A) (K := K) T hmem) := by
  intro x y hxy
  -- Forget the codomain subtype back to `K`, where the map is literally the identity.
  apply Subtype.ext
  simpa using congrArg (fun z : integralClosure A T ↦ ((z : T) : K)) hxy

/-- Helper for Lemma 10.162.2: if every element integral over `A` in `K` already lies in a named
intermediate field `T`, then finiteness of the integral closure in `T` descends to finiteness of
the integral closure in `K`. -/
lemma moduleFinite_integralClosure_of_mem_intermediateField
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [FaithfulSMul A K]
    [Algebra (FractionRing A) K] [IsScalarTower A (FractionRing A) K]
    (T : IntermediateField (FractionRing A) K)
    (hmem : ∀ x : integralClosure A K, (x : K) ∈ T)
    [Module.Finite A (integralClosure A T)] :
    Module.Finite A (integralClosure A K) := by
  let f := integralClosureToIntegralClosureIntermediateField (A := A) (K := K) T hmem
  -- The codrestricted map lands in the finite `A`-module `integralClosure A T` and stays
  -- injective after forgetting to `K`, so finiteness descends along the inclusion.
  exact Module.Finite.of_injective f.toLinearMap
    (integralClosureToIntegralClosureIntermediateField_injective (A := A) (K := K) T hmem)

omit [Algebra.EssFiniteType R S] in
/-- Helper for Chap10 Lemma 10 162 2: the kernel of the map from `R` to one minimal-prime
localization is prime because that localization is a field. -/
lemma ker_algebraMap_localizationAtPrime_isPrime
    (q : minimalPrimes S) :
    (RingHom.ker (algebraMap R (Localization.AtPrime q.1))).IsPrime := by
  let Kq := Localization.AtPrime q.1
  letI : Field Kq := (isField_localizationAtPrime_of_minimalPrime (R := S) q).toField
  -- Kernels of maps to fields are prime.
  exact RingHom.ker_isPrime (algebraMap R Kq)

omit [Algebra.EssFiniteType R S] [IsReduced S] in
/-- Helper for Chap10 Lemma 10 162 2: the quotient map to the minimal-prime localization
recovers the original map `R → S_q` after precomposing with the quotient projection. -/
lemma kernelQuotientToLocalizationAtPrime_comp
    (q : minimalPrimes S) :
    (kernelQuotientToLocalizationAtPrime (R := R) (S := S) q).comp
        (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.AtPrime q.1)))) =
      algebraMap R (Localization.AtPrime q.1) := by
  ext x
  -- On representatives, the quotient map is exactly the localization map.
  exact kernelQuotientToLocalizationAtPrime_mk (R := R) (S := S) q x

/-- Helper for Chap10 Lemma 10 162 2: after quotienting by the kernel of `R → S_q`, the
normalization inside the field `S_q` is finite over the quotient domain. -/
lemma moduleFinite_integralClosure_kernelQuotient_localizationAtPrime
    [NagataRing R] (q : minimalPrimes S) :
    Module.Finite
      (R ⧸ RingHom.ker (algebraMap R (Localization.AtPrime q.1)))
      (integralClosure
        (R ⧸ RingHom.ker (algebraMap R (Localization.AtPrime q.1)))
        (Localization.AtPrime q.1)) := by
  let Kq := Localization.AtPrime q.1
  letI : Field Kq := (isField_localizationAtPrime_of_minimalPrime (R := S) q).toField
  let Iq : Ideal R := RingHom.ker (algebraMap R Kq)
  let Rq := R ⧸ Iq
  letI : Iq.IsPrime := ker_algebraMap_localizationAtPrime_isPrime (R := R) (S := S) q
  letI : IsDomain Rq := Ideal.Quotient.isDomain Iq
  letI : IsScalarTower R Rq Kq := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    change
      (kernelQuotientToLocalizationAtPrime (R := R) (S := S) q)
          (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.AtPrime q.1))) x) =
        algebraMap R (Localization.AtPrime q.1) x
    exact kernelQuotientToLocalizationAtPrime_mk (R := R) (S := S) q x
  letI : FaithfulSMul Rq Kq :=
    (faithfulSMul_iff_algebraMap_injective Rq Kq).mpr <|
      RingHom.kerLift_injective (algebraMap R Kq)
  letI : Algebra.EssFiniteType S Kq := inferInstance
  letI : Algebra.EssFiniteType R Kq := Algebra.EssFiniteType.comp R S Kq
  letI : Algebra.EssFiniteType Rq Kq := Algebra.EssFiniteType.of_comp R Rq Kq
  letI : Algebra.EssFiniteType (FractionRing Rq) Kq :=
    Algebra.EssFiniteType.of_comp Rq (FractionRing Rq) Kq
  let Lq : IntermediateField (FractionRing Rq) Kq := algebraicClosure (FractionRing Rq) Kq
  letI : FiniteDimensional (FractionRing Rq) Lq :=
    finiteDimensional_algebraicClosure (k := FractionRing Rq) (K := Kq)
  letI : Module.Finite Rq (integralClosure Rq Lq) :=
    isN2Ring_integralClosure_finite_of_finiteDimensional_intermediateField
      (A := Rq) (K := Kq) Lq
  -- Every element integral over the quotient domain already lies in the algebraic closure.
  exact moduleFinite_integralClosure_of_mem_intermediateField (A := Rq) (K := Kq) Lq fun x ↦
    isIntegral_mem_algebraicClosure_fractionRing (A := Rq) (K := Kq) x.2

/-- Helper for Lemma 10.162.2: the integral closure over `R` in one minimal-prime localization is
finite over `R`. -/
lemma moduleFinite_integralClosure_localizationAtPrime_of_minimalPrime
    [NagataRing R] (q : minimalPrimes S) :
    Module.Finite R (integralClosure R (Localization.AtPrime q.1)) := by
  -- Route correction: keep the source proof on the single minimal-prime factor `Kq = S_q`,
  -- first passing to `Rq = R / ker(R → Kq)` and its algebraic closure `Lq`, and only then
  -- descending finiteness back to `integralClosure R Kq` by injectivity of the codrestricted map.
  let Kq := Localization.AtPrime q.1
  letI : Field Kq := (isField_localizationAtPrime_of_minimalPrime (R := S) q).toField
  let Iq : Ideal R := RingHom.ker (algebraMap R Kq)
  let Rq := R ⧸ Iq
  letI : Iq.IsPrime := ker_algebraMap_localizationAtPrime_isPrime (R := R) (S := S) q
  letI : IsDomain Rq := Ideal.Quotient.isDomain Iq
  letI : IsScalarTower R Rq Kq := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    change
      (kernelQuotientToLocalizationAtPrime (R := R) (S := S) q)
          (Ideal.Quotient.mk (RingHom.ker (algebraMap R (Localization.AtPrime q.1))) x) =
        algebraMap R (Localization.AtPrime q.1) x
    exact kernelQuotientToLocalizationAtPrime_mk (R := R) (S := S) q x
  letI : FaithfulSMul Rq Kq :=
    (faithfulSMul_iff_algebraMap_injective Rq Kq).mpr <|
      RingHom.kerLift_injective (algebraMap R Kq)
  letI : Module.Finite Rq (integralClosure Rq Kq) :=
    moduleFinite_integralClosure_kernelQuotient_localizationAtPrime (R := R) (S := S) q
  have hKq_normalization_R :
      Module.Finite R ((integralClosure Rq Kq).restrictScalars R) := by
    -- Finiteness over the quotient descends to finiteness over `R` because `Rq` itself is finite.
    simpa using (Module.Finite.trans Rq (integralClosure Rq Kq) :
      Module.Finite R (integralClosure Rq Kq))
  have hcomp :
      (algebraMap Rq Kq).comp (Ideal.Quotient.mk Iq) = algebraMap R Kq := by
    simpa [Kq, Iq, Rq] using kernelQuotientToLocalizationAtPrime_comp (R := R) (S := S) q
  have hle :
      integralClosure R Kq ≤ (integralClosure Rq Kq).restrictScalars R := by
    intro x hx
    -- Reuse the original integral witness after factoring `R → Kq` through its kernel quotient.
    change IsIntegral Rq x
    exact integral_over_ker_quotient (R := R) (A := Kq) hcomp ⟨x, hx⟩
  let f : integralClosure R Kq →ₗ[R] (integralClosure Rq Kq).restrictScalars R :=
    (Subalgebra.inclusion hle).toLinearMap
  -- The source normalization is a submodule of the finite `Rq`-normalization, so finiteness
  -- descends along the inclusion.
  exact Module.Finite.of_injective f (Subalgebra.inclusion_injective (h := hle))

omit [Algebra.EssFiniteType R S] [IsReduced S] in
/-- Helper for Lemma 10.162.2: an element integral over `R` in `S` stays integral in each
minimal-prime localization. -/
lemma map_integralClosure_to_minimalPrime_localization_mem
    (q : minimalPrimes S) (x : integralClosure R S) :
    IsScalarTower.toAlgHom R S (Localization.AtPrime q.1) x ∈
      integralClosure R (Localization.AtPrime q.1) := by
  -- Map the defining integrality witness along the scalar tower `R → S → S_q`.
  change IsIntegral R (IsScalarTower.toAlgHom R S (Localization.AtPrime q.1) x)
  exact IsIntegral.map (IsScalarTower.toAlgHom R S (Localization.AtPrime q.1)) x.2

/-- Helper for Lemma 10.162.2: the coordinate map from the integral closure in `S` to the
integral closure in one minimal-prime localization. -/
noncomputable def integralClosure_to_minimalPrime_localization
    (q : minimalPrimes S) :
    integralClosure R S →ₐ[R] integralClosure R (Localization.AtPrime q.1) :=
  ((IsScalarTower.toAlgHom R S (Localization.AtPrime q.1)).restrictDomain
      (integralClosure R S)).codRestrict
    (integralClosure R (Localization.AtPrime q.1))
    (map_integralClosure_to_minimalPrime_localization_mem (R := R) (S := S) q)

/-- Helper for Lemma 10.162.2: the integral closure in `S` embeds into the product of the
integral closures in the minimal-prime localizations. -/
noncomputable def integralClosure_embedding_into_product_of_minimalPrime_localizations :
    integralClosure R S →ₗ[R]
      ∀ q : minimalPrimes S, integralClosure R (Localization.AtPrime q.1) :=
  LinearMap.pi fun q ↦
    (integralClosure_to_minimalPrime_localization (R := R) (S := S) q).toLinearMap

omit [Algebra.EssFiniteType R S] in
/-- Helper for Lemma 10.162.2: the product map on integral closures is injective because the
ambient map `S → ∏_q S_q` is injective for a reduced ring. -/
lemma integralClosure_embedding_into_product_of_minimalPrime_localizations_injective :
    Function.Injective
      (integralClosure_embedding_into_product_of_minimalPrime_localizations
        (R := R) (S := S)) := by
  intro x y hxy
  have hambient :
      algebraMap S (∀ q : minimalPrimes S, Localization.AtPrime q.1) x =
        algebraMap S (∀ q : minimalPrimes S, Localization.AtPrime q.1) y := by
    -- Evaluate the equality of product-valued integral-closure coordinates and forget subtypes.
    ext q
    exact congrArg
      (fun z ↦ ((z q : integralClosure R (Localization.AtPrime q.1)) :
        Localization.AtPrime q.1)) hxy
  have hinj :
      Function.Injective (algebraMap S (∀ q : minimalPrimes S, Localization.AtPrime q.1)) :=
    (algebraMap_embedding_into_product_of_fields (R := S)).1
  -- The ambient reduced-ring embedding is injective, so the restricted map is injective as well.
  exact Subtype.ext (hinj hambient)

/-- Chap10 Lemma 10 162 2: if `R` is a Nagata ring and `S` is a reduced `R`-algebra essentially of
finite type, then the integral closure of `R` in `S` is finite over `R`. -/
-- Proof sketch: write the reduced essentially-finite-type algebra `S` as a subring of the product
-- of the residue fields at its finitely many minimal primes; for each factor, use the Nagata
-- hypothesis on the corresponding quotient domain of `R` to obtain finiteness of the integral
-- closure, then combine these finitely many finite modules inside the product. The canonical
-- owner bridge `[NagataRing R] → [UniversallyJapaneseRing R]` from Proposition `10.162.15` is
-- reused directly in the proof.
@[stacks 03GH]
theorem integralClosure_finite_of_nagataRing_of_essFiniteType_of_isReduced
    [NagataRing R] :
    Module.Finite R (integralClosure R S) := by
  haveI : UniversallyJapaneseRing.{u, v} R := inferInstance
  letI : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  letI : Fintype (minimalPrimes S) := (minimalPrimes.finite_of_isNoetherianRing (R := S)).fintype
  letI :
      ∀ q : minimalPrimes S,
        Module.Finite R (integralClosure R (Localization.AtPrime q.1)) :=
    fun q ↦ moduleFinite_integralClosure_localizationAtPrime_of_minimalPrime
      (R := R) (S := S) q
  let f := integralClosure_embedding_into_product_of_minimalPrime_localizations (R := R) (S := S)
  have hf :
      Function.Injective
        (integralClosure_embedding_into_product_of_minimalPrime_localizations
          (R := R) (S := S)) :=
    integralClosure_embedding_into_product_of_minimalPrime_localizations_injective
      (R := R) (S := S)
  letI :
      Module.Finite R
        (∀ q : minimalPrimes S, integralClosure R (Localization.AtPrime q.1)) := by
    infer_instance
  -- Descend finiteness from the finite product of factor normalizations.
  exact Module.Finite.of_injective f hf

end

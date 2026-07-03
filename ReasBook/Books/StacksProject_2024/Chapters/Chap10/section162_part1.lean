import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_162_1 (from Chap10) -/
universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: commutative algebra of Japanese and Nagata finiteness conditions on rings;
- sampled owner abstractions of the same kind in the project:
  - `IsN1Ring` and `IsN2Ring` from `Definition_10_161_1`,
  - `UniversallyCatenaryRing` from `Definition_10_105_3`,
  - `IsJ2Ring` from `Chap15/Definition_15_47_1`,
  - `IsQuasiExcellentRing` from `Chap15/Definition_15_52_1`.

Best owner abstraction:
- `UniversallyJapaneseRing` is the source-facing owner for the finite-type-domain `N-2` property;
- `NagataRing` is the source-facing owner for the Noetherian-plus-prime-quotient `N-2` property;
- `IsN2Ring` remains the core/canonical owner reused inside those two definitions.

Primitive data vs derived API:
- primitive data for `UniversallyJapaneseRing`: the `N-2` owner on each finite type domain
  `R`-algebra;
- primitive data for `NagataRing`: Noetherianity together with the `N-2` owner on each prime
  quotient;
- derived API: all later bridges such as `[NagataRing R] → [UniversallyJapaneseRing R]` and
  finite-type stability belong downstream, not as extra fields here.
-/

/-- Definition 10.162.1 (1): A ring is universally Japanese if every finite type `R`-algebra
that is a domain is `N-2`, i.e. Japanese. -/
class UniversallyJapaneseRing : Prop where
  /-- Every finite type domain over a universally Japanese ring is `N-2`. -/
  finiteType_algebra_isN2Ring {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [IsDomain S] : IsN2Ring S

attribute [instance] UniversallyJapaneseRing.finiteType_algebra_isN2Ring

/-- Definition 10.162.1 (2): A Nagata ring is a Noetherian ring whose quotient by every prime
ideal is `N-2`. -/
class NagataRing : Prop extends IsNoetherianRing R where
  /-- The quotient of a Nagata ring by any prime ideal is `N-2`. -/
  quotient_isN2Ring (p : Ideal R) [p.IsPrime] : IsN2Ring (R ⧸ p)

attribute [instance] NagataRing.quotient_isN2Ring

end

/-! ### Lemma_10_162_2 (from Chap10) -/
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
  `Proposition_10_162_16`, which supplies the source-to-owner bridge for the theorem below.

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
    {A : Type*} [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [Algebra (FractionRing A) K]
    [IsScalarTower A (FractionRing A) K] [IsN2Ring A]
    (T : IntermediateField (FractionRing A) K)
    [FiniteDimensional (FractionRing A) T] :
    Module.Finite A (integralClosure A T) := by
  -- TODO: replay the `Definition_10_161_1.IsN2Ring.integralClosure_finite_of_finiteDimensional`
  -- `Shrink` transport explicitly on the carrier `↥T`, using direct `Shrink` instance names to
  -- avoid the deterministic `whnf` timeout on the generic theorem application.
  sorry

/-- Helper for Lemma 10.162.2: the integral closure over `R` in one minimal-prime localization is
finite over `R`. -/
lemma moduleFinite_integralClosure_localizationAtPrime_of_minimalPrime
    [NagataRing R] (q : minimalPrimes S) :
    Module.Finite R (integralClosure R (Localization.AtPrime q.1)) := by
  -- Route correction: keep the source proof on the single minimal-prime factor `Kq = S_q`,
  -- first passing to `Rq = R / ker(R → Kq)` and its algebraic closure `Lq`, and only then
  -- descending finiteness back to `integralClosure R Kq` by injectivity of the codrestricted map.
  -- TODO: after the previous helper is available, instantiate
  -- `Kq := Localization.AtPrime q.1`, `Rq := R ⧸ ker(R → Kq)`, and
  -- `Lq := algebraicClosure (FractionRing Rq) Kq`; then codrestrict the identity map on `Kq`
  -- from `integralClosure R Kq` into `integralClosure Rq Lq`, prove it injective by forgetting
  -- subtypes, and descend `Module.Finite` from the quotient-domain normalization.
  sorry

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

/-- Lemma 10.162.2: if `R` is a Nagata ring and `S` is a reduced `R`-algebra essentially of
finite type, then the integral closure of `R` in `S` is finite over `R`. -/
-- Proof sketch: write the reduced essentially-finite-type algebra `S` as a subring of the product
-- of the residue fields at its finitely many minimal primes; for each factor, use the Nagata
-- hypothesis on the corresponding quotient domain of `R` to obtain finiteness of the integral
-- closure, then combine these finitely many finite modules inside the product. The canonical
-- owner bridge `[NagataRing R] → [UniversallyJapaneseRing R]` from Proposition `10.162.16` is
-- reused directly in the proof.
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

/-! ### Lemma_10_162_3 (from Chap10) -/
universe u v w

section

variable (R : Type u) [CommRing R]

omit [CommRing R] in
/-- Helper for Lemma 10.162.3: an element integral over a base ring remains integral after
enlarging the base ring inside the same ambient field. -/
lemma map_integralClosure_to_larger_base_mem
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) (x : integralClosure R L) :
    f x ∈ integralClosure S M := by
  -- The defining monic polynomial over `R` still witnesses integrality over `S`.
  change IsIntegral S (f x)
  exact (IsIntegral.map f x.2).tower_top

omit [CommRing R] in
/-- Helper for Lemma 10.162.3: an algebra map between ambient fields restricts to a map between
the corresponding integral closures after enlarging the base ring. -/
noncomputable def map_integralClosure_to_larger_base
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) :
    integralClosure R L →ₐ[R] (integralClosure S M).restrictScalars R :=
  (f.restrictDomain (integralClosure R L)).codRestrict ((integralClosure S M).restrictScalars R)
    (map_integralClosure_to_larger_base_mem f)

omit [CommRing R] in
/-- Helper for Lemma 10.162.3: the restricted map on integral closures is injective whenever the
ambient field map is injective. -/
lemma map_integralClosure_to_larger_base_injective
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    {L : Type*} {M : Type*} [Field L] [Field M] [Algebra R L] [Algebra S M] [Algebra R M]
    [IsScalarTower R S M] (f : L →ₐ[R] M) (hf : Function.Injective f) :
    Function.Injective (map_integralClosure_to_larger_base (R := R) (S := S) f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg (fun z : integralClosure S M ↦ (z : M)) hxy)

/-- Helper for Lemma 10.162.3: a finite extension of the fraction field of a domain is the
fraction field of a module-finite intermediate `S`-subalgebra. -/
lemma exists_moduleFinite_subalgebra_with_fractionRing
    {S : Type v} [CommRing S] [IsDomain S]
    {L : Type w} [Field L] [Algebra (FractionRing S) L] [FiniteDimensional (FractionRing S) L]
    [Algebra S L] [IsScalarTower S (FractionRing S) L] :
    ∃ A : Subalgebra S L, Module.Finite S A ∧ IsFractionRing A L := by
  -- Route correction: instead of constructing a custom comparison with `FractionRing A`, use
  -- the denominator-cleared generators to make a finite `S`-subalgebra and then prove directly
  -- that the subfield generated by its image is all of `L`.
  obtain ⟨t, ht⟩ := IntermediateField.fg_top (FractionRing S) L
  obtain ⟨y, hy, h_integral⟩ := exists_integral_multiples S (FractionRing S) t
  let s : Set L := (fun x : L ↦ y • x) '' (t : Set L)
  let A : Subalgebra S L := Algebra.adjoin S s
  have hs_integral : ∀ z ∈ s, IsIntegral S z := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact h_integral x (by simpa using hx)
  have hA_finite : Module.Finite S A := by
    -- The cleared generators are integral over `S`, so adjoining them is module-finite.
    exact Algebra.finite_adjoin_of_finite_of_isIntegral ((t.finite_toSet).image _) hs_integral
  have hyL : algebraMap S L y ≠ 0 := by
    -- The common denominator stays nonzero in the ambient field.
    intro h
    exact hy (((algebraMap (FractionRing S) L).injective.comp
      (IsFractionRing.injective S (FractionRing S)))
      (by simpa [IsScalarTower.algebraMap_eq S (FractionRing S) L] using h))
  letI : IsDomain A := inferInstance
  let T : IntermediateField (FractionRing S) L :=
    { Subfield.closure (Set.range (algebraMap A L)) with
      algebraMap_mem' := by
        intro z
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective S z
        -- Every base-field coefficient is already a quotient of elements coming from `A`.
        rw [map_div₀]
        exact (Subfield.closure (Set.range (algebraMap A L))).div_mem
          (Subfield.subset_closure
            (show algebraMap (FractionRing S) L (algebraMap S (FractionRing S) a) ∈
                Set.range (algebraMap A L) from
              ⟨algebraMap S A a, by
                simp [A, IsScalarTower.algebraMap_eq S (FractionRing S) L]⟩))
          (Subfield.subset_closure
            (show algebraMap (FractionRing S) L (algebraMap S (FractionRing S) b) ∈
                Set.range (algebraMap A L) from
              ⟨algebraMap S A b, by
                simp [A, IsScalarTower.algebraMap_eq S (FractionRing S) L]⟩)) }
  have ht_subset : (t : Set L) ⊆ T := by
    intro x hx
    change x ∈ T.toSubfield
    have hscaled : y • x ∈ T.toSubfield := by
      -- The cleared generator lies in `A`, hence in the generated subfield.
      exact Subfield.subset_closure
        (show y • x ∈ Set.range (algebraMap A L) from
          ⟨⟨y • x, Algebra.subset_adjoin ⟨x, hx, rfl⟩⟩, by simp [A]⟩)
    have hy_mem : algebraMap S L y ∈ T.toSubfield := by
      exact Subfield.subset_closure
        (show algebraMap S L y ∈ Set.range (algebraMap A L) from
          ⟨algebraMap S A y, by simp [A]⟩)
    have hx_div : (y • x) / algebraMap S L y = x := by
      rw [Algebra.smul_def, mul_comm, mul_div_assoc, div_self hyL]
      simp
    simpa [hx_div] using T.toSubfield.div_mem hscaled hy_mem
  have hT_top : T = ⊤ := by
    -- The original field generators all lie in `T`, so `T` must be the whole field.
    have hle : IntermediateField.adjoin (FractionRing S) (t : Set L) ≤ T :=
      IntermediateField.adjoin_le_iff.mpr ht_subset
    rw [ht] at hle
    exact top_le_iff.mp hle
  have hclosure_top : Subfield.closure (Set.range (algebraMap A L)) = ⊤ := by
    simpa [T] using congrArg (fun U : IntermediateField (FractionRing S) L ↦ U.toSubfield) hT_top
  have hA_fraction : IsFractionRing A L := by
    letI : Field (FractionRing A) := FractionRing.field (A := A)
    have hA_inj : Function.Injective (algebraMap A L) := by
      intro a b hab
      exact Subtype.ext hab
    let f : FractionRing A →+* L := IsFractionRing.lift (g := algebraMap A L) hA_inj
    have hf_range : f.fieldRange = ⊤ := by
      calc
        f.fieldRange = Subfield.closure (Set.range (algebraMap A L)) := by
          simpa [f] using
            (IsFractionRing.lift_fieldRange (A := A) (K := FractionRing A) (L := L)
              (g := algebraMap A L) hA_inj)
        _ = ⊤ := hclosure_top
    have hf_surj : Function.Surjective f := RingHom.fieldRange_eq_top_iff.mp hf_range
    -- Surjectivity of the lift shows that every element of `L` is a quotient of elements of `A`.
    refine IsFractionRing.of_field A L fun z ↦ ?_
    obtain ⟨q, rfl⟩ := hf_surj z
    obtain ⟨a, b, hb, hq⟩ := IsFractionRing.div_surjective A q
    refine ⟨a, b, ?_⟩
    calc
      f q = f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) := by
        rw [hq]
      _ = algebraMap A L a / algebraMap A L b := by
        simp [f, map_div₀]
  exact ⟨A, hA_finite, hA_fraction⟩

/-- Helper for Lemma 10.162.3: an `N-1` domain has finite normalization in any chosen model of
its fraction field. -/
lemma integralClosure_finite_of_isN1Ring_of_isFractionRing
    {S : Type v} [CommRing S] [IsDomain S] [IsN1Ring S]
    {L : Type w} [Field L] [Algebra S L] [IsFractionRing S L] :
    Module.Finite S (integralClosure S L) := by
  -- Transport the defining finite normalization statement for `FractionRing S` across the
  -- canonical fraction-field equivalence.
  exact Module.Finite.equiv (FractionRing.algEquiv S L).mapIntegralClosure.toLinearEquiv

/-- Helper for Lemma 10.162.3: if a finite intermediate `S`-subalgebra of `L` is `N-1`, then the
integral closure of `S` in `L` is finite over `S`. -/
lemma moduleFinite_integralClosure_of_moduleFinite_intermediate
    {S : Type v} [CommRing S] [IsDomain S]
    {L : Type w} [Field L] [Algebra S L]
    (A : Subalgebra S L) [Module.Finite S A] [IsFractionRing A L] [IsN1Ring A] :
    Module.Finite S (integralClosure S L) := by
  -- Route correction: because `A / S` is integral and both have fraction field `L`, the two
  -- integral closures inside `L` coincide. This gives the desired finiteness by transport.
  letI : Algebra.IsIntegral S A := inferInstance
  have hA_normalization : Module.Finite A (integralClosure A L) :=
    integralClosure_finite_of_isN1Ring_of_isFractionRing (S := A) (L := L)
  letI : Module.Finite A (integralClosure A L) := hA_normalization
  have hSA_normalization : Module.Finite S ((integralClosure A L).restrictScalars S) := by
    simpa using (Module.Finite.trans A (integralClosure A L) : Module.Finite S (integralClosure A L))
  have hclosures_eq : integralClosure S L = (integralClosure A L).restrictScalars S := by
    ext x
    constructor
    · intro hx
      -- Integrality over `S` remains integrality over the larger base `A`.
      exact IsIntegral.tower_top (A := A) hx
    · intro hx
      -- Integrality over `A` descends back to `S` because `A` is integral over `S`.
      exact isIntegral_trans (R := S) (A := A) (x := x) hx
  rw [hclosures_eq]
  exact hSA_normalization

/-
Domain-style sampling:
* primary domain: commutative algebra of finite normalization and the `N-1`/`N-2` criteria for
  universally Japanese rings;
* owner abstractions sampled for this refinement:
  - `IsN1Ring` and `IsN2Ring`, the chapter-owner source-facing classes from
    `Definition_10_161_1`;
  - `UniversallyJapaneseRing`, the source-facing owner introduced in `Definition_10_162_1`;
  - `isN2Ring_of_finite_extension`, the chapter bridge/view theorem for descending `N-2` along a
    finite extension of domains.
* layer triage:
  - `source-facing`: the theorem below, which gives a criterion for the existing owner
    `UniversallyJapaneseRing`;
  - `core/canonical`: the owner classes `IsN1Ring`, `IsN2Ring`, and `UniversallyJapaneseRing`;
  - `bridge/view`: finite domain models inside finite fraction-field extensions, together with the
    finite-extension descent theorem `isN2Ring_of_finite_extension`.

The primitive data are just the base ring `R` and the test family asserting `IsN1Ring` for every
finite type domain `R`-algebra. Finite-normalization statements in field extensions are derived
API from the sampled owners and should remain internal to the proof rather than being packaged
into a new public wrapper in this file.
-/

/-- Lemma 10.162.3: to prove that `R` is universally Japanese, it suffices to check that every
finite type `R`-algebra that is a domain is `N-1`. -/
-- Proof sketch: to show `R` is universally Japanese, fix a finite type domain `S` over `R` and a
-- finite extension `L / FractionRing S`. Choose a finite domain extension `S ⊆ S' ⊆ L` with
-- fraction field `L`; then `S'` is still finite type over `R`, hence `N-1` by hypothesis. The
-- integral closure of `S'` in `L` is therefore finite over `S'`, hence finite over `S`, and this
-- identifies with the integral closure of `S` in `L`, proving that `S` is `N-2`.
theorem universallyJapaneseRing_of_finiteType_domain_isN1
    (h :
      ∀ (S : Type v) [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [IsDomain S],
        IsN1Ring S) :
    UniversallyJapaneseRing.{u, v} R := by
  refine
    { finiteType_algebra_isN2Ring := fun (S : Type v) [CommRing S] [Algebra R S]
        [Algebra.FiniteType R S] [IsDomain S] ↦ ?_ }
  refine IsN2Ring.mk ?_
  intro L _ _ _ _ _
  -- Choose a finite intermediate domain `A ⊆ L` whose fraction field is all of `L`.
  obtain ⟨A, hA_finite, hA_fraction⟩ :=
    exists_moduleFinite_subalgebra_with_fractionRing (S := S) (L := L)
  letI : Module.Finite S A := hA_finite
  letI : IsFractionRing A L := hA_fraction
  letI : Algebra R A := (RingHom.comp (algebraMap S A) (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  have hRA_finiteType : (algebraMap R A).FiniteType := by
    -- Finite maps are finite type, and finite type composes along `R ⟶ S ⟶ A`.
    change (RingHom.comp (algebraMap S A) (algebraMap R S)).FiniteType
    have hSA_finiteType : (algebraMap S A).FiniteType :=
      RingHom.finiteType_algebraMap.mpr inferInstance
    exact RingHom.FiniteType.comp
      hSA_finiteType
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hRA_finiteType
  letI : IsN1Ring A := h A
  -- Apply the hypothesis to the finite intermediate domain and descend finiteness of
  -- normalization back to `S`.
  exact moduleFinite_integralClosure_of_moduleFinite_intermediate (S := S) (L := L) A

end

/-! ### Lemma_10_162_4 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: write the essentially finite type `R`-algebra `S` as a localization of a finite
-- type `R`-algebra `A`. The finite type case is immediate from the definition of
-- `UniversallyJapaneseRing`, since any finite type domain over `A` is also finite type over `R`.
-- Then apply the localization stability of the `N-2` property from Lemma `10.161.3` to conclude
-- that finite type domain algebras over `S` are Japanese.
/-- Lemma 10.162.4: if `R` is universally Japanese, then any `R`-algebra essentially of finite
type is universally Japanese. -/
theorem universallyJapaneseRing_of_essFiniteType [UniversallyJapaneseRing.{u, v} R]
    [Algebra.EssFiniteType R S] : UniversallyJapaneseRing.{v, v} S := by
  let A := Algebra.EssFiniteType.subalgebra R S
  letI : Algebra R A := A.algebra
  refine
    { finiteType_algebra_isN2Ring := fun {T} [CommRing T] [Algebra S T] [Algebra.FiniteType S T]
        [IsDomain T] ↦ ?_ }
  letI : Algebra A S := inferInstance
  letI : Algebra.EssFiniteType A S :=
    Algebra.EssFiniteType.of_isLocalization S (Algebra.EssFiniteType.submonoid R S)
  letI : Algebra A T := inferInstance
  letI : IsScalarTower A S T := inferInstance
  letI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.comp A S T
  let T₀ := Algebra.EssFiniteType.subalgebra A T
  letI : Algebra A T₀ := T₀.algebra
  letI : Algebra R T₀ := (RingHom.comp (algebraMap A T₀) (algebraMap R A)).toAlgebra
  have hRT₀ : (algebraMap R T₀).FiniteType := by
    change (RingHom.comp (algebraMap A T₀) (algebraMap R A)).FiniteType
    exact RingHom.FiniteType.comp
      (RingHom.finiteType_algebraMap.mpr inferInstance)
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType R T₀ := RingHom.finiteType_algebraMap.mp hRT₀
  let hR : UniversallyJapaneseRing.{u, v} R := inferInstance
  have hN2 : IsN2Ring T₀ := hR.finiteType_algebra_isN2Ring
  letI : IsN2Ring T₀ := hN2
  letI : Algebra T₀ T := inferInstance
  simpa [T₀] using isN2Ring_of_isLocalization (Algebra.EssFiniteType.submonoid A T)

end

/-! ### Lemma_10_162_5 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: stability of the source-facing owner `NagataRing` under algebra extensions;
- sampled owner abstractions in the same chapter/project:
  - `Algebra.FiniteType.QuasiFinite`, the source-facing owner for quasi-finite finite-type
    extensions from `Definition_10_122_3`;
  - `NagataRing`, the source-facing owner from `Definition_10_162_1`;
  - `UniversallyJapaneseRing`, the companion owner derived from `NagataRing` in
    `Proposition_10_162_16`;
  - `nagataRing_of_finiteType`, the canonical chapter theorem proving finite-type stability of
    `NagataRing`.

Best owner abstraction:
- `NagataRing` is the owner of the property under discussion;
- `Algebra.FiniteType.QuasiFinite R S` is the source-facing owner for the hypothesis;
- `nagataRing_of_finiteType` is the canonical upstream stability theorem for the conclusion;
- the quasi-finite lemma below is therefore a `source-facing` bridge/view corollary, not a second
  owner-level theorem.

Primitive data vs derived API:
- primitive data: the rings `R`, `S`, the `R`-algebra structure, and the source-faithful
  source-facing quasi-finite owner `Algebra.FiniteType.QuasiFinite R S`;
- derived API: the conclusion `NagataRing S`, obtained directly from the upstream finite-type
  theorem.
-/
-- Proof sketch: quasi-finite morphisms are finite type, so `S` is Noetherian because `R` is.
-- For a prime ideal `q` of `S`, let `p = q ∩ R`. Then `(R ⧸ p) → (S ⧸ q)` is again quasi-finite,
-- and the source is `N-2` because `R` is Nagata. Apply Lemma `10.161.5` to conclude that
-- `S ⧸ q` is `N-2`, which is exactly the Nagata condition for `S`.
/-- Lemma 10.162.5: if `R` is a Nagata ring and `R → S` is quasi-finite, then `S` is a Nagata
ring as well. In particular, this applies to finite ring maps. -/
theorem nagataRing_of_quasiFinite (hRSqf : Algebra.FiniteType.QuasiFinite R S) [NagataRing R] :
    NagataRing S := by
  letI : Algebra.FiniteType R S := hRSqf.finiteType
  exact nagataRing_of_finiteType R

end

/-! ### Lemma_10_162_6 (from Chap10) -/
section

universe u v

variable {R : Type u} {Rₘ : Type v} [CommRing R] [CommRing Rₘ] [Algebra R Rₘ]

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings, localizations, and essential finite type;
- sampled owner abstractions of the same kind in the project:
  - `NagataRing`, the source-facing owner from `Definition_10_162_1`;
  - `UniversallyJapaneseRing`, the chapter bridge owner obtained from `NagataRing` in
    `Proposition_10_162_16`;
  - `universallyJapaneseRing_of_essFiniteType`, the canonical permanence theorem for essentially
    finite type algebras from `Lemma_10_162_4`;
  - `IsLocalization.isNoetherianRing`, the canonical Noetherian localization owner recall from
    `Lemma_10_31_1`.

Best owner abstraction:
- `NagataRing` is the source-facing owner for this lemma;
- the Noetherian part should be derived directly from `IsLocalization.isNoetherianRing`;
- the prime-quotient `N-2` part should be derived through the existing owner bridge
  `NagataRing → UniversallyJapaneseRing` and then the essentially-finite-type permanence theorem,
  rather than by introducing a separate local quotient-localization wrapper.

Primitive data vs derived API:
- primitive data: the localization datum `R → Rₘ` and the ambient assumption `[NagataRing R]`;
- derived API: Noetherianity of `Rₘ`, essential finite type of `Rₘ` and of its prime quotients
  over `R`, and the resulting `IsN2Ring` instances for those prime quotients.

Source/core/bridge triage:
- `source-facing`: the localization permanence statement for `NagataRing`;
- `core/canonical`: `NagataRing`, `UniversallyJapaneseRing`,
  `universallyJapaneseRing_of_essFiniteType`, and `IsLocalization.isNoetherianRing`;
- `bridge/view`: the passage from a prime quotient of the localization to an essentially finite
  type domain over the base Nagata ring.
-/

/-- Lemma 10.162.6: a localization of a Nagata ring is again a Nagata ring. -/
-- Proof sketch: a localization of a Noetherian ring is Noetherian. For a prime ideal `q` of the
-- localization, the quotient `Rₘ ⧸ q` is essentially of finite type over `R`; since a Nagata ring
-- is universally Japanese, `Lemma 10.162.4` makes `Rₘ ⧸ q` universally Japanese, and because it
-- is a domain, it is `N-2`. These are exactly the two fields needed to build `NagataRing Rₘ`.
theorem localization_nagataRing (M : Submonoid R) [IsLocalization M Rₘ] [NagataRing R] :
    NagataRing Rₘ := by
  letI : IsNoetherianRing Rₘ := IsLocalization.isNoetherianRing M Rₘ inferInstance
  refine NagataRing.mk ?_
  intro q
  letI : Algebra.EssFiniteType R Rₘ := Algebra.EssFiniteType.of_isLocalization Rₘ M
  let hEssFiniteType : Algebra.EssFiniteType R (Rₘ ⧸ q) := inferInstance
  let hUniversallyJapanese : UniversallyJapaneseRing R := inferInstance
  letI : Algebra.EssFiniteType R (Rₘ ⧸ q) := hEssFiniteType
  letI : UniversallyJapaneseRing (Rₘ ⧸ q) :=
    @universallyJapaneseRing_of_essFiniteType R (Rₘ ⧸ q) _ _ _ hUniversallyJapanese hEssFiniteType
  exact inferInstance

end

/-! ### Lemma_10_162_7 (from Chap10) -/
noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
- primary domain: locality of the chapter owners `UniversallyJapaneseRing` and `NagataRing`
  under a finite principal-open cover;
- sampled owner declarations of the same kind:
  - `UniversallyJapaneseRing` and `NagataRing` from `Definition_10_162_1`,
  - `isN2Ring_of_isN2Ring_localizationAway` from `Lemma_10_161_4`,
  - `AlgebraicGeometry.isNoetherianRing_of_away` from `Lemma_10_23_2`,
  - the bridge instance `[NagataRing R] → [UniversallyJapaneseRing R]` from
    `Proposition_10_162_16`.

Best owner abstraction:
- `UniversallyJapaneseRing` and `NagataRing` are already the correct source-facing owners;
- `IsN2Ring` is the core/canonical owner used to discharge both locality statements;
- the right bridge is a private helper proving `IsN2Ring A` for any finite type domain `A` over
  `R` from the localized universally-Japanese hypotheses on `R`.

Primitive data vs. derived API:
- primitive data for the helper: a finite type domain `A` over `R`, a finite cover `s`, and the
  localized owner hypotheses on `R_f`;
- derived API: the localized finite-type algebra structures `R_f → A_g`, the domain instances for
  the nonzero principal localizations of `A`, and the owner-level conclusions
  `UniversallyJapaneseRing R` and `NagataRing R`.

Source/core/bridge triage:
- `source-facing`: the two public locality theorems for `UniversallyJapaneseRing` and `NagataRing`;
- `core/canonical`: `IsN2Ring`, `UniversallyJapaneseRing`, `NagataRing`,
  `isN2Ring_of_isN2Ring_localizationAway`, and `AlgebraicGeometry.isNoetherianRing_of_away`;
- `bridge/view`: the private passage from `R_f` to the localization of a finite type domain
  `A_g`, expressed via the canonical away-localization algebra map and finite-type descent.
-/

section DomainBridge

variable {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A]

private noncomputable instance localizationAwayImageAlgebra (f : R) :
    Algebra (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  simpa [Algebra.ofId_apply] using
    (Localization.awayMapₐ (Algebra.ofId R A) f).toAlgebra

omit [IsDomain A] in
private theorem finiteType_localizationAwayImage (f : R) :
    Algebra.FiniteType (Localization.Away f) (Localization.Away (algebraMap R A f)) := by
  let φ : Localization.Away f →+* Localization.Away (algebraMap R A f) :=
    Localization.awayMap (algebraMap R A) f
  have hcomp : (φ.comp (algebraMap R (Localization.Away f))).FiniteType := by
    rw [show φ.comp (algebraMap R (Localization.Away f)) =
        algebraMap R (Localization.Away (algebraMap R A f)) by
          ext x
          simp [φ, IsLocalization.Away.map, IsLocalization.map,
            IsScalarTower.algebraMap_eq R A (Localization.Away (algebraMap R A f))]]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType hcomp)

private theorem isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, UniversallyJapaneseRing (Localization.Away f.1)) :
    IsN2Ring A := by
  let _ := (inferInstance : Algebra.FiniteType R A)
  classical
  let t : Finset A := (s.image fun f ↦ algebraMap R A f).erase 0
  have ht : Ideal.span (t : Set A) = ⊤ := by
    rw [show (t : Set A) = (((s.image fun f ↦ algebraMap R A f) : Finset A) : Set A) \ {0} by
          ext x
          simp [t]]
    rw [Ideal.span_sdiff_singleton_zero]
    rw [show ((((s.image fun f ↦ algebraMap R A f) : Finset A) : Set A)) =
        algebraMap R A '' (s : Set R) by
          ext x
          simp]
    rw [← Ideal.map_span, hs, Ideal.map_top]
  have hdom : ∀ g : t, IsDomain (Localization.Away g.1) := fun g ↦ by
    have hg_ne : g.1 ≠ 0 := by
      simpa [t] using Finset.mem_erase.mp g.2 |>.1
    exact
      IsLocalization.isDomain_of_le_nonZeroDivisors _
        (powers_le_nonZeroDivisors_of_noZeroDivisors hg_ne)
  refine isN2Ring_of_isN2Ring_localizationAway t ht hdom ?_
  rintro ⟨g, hg⟩
  have hg_ne : g ≠ 0 := by
    simpa [t] using Finset.mem_erase.mp hg |>.1
  have hg_mem : g ∈ s.image fun f ↦ algebraMap R A f := by
    exact Finset.mem_of_mem_erase hg
  obtain ⟨f, hf_mem, rfl⟩ := Finset.mem_image.mp hg_mem
  let Af : Type v := Localization.Away (algebraMap R A f)
  letI : IsDomain Af :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg_ne)
  letI : Algebra.FiniteType (Localization.Away f) Af :=
    finiteType_localizationAwayImage f
  have hUf : UniversallyJapaneseRing (Localization.Away f) := by
    simpa using h ⟨f, hf_mem⟩
  letI : UniversallyJapaneseRing (Localization.Away f) := hUf
  change IsN2Ring Af
  infer_instance

end DomainBridge

-- Proof sketch: to show `R` is universally Japanese, it suffices to check that every finite type
-- domain `A` over `R` is `N-2`. For such an `A`, remove the zero images from the principal-open
-- cover induced by `s`, so each localization `A_g` remains a domain. Each `A_g` is finite type
-- over the corresponding `R_f`, hence `N-2` by the localized universally-Japanese hypothesis; now
-- descend `N-2` along the finite cover using `isN2Ring_of_isN2Ring_localizationAway`.
/-- Lemma 10.162.7 (1): if the elements of `s` generate the unit ideal and each principal
localization `R_f` is universally Japanese, then `R` is universally Japanese. -/
theorem universallyJapaneseRing_of_localizationAway (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, UniversallyJapaneseRing (Localization.Away f.1)) :
    UniversallyJapaneseRing R := by
  refine ⟨fun {A} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] [IsDomain A] ↦ ?_⟩
  exact
    isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese
      s hs h

-- Proof sketch: the Noetherian part descends from the cover via
-- `AlgebraicGeometry.isNoetherianRing_of_away`. For a prime ideal `p`, the quotient `R ⧸ p` is a
-- finite type domain over `R`; applying the previous private `IsN2Ring` bridge with the localized
-- Nagata hypotheses viewed through the canonical owner instance
-- `[NagataRing (R_f)] → [UniversallyJapaneseRing (R_f)]` proves `R ⧸ p` is `N-2`.
/-- Lemma 10.162.7 (2): if the elements of `s` generate the unit ideal and each principal
localization `R_f` is Nagata, then `R` is Nagata. -/
theorem nagataRing_of_localizationAway (s : Finset R)
    (hs : Ideal.span (s : Set R) = ⊤)
    (h : ∀ f : s, NagataRing (Localization.Away f.1)) :
    NagataRing R := by
  let _ := h
  letI : IsNoetherianRing R :=
    AlgebraicGeometry.isNoetherianRing_of_away s hs fun f ↦ by
      letI : NagataRing (Localization.Away f.1) := h f
      infer_instance
  refine NagataRing.mk ?_
  intro p hp
  letI : p.IsPrime := hp
  let hU : ∀ f : s, UniversallyJapaneseRing.{u, u} (Localization.Away f.1) := fun f ↦ by
    letI : NagataRing (Localization.Away f.1) := h f
    infer_instance
  exact
    isN2Ring_of_span_eq_top_of_localizationAway_universallyJapanese
      s hs hU

end

/-! ### Lemma_10_162_8 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings and the complete-local criterion for the
  `N-2` condition on prime quotients;
- sampled owner declarations of the same kind:
  `IsCompleteLocalRing`,
  `NagataRing`,
  `quotient_isCompleteLocalRing`,
  `IsN2Ring`;
- best owner abstraction: `NagataRing` is the source-facing owner for this item, with complete
  locality and Noetherianity as primitive hypotheses and the prime-quotient `N-2` conditions as
  derived owner data;
- primitive data vs. derived API:
  the primitive inputs are only `[IsCompleteLocalRing R]` and `[IsNoetherianRing R]`,
  while the quotient-by-prime `IsN2Ring` instances belong to the `NagataRing` owner API.

Source/core/bridge triage:
- `source-facing`: the complete-local criterion proving `NagataRing R`;
- `core/canonical`: the owner class `NagataRing` together with its quotient field
  `quotient_isN2Ring`;
- `bridge/view`: the quotient stability theorem `quotient_isCompleteLocalRing`, which supplies the
  canonical complete-local input on each prime quotient.
-/
-- Proof sketch: for each prime ideal `p`, the quotient `R ⧸ p` is again complete local by
-- `quotient_isCompleteLocalRing`, and it is Noetherian by the canonical quotient instance. Hence
-- it remains to show that a
-- Noetherian complete local domain is `N-2`; reduce by the Cohen structure theorem and the finite
-- extension reduction to formal power series rings over a field or a Cohen ring, then apply the
-- power-series and Tate lemmas to reduce to the field case.
/-- Lemma 10.162.8: a Noetherian complete local ring is a Nagata ring. -/
instance nagataRing_of_noetherian_completeLocalRing : NagataRing R := sorry

end

/-! ### Definition_10_162_9 (from Chap10) -/
universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The quotient of a local ring by a prime ideal is again a local ring. -/
instance primeSpectrum_quotient_isLocalRing (p : PrimeSpectrum R) : IsLocalRing (R ⧸ p.asIdeal) :=
  by
    -- The quotient map is surjective, so locality descends to the prime quotient.
    exact IsLocalRing.of_surjective' (Ideal.Quotient.mk p.asIdeal) Ideal.Quotient.mk_surjective

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Definition 10.162.9: a local ring is analytically unramified when its completion with
respect to the maximal ideal is reduced. -/
@[mk_iff isAnalyticallyUnramified_iff]
class IsAnalyticallyUnramified : Prop where
  completion_isReduced : IsReduced (AdicCompletion (maximalIdeal R) R)

attribute [instance] IsAnalyticallyUnramified.completion_isReduced

end

section

variable (K : Type u) [Field K]

/-- Helper for Definition 10.162.9: a field is complete for the adic topology defined by the zero
ideal. -/
theorem field_isAdicComplete_bot : IsAdicComplete (⊥ : Ideal K) K := by
  -- The `⊥`-adic topology is discrete, so the standard `bot` instances give completeness.
  infer_instance

/-- Helper for Definition 10.162.9: the completion of a field at its maximal ideal is reduced. -/
theorem field_completion_isReduced : IsReduced (AdicCompletion (maximalIdeal K) K) := by
  let _ : IsAdicComplete (⊥ : Ideal K) K := field_isAdicComplete_bot K
  -- Replace the maximal ideal by `⊥`, then identify the completion with the field itself.
  rw [IsLocalRing.maximalIdeal_eq_bot]
  let e : K ≃ₐ[K] AdicCompletion (⊥ : Ideal K) K := AdicCompletion.ofAlgEquiv (⊥ : Ideal K)
  -- Reducedness descends along the inverse of the completion equivalence.
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Fields are analytically unramified. -/
instance : IsAnalyticallyUnramified K where
  -- The completion at the maximal ideal is identified with the field itself.
  completion_isReduced := field_completion_isReduced K

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace PrimeSpectrum

/-- A prime ideal of a local ring is analytically unramified when the quotient ring by
that prime ideal is analytically unramified. -/
def IsAnalyticallyUnramified (p : PrimeSpectrum R) : Prop :=
  _root_.IsAnalyticallyUnramified (R ⧸ p.asIdeal)

end PrimeSpectrum

end

/-! ### Lemma_10_162_10 (from Chap10) -/
universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: analytically unramified Noetherian local rings, their minimal-prime quotients,
  and the finite normalization (`N-1`) consequence;
- sampled owner declarations:
  `IsAnalyticallyUnramified`,
  `PrimeSpectrum.IsAnalyticallyUnramified`,
  `IsN1Ring`,
  and the canonical minimal-prime index type `minimalPrimes R`;
- best owner abstraction: the ambient owner is `IsAnalyticallyUnramified R`, while minimal-prime
  inputs should use the canonical `minimalPrimes R` owner rather than a separate prime-spectrum
  point together with a membership proof;
- primitive data vs. derived API: the primitive source data are the ring `R`, the owner
  hypothesis `[IsAnalyticallyUnramified R]`, and the minimal-prime family. Reducedness of `R`,
  analytic unramifiedness of each minimal-prime quotient, and the `N-1` finiteness statement are
  derived theorem-level API and should not be repackaged as extra structures.
-/

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

local instance (p : minimalPrimes R) : IsLocalRing (R ⧸ p.1) :=
  primeSpectrum_quotient_isLocalRing ⟨p.1, inferInstance⟩

-- Proof sketch: the completion map `R → AdicCompletion (maximalIdeal R) R` is faithfully flat, so
-- it is injective. If the completion is reduced, then a nilpotent element of `R` maps to `0`, hence
-- already vanishes in `R`.
/-- Lemma 10.162.10 (1): an analytically unramified Noetherian local ring is reduced. -/
theorem isReduced_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsReduced R := sorry

-- Proof sketch: for a minimal prime `p`, use exactness of completion on the quotient `R ⧸ p.asIdeal`
-- to identify its completion with the quotient of the completion of `R`. Reducedness of the latter
-- modulo the extended minimal prime shows the quotient ring is analytically unramified.
/-- Lemma 10.162.10 (2): if `R` is analytically unramified, then every minimal prime quotient of
`R` is analytically unramified. -/
theorem minimalPrime_isAnalyticallyUnramified_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] (p : minimalPrimes R) :
    IsAnalyticallyUnramified (R ⧸ p.1) := sorry

-- Proof sketch: embed `R` into the product of the quotient rings by its minimal primes. Exactness
-- of completion gives an embedding of the completion of `R` into the product of the completions of
-- those quotients, and each factor is reduced by the analytic unramifiedness hypothesis.
/-- Lemma 10.162.10 (3): if `R` is reduced and each minimal prime quotient of `R` is analytically
unramified, then `R` is analytically unramified. -/
theorem isAnalyticallyUnramified_of_isReduced_of_minimalPrimes
    [IsReduced R]
    (hmin : ∀ p : minimalPrimes R, IsAnalyticallyUnramified (R ⧸ p.1)) :
    IsAnalyticallyUnramified R := sorry

-- Proof sketch: the completion of `R` is reduced, so its minimal-prime decomposition identifies
-- its total quotient ring with a finite product of fields. The integral closure over the completion
-- is finite by the domain case on each factor, and faithful flatness of completion descends a
-- finite generating set to the integral closure of `R` in `Q(R)`.
/-- Lemma 10.162.10 (4): if `R` is analytically unramified, then the integral closure of `R` in
its total ring of fractions is finite over `R`. -/
theorem integralClosure_fractionRing_finite_of_isAnalyticallyUnramified
    [IsAnalyticallyUnramified R] :
    Module.Finite R (integralClosure R (FractionRing R)) := sorry

end

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]

-- Proof sketch: apply part (4) to obtain finiteness of the integral closure of `R` in
-- `FractionRing R`; this is exactly the defining field of `IsN1Ring R`.
/-- Lemma 10.162.10 (5): an analytically unramified Noetherian local domain is `N-1`. -/
theorem isN1Ring_of_isAnalyticallyUnramified [IsAnalyticallyUnramified R] :
    IsN1Ring R := sorry

end

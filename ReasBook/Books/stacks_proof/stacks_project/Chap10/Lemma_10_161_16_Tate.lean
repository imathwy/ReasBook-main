import StacksProject_2024.Chap10.Lemma_10_161_16_Tate.Index
import StacksProject_2024.Chap10.Lemma_10_96_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal
open IsLocalRing
open IntermediateField Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-
Domain-style sampling:
* primary domain: commutative algebra of Japanese (`N-2`) domains under a principal `x`-adic
  reduction step;
* sampled owner abstractions:
  - `IsN2Ring`, the chapter-owner source-facing `N-2` condition from
    `Definition_10_161_1`;
  - `IsAdicComplete`, the canonical owner for `x`-adic completeness;
  - `moduleFinite_of_finite_quotient_of_isHausdorff`, the owner-facing finite-generation criterion
    from Lemma `10.96.12` used in the Tate argument;
  - `IsIntegralClosure.finite`, recalled in Lemma `10.161.8` for the separable normalization step.
* layer triage:
  - `source-facing`: the Tate criterion upgrading the quotient `R / xR` being `N-2` to `R`
    itself being `N-2`;
  - `core/canonical`: the owners `IsN2Ring` and `IsAdicComplete`;
  - `bridge/view`: the principal-quotient reduction and the finite-normalization argument inside
    the proof.

Primitive data are the ambient normal Noetherian domain `R`, the element `x`, the quotient-domain
assumption on `R ⧸ span ({x} : Set R)`, the owner hypothesis
`[IsN2Ring (R ⧸ span ({x} : Set R))]`, and the owner completeness hypothesis
`[IsAdicComplete (span ({x} : Set R)) R]`. The finite integral-closure statements and the
separated finite-generation step are derived API from the sampled owners and should remain
proof-level, not additional public wrapper data in this file.
-/

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Helper for Chap10 Lemma 10 161 16 Tate: the raw localization `S_q` maps to the ambient
fraction-field model `M` of the normalization `S`. -/
noncomputable def rawPrimeLocalizationToField
    {M : Type u} [Field M] [Algebra R M] [FaithfulSMul R M]
    [IsFractionRing (integralClosure R M) M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    Localization.AtPrime q.1 →ₐ[integralClosure R M] M :=
  Localization.mapToFractionRing M q.1.primeCompl (Localization.AtPrime q.1)
    q.1.primeCompl_le_nonZeroDivisors

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the map `S_q → M` agrees with the ambient
normalization map on elements of `S`. -/
lemma rawPrimeLocalizationToField_apply_algebraMap
    {M : Type u} [Field M] [Algebra R M] [FaithfulSMul R M]
    [IsFractionRing (integralClosure R M) M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M))
    (s : integralClosure R M) :
    rawPrimeLocalizationToField (R := R) (M := M) x q
        (algebraMap (integralClosure R M) (Localization.AtPrime q.1) s) =
      algebraMap (integralClosure R M) M s := by
  let g := rawPrimeLocalizationToField (R := R) (M := M) x q
  -- Proof comment: this is the defining commutation rule for the localization map into the
  -- fraction-field model.
  exact g.commutes s

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the ambient field `M` is also a fraction field of
the raw prime localization `S_q`. -/
lemma rawPrimeLocalizationToField_isFractionRing
    {M : Type u} [Field M] [Algebra R M] [FaithfulSMul R M]
    [IsFractionRing (integralClosure R M) M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let g := rawPrimeLocalizationToField (R := R) (M := M) x q
    letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
    IsFractionRing (Localization.AtPrime q.1) M := by
  let S := integralClosure R M
  let Sq : Type u := Localization.AtPrime q.1
  letI : q.1.IsPrime := q.2.1
  letI hAlgSSq : Algebra S Sq := inferInstance
  letI : SMul S Sq := hAlgSSq.toSMul
  letI : Module S Sq := Algebra.toModule
  let g := rawPrimeLocalizationToField (R := R) (M := M) x q
  letI hAlgSqM : Algebra Sq M := g.toRingHom.toAlgebra
  letI : SMul Sq M := hAlgSqM.toSMul
  letI : Module Sq M := Algebra.toModule
  let hAlgSM : Algebra S M := inferInstance
  letI hTower : IsScalarTower S Sq M := by
    -- Proof comment: convert the algebra-map computation for `g` into a scalar tower.
    exact IsScalarTower.of_algebraMap_eq fun s ↦
      (rawPrimeLocalizationToField_apply_algebraMap (R := R) (M := M) x q s).symm
  -- Proof comment: localizing a domain at a prime complement does not change the total
  -- fraction field.
  exact
    @IsFractionRing.isFractionRing_of_isDomain_of_isLocalization S inferInstance
      q.1.primeCompl inferInstance Sq M inferInstance inferInstance hAlgSSq hAlgSM hAlgSqM
      hTower inferInstance inferInstance

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the composite `R_(x) → S_q → M` is compatible with
the original scalar map `R → M`. -/
lemma rawBaseLocalizationToField_isScalarTower
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [FaithfulSMul R M] [IsFractionRing (integralClosure R M) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
      Ideal.LiesOver.over (p := p0) (P := q.1)
    let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
    let g := rawPrimeLocalizationToField (R := R) (M := M) x q
    letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
    letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
    letI : Algebra (Localization.AtPrime p0) M :=
      ((algebraMap (Localization.AtPrime q.1) M).comp f).toAlgebra
    IsScalarTower R (Localization.AtPrime p0) M := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
    Ideal.LiesOver.over (p := p0) (P := q.1)
  let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
  let g := rawPrimeLocalizationToField (R := R) (M := M) x q
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  letI : q.1.IsPrime := q.2.1
  letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
  letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime p0) M :=
    ((algebraMap (Localization.AtPrime q.1) M).comp f).toAlgebra
  -- Proof comment: compare the two maps from the base ring on generators of the localization.
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  change algebraMap R M r =
    algebraMap (Localization.AtPrime q.1) M
      (f (algebraMap R (Localization.AtPrime p0) r))
  rw [Localization.localRingHom_to_map]
  change algebraMap R M r =
    g (algebraMap S (Localization.AtPrime q.1) (algebraMap R S r))
  rw [g.commutes]
  exact (IsScalarTower.algebraMap_apply R S M r).symm

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: `M` is faithful over the principal prime
localization `R_(x)` through the raw localized normalization. -/
lemma rawBaseLocalizationToField_faithfulSMul
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [FaithfulSMul R M] [IsFractionRing (integralClosure R M) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
      Ideal.LiesOver.over (p := p0) (P := q.1)
    let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
    let g := rawPrimeLocalizationToField (R := R) (M := M) x q
    letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
    letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
    letI : Algebra (Localization.AtPrime p0) M :=
      ((algebraMap (Localization.AtPrime q.1) M).comp f).toAlgebra
    FaithfulSMul (Localization.AtPrime p0) M := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
    Ideal.LiesOver.over (p := p0) (P := q.1)
  let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
  let g := rawPrimeLocalizationToField (R := R) (M := M) x q
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  letI : q.1.IsPrime := q.2.1
  letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
  letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime p0) M :=
    ((algebraMap (Localization.AtPrime q.1) M).comp f).toAlgebra
  letI : IsScalarTower R (Localization.AtPrime p0) M :=
    rawBaseLocalizationToField_isScalarTower (R := R) (M := M) x q
  -- Proof comment: injectivity of `R_(x) → M` follows from the fraction-field extension
  -- model of `M`.
  exact
    (faithfulSMul_iff_algebraMap_injective (Localization.AtPrime p0) M).2
      (localizationAtPrime_algebraMap_injective_to_fractionField_extension
        (A := R) (p := p0) (K := FractionRing R) (L := M))

omit [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the fraction-field algebra obtained by transporting
scalars through a common field model. -/
noncomputable abbrev fractionRingAlgebraViaCommonField
    {A B L : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field L]
    [Algebra (FractionRing A) L] [Algebra B L] [IsFractionRing B L] :
    Algebra (FractionRing A) (FractionRing B) :=
  ((FractionRing.algEquiv B L).symm.toRingEquiv.toRingHom.comp
    (algebraMap (FractionRing A) L)).toAlgebra

/-- Helper for Chap10 Lemma 10 161 16 Tate: the raw prime localization has a finite fraction
field over the fraction field of the principal localization, using `M` as common field model. -/
lemma rawPrimeLocalization_fractionRing_finiteDimensional
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M))
    [q.1.IsPrime]
    [FaithfulSMul R M] [IsFractionRing (integralClosure R M) M]
    [Algebra (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [IsScalarTower R (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [FaithfulSMul (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [Algebra (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M]
    [IsScalarTower (Localization.AtPrime (Ideal.span ({x} : Set R)))
      (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M]
    [Algebra (Localization.AtPrime q.1) M]
    [IsFractionRing (Localization.AtPrime q.1) M] :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    letI : Algebra (FractionRing (Localization.AtPrime p0)) M :=
      FractionRing.liftAlgebra (Localization.AtPrime p0) M
    letI : IsScalarTower (Localization.AtPrime p0)
        (FractionRing (Localization.AtPrime p0)) M :=
      FractionRing.isScalarTower_liftAlgebra (Localization.AtPrime p0) M
    let hAlgFrac : Algebra (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) :=
      fractionRingAlgebraViaCommonField
        (A := Localization.AtPrime p0) (B := Localization.AtPrime q.1) (L := M)
    letI : Algebra (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) := hAlgFrac
    letI : SMul (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) := hAlgFrac.toSMul
    letI : Module (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) :=
      @Algebra.toModule
        (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) _ _ hAlgFrac
    FiniteDimensional
      (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) := by
  -- Proof comment: the common field model `M` identifies `Frac(S_q)` with a finite-dimensional
  -- extension of `Frac(R_(x))` under the transported scalar structure chosen in the statement.
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  letI : Algebra (FractionRing (Localization.AtPrime p0)) M :=
    FractionRing.liftAlgebra (Localization.AtPrime p0) M
  letI : IsScalarTower (Localization.AtPrime p0)
      (FractionRing (Localization.AtPrime p0)) M :=
    FractionRing.isScalarTower_liftAlgebra (Localization.AtPrime p0) M
  letI : FiniteDimensional (FractionRing (Localization.AtPrime p0)) M :=
    localized_base_fraction_field_finite (R := R) (p := p0) (M := M)
  exact
    fractionRing_finiteDimensional_of_isFractionRing
      (A := Localization.AtPrime p0)
      (B := Localization.AtPrime q.1) (L := M)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the transported fraction-field algebra for the raw
prime localization is compatible with the base localization map. -/
lemma rawPrimeLocalization_fractionRing_isScalarTower
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M))
    [q.1.IsPrime]
    [FaithfulSMul R M] [IsFractionRing (integralClosure R M) M]
    [Algebra (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [IsScalarTower R (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [FaithfulSMul (Localization.AtPrime (Ideal.span ({x} : Set R))) M]
    [Algebra (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M]
    [IsScalarTower (Localization.AtPrime (Ideal.span ({x} : Set R)))
      (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M]
    [Algebra (Localization.AtPrime (Ideal.span ({x} : Set R))) (Localization.AtPrime q.1)]
    [Algebra (Localization.AtPrime q.1) M]
    [IsScalarTower (Localization.AtPrime (Ideal.span ({x} : Set R)))
      (Localization.AtPrime q.1) M]
    [IsFractionRing (Localization.AtPrime q.1) M] :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    letI : Algebra (FractionRing (Localization.AtPrime p0)) M :=
      FractionRing.liftAlgebra (Localization.AtPrime p0) M
    letI : IsScalarTower (Localization.AtPrime p0)
        (FractionRing (Localization.AtPrime p0)) M :=
      FractionRing.isScalarTower_liftAlgebra (Localization.AtPrime p0) M
    let hAlgFrac : Algebra (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) :=
      fractionRingAlgebraViaCommonField
        (A := Localization.AtPrime p0) (B := Localization.AtPrime q.1) (L := M)
    letI : Algebra (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) := hAlgFrac
    letI : SMul (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) := hAlgFrac.toSMul
    letI : Module (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) :=
      @Algebra.toModule
        (FractionRing (Localization.AtPrime p0))
        (FractionRing (Localization.AtPrime q.1)) _ _ hAlgFrac
    IsScalarTower (Localization.AtPrime p0)
      (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) := by
  -- Proof comment: the same common-field normal form used for finite-dimensionality also
  -- identifies the base-localization map with the composite through the two fraction fields.
  letI : Algebra (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M :=
    FractionRing.liftAlgebra (Localization.AtPrime (Ideal.span ({x} : Set R))) M
  letI : IsScalarTower (Localization.AtPrime (Ideal.span ({x} : Set R)))
      (FractionRing (Localization.AtPrime (Ideal.span ({x} : Set R)))) M :=
    FractionRing.isScalarTower_liftAlgebra
      (Localization.AtPrime (Ideal.span ({x} : Set R))) M
  dsimp [fractionRingAlgebraViaCommonField]
  exact
    fractionRing_isScalarTower_of_isFractionRing
      (A := Localization.AtPrime (Ideal.span ({x} : Set R)))
      (B := Localization.AtPrime q.1) (L := M)

omit [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the closed-fiber residue-field finiteness theorem
also holds for the explicit algebra induced by `Ideal.ResidueField.map`. -/
lemma moduleFinite_maximalIdealResidueField_of_finite_fractionField_extension_mapAlgebra
    {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [FiniteDimensional (FractionRing A) (FractionRing B)]
    [IsLocalHom (algebraMap A B)] (hdim : ringKrullDim A = 1) :
    letI : Algebra (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField :=
      (Ideal.ResidueField.map
        (maximalIdeal A)
        (maximalIdeal B)
        (algebraMap A B)
        (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm).toAlgebra
    Module.Finite (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField := by
  let K : Type u := (maximalIdeal A).ResidueField
  let L : Type u := (maximalIdeal B).ResidueField
  let hAlgDefault : Algebra K L := inferInstance
  have hclosedDefault :
      @Module.Finite K L _ _ (@Algebra.toModule K L _ _ hAlgDefault) := by
    letI : Algebra K L := hAlgDefault
    -- Proof comment: first use Lemma `10.119.10` in its default residue-field algebra form.
    exact moduleFinite_maximalIdealResidueField_of_finite_fractionField_extension
      (A := A) (B := B) hdim
  let hAlgMap : Algebra K L :=
    (Ideal.ResidueField.map
      (maximalIdeal A)
      (maximalIdeal B)
      (algebraMap A B)
      (IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm).toAlgebra
  have hcompat :
      RingHom.comp (@algebraMap K L _ _ hAlgMap) ↑(RingEquiv.refl K) =
        RingHom.comp ↑(RingEquiv.refl L) (@algebraMap K L _ _ hAlgDefault) := by
    -- Proof comment: with both algebra structures named, identity equivalences make the
    -- comparison of scalar maps definitional.
    rfl
  -- Proof comment: transfer finite generation from the default residue-field algebra to the
  -- explicit map-induced algebra required by the prime-localization transport.
  exact
    @Module.Finite.of_equiv_equiv K L K L _ _ _ _ hAlgDefault hAlgMap
      (RingEquiv.refl K) (RingEquiv.refl L) hcompat hclosedDefault

/-- Chap10 Lemma 10 161 16 Tate: the closed point of the raw prime localization `S_q` has
finite residue field over the closed point of `R_(x)`. -/
lemma localizedSubalgebra_rawClosedPointResidueField_finite
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime]
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
      Ideal.LiesOver.over (p := p0) (P := q.1)
    let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
    letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
    letI : Algebra (maximalIdeal (Localization.AtPrime p0)).ResidueField
        (maximalIdeal (Localization.AtPrime q.1)).ResidueField :=
      (Ideal.ResidueField.map
        (maximalIdeal (Localization.AtPrime p0))
        (maximalIdeal (Localization.AtPrime q.1))
        f
        (IsLocalRing.maximalIdeal_comap f).symm).toAlgebra
    Module.Finite
      (maximalIdeal (Localization.AtPrime p0)).ResidueField
      (maximalIdeal (Localization.AtPrime q.1)).ResidueField := by
  -- Route correction: the `Aq`-residue-field route timed out at `whnf`.  The proved prefix now
  -- uses the raw `S_q → M` fraction-field model and applies the closed-fiber theorem after
  -- installing the two named fraction-field side conditions.
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
    Ideal.LiesOver.over (p := p0) (P := q.1)
  let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  letI : q.1.IsPrime := q.2.1
  letI : FaithfulSMul R M :=
    (faithfulSMul_iff_algebraMap_injective R M).2
      (algebraMap_injective_to_fractionField_extension (R := R) (K := M))
  letI : IsFractionRing S M :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := M)
  let g := rawPrimeLocalizationToField (R := R) (M := M) x q
  letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
  letI : Algebra (Localization.AtPrime q.1) M := g.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime p0) M :=
    ((algebraMap (Localization.AtPrime q.1) M).comp f).toAlgebra
  letI :=
    rawBaseLocalizationToField_isScalarTower (R := R) (M := M) x q
  letI :=
    rawBaseLocalizationToField_faithfulSMul (R := R) (M := M) x q
  letI :=
    rawPrimeLocalizationToField_isFractionRing (R := R) (M := M) x q
  letI : IsScalarTower (Localization.AtPrime p0) (Localization.AtPrime q.1) M :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra (FractionRing (Localization.AtPrime p0)) M :=
    FractionRing.liftAlgebra (Localization.AtPrime p0) M
  letI : IsScalarTower (Localization.AtPrime p0)
      (FractionRing (Localization.AtPrime p0)) M :=
    FractionRing.isScalarTower_liftAlgebra (Localization.AtPrime p0) M
  let hAlgFrac : Algebra (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) :=
    fractionRingAlgebraViaCommonField
      (A := Localization.AtPrime p0) (B := Localization.AtPrime q.1) (L := M)
  letI : Algebra (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) := hAlgFrac
  letI : SMul (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) := hAlgFrac.toSMul
  letI : Module (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) :=
    @Algebra.toModule
      (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) _ _ hAlgFrac
  letI : FiniteDimensional (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) :=
    rawPrimeLocalization_fractionRing_finiteDimensional (R := R) (M := M) x q
  letI : IsScalarTower (Localization.AtPrime p0)
      (FractionRing (Localization.AtPrime p0))
      (FractionRing (Localization.AtPrime q.1)) :=
    rawPrimeLocalization_fractionRing_isScalarTower (R := R) (M := M) x q
  letI : IsLocalHom (algebraMap (Localization.AtPrime p0) (Localization.AtPrime q.1)) := by
    simpa [f] using
      Localization.isLocalHom_localRingHom p0 q.1 (algebraMap R S) hq
  -- Proof comment: the map-algebra adapter packages the residue-field algebra transport, so the
  -- target proof only supplies the one-dimensionality and fraction-field side conditions.
  exact
    moduleFinite_maximalIdealResidueField_of_finite_fractionField_extension_mapAlgebra
      (A := Localization.AtPrime p0) (B := Localization.AtPrime q.1)
      (principal_prime_localization_dim_one (R := R) x hx)

lemma localized_prime_residue_field_finite
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime]
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    Module.Finite (Ideal.span ({x} : Set R)).ResidueField q.1.ResidueField := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  letI : q.1.IsPrime := q.2.1
  letI : q.1.LiesOver p0 := q.2.2
  -- Route correction: isolate the previously blocking residue-field transport.  The remaining
  -- local goal is now only the Lemma `10.119.10` application over `R_p → S_q`.
  have hlocalFinite :
      let hq : p0 = Ideal.comap (algebraMap R S) q.1 :=
        Ideal.LiesOver.over (p := p0) (P := q.1)
      let f := Localization.localRingHom p0 q.1 (algebraMap R S) hq
      letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q.1) := f.toAlgebra
      letI : Algebra (maximalIdeal (Localization.AtPrime p0)).ResidueField
          (maximalIdeal (Localization.AtPrime q.1)).ResidueField :=
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p0))
          (maximalIdeal (Localization.AtPrime q.1))
          f
          (IsLocalRing.maximalIdeal_comap f).symm).toAlgebra
      Module.Finite
        (maximalIdeal (Localization.AtPrime p0)).ResidueField
        (maximalIdeal (Localization.AtPrime q.1)).ResidueField := by
    -- Proof comment: the closed-fiber finiteness is isolated in the `Aq`-route helper, so the
    -- present proof only has to feed it into the already-proved prime-localization transport.
    exact localizedSubalgebra_rawClosedPointResidueField_finite (R := R) (M := M) x hx p q
  -- Proof comment: the transport helper converts the local closed-point residue-field result
  -- into the prime residue-field finiteness needed by the quotient-normalization step.
  simpa [p0, S] using
    (primeLocalization_residueFieldFinite_transport
      (A := R) (B := S) p0 q.1 hlocalFinite)

/-- Helper for Lemma 10.161.16 (Tate): the finite residue-field extension over `κ((x))`
determines the finite-dimensional `Frac(R / (x))`-structure needed for the `N-2` owner on the
principal quotient. -/
lemma principal_quotient_residueField_finiteDimensional
    {M : Type u} [Field M] [Algebra R M]
    (x : R)
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M))
    (hfinite : Module.Finite (Ideal.span ({x} : Set R)).ResidueField q.1.ResidueField) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    letI : Algebra (R ⧸ p0) q.1.ResidueField :=
      principal_quotient_residueField_algebra (R := R) (M := M) x q
    letI : FaithfulSMul (R ⧸ p0) q.1.ResidueField :=
      (faithfulSMul_iff_algebraMap_injective (R ⧸ p0) q.1.ResidueField).2
        (principal_quotient_to_prime_residueField_map_injective
          (R := R) (M := M) x q)
    letI : Algebra (FractionRing (R ⧸ p0)) q.1.ResidueField :=
      FractionRing.liftAlgebra (R ⧸ p0) q.1.ResidueField
    FiniteDimensional (FractionRing (R ⧸ p0)) q.1.ResidueField := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  letI : Algebra (R ⧸ p0) q.1.ResidueField :=
    principal_quotient_residueField_algebra (R := R) (M := M) x q
  letI : FaithfulSMul (R ⧸ p0) q.1.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective (R ⧸ p0) q.1.ResidueField).2
      (principal_quotient_to_prime_residueField_map_injective
        (R := R) (M := M) x q)
  letI : Algebra (FractionRing (R ⧸ p0)) q.1.ResidueField :=
    FractionRing.liftAlgebra (R ⧸ p0) q.1.ResidueField
  let e : FractionRing (R ⧸ p0) ≃+* p0.ResidueField :=
    FractionRing.algEquiv (R ⧸ p0) p0.ResidueField
  have hcompat :
      RingHom.comp (algebraMap (FractionRing (R ⧸ p0)) q.1.ResidueField) ↑e.symm =
        RingHom.comp (RingEquiv.refl q.1.ResidueField).toRingHom
          (algebraMap p0.ResidueField q.1.ResidueField) := by
    -- Proof comment: it is enough to compare the two maps on quotient classes from `R / (x)`.
    apply Ideal.ResidueField.ringHom_ext
    ext r
    change algebraMap (FractionRing (R ⧸ p0)) q.1.ResidueField
        (e.symm (algebraMap (R ⧸ p0) p0.ResidueField (Ideal.Quotient.mk p0 r))) =
      algebraMap p0.ResidueField q.1.ResidueField
        (algebraMap (R ⧸ p0) p0.ResidueField (Ideal.Quotient.mk p0 r))
    have he : e (algebraMap (R ⧸ p0) (FractionRing (R ⧸ p0))
        (Ideal.Quotient.mk p0 r)) =
        algebraMap (R ⧸ p0) p0.ResidueField (Ideal.Quotient.mk p0 r) := by
      exact AlgEquiv.commutes (FractionRing.algEquiv (R ⧸ p0) p0.ResidueField) _
    have hsymm : e.symm
        (algebraMap (R ⧸ p0) p0.ResidueField (Ideal.Quotient.mk p0 r)) =
        algebraMap (R ⧸ p0) (FractionRing (R ⧸ p0))
          (Ideal.Quotient.mk p0 r) := by
      rw [← he]
      simp only [RingEquiv.symm_apply_apply]
    -- Proof comment: after transporting the fraction-field model, both maps are the same
    -- `R / (x)`-algebra map into `κ(q)`.
    rw [hsymm]
    rw [← IsScalarTower.algebraMap_apply (R ⧸ p0)
      (FractionRing (R ⧸ p0)) q.1.ResidueField]
    rfl
  -- Proof comment: finite generation now transfers across the fraction-field equivalence.
  exact Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl q.1.ResidueField) hcompat

/-- Helper for Lemma 10.161.16 (Tate): an integral domain whose fraction field lands in a finite
normalization is finite over the base ring. -/
lemma moduleFinite_of_isIntegral_of_fractionRing_finite_integralClosure
    {A : Type u} {B : Type u} {K : Type u}
    [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Field K]
    [Algebra A B] [Algebra A K] [Algebra B K] [IsScalarTower A B K]
    [IsFractionRing B K]
    [Algebra.IsIntegral A B]
    [Module.Finite A (integralClosure A K)] :
    Module.Finite A B := by
  let f : B →ₐ[A] K := IsScalarTower.toAlgHom A B K
  let g : B →ₗ[A] integralClosure A K :=
    (f.codRestrict (integralClosure A K) (fun z ↦ by
      exact (Algebra.IsIntegral.isIntegral z).map f)).toLinearMap
  have hg_injective : Function.Injective g := by
    intro z w hzw
    apply IsFractionRing.injective B K
    change f z = f w
    exact congrArg Subtype.val hzw
  -- Proof comment: after codrestricting to the finite integral closure, the original domain
  -- inherits finite generation from the injective linear map into that finite module.
  exact Module.Finite.of_injective g hg_injective


/-- Helper for Lemma 10.161.16 (Tate): the quotient `S / q` is finite over `R / (x)` via the
localized residue-field extension and the normalization of `R / (x)` inside `κ(q)`. -/
lemma module_finite_prime_quotient_via_localized_residue_normalization
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime]
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))]
    [IsN2Ring (R ⧸ Ideal.span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R))
      (integralClosure R M ⧸ q.1) := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  let A := R ⧸ p0
  let K := q.1.ResidueField
  letI : Algebra A (S ⧸ q.1) := Ideal.Quotient.algebraOfLiesOver q.1 p0
  letI : Algebra A K := principal_quotient_residueField_algebra (R := R) (M := M) x q
  letI : IsScalarTower A (S ⧸ q.1) K :=
    principal_quotient_to_residueField_isScalarTower (R := R) (M := M) x q
  letI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2
      (principal_quotient_to_prime_residueField_map_injective (R := R) (M := M) x q)
  letI : Algebra (FractionRing A) K := FractionRing.liftAlgebra A K
  have hresFinite : Module.Finite p0.ResidueField q.1.ResidueField := by
    exact localized_prime_residue_field_finite (R := R) (M := M) x hx p q
  have hfiniteDimensional : FiniteDimensional (FractionRing A) K := by
    simpa [A, K, p0] using
      principal_quotient_residueField_finiteDimensional (R := R) (M := M) x q hresFinite
  letI : FiniteDimensional (FractionRing A) K := hfiniteDimensional
  have hintegralClosureFinite : Module.Finite A (integralClosure A K) := by
    exact IsN2Ring.integralClosure_finite_of_finiteDimensional (R := A) (L := K)
  letI : Module.Finite A (integralClosure A K) := hintegralClosureFinite
  -- Proof comment: `S / q` is integral over `A` and embeds in its fraction field `κ(q)`, so the
  -- finite normalization of `A` in `κ(q)` controls this quotient.
  exact moduleFinite_of_isIntegral_of_fractionRing_finite_integralClosure (A := A) (B := S ⧸ q.1)
    (K := K)

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Lemma 10.161.16 (Tate): finiteness of the first principal quotient implies
finiteness of every positive power quotient of the same principal ideal. -/
lemma principal_power_quotients_finite_of_finite_first_quotient
    {A : Type*} [CommRing A] [IsDomain A] [Algebra R A]
    {y : A} (hy : y ≠ 0)
    [Module.Finite R (A ⧸ Ideal.span ({y} : Set A))]
    (n : ℕ) :
    Module.Finite R (A ⧸ Ideal.span ({y ^ (n + 1)} : Set A)) := by
  have _hy : y ≠ 0 := hy
  induction n with
  | zero =>
      have hspan : Ideal.span ({y ^ (0 + 1)} : Set A) = Ideal.span ({y} : Set A) := by
        simp
      rw [hspan]
      infer_instance
  | succ n ih =>
      let I0 : Submodule R A :=
        Submodule.restrictScalars R ((Ideal.span ({y} : Set A) : Ideal A) : Submodule A A)
      let I1 : Submodule R A :=
        Submodule.restrictScalars R
          ((Ideal.span ({y ^ (n + 1)} : Set A) : Ideal A) : Submodule A A)
      let I2 : Submodule R A :=
        Submodule.restrictScalars R
          ((Ideal.span ({y ^ (n + 2)} : Set A) : Ideal A) : Submodule A A)
      -- Proof comment: the transition `A/(y^(n+2)) → A/(y^(n+1))` is induced by the
      -- containment of successive principal powers.
      have hleIdeal12 :
          Ideal.span ({y ^ (n + 2)} : Set A) ≤ Ideal.span ({y ^ (n + 1)} : Set A) := by
        rw [← Ideal.span_singleton_pow y (n + 2), ← Ideal.span_singleton_pow y (n + 1)]
        exact Ideal.pow_le_pow_right (Nat.le_succ (n + 1))
      have hle12 : I2 ≤ I1 := by
        intro a ha
        exact hleIdeal12 ha
      let g : (A ⧸ I2) →ₗ[R] (A ⧸ I1) := Submodule.factor hle12
      let mulStep : A →ₗ[R] A := Algebra.lmul R A (y ^ (n + 1))
      -- Proof comment: multiplication by `y^(n+1)` kills `A/(y)` modulo `y^(n+2)`, giving
      -- the left map in the short exact sequence.
      have hle0ker : I0 ≤ ((Submodule.mkQ I2).comp mulStep).ker := by
        intro a ha
        rw [LinearMap.mem_ker]
        change I2.mkQ (mulStep a) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        dsimp [mulStep, I0, I2] at ha ⊢
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
        apply Ideal.mem_span_singleton'.2
        refine ⟨c, ?_⟩
        rw [← hc]
        ring
      let f : (A ⧸ I0) →ₗ[R] (A ⧸ I2) :=
        I0.liftQ ((Submodule.mkQ I2).comp mulStep) hle0ker
      have hfac_apply (a : A) : g (I2.mkQ a) = I1.mkQ a := by
        change (Submodule.factor hle12 ∘ₗ I2.mkQ) a = I1.mkQ a
        rw [Submodule.factor_comp_mk]
      have hlift_apply (a : A) : f (I0.mkQ a) = I2.mkQ (mulStep a) := by
        change (I0.liftQ ((Submodule.mkQ I2).comp mulStep) hle0ker ∘ₗ I0.mkQ) a =
          ((Submodule.mkQ I2).comp mulStep) a
        rw [Submodule.liftQ_mkQ]
      have hg_surj : Function.Surjective g := by
        intro z
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I1 z
        refine ⟨Submodule.mkQ I2 a, ?_⟩
        exact hfac_apply a
      have hexact : Function.Exact f g := by
        intro z
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I2 z
        constructor
        · intro hg0
          have hga : g (I2.mkQ a) = 0 := by
            simpa [Submodule.mkQ_apply] using hg0
          have hzero : I1.mkQ a = 0 := by
            exact (hfac_apply a).symm.trans hga
          have haI1 : a ∈ I1 := (Submodule.Quotient.mk_eq_zero I1).mp hzero
          dsimp [I1] at haI1
          obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp haI1
          refine ⟨Submodule.mkQ I0 c, ?_⟩
          rw [hlift_apply]
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
          rw [← hc]
          simp [mulStep, mul_comm]
        · intro hzrange
          rcases hzrange with ⟨w, hw⟩
          rw [← hw]
          obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective I0 w
          rw [hlift_apply]
          rw [hfac_apply]
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          dsimp [I1, mulStep]
          apply Ideal.mem_span_singleton'.2
          have hmul : c * y ^ (n + 1) = y ^ (n + 1) * c := by
            ring
          exact ⟨c, hmul⟩
      letI : Module.Finite R (A ⧸ I0) := by
        dsimp [I0]
        exact (inferInstance : Module.Finite R (A ⧸ Ideal.span ({y} : Set A)))
      letI : Module.Finite R (A ⧸ I1) := by
        dsimp [I1]
        exact ih
      -- Proof comment: finite generation of the two outer terms transfers to the middle term
      -- by the exact-sequence finiteness criterion.
      exact (Module.Finite.of_exact hexact hg_surj : Module.Finite R (A ⧸ I2))

/-- Helper for Chap10 Lemma 10 161 16 Tate: the quotient by the principal ideal generated by the
chosen root is finite over the original base ring. -/
lemma rootPower_firstRootQuotient_finite
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime] (e : ℕ)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (y : integralClosure R M)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R M) x)
    (hpowS :
      ∀ z : integralClosure R M,
        z ^ (p ^ e) ∈ Set.range (algebraMap R (integralClosure R M))) :
    Module.Finite R (integralClosure R M ⧸
      Ideal.span ({y} : Set (integralClosure R M))) := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  letI : p0.IsPrime := by
    simpa [p0] using (inferInstance : (Ideal.span ({x} : Set R)).IsPrime)
  letI : Algebra.IsIntegral R S := inferInstance
  letI : Module.IsTorsionFree R M :=
    Module.IsTorsionFree.trans_faithfulSMul R (FractionRing R) M
  letI : Module.IsTorsionFree R S := inferInstance
  let q : p0.primesOver S := Classical.choice (inferInstance : Nonempty (p0.primesOver S))
  have hq_eq : q.1 = Ideal.span ({y} : Set S) := by
    -- Proof comment: the common-power hypothesis identifies the prime over `(x)` with `(y)`.
    simpa [p0, S] using
      (prime_over_span_singleton_eq_span_root (R := R) (M := M) hx p e q hpowS hy)
  letI : Algebra (R ⧸ p0) (S ⧸ q.1) := Ideal.Quotient.algebraOfLiesOver q.1 p0
  have hqFiniteQuot : Module.Finite (R ⧸ p0) (S ⧸ q.1) := by
    -- Proof comment: the residue-field normalization criterion gives finiteness over `R/(x)`.
    simpa [p0, S] using
      (module_finite_prime_quotient_via_localized_residue_normalization
        (R := R) (M := M) x hx p q)
  have hqFiniteR : Module.Finite R (S ⧸ q.1) := by
    -- Proof comment: forget scalars from `R/(x)` to `R`.
    exact Module.Finite.trans (R ⧸ p0) (S ⧸ q.1)
  rw [← hq_eq]
  exact hqFiniteR

/-- Helper for Chap10 Lemma 10 161 16 Tate: the quotient by `y ^ (p ^ e)` is finite over `R`
once the quotient by `y` is finite. -/
lemma rootPower_powerRootQuotient_finite
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime] (e : ℕ)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (y : integralClosure R M)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R M) x)
    (hpowS :
      ∀ z : integralClosure R M,
        z ^ (p ^ e) ∈ Set.range (algebraMap R (integralClosure R M))) :
    Module.Finite R (integralClosure R M ⧸
      Ideal.span ({y ^ (p ^ e)} : Set (integralClosure R M))) := by
  let S := integralClosure R M
  have hpow_pos : 0 < p ^ e := pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) e
  have hy_ne_zero : y ≠ 0 := by
    intro hy_zero
    have hxM : algebraMap R M x = 0 := by
      have hyM : (y : M) ^ (p ^ e) = algebraMap R M x := by
        exact congrArg (fun z : S => (z : M)) hy
      simpa [hy_zero, zero_pow hpow_pos.ne'] using hyM.symm
    exact hx ((algebraMap_injective_to_fractionField_extension (R := R) (K := M)) (by
      simpa using hxM))
  have hfirstR : Module.Finite R (S ⧸ Ideal.span ({y} : Set S)) := by
    -- Proof comment: use the first-quotient finiteness helper before applying the filtration.
    simpa [S] using
      (rootPower_firstRootQuotient_finite (R := R) (M := M) x hx p e y hy hpowS)
  letI : Module.Finite R (S ⧸ Ideal.span ({y} : Set S)) := hfirstR
  have hpow_sub : p ^ e - 1 + 1 = p ^ e :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpow_pos)
  have hpowerSub : Module.Finite R
      (S ⧸ Ideal.span ({y ^ (p ^ e - 1 + 1)} : Set S)) :=
    principal_power_quotients_finite_of_finite_first_quotient
      (R := R) (A := S) (y := y) hy_ne_zero (p ^ e - 1)
  have hspan :
      Ideal.span ({y ^ (p ^ e - 1 + 1)} : Set S) =
        Ideal.span ({y ^ (p ^ e)} : Set S) := by
    rw [hpow_sub]
  rw [← hspan]
  exact hpowerSub

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 161 16 Tate: the ideal generated by `x` after extension to the
normalization is the submodule generated by `y ^ (p ^ e)`. -/
lemma rootPower_baseIdeal_smul_top_eq_span_rootPower
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (p : ℕ) [Fact p.Prime] (e : ℕ)
    (y : integralClosure R M)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R M) x) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let S := integralClosure R M
    let J : Submodule R S :=
      Submodule.restrictScalars R
        ((Ideal.span ({y ^ (p ^ e)} : Set S) : Ideal S) : Submodule S S)
    p0 • (⊤ : Submodule R S) = J := by
  intro p0 S J
  have hmap : Ideal.map (algebraMap R S) p0 =
      Ideal.span ({y ^ (p ^ e)} : Set S) := by
    have hmap0 :
        Ideal.map (algebraMap R S) p0 =
          Ideal.span ({algebraMap R S x} : Set S) := by
      change Ideal.map (algebraMap R S) (Ideal.span ({x} : Set R)) =
        Ideal.span ({algebraMap R S x} : Set S)
      rw [Ideal.map_span, Set.image_singleton]
    rw [hmap0, hy.symm]
  -- Proof comment: compare the two extended ideals elementwise as `R`-submodules.
  rw [Ideal.smul_top_eq_map]
  dsimp [J]
  ext z
  change z ∈ Ideal.map (algebraMap R S) p0 ↔
    z ∈ Ideal.span ({y ^ (p ^ e)} : Set S)
  rw [hmap]

/-- Helper for Chap10 Lemma 10 161 16 Tate: if a `p ^ e`-th root `y` of `x` exists in the
normalization and all `p ^ e`-th powers come from `R`, then the quotient by `xS` is finite over
`R / (x)`. -/
lemma rootPower_baseQuotient_finite
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R) (hx : x ≠ 0)
    (p : ℕ) [Fact p.Prime] (e : ℕ)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (y : integralClosure R M)
    (hy : y ^ (p ^ e) = algebraMap R (integralClosure R M) x)
    (hpowS :
      ∀ z : integralClosure R M,
        z ^ (p ^ e) ∈ Set.range (algebraMap R (integralClosure R M))) :
    Module.Finite (R ⧸ Ideal.span ({x} : Set R))
      (integralClosure R M ⧸ Ideal.span ({x} : Set R) •
        (⊤ : Submodule R (integralClosure R M))) := by
  -- Proof comment: the source argument chooses the unique prime over `(x)`, identifies it with
  -- `(y)` using the common-power hypothesis, proves `S / yS` finite by residue-field
  -- normalization, and then passes from `yS` to `y ^ (p ^ e)S = xS` by the principal-power
  -- filtration.
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let S := integralClosure R M
  have hpowerR : Module.Finite R (S ⧸ Ideal.span ({y ^ (p ^ e)} : Set S)) := by
    -- Proof comment: the finite first quotient and principal-power filtration are packaged in a
    -- separate helper to keep this final assembly small.
    simpa [S] using
      (rootPower_powerRootQuotient_finite (R := R) (M := M) x hx p e y hy hpowS)
  let J : Submodule R S :=
    Submodule.restrictScalars R
      ((Ideal.span ({y ^ (p ^ e)} : Set S) : Ideal S) : Submodule S S)
  have hsubmodule_eq : p0 • (⊤ : Submodule R S) = J := by
    -- Proof comment: rewrite `xS` to `y^(p^e)S` using the root equation.
    simpa [p0, S, J] using
      (rootPower_baseIdeal_smul_top_eq_span_rootPower
        (R := R) (M := M) x p e y hy)
  have hpowerRJ : Module.Finite R (S ⧸ J) := by
    dsimp [J]
    exact hpowerR
  have htargetR : Module.Finite R (S ⧸ p0 • (⊤ : Submodule R S)) := by
    -- Proof comment: transfer finite generation across the quotient equivalence induced by
    -- the equality between `xS` and `y^(p^e)S`.
    rw [hsubmodule_eq]
    exact hpowerRJ
  letI : Module.Finite R (S ⧸ p0 • (⊤ : Submodule R S)) := htargetR
  -- Proof comment: because `(x)` kills this quotient, finite generation over `R` upgrades to
  -- finite generation over the quotient ring `R / (x)`.
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ p0)
    (S ⧸ p0 • (⊤ : Submodule R S))

/-- Helper for Lemma 10.161.16 (Tate): in positive characteristic, the Tate argument reduces the
`N-2` conclusion to finiteness of normalization for finite purely inseparable extensions. -/
lemma moduleFinite_integralClosure_of_finite_purelyInseparable_of_adicComplete_principal_quotient
    (x : R) (hx : x ≠ 0) (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p]
    [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [IsAdicComplete (span ({x} : Set R)) R]
    (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
    [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
    [IsPurelyInseparable (FractionRing R) L] :
    Module.Finite R (integralClosure R L) := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  letI : p0.IsPrime := by
    -- Proof comment: the quotient-domain hypothesis makes the principal ideal `(x)` prime.
    simpa [p0] using
      (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span ({x} : Set R))).1 inferInstance
  obtain ⟨e, hpowL⟩ :=
    exists_common_qpow_in_fractionRing_of_finite_purelyInseparable
      (R := R) p L
  obtain ⟨M, hFieldM, hAlgRM, hAlgFracM, hTowerRM, hFiniteM, iota, y0, hy0, hpowM⟩ :=
    exists_root_overfield_of_given_common_qpow (R := R) x p L e hpowL
  letI : Field M := hFieldM
  letI : Algebra R M := hAlgRM
  letI : Algebra (FractionRing R) M := hAlgFracM
  letI : IsScalarTower R (FractionRing R) M := hTowerRM
  letI : FiniteDimensional (FractionRing R) M := hFiniteM
  let S := integralClosure R M
  have hpowS :
      ∀ z : S, z ^ (p ^ e) ∈ Set.range (algebraMap R S) := by
    -- Proof comment: powers in the overfield that come from `Frac(R)` contract to powers in the
    -- normalization that already come from `R`.
    simpa [S] using
      (power_mem_range_of_integralClosure (R := R) (M := M) (n := p ^ e) hpowM)
  have hrootIntegral : IsIntegral R y0 := by
    -- Proof comment: a positive `p ^ e`-th power of the chosen root is the scalar `x`, hence the
    -- root is integral over `R`.
    have hxIntegral : IsIntegral R (algebraMap R M x) :=
      isIntegral_algebraMap
    exact IsIntegral.of_pow (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) e)
      (hy0.symm ▸ hxIntegral)
  let y : S := ⟨y0, hrootIntegral⟩
  have hyS : y ^ (p ^ e) = algebraMap R S x := by
    -- Proof comment: restate the root equation on the normalization carrier.
    apply Subtype.ext
    exact hy0
  have hquot :
      Module.Finite (R ⧸ p0) (S ⧸ p0 • (⊤ : Submodule R S)) := by
    -- Proof comment: the remaining quotient step packages the finite first quotient and the
    -- principal-power filtration.
    simpa [p0, S] using
      (rootPower_baseQuotient_finite (R := R) (M := M) x hx p e y hyS hpowS)
  letI : Module.Finite (R ⧸ p0) (S ⧸ p0 • (⊤ : Submodule R S)) := hquot
  have hhaus : IsHausdorff p0 S := by
    -- Proof comment: the common power condition forces the normalization to be separated for the
    -- `x`-adic filtration.
    simpa [p0, S] using
      (isHausdorff_span_singleton_of_common_qpow
        (R := R) (M := M) x hx (p ^ e)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) e) hpowS)
  letI : IsHausdorff p0 S := hhaus
  have hfiniteM : Module.Finite R S := by
    -- Proof comment: Lemma `10.96.12` upgrades finite quotient plus Hausdorffness and
    -- `x`-adic completeness to finite generation of the full normalization in `M`.
    exact moduleFinite_of_finite_quotient_of_isHausdorff (I := p0) (R := R) (M := S)
  -- Proof comment: descend finite generation from the root overfield back along
  -- `L →ₐ[FractionRing R] M`.
  exact
    finite_integralClosure_of_normal_overfield
      (R := R) (K := FractionRing R) (L := L) (M := M) iota hfiniteM

-- Proof sketch: reduce finite extensions of `FractionRing R` to the purely inseparable case using
-- Lemma `10.161.12`, adjoin a `q`th root `y` of `x`, and study the integral closure `S` of `R`
-- in the resulting extension. The quotient `S / yS` sits inside the integral closure of
-- `R / xR`, hence is finite by the `N-2` hypothesis on `R / xR`; then all quotients `S / y^n S`
-- are finite by a filtration argument, so also `S / xS` is finite. Finally apply the completeness
-- criterion of Lemma `10.96.12` to `S`, using Krull intersection to show `⋂ n, x^n S = 0`.
/-- Tate criterion for Chap10 Lemma 10 161 16 Tate: if `R` is a normal Noetherian domain,
`R ⧸ (x)` is a domain and `N-2`, and `R` is complete for the `x`-adic topology, then `R` is
`N-2`. -/
@[stacks 032P]
theorem isN2Ring_of_normal_of_adicComplete_of_principal_quotient_isN2Ring
    (x : R) [IsDomain (R ⧸ span ({x} : Set R))]
    [IsN2Ring (R ⧸ span ({x} : Set R))]
    [IsAdicComplete (span ({x} : Set R)) R] :
    IsN2Ring R := by
  by_cases hx : x = 0
  · subst hx
    let I : Ideal R := span ({(0 : R)} : Set R)
    have hI : I = ⊥ := by
      simp [I]
    let e : R ⧸ I ≃+* R := (Ideal.quotEquivOfEq hI).trans (RingEquiv.quotientBot R)
    have h_injective : Function.Injective (algebraMap R (R ⧸ I)) := by
      intro a b hab
      simpa [e] using congrArg e hab
    letI : Module.Finite R (R ⧸ I) := by
      exact Module.Finite.of_surjective
        (Ideal.Quotient.mkₐ R I).toLinearMap
        (Ideal.Quotient.mkₐ_surjective R I)
    letI : IsN2Ring (R ⧸ I) := inferInstance
    -- When `x = 0`, the quotient hypothesis already gives an `N-2` finite extension of `R`.
    exact isN2Ring_of_finite_extension (R := R) (S := R ⧸ I) h_injective
  by_cases hchar0 : ringChar (FractionRing R) = 0
  · haveI : CharZero (FractionRing R) :=
      (CharP.ringChar_zero_iff_CharZero (R := FractionRing R)).1 hchar0
    have hN1 : IsN1Ring R := isN1Ring_of_isIntegrallyClosed_noetherian_domain (R := R)
    -- In characteristic zero, Lemma `10.161.11` upgrades `N-1` to `N-2`.
    exact
      (isN1Ring_iff_isN2Ring_of_noetherian_of_fractionRing_charZero
        (R := R)).1 hN1
  · let p := ringChar (FractionRing R)
    have hp0 : p ≠ 0 := hchar0
    haveI : CharP (FractionRing R) p := ringChar.of_eq (R := FractionRing R) rfl
    haveI : NeZero p := ⟨hp0⟩
    haveI : Fact p.Prime := CharP.char_is_prime_of_pos (FractionRing R) p
    -- In characteristic `p`, reduce `N-2` to the purely inseparable test family from
    -- Lemma `10.161.12`.
    refine
      (isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions
        (R := R)).2 ?_
    intro L _ _ _ _ _ _
    exact
      moduleFinite_integralClosure_of_finite_purelyInseparable_of_adicComplete_principal_quotient
        (R := R) x hx p L

end

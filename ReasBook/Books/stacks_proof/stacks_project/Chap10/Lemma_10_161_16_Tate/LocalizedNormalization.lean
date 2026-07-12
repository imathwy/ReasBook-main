import StacksProject_2024.Chap10.Lemma_10_161_16_Tate.ResidueFieldBridge
universe u

open Ideal
open IsLocalRing
open IntermediateField Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Helper for Lemma 10.161.16 (Tate): after identifying the localized normalization model
`Aq ⊆ M` with the raw prime localization `S_q`, the canonical map `Rp → Aq` becomes the usual
localization map induced by `R → S`. -/
lemma principal_localized_subalgebra_comp_eq_localRingHom
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [IsFractionRing (integralClosure R M) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let Rp := Localization.AtPrime p0
    let S := integralClosure R M
    let Aq : Subalgebra S M :=
      Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    let fLoc : Rp →+* Localization.AtPrime q.1 :=
      Localization.localRingHom p0 q.1 (algebraMap R S) q.2.2.over
    let hsub :
        p0.primeCompl ≤ Submonoid.comap (algebraMap R S) q.1.primeCompl :=
      (Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
        (ge_of_eq q.2.2.over)
    let f : Rp →+* Aq := IsLocalization.map Aq (algebraMap R S) hsub
    let eLoc : Localization.AtPrime q.1 ≃ₐ[S] Aq :=
      IsLocalization.algEquiv q.1.primeCompl (Localization.AtPrime q.1) Aq
    (eLoc.symm : Aq →+* Localization.AtPrime q.1).comp f = fLoc := by
  intro p0 Rp S Aq fLoc hsub f eLoc
  -- Proof comment: both maps out of `Rp` are obtained from the same map `R → S` by the universal
  -- property of localization at the prime complement of `(x)`.
  apply IsLocalization.ringHom_ext p0.primeCompl
  ext r
  calc
    (((eLoc.symm : Aq →+* Localization.AtPrime q.1).comp f).comp (algebraMap R Rp)) r =
        eLoc.symm (algebraMap S Aq (algebraMap R S r)) := by
          simp [f]
    _ = algebraMap S (Localization.AtPrime q.1) (algebraMap R S r) := by
      simpa using (eLoc.symm.commutes (algebraMap R S r))
    _ = (fLoc.comp (algebraMap R Rp)) r := by
      exact (Localization.localRingHom_to_map p0 q.1 (algebraMap R S) q.2.2.over r).symm

/-- Helper for Lemma 10.161.16 (Tate): the canonical map from the principal localization `Rp`
to the localized normalization model `Aq` is a local ring homomorphism. -/
lemma principal_localized_subalgebra_isLocalHom
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [IsFractionRing (integralClosure R M) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let Rp := Localization.AtPrime p0
    let S := integralClosure R M
    let Aq : Subalgebra S M :=
      Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    let f : Rp →+* Aq :=
      IsLocalization.map Aq (algebraMap R S)
        ((Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
          (ge_of_eq q.2.2.over))
    IsLocalHom f := by
  intro p0 Rp S Aq f
  let fLoc : Rp →+* Localization.AtPrime q.1 :=
    Localization.localRingHom p0 q.1 (algebraMap R S) q.2.2.over
  let eLoc : Localization.AtPrime q.1 ≃ₐ[S] Aq :=
    IsLocalization.algEquiv q.1.primeCompl (Localization.AtPrime q.1) Aq
  letI : IsLocalRing Aq := RingEquiv.isLocalRing eLoc.toRingEquiv
  have hf_eq :
      (eLoc.symm : Aq →+* Localization.AtPrime q.1).comp f = fLoc :=
    principal_localized_subalgebra_comp_eq_localRingHom (R := R) (M := M) x q
  letI : IsLocalHom fLoc :=
    Localization.isLocalHom_localRingHom p0 q.1 (algebraMap R S) q.2.2.over
  letI : IsLocalHom (eLoc.symm : Aq →+* Localization.AtPrime q.1) :=
    eLoc.symm.surjective.isLocalHom
  letI : IsLocalHom ((eLoc.symm : Aq →+* Localization.AtPrime q.1).comp f) := by
    exact hf_eq ▸ inferInstance
  -- Proof comment: once the comparison with the raw prime localization is fixed, locality
  -- descends from the composite `Rp → S_q`.
  exact isLocalHom_of_comp f (eLoc.symm : Aq →+* Localization.AtPrime q.1)

/-- Helper for Lemma 10.161.16 (Tate): the explicit composite `Rp → Aq → M` agrees with the
original scalar map `R → M` on base elements. This is the transport-stable core of the
`Rp → Aq → M` tower used later in the local residue-field step. -/
lemma principal_localized_subalgebra_comp_apply_algebraMap
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let Rp := Localization.AtPrime p0
    let S := integralClosure R M
    letI : FaithfulSMul R M :=
      (faithfulSMul_iff_algebraMap_injective R M).2
        (algebraMap_injective_to_fractionField_extension (R := R) (K := M))
    letI : IsFractionRing S M :=
      integralClosure.isFractionRing_of_finite_extension
        (A := R) (K := FractionRing R) (L := M)
    let Aq : Subalgebra S M :=
      Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    let hsub :
        p0.primeCompl ≤ Submonoid.comap (algebraMap R S) q.1.primeCompl :=
      (Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
        (ge_of_eq q.2.2.over)
    let f : Rp →+* Aq := IsLocalization.map Aq (algebraMap R S) hsub
    ∀ r : R, ((algebraMap Aq M).comp f) (algebraMap R Rp r) = algebraMap R M r := by
  intro p0 Rp S Aq hsub f
  intro r
  -- Proof comment: on a base element, the localization map `Rp → Aq` sends `r / 1` to the same
  -- scalar in the localization subalgebra, and forgetting to `M` recovers the original image.
  change algebraMap Aq M (f (algebraMap R Rp r)) = algebraMap R M r
  rw [show f (algebraMap R Rp r) = algebraMap S Aq (algebraMap R S r) by
    simp [f]]
  simpa using (IsScalarTower.algebraMap_apply R S M r).symm

/-- Helper for Lemma 10.161.16 (Tate): the explicit localized normalization model yields the
source-faithful scalar tower `R → Rp → M`. -/
lemma principal_localized_subalgebra_base_isScalarTower
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let Rp := Localization.AtPrime p0
    let S := integralClosure R M
    letI : FaithfulSMul R M :=
      (faithfulSMul_iff_algebraMap_injective R M).2
        (algebraMap_injective_to_fractionField_extension (R := R) (K := M))
    letI : IsFractionRing S M :=
      integralClosure.isFractionRing_of_finite_extension
        (A := R) (K := FractionRing R) (L := M)
    let Aq : Subalgebra S M :=
      Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    let hsub :
        p0.primeCompl ≤ Submonoid.comap (algebraMap R S) q.1.primeCompl :=
      (Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
        (ge_of_eq q.2.2.over)
    let f : Rp →+* Aq := IsLocalization.map Aq (algebraMap R S) hsub
    letI : Algebra Rp Aq := f.toAlgebra
    letI : Algebra Rp M := ((algebraMap Aq M).comp f).toAlgebra
    IsScalarTower R Rp M := by
  let p0 : Ideal R := Ideal.span ({x} : Set R)
  let Rp := Localization.AtPrime p0
  let S := integralClosure R M
  letI : FaithfulSMul R M :=
    (faithfulSMul_iff_algebraMap_injective R M).2
      (algebraMap_injective_to_fractionField_extension (R := R) (K := M))
  letI : IsFractionRing S M :=
    integralClosure.isFractionRing_of_finite_extension
      (A := R) (K := FractionRing R) (L := M)
  let Aq : Subalgebra S M :=
    Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
  let hsub :
      p0.primeCompl ≤ Submonoid.comap (algebraMap R S) q.1.primeCompl :=
    (Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
      (ge_of_eq q.2.2.over)
  let f : Rp →+* Aq := IsLocalization.map Aq (algebraMap R S) hsub
  letI : Algebra Rp Aq := f.toAlgebra
  letI : Algebra Rp M := ((algebraMap Aq M).comp f).toAlgebra
  -- Proof comment: the localized normalization map `Rp → Aq → M` was defined by composing
  -- the localization map with the ambient embedding `Aq ⊆ M`, so the scalar tower is exactly
  -- the base-element computation proved in `principal_localized_subalgebra_comp_apply_algebraMap`.
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  change algebraMap R M r = algebraMap Aq M (f (algebraMap R Rp r))
  exact (principal_localized_subalgebra_comp_apply_algebraMap (R := R) (M := M) x q r).symm

/-- Helper for Chap10 Lemma 10 161 16 Tate: the transported fraction-field algebra for
`Frac(Aq)` is compatible with the localized base ring `Rp`. -/
lemma localizedSubalgebra_fractionRing_isScalarTower
    {M : Type u} [Field M] [Algebra R M] [Algebra (FractionRing R) M]
    [IsScalarTower R (FractionRing R) M] [FiniteDimensional (FractionRing R) M]
    [FaithfulSMul R M] [IsFractionRing (integralClosure R M) M]
    (x : R)
    [IsDomain (R ⧸ span ({x} : Set R))]
    [(Ideal.span ({x} : Set R)).IsPrime]
    (q : (Ideal.span ({x} : Set R)).primesOver (integralClosure R M)) :
    let p0 : Ideal R := Ideal.span ({x} : Set R)
    let Rp := Localization.AtPrime p0
    let S := integralClosure R M
    let Aq : Subalgebra S M :=
      Localization.subalgebra.ofField M q.1.primeCompl q.1.primeCompl_le_nonZeroDivisors
    let hsub :
        p0.primeCompl ≤ Submonoid.comap (algebraMap R S) q.1.primeCompl :=
      (Localization.le_comap_primeCompl_iff (I := p0) (J := q.1) (f := algebraMap R S)).2
        (ge_of_eq q.2.2.over)
    let f : Rp →+* Aq := IsLocalization.map Aq (algebraMap R S) hsub
    letI : Algebra Rp Aq := f.toAlgebra
    letI : Algebra Rp M := ((algebraMap Aq M).comp f).toAlgebra
    letI : IsScalarTower R Rp M :=
      principal_localized_subalgebra_base_isScalarTower (R := R) (M := M) x q
    letI : FaithfulSMul Rp M :=
      (faithfulSMul_iff_algebraMap_injective Rp M).2
        (localizationAtPrime_algebraMap_injective_to_fractionField_extension
          (A := R) (p := p0) (K := FractionRing R) (L := M))
    letI : Algebra Aq M := Algebra.ofSubsemiring Aq.toSubsemiring
    letI : IsScalarTower Rp Aq M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsFractionRing Aq M := inferInstance
    letI : Algebra (FractionRing Rp) (FractionRing Aq) :=
      ((FractionRing.algEquiv Aq M).symm.toRingHom.comp
        (algebraMap (FractionRing Rp) M)).toAlgebra
    letI : SMul (FractionRing Rp) (FractionRing Aq) := Algebra.toSMul
    letI : Module (FractionRing Rp) (FractionRing Aq) := Algebra.toModule
    IsScalarTower Rp (FractionRing Rp) (FractionRing Aq) := by
  intro p0 Rp S Aq hsub f
  letI : Algebra Rp Aq := f.toAlgebra
  letI : Algebra Rp M := ((algebraMap Aq M).comp f).toAlgebra
  letI : IsScalarTower R Rp M :=
    principal_localized_subalgebra_base_isScalarTower (R := R) (M := M) x q
  letI : FaithfulSMul Rp M :=
    (faithfulSMul_iff_algebraMap_injective Rp M).2
      (localizationAtPrime_algebraMap_injective_to_fractionField_extension
        (A := R) (p := p0) (K := FractionRing R) (L := M))
  letI : Algebra Aq M := Algebra.ofSubsemiring Aq.toSubsemiring
  letI : IsScalarTower Rp Aq M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsFractionRing Aq M := inferInstance
  letI : Algebra (FractionRing Rp) (FractionRing Aq) :=
    ((FractionRing.algEquiv Aq M).symm.toRingHom.comp
      (algebraMap (FractionRing Rp) M)).toAlgebra
  letI : SMul (FractionRing Rp) (FractionRing Aq) := Algebra.toSMul
  letI : Module (FractionRing Rp) (FractionRing Aq) := Algebra.toModule
  -- Proof comment: reduce the tower compatibility to the generic fraction-field transport lemma.
  exact fractionRing_isScalarTower_of_isFractionRing (A := Rp) (B := Aq) (L := M)

end

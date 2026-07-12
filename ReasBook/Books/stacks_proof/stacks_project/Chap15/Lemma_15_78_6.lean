import Mathlib
import StacksProject_2024.Chap10.Proposition_10_110_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_105_3
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_51_11
import StacksProject_2024.Chap15.Lemma_15_67_18
import StacksProject_2024.Chap15.Lemma_15_67_11
import StacksProject_2024.Chap15.Lemma_15_67_3
import StacksProject_2024.Chap15.Lemma_15_78_2
import StacksProject_2024.Chap15.Lemma_15_105_5

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open IsLocalRing

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "KModA" => HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ)
local notation "KModB" => HomotopyCategory (ModuleCat B) (ComplexShape.up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QhB" => (DerivedCategory.Qh : KModB ⥤ DModB)

/-- Helper for Lemma 15.78.6: a natural isomorphism between exact module functors induces the
corresponding objectwise isomorphism on derived categories. -/
noncomputable def mapDerivedCategory_obj_iso_of_natIso
    {R S : Type u} [CommRing R] [CommRing S]
    {F G : ModuleCat R ⥤ ModuleCat S}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory (ModuleCat R)) :
    (F.mapDerivedCategory.obj K) ≅ (G.mapDerivedCategory.obj K) :=
  let C := DerivedCategory.Q.objPreimage K
  (F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (F.mapDerivedCategoryFactors.app C) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app C) ≪≫
    (G.mapDerivedCategoryFactors.app C).symm ≪≫
    (G.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K)

/-- Helper for Lemma 15.78.6: the derived functor of an exact composite agrees objectwise with the
composite of the induced derived functors. -/
noncomputable def mapDerivedCategory_comp_obj_iso
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (F : ModuleCat R ⥤ ModuleCat S) (G : ModuleCat S ⥤ ModuleCat T)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory (ModuleCat R)) :
    ((F ⋙ G).mapDerivedCategory.obj K) ≅
      (G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K)) :=
  let C := DerivedCategory.Q.objPreimage K
  ((F ⋙ G).mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    ((F ⋙ G).mapDerivedCategoryFactors.app C) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)).symm ≪≫
    (G.mapDerivedCategory).mapIso ((F.mapDerivedCategoryFactors.app C).symm) ≪≫
    (G.mapDerivedCategory).mapIso
      ((F.mapDerivedCategory).mapIso (DerivedCategory.Q.objObjPreimageIso K))

/-- Helper for Lemma 15.78.6: scalar extension along a ring equivalence is canonically the inverse
restriction-of-scalars equivalence. -/
noncomputable def extendScalars_iso_restrictScalars_inverse
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    ModuleCat.extendScalars e.toRingHom ≅ ModuleCat.restrictScalars e.symm :=
  (ModuleCat.extendRestrictScalarsAdj e.toRingHom).leftAdjointUniq
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- Helper for Lemma 15.78.6: the cochain-level scalar-extension functor along `A → B`. -/
private abbrev ExtCpx :
    CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat B) ℤ :=
  (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Helper for Lemma 15.78.6: termwise scalar extension preserves the lower support bound of a
cochain complex. -/
lemma extendScalarsComplex_isStrictlyGE
    {E : CochainComplex (ModuleCat A) ℤ} {a : ℤ}
    (hE : E.IsStrictlyGE a) :
    ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff] at hE ⊢
  intro i hi
  change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (E.X i) : ModuleCat B))
  simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hE i hi)

/-- Helper for Lemma 15.78.6: termwise scalar extension preserves the upper support bound of a
cochain complex. -/
lemma extendScalarsComplex_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ} {b : ℤ}
    (hE : E.IsStrictlyLE b) :
    ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff] at hE ⊢
  intro i hi
  change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (E.X i) : ModuleCat B))
  simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hE i hi)

/-- Helper for Lemma 15.78.6: termwise scalar extension carries flat terms to flat terms. -/
lemma extendScalarsComplex_isTermwiseFlat
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) :
    ((ExtCpx (A := A) (B := B)).obj E).IsTermwiseFlat := by
  change ∀ i : ℤ, Module.Flat B (((ExtCpx (A := A) (B := B)).obj E).X i : Type u)
  intro i
  letI : Module.Flat A (E.X i : Type u) := hE i
  let eSelf :
      ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
    { __ := AddEquiv.refl B
      map_smul' := fun _ _ ↦ rfl }
  let eTensor :
      TensorProduct A
          ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))
          ↑(E.X i) ≃ₗ[B]
        TensorProduct A B (E.X i : Type u) :=
    TensorProduct.AlgebraTensorModule.congr
      eSelf
      (LinearEquiv.refl A (E.X i : Type u))
  have hFlatTensor : Module.Flat B (TensorProduct A B (E.X i : Type u)) := inferInstance
  have hFlatExt :
      Module.Flat B (((ModuleCat.extendScalars (algebraMap A B)).obj (E.X i) : ModuleCat B) : Type u) := by
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      Module.Flat.of_linearEquiv eTensor.symm hFlatTensor
  simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using hFlatExt

/-- Helper for Lemma 15.78.6: a bounded-above termwise-flat complex is K-flat. -/
private theorem isKFlat_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    E.IsKFlat := by
  have hminus : CochainComplex.minus (ModuleCat A) E :=
    (CochainComplex.minus_iff (ModuleCat A) E).2 ⟨b, hLE⟩
  exact CochainComplex.isKFlat_of_boundedAbove_of_flat E hminus hE

/-- Helper for Lemma 15.78.6: this is the explicit total-left-derived counit comparison from the
derived scalar extension of a strict cochain model to its ordinary scalar extension. -/
private noncomputable def derivedTensorWithAlgebra_complexComparison
    (E : CochainComplex (ModuleCat A) ℤ) :
    ((derivedTensorWithAlgebra (algebraMap A B)).obj (DerivedCategory.Q.obj E)) ⟶
      DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj E) :=
  let F₀ : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive
  let F : KModA ⥤ DModB := F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QhB
  letI : F.HasLeftDerivedFunctor QisA := by
    change
      ((ModuleCat.extendScalars (algebraMap A B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        QhB).HasLeftDerivedFunctor QisA
    simpa using extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap A B)
  (derivedTensorWithAlgebra (algebraMap A B)).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat A)).app E).inv ≫
    (F.totalLeftDerivedCounit QhA QisA).app
      ((HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).obj E) ≫
    QhB.map
      ((Functor.mapHomotopyCategoryFactors
        (ModuleCat.extendScalars (algebraMap A B)) (ComplexShape.up ℤ)).inv.app E) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat B)).app
      ((ExtCpx (A := A) (B := B)).obj E)).hom

/-- Helper for Lemma 15.78.6: a bounded-above termwise-flat representative computes derived
scalar extension through the canonical counit comparison. -/
private theorem derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) := by
  let F₀ : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).left_adjoint_additive
  let F : KModA ⥤ DModB := F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ QhB
  let qE : KModA := (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).obj E
  letI : F.HasLeftDerivedFunctor QisA := by
    change
      ((ModuleCat.extendScalars (algebraMap A B)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        QhB).HasLeftDerivedFunctor QisA
    simpa using extendScalarsToDerived_hasLeftDerivedFunctor (algebraMap A B)
  letI : E.IsKFlat :=
    isKFlat_of_termwiseFlat_of_isStrictlyLE (A := A) hE hLE
  letI : F.ComputesLeftDerivedAt QisA qE := by
    infer_instance
  letI : IsIso ((F.totalLeftDerivedCounit QhA QisA).app qE) :=
    (Functor.computesLeftDerivedAt_iff (F := F) (S := QisA) (X := qE)).1 inferInstance
  simpa [derivedTensorWithAlgebra_complexComparison, F, F₀, qE]

/-- Helper for Lemma 15.78.6: a bounded-above termwise-flat cochain model computes derived scalar
extension by termwise scalar extension. -/
noncomputable def derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    ((DerivedCategory.Q.obj E) ⊗[A]^L[B]) ≅
      DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj E) :=
  letI :
      IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) :=
    derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFlat_of_isStrictlyLE
      (A := A) (B := B) hE hLE
  asIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E)

/-- Helper for Lemma 15.78.6: derived scalar extension preserves tor-amplitude. -/
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra
    (K : DModA) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn (K ⊗[A]^L[B]) a b := by
  obtain ⟨E, eE, hEGE, hELE, hEFlat⟩ :=
    (hasTorAmplitudeIn_iff_exists_flat_representative (R := A) K a b).1 hK
  have hExtGE :
      ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyGE a :=
    extendScalarsComplex_isStrictlyGE (A := A) (B := B) hEGE
  have hExtLE :
      ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyLE b :=
    extendScalarsComplex_isStrictlyLE (A := A) (B := B) hELE
  have hExtFlat :
      ((ExtCpx (A := A) (B := B)).obj E).IsTermwiseFlat :=
    extendScalarsComplex_isTermwiseFlat (A := A) (B := B) hEFlat
  have hModel :
      HasTorAmplitudeIn
        (DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj E))
        a b := by
    exact
      (hasTorAmplitudeIn_iff_exists_flat_representative
        (R := B)
        (DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj E))
        a
        b).2
        ⟨(ExtCpx (A := A) (B := B)).obj E, Iso.refl _, hExtGE, hExtLE, hExtFlat⟩
  have hBaseChangeModel :
      HasTorAmplitudeIn
        (((DerivedCategory.Q.obj E) ⊗[A]^L[B]))
        a b := by
    exact
      (hasTorAmplitudeIn_of_iso_local
        (R := B)
        (a := a) (b := b)
        (derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
          (A := A) (B := B) hEFlat hELE)).2
        hModel
  exact
    (hasTorAmplitudeIn_of_iso_local
      (R := B)
      (a := a) (b := b)
      ((derivedTensorWithAlgebra (algebraMap A B)).mapIso eE)).2
      hBaseChangeModel

/- Domain-style sampling for Lemma 15.78.6:
- primary domain: pseudo-coherent derived complexes over a flat local ring map, with perfection
  and tor-amplitude detected on the closed-fiber residue field;
- sampled owner declarations:
  `K.IsPerfect`,
  `HasTorAmplitudeIn`,
  `primeResidueFieldDerivedHomology`,
  `hasGlobalDimensionLE_of_isRegularLocalRing`;
- best owner abstraction: the core/canonical owners are `K.IsPerfect`, `HasTorAmplitudeIn`, and
  the residue-field-fiber bridge `primeResidueFieldDerivedHomology`; this file is only a
  `source-facing` local closed-fiber specialization, so it should reuse those owners rather than
  restating the derived special fiber entrywise;
- primitive vs. derived:
  primitive data are the pseudo-coherent object `K`, the local closed-fiber regularity hypothesis,
  the dimension bound `ringKrullDim ((maximalIdeal A).Fiber B) = d`, and the closed-point
  residue-field homology vanishing of the restriction of scalars of `K` to `D(A)`;
  derived API is the conjunction `K.IsPerfect ∧ HasTorAmplitudeIn K (a - d) b` and the thin
  bridge from tor-amplitude over `A` to the closed-point vanishing hypothesis;
- source/core/bridge triage:
  `source-facing`: the two local closed-fiber criteria below;
  `core/canonical`: `K.IsPerfect`, `HasTorAmplitudeIn`, and
    `primeResidueFieldDerivedHomology`;
  `bridge/view`: restriction of scalars along `A → B`.
-/

-- Proof sketch: identify the derived tensor with `κ(maximalIdeal A)` as a complex over the closed
-- fiber `(maximalIdeal A).Fiber B`, use the regular-local hypothesis and Proposition `10.110.1`
-- to bound the global dimension of that fiber by `d`, and then apply Lemma `15.67.19` to shift
-- the homology support from `[a, b]` to `[(a - d), b]`. Finally use the maximal-ideal case of
-- Lemma `15.78.2` for the local ring `B`.
/-- Helper for Lemma 15.78.6: tor-amplitude of the restriction of scalars should force vanishing
of the closed-point derived fiber over `A`. -/
lemma base_residueFieldDerivedHomology_isZero_of_hasTorAmplitudeIn_outside
    (K : DModB) {a b i : ℤ}
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b)
    (hi : i ∉ Set.Icc a b) :
    IsZero
      (primeResidueFieldDerivedHomology
        (closedPoint A)
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        i) := by
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
  let κA := (closedPoint A).asIdeal.ResidueField
  have hKκ :
      HasTorAmplitudeIn
        ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
        a b := by
    -- Proof comment: derived base change to the residue field preserves the original
    -- tor-amplitude interval.
    simpa [KA, κA] using
      hasTorAmplitudeIn_derivedTensorWithAlgebra
        (A := A) (B := κA) KA a b hKamp
  -- Proof comment: after passing to the residue field, tor-amplitude directly forces the
  -- degree-`i` homology of the derived fiber to vanish outside `[a, b]`.
  simpa [primeResidueFieldDerivedHomology, KA, κA] using
    isZero_homology_of_hasTorAmplitudeIn_outside (R := κA) hKκ hi

/-- Helper for Lemma 15.78.6: vanishing of the `κ(A)`-fiber homology outside `[a, b]` upgrades to
tor-amplitude in `[a, b]` over the residue field `κ(A)`. -/
lemma residue_field_torAmplitude_of_homology_vanishing
    (K : DModB) {a b : ℤ}
    (hKκ :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint A)
            ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
            i)) :
    let κA := (closedPoint A).asIdeal.ResidueField
    let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
    HasTorAmplitudeIn
      ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
      a b := by
  let κA := (closedPoint A).asIdeal.ResidueField
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
  let Kκ : DerivedCategory (ModuleCat κA) :=
    (derivedTensorWithAlgebra (algebraMap A κA)).obj KA
  have hGE : Kκ.IsGE a := by
    -- Proof comment: the residue-field homology vanishing gives the lower t-structure bound.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hKκ i <| by
      intro hmem
      exact (not_lt_of_ge hmem.1 hi).elim
  have hLE : Kκ.IsLE b := by
    -- Proof comment: the same homology vanishing gives the upper t-structure bound.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hKκ i <| by
      intro hmem
      exact (not_lt_of_ge hmem.2 hi).elim
  letI : HasWeakDimensionLE κA 0 :=
    hasWeakDimensionLEZero_of_isAbsolutelyFlatRing κA
  -- Proof comment: over the field `κ(A)`, cohomology concentration in `[a, b]` is already
  -- tor-amplitude in `[a, b]`.
  simpa [κA, KA, Kκ] using
    hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
      (R := κA) 0 Kκ a b hGE hLE

/-- Helper for Lemma 15.78.6: in a local ring, vanishing of the closed-point residue-field
homology outside `[a, b]` is enough to recover perfectness with tor-amplitude in `[a, b]`. -/
lemma local_perfect_torAmplitude_of_closedPoint_residueField_vanishing
    (K : DModB) (a b : ℤ) (hKpc : K.IsPseudoCoherent)
    (hclosed :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology (closedPoint B) K i)) :
    K.IsPerfect ∧ HasTorAmplitudeIn K a b := by
  let hTFAE :=
    perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
      K a b hKpc
  have hmax :
      ∀ (m : PrimeSpectrum B) (_ : m.asIdeal.IsMaximal) (i : ℤ), i ∉ Set.Icc a b →
        IsZero (primeResidueFieldDerivedHomology m K i) := by
    intro m hm i hi
    have hmClosed : m = closedPoint B := by
      apply PrimeSpectrum.ext
      calc
        m.asIdeal = maximalIdeal B := IsLocalRing.eq_maximalIdeal hm
        _ = (closedPoint B).asIdeal := (closedPoint_asIdeal_eq_maximalIdeal B).symm
    -- Proof comment: a local ring has only one maximal point, so every maximal fiber test is the
    -- closed-point test.
    simpa [hmClosed] using hclosed i hi
  -- Proof comment: clause `(3)` of Lemma `15.78.2` is now exactly the closed-point hypothesis.
  exact (hTFAE.out 2 0).mp hmax

/-- Helper for Lemma 15.78.6: the closed point of `B` contracts to the closed point of `A`
under a local ring homomorphism. -/
lemma comap_closedPoint_eq_closedPoint :
    PrimeSpectrum.comap (algebraMap A B) (closedPoint B) = closedPoint A := by
  -- Proof comment: on ideals, a local map contracts the maximal ideal of `B` to the maximal
  -- ideal of `A`.
  apply PrimeSpectrum.ext
  simpa [closedPoint_asIdeal_eq_maximalIdeal A, closedPoint_asIdeal_eq_maximalIdeal B] using
    (IsLocalRing.maximalIdeal_comap (algebraMap A B))

/-- Helper for Lemma 15.78.6: the canonical prime of the closed fiber attached to `closedPoint B`
is the closed point of the local closed fiber. -/
lemma closed_fiber_prime_over_closed_point_eq_closedPoint :
    let C := ((maximalIdeal A).Fiber B)
    let qbar : PrimeSpectrum C :=
      (PrimeSpectrum.preimageOrderIsoFiber A B (closedPoint A))
        ⟨closedPoint B, comap_closedPoint_eq_closedPoint (A := A) (B := B)⟩
    qbar = closedPoint C := by
  let C := ((maximalIdeal A).Fiber B)
  let qOver : PrimeSpectrum.comap (algebraMap A B) ⁻¹' {closedPoint A} :=
    ⟨closedPoint B, comap_closedPoint_eq_closedPoint (A := A) (B := B)⟩
  let e := PrimeSpectrum.preimageOrderIsoFiber A B (closedPoint A)
  let qbar : PrimeSpectrum C := e qOver
  have hqOver_max : IsMax qOver := by
    intro r hr
    apply Subtype.ext
    apply PrimeSpectrum.ext
    have hclosedMax : (closedPoint B).asIdeal.IsMaximal := by
      simpa [closedPoint_asIdeal_eq_maximalIdeal B] using (maximalIdeal.isMaximal B)
    have hrIdeal : (closedPoint B).asIdeal ≤ r.1.asIdeal := hr
    exact Ideal.IsMaximal.eq_of_le hclosedMax r.1.2.1.ne_top hrIdeal
  have hqbar_max : IsMax qbar := by
    intro r hr
    have hr' : qOver ≤ e.symm r := by
      simpa [qbar] using (e.symm.monotone hr : e.symm qbar ≤ e.symm r)
    have hback : e.symm r ≤ qOver := hqOver_max hr'
    simpa [qbar] using (e.monotone hback : e (e.symm r) ≤ e qOver)
  have hqbar_le_closed : qbar ≤ closedPoint C := by
    -- Proof comment: every prime of the local closed fiber lies under its unique closed point.
    show qbar.asIdeal ≤ (closedPoint C).asIdeal
    simpa [closedPoint_asIdeal_eq_maximalIdeal C] using
      (IsLocalRing.le_maximalIdeal qbar.2.1.ne_top)
  have hclosed_le_qbar : closedPoint C ≤ qbar := hqbar_max hqbar_le_closed
  exact le_antisymm hqbar_le_closed hclosed_le_qbar

/-- Helper for Lemma 15.78.6: the canonical `preimageEquivFiber` prime over `closedPoint B`
is the closed point of the local closed fiber. -/
lemma closed_fiber_equiv_prime_over_closed_point_eq_closedPoint :
    let C := ((maximalIdeal A).Fiber B)
    let qbar : PrimeSpectrum C :=
      PrimeSpectrum.preimageEquivFiber A B (closedPoint A)
        ⟨closedPoint B, comap_closedPoint_eq_closedPoint (A := A) (B := B)⟩
    qbar = closedPoint C := by
  -- Proof comment: compare ideals rather than points, so the earlier order-iso version rewrites
  -- the canonical fiber prime without further transport noise.
  apply PrimeSpectrum.ext
  simpa using congrArg PrimeSpectrum.asIdeal
    (closed_fiber_prime_over_closed_point_eq_closedPoint (A := A) (B := B))

/-- Helper for Lemma 15.78.6: the iterated closed-fiber base change
`K|_A ⊗[A]^L κ(A) ⊗[κ(A)]^L C` has the same closed-point residue-field homology as the direct
closed-fiber base change `K|_A ⊗[A]^L C`. -/
lemma closed_fiber_iterated_baseChange_homology_iso
    (K : DModB) (j : ℤ) :
    let κA := (closedPoint A).asIdeal.ResidueField
    let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
    let C := ((maximalIdeal A).Fiber B)
    let L : DerivedCategory (ModuleCat C) :=
      (derivedTensorWithAlgebra (algebraMap κA C)).obj
        ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
    let Kbase : DerivedCategory (ModuleCat C) :=
      (derivedTensorWithAlgebra (algebraMap A C)).obj KA
    primeResidueFieldDerivedHomology (closedPoint C) L j ≅
      primeResidueFieldDerivedHomology (closedPoint C) Kbase j := by
  let κA := (closedPoint A).asIdeal.ResidueField
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
  let C := ((maximalIdeal A).Fiber B)
  let L : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap κA C)).obj
      ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
  let Kbase : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap A C)).obj KA
  have hcomp :
      (algebraMap κA C).comp (algebraMap A κA) = algebraMap A C := by
    -- Proof comment: the direct scalar map `A → C` is the composition `A → κ(A) → C`.
    ext x
    rfl
  let eBase : L ≅ Kbase :=
    (derivedTensorWithAlgebraCompIso
      (algebraMap A κA)
      (algebraMap κA C)
      (algebraMap A C)
      hcomp).app KA
  -- Proof comment: after normalizing the two `C`-objects, the closed-point homology comparison
  -- is just functoriality of the final tensor with `κ(closedPoint C)` and then of homology.
  exact
    (DerivedCategory.homologyFunctor (ModuleCat (closedPoint C).asIdeal.ResidueField) j).mapIso
      ((derivedTensorWithAlgebra
          (algebraMap C (closedPoint C).asIdeal.ResidueField)).mapIso eBase)

/-- Helper for Lemma 15.78.6: the closed-point residue-field homology of `K` over `B` should agree
with the closed-point residue-field homology of the closed-fiber base change over
`((maximalIdeal A).Fiber B)`. -/
lemma closed_point_residueFieldDerivedHomology_isZero_iff_closed_fiber_baseChange
    (K : DModB) (j : ℤ) :
    let κA := (closedPoint A).asIdeal.ResidueField
    let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
    let C := ((maximalIdeal A).Fiber B)
    let L : DerivedCategory (ModuleCat C) :=
      (derivedTensorWithAlgebra (algebraMap κA C)).obj
        ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
    IsZero (primeResidueFieldDerivedHomology (closedPoint B) K j) ↔
      IsZero (primeResidueFieldDerivedHomology (closedPoint C) L j) := by
  let κA := (closedPoint A).asIdeal.ResidueField
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
  let C := ((maximalIdeal A).Fiber B)
  let κB := (closedPoint B).asIdeal.ResidueField
  let κC := (closedPoint C).asIdeal.ResidueField
  let L : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap κA C)).obj
      ((derivedTensorWithAlgebra (algebraMap A κA)).obj KA)
  let Kbase : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap A C)).obj KA
  let KκB : DerivedCategory (ModuleCat κB) :=
    (derivedTensorWithAlgebra (algebraMap A κB)).obj KA
  let KκC : DerivedCategory (ModuleCat κC) :=
    (derivedTensorWithAlgebra (algebraMap A κC)).obj KA
  let p : PrimeSpectrum A := closedPoint A
  let q : PrimeSpectrum B := closedPoint B
  let qOver : p.asIdeal.primesOver B := Ideal.primesOver.mk p.asIdeal q.asIdeal
  have hq :
      PrimeSpectrum.comap (algebraMap A B) q = p :=
    comap_closedPoint_eq_closedPoint (A := A) (B := B)
  have hqbar :
      Ideal.comap Algebra.TensorProduct.includeRight.toRingHom (closedPoint C).asIdeal =
        q.asIdeal := by
    -- Proof comment: the closed point of the local closed fiber is the canonical fiber prime over
    -- the closed point of `B`, so its contraction along the right tensor factor is exactly
    -- `closedPoint B`.
    let qSpec :
        PrimeSpectrum.comap (algebraMap A B) ⁻¹' ({p} : Set (PrimeSpectrum A)) :=
      ⟨q, hq⟩
    let e := PrimeSpectrum.preimageEquivFiber A B p
    have hpreimage :
        Ideal.comap Algebra.TensorProduct.includeRight.toRingHom ((e qSpec).asIdeal) =
          q.asIdeal := by
      change ((e.symm (e qSpec)).1).asIdeal = q.asIdeal
      exact congrArg
        (fun x : PrimeSpectrum.comap (algebraMap A B) ⁻¹' ({p} : Set (PrimeSpectrum A)) ↦ x.1.asIdeal)
        (e.symm_apply_apply qSpec)
    simpa [p, q, C, closed_fiber_equiv_prime_over_closed_point_eq_closedPoint (A := A) (B := B)] using
      hpreimage
  let eκ : κB ≃ₐ[κA] κC := by
    let e : κB ≃+* κC :=
      RingEquiv.ofBijective
        (Ideal.ResidueField.map q.asIdeal (closedPoint C).asIdeal
          Algebra.TensorProduct.includeRight.toRingHom hqbar.symm)
        ((p.asIdeal.surjectiveOnStalks_residueField.baseChange').residueFieldMap_bijective
          q.asIdeal (closedPoint C).asIdeal hqbar.symm)
    refine AlgEquiv.ofRingEquiv (f := e) ?_
    intro x
    obtain ⟨a, rfl⟩ := p.asIdeal.algebraMap_residueField_surjective x
    change
      e (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) (qOver.1.over_def p.asIdeal)
        (algebraMap A p.asIdeal.ResidueField a)) =
        algebraMap p.asIdeal.ResidueField (closedPoint C).asIdeal.ResidueField
          (algebraMap A p.asIdeal.ResidueField a)
    rw [show e =
      Ideal.ResidueField.map q.asIdeal (closedPoint C).asIdeal
        Algebra.TensorProduct.includeRight.toRingHom hqbar.symm from rfl]
    rw [Ideal.ResidueField.map_algebraMap q.asIdeal (closedPoint C).asIdeal
      Algebra.TensorProduct.includeRight.toRingHom hqbar.symm ((algebraMap A B) a)]
    have hbase :
        (Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B) ((algebraMap A B) a) =
          (Algebra.TensorProduct.includeLeft : p.asIdeal.ResidueField →ₐ[A] p.asIdeal.Fiber B)
            ((algebraMap A p.asIdeal.ResidueField) a) := by
      simpa using congrArg (fun f : A →+* p.asIdeal.Fiber B => f a)
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
          ((Algebra.TensorProduct.includeLeft :
              p.asIdeal.ResidueField →ₐ[A] p.asIdeal.Fiber B).toRingHom.comp
              (algebraMap A p.asIdeal.ResidueField)) =
            ((Algebra.TensorProduct.includeRight :
                B →ₐ[A] p.asIdeal.Fiber B).toRingHom.comp
              (algebraMap A B))).symm
    calc
      algebraMap (p.asIdeal.Fiber B) (closedPoint C).asIdeal.ResidueField
          ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B) ((algebraMap A B) a)) =
        algebraMap (p.asIdeal.Fiber B) (closedPoint C).asIdeal.ResidueField
          ((Algebra.TensorProduct.includeLeft :
              p.asIdeal.ResidueField →ₐ[A] p.asIdeal.Fiber B)
            ((algebraMap A p.asIdeal.ResidueField) a)) := by
          exact congrArg
            (algebraMap (p.asIdeal.Fiber B) (closedPoint C).asIdeal.ResidueField)
            hbase
      _ =
        algebraMap p.asIdeal.ResidueField (closedPoint C).asIdeal.ResidueField
          (algebraMap A p.asIdeal.ResidueField a) := by
          rfl
  let E : ModuleCat κC ≌ ModuleCat κB :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv eκ.toRingEquiv
  letI : Algebra κB κC := eκ.toAlgHom.toAlgebra
  have hcompB :
      (algebraMap B κB).comp (algebraMap A B) = algebraMap A κB := by
    ext x
    rfl
  have hcompC :
      (algebraMap C κC).comp (algebraMap A C) = algebraMap A κC := by
    ext x
    rfl
  have hcompκ :
      eκ.toRingHom.comp (algebraMap A κB) = algebraMap A κC := by
    ext x
    simpa [RingHom.comp_apply] using eκ.commutes (algebraMap A κA x)
  have eCounit :
      ((derivedTensorWithAlgebra (algebraMap A B)).obj KA) ≅ K := by
    let F : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
    let G : ModuleCat B ⥤ ModuleCat A := ModuleCat.restrictScalars (algebraMap A B)
    let ε : G ⋙ F ≅ 𝟭 (ModuleCat B) :=
      NatIso.ofComponents
        (fun M ↦ asIso ((ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.app M))
        (fun M N f ↦ by
          simpa [F, G] using
            (ModuleCat.extendRestrictScalarsAdj (algebraMap A B)).counit.naturality f)
    -- Proof comment: exact flat extension back from `A` to `B` collapses the restricted object
    -- to the original `B`-linear derived object.
    simpa [KA, F, G] using
      (((extendScalars_mapDerivedCategory_iso_of_flat (R := A) (R' := B)).app KA).symm ≪≫
        (mapDerivedCategory_comp_obj_iso G F K).symm ≪≫
        mapDerivedCategory_obj_iso_of_natIso ε K)
  have eBfiberObj :
      KκB ≅ (derivedTensorWithAlgebra (algebraMap B κB)).obj K := by
    -- Proof comment: tensoring the restricted `A`-object with `κ(B)` agrees with taking the
    -- honest `B`-residue-field fiber of `K`.
    simpa [KA, KκB] using
      (((derivedTensorWithAlgebraCompIso
          (algebraMap A B)
          (algebraMap B κB)
          (algebraMap A κB)
          hcompB).app KA).symm ≪≫
        ((derivedTensorWithAlgebra (algebraMap B κB)).mapIso eCounit))
  have eBfiberH :
      primeResidueFieldDerivedHomology (closedPoint B) K j ≅
        (DerivedCategory.homologyFunctor (ModuleCat κB) j).obj KκB := by
    simpa [primeResidueFieldDerivedHomology, KκB] using
      ((DerivedCategory.homologyFunctor (ModuleCat κB) j).mapIso eBfiberObj).symm
  have eκTensor :
      (derivedTensorWithAlgebra eκ.toRingHom).obj KκB ≅ KκC := by
    -- Proof comment: after identifying the scalar map `A → κ(C)` as the composite
    -- `A → κ(B) → κ(C)`, iterated and direct base change coincide.
    simpa [KκB, KκC] using
      (derivedTensorWithAlgebraCompIso
        (algebraMap A κB)
        eκ.toRingHom
        (algebraMap A κC)
        hcompκ).app KA
  have eExtendInverse :
      ModuleCat.extendScalars eκ.toRingHom ≅ E.inverse := by
    simpa [E] using extendScalars_iso_restrictScalars_inverse eκ.toRingEquiv
  have eTensorInverse :
      (derivedTensorWithAlgebra eκ.toRingHom).obj KκB ≅ E.inverse.mapDerivedCategory.obj KκB := by
    -- Proof comment: scalar extension along the field equivalence `κ(B) ≃ κ(C)` is exactly the
    -- inverse equivalence on module categories, hence also on derived categories.
    simpa [E] using
      (((extendScalars_mapDerivedCategory_iso_of_flat (R := κB) (R' := κC)).app KκB).symm ≪≫
        mapDerivedCategory_obj_iso_of_natIso eExtendInverse KκB)
  have eToInverse :
      KκC ≅ E.inverse.mapDerivedCategory.obj KκB :=
    eκTensor.symm ≪≫ eTensorInverse
  have eTransport :
      E.functor.mapDerivedCategory.obj KκC ≅ KκB := by
    -- Proof comment: applying the forward equivalence to the transported `κ(C)`-object recovers
    -- the original `κ(B)`-fiber.
    exact
      (E.functor.mapDerivedCategory).mapIso eToInverse ≪≫
        (mapDerivedCategory_comp_obj_iso E.inverse E.functor KκB).symm ≪≫
        mapDerivedCategory_obj_iso_of_natIso E.counitIso KκB
  have eFieldH :
      (DerivedCategory.homologyFunctor (ModuleCat κB) j).obj KκB ≅
        E.functor.obj ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC) := by
    -- Proof comment: combine the derived transport across the residue-field equivalence with the
    -- exact commutation of restriction of scalars and homology.
    exact
      ((DerivedCategory.homologyFunctor (ModuleCat κB) j).mapIso eTransport).symm ≪≫
        restrictScalars_homology_iso (A := κB) (B := κC) KκC j
  have eCbaseObj :
      (derivedTensorWithAlgebra (algebraMap C κC)).obj Kbase ≅ KκC := by
    -- Proof comment: the closed-point fiber of the direct closed-fiber base change is the same as
    -- the direct `A`-to-`κ(C)` base change.
    simpa [Kbase, KκC] using
      (derivedTensorWithAlgebraCompIso
        (algebraMap A C)
        (algebraMap C κC)
        (algebraMap A κC)
        hcompC).app KA
  have eCbaseH :
      primeResidueFieldDerivedHomology (closedPoint C) Kbase j ≅
        (DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC := by
    simpa [primeResidueFieldDerivedHomology, Kbase, KκC] using
      (DerivedCategory.homologyFunctor (ModuleCat κC) j).mapIso eCbaseObj
  let eBase := closed_fiber_iterated_baseChange_homology_iso (A := A) (B := B) K j
  let eLκC :
      primeResidueFieldDerivedHomology (closedPoint C) L j ≅
        (DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC :=
    eBase ≪≫ eCbaseH
  let eBH :
      primeResidueFieldDerivedHomology (closedPoint B) K j ≅
        E.functor.obj ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC) :=
    eBfiberH ≪≫ eFieldH
  constructor
  · intro hB
    have hEFiber :
        IsZero (E.functor.obj ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC)) :=
      eBH.isZero_iff.1 hB
    have hFiber :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC) := by
      have hInverse :
          IsZero
            (E.inverse.obj
              (E.functor.obj ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC))) :=
        E.inverse.map_isZero hEFiber
      exact (E.unitIso.app ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC)).isZero_iff.2
        hInverse
    exact eLκC.isZero_iff.2 hFiber
  · intro hL
    have hFiber :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC) :=
      eLκC.isZero_iff.1 hL
    have hEFiber :
        IsZero (E.functor.obj ((DerivedCategory.homologyFunctor (ModuleCat κC) j).obj KκC)) :=
      E.functor.map_isZero hFiber
    exact eBH.isZero_iff.2 hEFiber

/-- A weaker sufficient hypothesis for Lemma `15.78.6`: it is enough to assume that the derived
special fiber `K^• \otimes_A^{\mathbf L} κ(\mathfrak m_A)` has vanishing homology outside
`[a, b]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKκ :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint A)
            ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
            i)) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := by
  let κA := (closedPoint A).asIdeal.ResidueField
  let KA : DModA := ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
  let C := ((maximalIdeal A).Fiber B)
  let Kκ : DerivedCategory (ModuleCat κA) :=
    (derivedTensorWithAlgebra (algebraMap A κA)).obj KA
  let L : DerivedCategory (ModuleCat C) :=
    (derivedTensorWithAlgebra (algebraMap κA C)).obj Kκ
  have hKκAmp : HasTorAmplitudeIn Kκ a b := by
    -- Proof comment: the source hypothesis on the `κ(A)`-fiber packages into tor-amplitude over
    -- the field `κ(A)`.
    simpa [κA, KA, Kκ] using
      residue_field_torAmplitude_of_homology_vanishing (A := A) (B := B) (K := K) hKκ
  have hLAmp_ab : HasTorAmplitudeIn L a b := by
    -- Proof comment: scalar extension from the field `κ(A)` to the closed fiber preserves the
    -- original tor-amplitude interval.
    simpa [κA, Kκ, L] using
      hasTorAmplitudeIn_derivedTensorWithAlgebra
        (A := κA) (B := C) Kκ a b hKκAmp
  have hLGE : L.IsGE a := by
    -- Proof comment: tor-amplitude over the closed fiber gives the lower cohomological bound.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact
      isZero_homology_of_hasTorAmplitudeIn_outside (R := C) hLAmp_ab <| by
        intro hmem
        exact (not_lt_of_ge hmem.1 hi).elim
  have hLLE : L.IsLE b := by
    -- Proof comment: the same tor-amplitude bound gives the upper cohomological bound.
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact
      isZero_homology_of_hasTorAmplitudeIn_outside (R := C) hLAmp_ab <| by
        intro hmem
        exact (not_lt_of_ge hmem.2 hi).elim
  letI : HasGlobalDimensionLE C d :=
    hasGlobalDimensionLE_of_isRegularLocalRing (R := C) hdim
  have hLShifted : HasTorAmplitudeIn L (a - (d : ℤ)) b := by
    -- Proof comment: the regular-local closed fiber has weak dimension at most `d`, so
    -- Lemma `15.67.19` shifts the lower tor-amplitude bound by `d`.
    simpa [L] using
      hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
        (R := C) d L a b hLGE hLLE
  have hclosedFiberClosedPoint :
      ∀ i : ℤ, i ∉ Set.Icc (a - (d : ℤ)) b →
        IsZero (primeResidueFieldDerivedHomology (closedPoint C) L i) := by
    intro i hi
    have hResidueAmp :
        HasTorAmplitudeIn
          ((derivedTensorWithAlgebra
              (algebraMap C ((closedPoint C).asIdeal.ResidueField))).obj L)
          (a - (d : ℤ)) b := by
      -- Proof comment: one more derived scalar extension moves the closed-fiber complex to its
      -- closed-point residue field without changing the interval.
      simpa using
        hasTorAmplitudeIn_derivedTensorWithAlgebra
          (A := C) (B := (closedPoint C).asIdeal.ResidueField)
          L (a - (d : ℤ)) b hLShifted
    -- Proof comment: over the residue field of the closed fiber, the tor-amplitude interval is
    -- equivalent to vanishing of ordinary homology outside that interval.
    simpa [primeResidueFieldDerivedHomology, L] using
      isZero_homology_of_hasTorAmplitudeIn_outside
        (R := (closedPoint C).asIdeal.ResidueField) hResidueAmp hi
  have hclosedPointB :
      ∀ i : ℤ, i ∉ Set.Icc (a - (d : ℤ)) b →
        IsZero (primeResidueFieldDerivedHomology (closedPoint B) K i) := by
    intro i hi
    -- Proof comment: the remaining interface step compares the closed-point fiber of `K` over
    -- `B` with the closed-point fiber of the closed-fiber base change `L`.
    exact
      (closed_point_residueFieldDerivedHomology_isZero_iff_closed_fiber_baseChange
        (A := A) (B := B) K i).2 (hclosedFiberClosedPoint i hi)
  -- Proof comment: once the unique closed-point test on `B` is established, the local form of
  -- Lemma `15.78.2` gives the desired perfectness and shifted tor-amplitude.
  exact
    local_perfect_torAmplitude_of_closedPoint_residueField_vanishing
      (A := A) (B := B) K (a - (d : ℤ)) b hKpc hclosedPointB

-- Proof sketch: tor-amplitude over `A` implies the required vanishing of the derived special
-- fiber over `κ(maximalIdeal A)`. Apply the residue-field criterion above to obtain perfection of
-- `K` over `B` and tor-amplitude in `[(a - d), b]`.
/-- Lemma 15.78.6: let `A → B` be a flat local ring homomorphism, let `d ≥ 0`, and let `K^•` be a
pseudo-coherent object of `D(B)`. If the closed fiber `(maximalIdeal A).Fiber B`, equivalently
`B ⧸ (Ideal.map (algebraMap A B) (maximalIdeal A))`, is a regular local ring of dimension `d`,
and `K^•`, viewed over `A`, has tor-amplitude in `[a, b]`, then `K^•` is perfect over `B` with
tor-amplitude in `[(a - d), b]`. -/
@[stacks 09PC]
theorem isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_restrictScalars_of_closedFiber_isRegularLocalRing
    (K : DModB) (a b : ℤ) (d : ℕ)
    [IsRegularLocalRing ((maximalIdeal A).Fiber B)]
    (hdim : ringKrullDim ((maximalIdeal A).Fiber B) = d)
    (hKpc : K.IsPseudoCoherent)
    (hKamp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
        a b) :
    K.IsPerfect ∧ HasTorAmplitudeIn K (a - (d : ℤ)) b := by
  have hKκ :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint A)
            ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
            i) := by
    intro i hi
    -- Proof comment: this is the tor-amplitude-to-fiber-vanishing bridge isolated in the local
    -- helper above.
    exact
      base_residueFieldDerivedHomology_isZero_of_hasTorAmplitudeIn_outside
        (A := A) (B := B) K hKamp hi
  -- Proof comment: the residue-field vanishing criterion is the source-facing reduction proved
  -- just above.
  exact
    isPerfect_and_hasTorAmplitudeIn_of_isPseudoCoherent_of_baseResidueFieldDerivedHomology_vanishing_of_closedFiber_isRegularLocalRing
      (K := K) (a := a) (b := b) (d := d) hdim hKpc hKκ

end

end CategoryTheory

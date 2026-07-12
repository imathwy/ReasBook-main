import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_74_4
import StacksProject_2024.Chap15.Definition_15_92_4
import StacksProject_2024.Chap15.Lemma_15_92_1
import StacksProject_2024.Chap15.Lemma_15_92_2
import StacksProject_2024.Chap15.Lemma_15_29_5.UniverseBridges
import StacksProject_2024.Chap15.Lemma_15_29_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open Opposite
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The extended alternating Čech complex on a finite generating family `f`, viewed as an object
of `D(A)` by extending the natural `ℕ`-indexed cochain complex to a `ℤ`-indexed one and passing to
the derived category. -/
abbrev extendedAlternatingCechDerivedObject {r : ℕ} (f : Fin r → A) : DMod :=
  Q.obj ((extendedAlternatingCechComplex f A).extend embeddingUpNat)

/-- Helper for Lemma 15.92.10: right derived tensoring with `A[0]` is naturally the identity on
`D(A)`. -/
noncomputable theorem ringSingle_rightDerivedTensor_natIso_for_completion :
    CategoryTheory.derivedTensorProduct ((single₀).obj (ModuleCat.of A A)) ≅ 𝟭 DMod := by
  refine NatIso.ofComponents
    (fun K ↦
      (derivedTensorProduct_comm K ((single₀).obj (ModuleCat.of A A))) ≪≫
        singleZeroDerivedTensorIso K)
    ?_
  intro K L g
  -- Proof comment: both components are built from the standard symmetry and tensor-unit
  -- comparisons, so naturality is the same monoidal naturality calculation as in Lemma `15.92.1`.
  simp only [singleZeroDerivedTensorIso, derivedTensorProduct_comm,
    derivedCategory_tensorObj_iso_derivedTensorProduct,
    tensoringRightIsoDerivedTensorProduct_hom_app,
    tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit, Category.assoc]

/-- Helper for Lemma 15.92.10: the derived internal Hom out of `A[0]` is naturally the identity
functor on `D(A)`. -/
noncomputable theorem ringSingle_internalHom_natIso_for_completion
    (H : RHomPkg) :
    letI := H
    ihom ((single₀).obj (ModuleCat.of A A)) ≅ 𝟭 DMod := by
  letI := H
  let adjRing :
      CategoryTheory.derivedTensorProduct ((single₀).obj (ModuleCat.of A A)) ⊣
        ihom ((single₀).obj (ModuleCat.of A A)) :=
    H.derivedTensorAdj ((single₀).obj (ModuleCat.of A A))
  let adjId : 𝟭 DMod ⊣ 𝟭 DMod := Adjunction.id
  -- Proof comment: identify the left adjoint `A[0] ⊗^L -` with the identity and transport the
  -- right adjoint by uniqueness.
  exact
    Adjunction.rightAdjointUniq
      (adjRing.ofNatIsoLeft (ringSingle_rightDerivedTensor_natIso_for_completion (A := A)))
      adjId

/-- Helper for Lemma 15.92.10: the extended alternating Čech complex has the canonical projection
to the degree-zero complex `A[0]`. -/
noncomputable def extendedAlternatingCechComplex_projection {r : ℕ} (f : Fin r → A) :
    extendedAlternatingCechComplex f A ⟶
      (CochainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A A) :=
  (CochainComplex.toSingle₀Equiv
      (extendedAlternatingCechComplex f A)
      (ModuleCat.of A A)).symm
    (𝟙 (ModuleCat.of A A))

/-- Helper for Lemma 15.92.10: after extending to `ℤ`-indexed complexes and passing to `D(A)`,
the Čech projection becomes a morphism `\check C(f) ⟶ A[0]`. -/
noncomputable def extendedAlternatingCechDerivedProjection {r : ℕ} (f : Fin r → A) :
    extendedAlternatingCechDerivedObject f ⟶
      (single₀).obj (ModuleCat.of A A) :=
  Q.map
      ((embeddingUpNat.extendFunctor (CochainComplex (ModuleCat A) ℤ)).map
        (extendedAlternatingCechComplex_projection (A := A) f)) ≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A A)).symm.hom

/-- Helper for Lemma 15.92.10: the universal map `K ⟶ RHom_A(\check C(f), K)` induced by the
Čech projection `\check C(f) ⟶ A[0]`. -/
noncomputable def cech_completion_unit
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K : DMod) :
    K ⟶ RHom[H](extendedAlternatingCechDerivedObject f, K) :=
  ((ringSingle_internalHom_natIso_for_completion (A := A) H).inv.app K) ≫
    (MonoidalClosed.pre (extendedAlternatingCechDerivedProjection (A := A) f)).app K

/-- Helper for Lemma 15.92.10: the Čech completion unit is natural in the source object. -/
theorem cech_completion_unit_natural
    (H : RHomPkg) {r : ℕ} (f : Fin r → A)
    {K L : DMod} (a : K ⟶ L) :
    a ≫ cech_completion_unit H f L =
      cech_completion_unit H f K ≫
        (ihom (extendedAlternatingCechDerivedObject f)).map a := by
  let e := ringSingle_internalHom_natIso_for_completion (A := A) H
  -- Proof comment: combine the naturality of the inverse comparison
  -- `𝟭 ⟶ RHom_A(A[0], -)` with the naturality of `MonoidalClosed.pre`.
  calc
    a ≫ cech_completion_unit H f L
        = ((e.inv.app K ≫
              (ihom ((single₀).obj (ModuleCat.of A A))).map a) ≫
            (MonoidalClosed.pre
              (extendedAlternatingCechDerivedProjection (A := A) f)).app L) := by
            simp [cech_completion_unit, Category.assoc, e.inv.naturality a]
    _ = e.inv.app K ≫
          ((ihom ((single₀).obj (ModuleCat.of A A))).map a ≫
            (MonoidalClosed.pre
              (extendedAlternatingCechDerivedProjection (A := A) f)).app L) := by
          simp [Category.assoc]
    _ = e.inv.app K ≫
          ((MonoidalClosed.pre
              (extendedAlternatingCechDerivedProjection (A := A) f)).app K ≫
            (ihom (extendedAlternatingCechDerivedObject f)).map a) := by
          rw [(MonoidalClosed.pre
            (extendedAlternatingCechDerivedProjection (A := A) f)).naturality a]
    _ = cech_completion_unit H f K ≫
          (ihom (extendedAlternatingCechDerivedObject f)).map a := by
          simp [cech_completion_unit, Category.assoc]

-- TODO(Lemma 15.92.10): after rewriting
-- `T(RHom_A(\check C(f), K), f_i)` via `derivedInternalHomTensorIso`, transport the tensor source
-- to the localized-coefficient extended Čech object and contract it over `A_{f_i}` using
-- `extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at`.
/-- Helper for Lemma 15.92.10: the localized-coefficient extended Čech source over `A_(f_i)`,
viewed as an object of `D(A_(f_i))`. -/
abbrev generator_localizedExtendedAlternatingCechDerivedObject
    {r : ℕ} (f : Fin r → A) (i : Fin r) :
    DerivedCategory (ModuleCat (Localization.Away (f i))) :=
  (DerivedCategory.Q :
      CochainComplex (ModuleCat (Localization.Away (f i))) ℤ ⥤
        DerivedCategory (ModuleCat (Localization.Away (f i)))).obj
    (((extendedAlternatingCechComplex
        (fun j ↦ algebraMap A (Localization.Away (f i)) (f j))
        ((Localization.Away (f i)) ⊗[A] A)).extend embeddingUpNat))

/-- Helper for Lemma 15.92.10: tensoring the extended Čech object with the degree-zero
localization object `A_(f_i)[0]` identifies with the restricted localized Čech complex obtained by
extending scalars to `A_(f_i)` on coefficients. -/
noncomputable def generator_localization_tensor_extendedAlternatingCechDerivedObject_iso
    {r : ℕ} (f : Fin r → A) (i : Fin r) :
    ((((single₀).obj (ModuleCat.of A (Localization.Away (f i)))) ⊗[A]^L
        extendedAlternatingCechDerivedObject f)) ≅
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away (f i)))).mapDerivedCategory.obj
        (generator_localizedExtendedAlternatingCechDerivedObject f i)) := by
  let S := Localization.Away (f i)
  let σ : A →+* S := algebraMap A S
  let C : CochainComplex (ModuleCat A) ℤ :=
    ((extendedAlternatingCechComplex f A).extend embeddingUpNat)
  let C' : CochainComplex (ModuleCat S) ℤ :=
    ((extendedAlternatingCechComplex
        (fun j ↦ σ (f j))
        (S ⊗[A] A)).extend embeddingUpNat)
  let res := (ModuleCat.restrictScalars σ).mapDerivedCategory
  -- Proof comment: first rewrite tensoring by `A_(f_i)[0]` as restricted derived scalar extension,
  -- then push exact scalar extension through `Q`, and finally use the Čech base-change bridge on
  -- the underlying cochain complexes.
  have hC :
      (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj C) ≅ C' := by
    simpa [C, C'] using
      ((embeddingUpNat.extendFunctor (CochainComplex (ModuleCat S) ℤ)).map
        (extendedAlternatingCechComplex_iso_extendScalars_universe
          (R := A) (S := S) (M := A) (r := r) f)).symm
  calc
    ((((single₀).obj (ModuleCat.of A S)) ⊗[A]^L
        extendedAlternatingCechDerivedObject f)) ≅
        res.obj ((CategoryTheory.derivedTensorWithAlgebra σ).obj
          (extendedAlternatingCechDerivedObject f)) :=
      (CategoryTheory.DerivedCategory.localizationAway_restrict_derivedTensorWithAlgebra_iso
        (A := A) (f := f i) (X := extendedAlternatingCechDerivedObject f)).symm
    _ ≅ res.obj
        (((ModuleCat.extendScalars σ).mapDerivedCategory).obj
          (extendedAlternatingCechDerivedObject f)) :=
      res.mapIso
        ((CategoryTheory.extendScalars_mapDerivedCategory_iso
          (R := A) (R' := S)).symm.app (extendedAlternatingCechDerivedObject f))
    _ ≅ res.obj (Q.obj (((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj C)) :=
      res.mapIso ((ModuleCat.extendScalars σ).mapDerivedCategoryFactors.app C)
    _ ≅ res.obj
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat S) ℤ ⥤ DerivedCategory (ModuleCat S)).obj C') :=
      res.mapIso
        ((DerivedCategory.Q :
            CochainComplex (ModuleCat S) ℤ ⥤ DerivedCategory (ModuleCat S)).mapIso hC)

/-- Helper for Lemma 15.92.10: after localizing at a chosen generator, the localized Čech source
is contractible, so the tensor source used in the generator vanishing step is zero in `D(A)`. -/
theorem localized_extendedAlternatingCechDerivedObject_isZero_at_generator
    {r : ℕ} (f : Fin r → A) (i : Fin r) :
    IsZero ((((single₀).obj (ModuleCat.of A (Localization.Away (f i)))) ⊗[A]^L
      extendedAlternatingCechDerivedObject f)) := by
  let S := Localization.Away (f i)
  let σ : A →+* S := algebraMap A S
  let QS :
      CochainComplex (ModuleCat S) ℤ ⥤ DerivedCategory (ModuleCat S) :=
    DerivedCategory.Q
  let C' : CochainComplex (ModuleCat S) ℤ :=
    ((extendedAlternatingCechComplex
        (fun j ↦ σ (f j))
        (S ⊗[A] A)).extend embeddingUpNat)
  let res := (ModuleCat.restrictScalars σ).mapDerivedCategory
  have hunit : IsUnit (σ (f i)) := by
    simpa using (IsLocalization.Away.algebraMap_isUnit (f i))
  obtain ⟨eNat⟩ :=
    extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at
      (R := S) (M := S ⊗[A] A) (f := fun j ↦ σ (f j)) i hunit
  have e :
      HomotopyEquiv C' 0 := by
    -- Proof comment: extend the source-side contracting homotopy from the `ℕ`-indexed Čech
    -- complex to the `ℤ`-indexed complex used by the derived category.
    simpa [C'] using
      ((embeddingUpNat.extendFunctor (CochainComplex (ModuleCat S) ℤ)).mapHomotopyEquiv eNat)
  have hq : QuasiIso e.hom := by
    rw [← HomologicalComplex.mem_quasiIso_iff]
    exact
      (homotopyEquivalences_le_quasiIso (ModuleCat S) (up ℤ))
        e.isHomotopyEquivalence
  let _ : QuasiIso e.hom := hq
  have hQ0 :
      IsZero (QS.obj (0 : CochainComplex (ModuleCat S) ℤ)) :=
    QS.map_isZero (Limits.isZero_zero (CochainComplex (ModuleCat S) ℤ))
  let eQ0 :
      QS.obj (0 : CochainComplex (ModuleCat S) ℤ) ≅ (0 : DerivedCategory (ModuleCat S)) :=
    hQ0.iso (Limits.isZero_zero (DerivedCategory (ModuleCat S)))
  have hzeroLocalized :
      IsZero (QS.obj C') := by
    -- Proof comment: the contracting homotopy makes `e.hom` a quasi-isomorphism to zero, so `Q`
    -- turns it into an isomorphism onto the zero object.
    let _ : IsIso (QS.map e.hom) := by
      exact DerivedCategory.Q_isInverted _ e.hom
    exact (((asIso (QS.map e.hom)) ≪≫ eQ0).isZero_iff).2
      (Limits.isZero_zero (DerivedCategory (ModuleCat S)))
  have hzeroRestricted :
      IsZero (res.obj (QS.obj C')) := by
    -- Proof comment: exact restriction of scalars preserves zero objects.
    exact res.map_isZero hzeroLocalized
  exact hzeroRestricted.of_iso
    (generator_localization_tensor_extendedAlternatingCechDerivedObject_iso
      (A := A) f i).symm

/-- Helper for Lemma 15.92.10: if the left source of the derived internal Hom is zero, then the
derived internal Hom object is also zero. -/
theorem derivedInternalHom_isZero_of_isZero_left
    (H : RHomPkg) {X K : DMod} (hX : IsZero X) :
    IsZero (RHom[H](X, K)) := by
  letI := H
  let eZero :
      RHom[H]((0 : DMod), K) ≅ RHom[H](X, K) := by
    refine
      { hom := (MonoidalClosed.pre hX.isoZero.hom).app K
        inv := (MonoidalClosed.pre hX.isoZero.inv).app K
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · simpa using
        (congrArg (fun α ↦ α.app K)
          (MonoidalClosed.pre_map hX.isoZero.inv hX.isoZero.hom)).symm
    · simpa using
        (congrArg (fun α ↦ α.app K)
          (MonoidalClosed.pre_map hX.isoZero.hom hX.isoZero.inv)).symm
  have hzeroZeroSource :
      IsZero (RHom[H]((0 : DMod), K)) := by
    -- Proof comment: endomorphisms of `RHom_A(0, K)` are adjoint to morphisms out of
    -- `RHom_A(0, K) ⊗^L 0`, and that tensor source is zero by commuting the `0` factor to the
    -- left and applying `Functor.map_isZero`.
    rw [IsZero.iff_id_eq_zero]
    have htensorZero :
        IsZero (RHom[H]((0 : DMod), K) ⊗[A]^L (0 : DMod)) := by
      have hzeroLeftTensor :
          IsZero ((0 : DMod) ⊗[A]^L RHom[H]((0 : DMod), K)) := by
        simpa using
          (CategoryTheory.derivedTensorProduct (RHom[H]((0 : DMod), K))).map_isZero
            (Limits.isZero_zero DMod)
      exact hzeroLeftTensor.of_iso
        (CategoryTheory.derivedTensorProduct_comm
          (RHom[H]((0 : DMod), K)) (0 : DMod))
    have hsubTensor :
        Subsingleton ((RHom[H]((0 : DMod), K) ⊗[A]^L (0 : DMod)) ⟶ K) := by
      exact ⟨fun a b ↦ htensorZero.eq_of_src a b⟩
    let adjZero :
        CategoryTheory.derivedTensorProduct (0 : DMod) ⊣ ihom (0 : DMod) :=
      H.derivedTensorAdj (0 : DMod)
    have hsubEnd :
        Subsingleton ((RHom[H]((0 : DMod), K)) ⟶ RHom[H]((0 : DMod), K)) := by
      let eAdj := adjZero.homEquiv (RHom[H]((0 : DMod), K)) K
      letI :
          Subsingleton ((RHom[H]((0 : DMod), K) ⊗[A]^L (0 : DMod)) ⟶ K) := hsubTensor
      exact eAdj.symm.injective.subsingleton
    letI :
        Subsingleton ((RHom[H]((0 : DMod), K)) ⟶ RHom[H]((0 : DMod), K)) := hsubEnd
    exact Subsingleton.elim _ _
  exact hzeroZeroSource.of_iso eZero

/-- Helper for Lemma 15.92.10: every chosen generator `f i` satisfies the localization-away
vanishing condition for the explicit Čech completion object. -/
theorem generator_localizationAway_vanishing_of_cech_completion
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K : DMod) (i : Fin r) :
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition
      (f i) (RHom[H](extendedAlternatingCechDerivedObject f, K)) := by
  -- Route correction: after the generator-localized Čech source is known to be zero, the only
  -- remaining step is to transport that zero object across the tensor-Hom comparison.
  rw [CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff (H := H)]
  let eTensor :
      CategoryTheory.DerivedCategory.localizationAwayT H (f i)
        (RHom[H](extendedAlternatingCechDerivedObject f, K)) ≅
      RHom[H]
        ((((single₀).obj (ModuleCat.of A (Localization.Away (f i)))) ⊗[A]^L
          extendedAlternatingCechDerivedObject f), K) :=
    CategoryTheory.derivedInternalHomTensorIso H
      ((single₀).obj (ModuleCat.of A (Localization.Away (f i))))
      (extendedAlternatingCechDerivedObject f)
      K
  have hzeroTensor :
      IsZero
        (RHom[H]
          ((((single₀).obj (ModuleCat.of A (Localization.Away (f i)))) ⊗[A]^L
            extendedAlternatingCechDerivedObject f), K)) :=
    derivedInternalHom_isZero_of_isZero_left (A := A) (H := H)
      (K := K)
      (localized_extendedAlternatingCechDerivedObject_isZero_at_generator (A := A) f i)
  exact hzeroTensor.of_iso eTensor.symm

/-- Helper for Lemma 15.92.10: derived completeness is preserved by shifts. -/
theorem isDerivedCompleteWithRespectTo_shift
    {I : Ideal A} {K : DMod} (hK : K.IsDerivedCompleteWithRespectTo I) (n : ℤ) :
    (K⟦n⟧).IsDerivedCompleteWithRespectTo I := by
  intro g hg E
  have hsub :
      Subsingleton
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj
          E) ⟶ K) :=
    hK g hg E
  letI := hsub
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Proof comment: the shift functor is an equivalence, so morphisms into `K⟦n⟧` are the same as
  -- morphisms into `K` after shifting the source by `-n`.
  let eφ :=
    (shiftFunctorCompIsoId DMod n).app
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj
        E))
  have hshift :
      eφ.hom ≫ φ⟦-n⟧' = eφ.hom ≫ ψ⟦-n⟧' := Subsingleton.elim _ _
  exact (cancel_mono eφ.hom).1 hshift

/-- Helper for Lemma 15.92.10: if `g` lies in the defining ideal of a derived-complete target,
then the canonical localized degree-zero object has no nonzero maps into that target. -/
theorem subsingleton_hom_from_localizationAway_single_of_isDerivedComplete
    {I : Ideal A} {E : DMod} (hE : E.IsDerivedCompleteWithRespectTo I)
    {g : A} (hg : g ∈ I) :
    Subsingleton (((single₀).obj (ModuleCat.of A (Localization.Away g))) ⟶ E) := by
  let singleAway :=
    DerivedCategory.singleFunctor (ModuleCat (Localization.Away g)) (0 : ℤ)
  let sourceIso :=
    CategoryTheory.DerivedCategory.localizationAway_restrict_single_iso (A := A) g
  have hDerived :
      Subsingleton
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away g))).mapDerivedCategory.obj
          (singleAway.obj (ModuleCat.of (Localization.Away g) (Localization.Away g)))) ⟶
            E) :=
    hE g hg (singleAway.obj (ModuleCat.of (Localization.Away g) (Localization.Away g)))
  letI := hDerived
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Proof comment: the completeness hypothesis already kills maps from the restricted localized
  -- ring object; the standard restriction/single-object comparison transports that subsingleton to
  -- the canonical source `A_g[0]`.
  have hcomp : sourceIso.hom ≫ φ = sourceIso.hom ≫ ψ := Subsingleton.elim _ _
  exact (cancel_mono sourceIso.hom).1 hcomp

/-- Helper for Lemma 15.92.10: the same localized degree-zero vanishing holds into every shift of
a derived-complete target. -/
theorem subsingleton_hom_from_localizationAway_single_shift_of_isDerivedComplete
    {I : Ideal A} {E : DMod} (hE : E.IsDerivedCompleteWithRespectTo I)
    {g : A} (hg : g ∈ I) (n : ℤ) :
    Subsingleton (((single₀).obj (ModuleCat.of A (Localization.Away g))) ⟶ E⟦n⟧) := by
  -- Proof comment: shifts preserve derived completeness, so the degree-zero localization source is
  -- still left-orthogonal after shifting the target.
  exact
    subsingleton_hom_from_localizationAway_single_of_isDerivedComplete
      (A := A) (I := I)
      (E := E⟦n⟧)
      (isDerivedCompleteWithRespectTo_shift (A := A) (I := I) hE n)
      hg

/-- Helper for Lemma 15.92.10: a nonempty product of the chosen generators lies in the ideal they
generate. -/
theorem finset_prod_mem_span_range_of_nonempty
    {r : ℕ} (f : Fin r → A) :
    ∀ {s : Finset (Fin r)}, s.Nonempty →
      ∏ i in s, f i ∈ Ideal.span (Set.range f) := by
  intro s
  refine Finset.induction_on s ?_ ?_
  · intro hs
    cases hs
  · intro i s hi hs hne
    by_cases hs' : s.Nonempty
    · -- Proof comment: peel off one generator; the tail product stays in the span ideal by
      -- induction, and ideals are stable under left multiplication.
      rw [Finset.prod_insert hi]
      exact (Ideal.span (Set.range f)).mul_mem_left _ (hs hs')
    · -- Proof comment: when the tail is empty, the whole product is just the chosen generator.
      have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      rw [hs0, Finset.prod_empty, mul_one]
      exact Ideal.subset_span ⟨i, rfl⟩

/-- Helper for Lemma 15.92.10: the explicit Čech completion object satisfies the localization-away
vanishing condition after inverting any nonempty product of the chosen generators. -/
theorem nonempty_generator_product_localizationAway_vanishing_of_cech_completion
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K : DMod)
    {s : Finset (Fin r)} (hs : s.Nonempty) :
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition
      (∏ i in s, f i) (RHom[H](extendedAlternatingCechDerivedObject f, K)) := by
  let C : DMod := RHom[H](extendedAlternatingCechDerivedObject f, K)
  have hspan :
      Ideal.span (Set.range f) ≤ C.localizationAwayDerivedHomVanishingIdeal := by
    -- Proof comment: the vanishing ideal already contains each chosen generator by the generator
    -- localization calculation proved above, hence it contains the span of their image.
    refine Ideal.span_le.2 ?_
    intro g hg
    rcases hg with ⟨i, rfl⟩
    exact
      (CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff
        C (f i)).2
        (generator_localizationAway_vanishing_of_cech_completion
          (A := A) (H := H) f K i)
  have hprod :
      ∏ i in s, f i ∈ C.localizationAwayDerivedHomVanishingIdeal :=
    hspan (finset_prod_mem_span_range_of_nonempty (f := f) hs)
  -- Proof comment: transport membership in the vanishing ideal back to the source-facing
  -- localization-away predicate.
  exact
    (CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff
      C (∏ i in s, f i)).1 hprod

/-- Helper for Lemma 15.92.10: every positive Čech branch, indexed by a nonempty finite set of
generators, has subsingleton maps into every shift of a derived-complete target. -/
theorem nonempty_generator_product_subsingleton_hom_shift_of_isDerivedComplete
    {r : ℕ} (f : Fin r → A) {E : DMod}
    (hE : E.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)))
    {s : Finset (Fin r)} (hs : s.Nonempty) (n : ℤ) :
    Subsingleton
      (((single₀).obj
          (ModuleCat.of A (Localization.Away (∏ i in s, f i)))) ⟶ E⟦n⟧) := by
  -- Proof comment: the product element lies in the span ideal, so the previously established
  -- localization-away orthogonality applies directly.
  have hg : ∏ i in s, f i ∈ Ideal.span (Set.range f) :=
    finset_prod_mem_span_range_of_nonempty (f := f) hs
  exact
    subsingleton_hom_from_localizationAway_single_shift_of_isDerivedComplete
      (A := A) (I := Ideal.span (Set.range f)) (E := E) hE hg n

/- Helper for Lemma 15.92.10: once the Čech completion unit on the complete target object is
invertible, the universal map is formally surjective on morphisms into that target. -/
theorem cech_completion_unit_surjective_of_isIso_target
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K E : DMod)
    [IsIso (cech_completion_unit H f E)] :
    Function.Surjective
      (fun φ : RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E ↦
        cech_completion_unit H f K ≫ φ) := by
  intro ψ
  let eE : RHom[H](extendedAlternatingCechDerivedObject f, E) ≅ E :=
    asIso (cech_completion_unit H f E)
  refine ⟨(ihom (extendedAlternatingCechDerivedObject f)).map ψ ≫ eE.inv, ?_⟩
  -- Proof comment: the candidate lift is the formal adjunction-style one, obtained by applying
  -- `RHom_A(\check C(f), -)` to `ψ` and then cancelling the invertible unit on `E`.
  calc
    cech_completion_unit H f K ≫
        ((ihom (extendedAlternatingCechDerivedObject f)).map ψ ≫ eE.inv)
        = (cech_completion_unit H f K ≫
            (ihom (extendedAlternatingCechDerivedObject f)).map ψ) ≫ eE.inv := by
            simp [Category.assoc]
    _ = (ψ ≫ cech_completion_unit H f E) ≫ eE.inv := by
          rw [← cech_completion_unit_natural (A := A) (H := H) (f := f) (a := ψ)]
    _ = ψ := by
          simp [eE, Category.assoc]

/-- Helper for Lemma 15.92.10: on a derived-complete target, the Čech completion unit is an
isomorphism. -/
theorem cech_completion_unit_isIso_of_isDerivedComplete
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) {E : DMod}
    (hE : E.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    IsIso (cech_completion_unit H f E) := by
  -- TODO(Lemma 15.92.10): follow the source-faithful positive-tail route. First compare the cone
  -- of `extendedAlternatingCechDerivedProjection f` with the normalized positive Čech tail, then
  -- use `nonempty_generator_product_subsingleton_hom_shift_of_isDerivedComplete` to kill every
  -- positive branch against `E`, and finally conclude that the unit into `RHom_A(\check C(f), E)`
  -- is invertible.
  sorry

/-- Helper for Lemma 15.92.10: applying the completion functor to the Čech completion unit
recovers the unit of the completed object. -/
theorem cech_completion_unit_map_eq_completion_unit
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K : DMod) :
    (ihom (extendedAlternatingCechDerivedObject f)).map (cech_completion_unit H f K) =
      cech_completion_unit H f (RHom[H](extendedAlternatingCechDerivedObject f, K)) := by
  -- TODO(Lemma 15.92.10): unfold `cech_completion_unit`, rewrite both sides through the natural
  -- isomorphism `RHom_A(A[0], -) ≅ 𝟭`, and identify the two resulting morphisms by naturality of
  -- `MonoidalClosed.pre` for the projection `\check C(f) ⟶ A[0]`.
  sorry

/-- Helper for Lemma 15.92.10: precomposition with the Čech completion unit is bijective whenever
the target object is derived complete with respect to the ideal generated by `f`. -/
theorem cech_completion_unit_bijective_of_isDerivedComplete
    (H : RHomPkg) {r : ℕ} (f : Fin r → A) (K : DMod)
    {E : DMod}
    (hE : E.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))) :
    Function.Bijective
      (fun φ : RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E ↦
        cech_completion_unit H f K ≫ φ) := by
  let eE :
      RHom[H](extendedAlternatingCechDerivedObject f, E) ≅ E :=
    @asIso _ _ _ _ (cech_completion_unit H f E)
      (cech_completion_unit_isIso_of_isDerivedComplete
        (A := A) (H := H) (f := f) hE)
  let invFun :
      (K ⟶ E) → (RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E) :=
    fun ψ ↦ (ihom (extendedAlternatingCechDerivedObject f)).map ψ ≫ eE.inv
  refine ⟨?_, ?_⟩
  · intro φ ψ hφψ
    -- Proof comment: the explicit inverse formula below is a left inverse to precomposition by
    -- the unit, so equality after precomposition already forces `φ = ψ`.
    have hleft :
        Function.LeftInverse
          invFun
          (fun χ : RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E ↦
            cech_completion_unit H f K ≫ χ) := by
      intro χ
      -- Proof comment: rewrite the completion-functor image of the unit as the unit of the
      -- completed object, then use naturality of the unit and cancel the target-side inverse.
      calc
        invFun (cech_completion_unit H f K ≫ χ)
            = (ihom (extendedAlternatingCechDerivedObject f)).map
                (cech_completion_unit H f K ≫ χ) ≫ eE.inv := by
                  rfl
        _ =
            (((ihom (extendedAlternatingCechDerivedObject f)).map
                (cech_completion_unit H f K)) ≫
              (ihom (extendedAlternatingCechDerivedObject f)).map χ) ≫ eE.inv := by
                rw [Functor.map_comp]
        _ =
            (cech_completion_unit H f
                (RHom[H](extendedAlternatingCechDerivedObject f, K)) ≫
              (ihom (extendedAlternatingCechDerivedObject f)).map χ) ≫ eE.inv := by
                rw [cech_completion_unit_map_eq_completion_unit
                  (A := A) (H := H) (f := f) (K := K)]
        _ = (χ ≫ cech_completion_unit H f E) ≫ eE.inv := by
              rw [← cech_completion_unit_natural
                (A := A) (H := H) (f := f)
                (K := RHom[H](extendedAlternatingCechDerivedObject f, K))
                (L := E) (a := χ)]
        _ = χ := by
              simp [eE, Category.assoc]
    exact hleft.injective hφψ
  · -- Proof comment: once the unit on the target is invertible, the standard adjunction-style
    -- candidate gives a right inverse to precomposition.
    exact
      cech_completion_unit_surjective_of_isIso_target
        (A := A) (H := H) (f := f) K E

-- Proof sketch: identify `I` with the ideal generated by `f`, use Lemma `15.92.9` to compute
-- `RHom_A(A_g, RHom_A(\check C(f), K))` by adjoining `g` to the Čech family, and then apply
-- Lemmas `15.29.4`, `15.29.5`, and `15.92.1` exactly as in the textbook argument to show the
-- resulting derived internal-Hom object vanishes for every `g ∈ I`.
/-- For a chosen finite generating family of `I`, the explicit completion object
`RHom_A(\check C(f), K)` is derived complete with respect to `I`. -/
theorem derivedCompletionObj_isDerivedComplete_of_span_range
    (I : Ideal A) (H : RHomPkg)
    {r : ℕ} (f : Fin r → A) (hI : I = Ideal.span (Set.range f)) (K : DMod) :
    (RHom[H](extendedAlternatingCechDerivedObject f, K)).IsDerivedCompleteWithRespectTo I := by
  let C : DMod := RHom[H](extendedAlternatingCechDerivedObject f, K)
  -- Proof comment: it suffices to show that each chosen generator lies in the canonical
  -- localization-away vanishing ideal of the explicit completion object.
  rw [CategoryTheory.DerivedCategory.isDerivedCompleteWithRespectTo_iff]
  rw [hI]
  have hspan :
      Ideal.span (Set.range f) ≤ C.localizationAwayDerivedHomVanishingIdeal := by
    -- Proof comment: the span inclusion is generated by the source-faithful generatorwise
    -- vanishing statement.
    refine Ideal.span_le.2 ?_
    intro g hg
    rcases hg with ⟨i, rfl⟩
    exact
      (CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff
        C (f i)).2
        (generator_localizationAway_vanishing_of_cech_completion
          (A := A) (H := H) f K i)
  intro g hg
  exact
    (CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff C g).1
      (hspan hg)

-- Proof sketch: the map from the extended alternating Čech complex to `A[0]` induces a morphism
-- `η : K ⟶ RHom_A(\check C(f), K)`. The previous theorem gives that the target is derived
-- complete, and the textbook argument shows that precomposition with `η` gives a bijection on
-- morphism sets into every derived-complete object.
/-- For a chosen finite generating family of `I`, the explicit completion object carries a
universal morphism from `K` whose induced map on morphism sets into any derived-complete object is
bijective. -/
theorem exists_derivedCompletionMap_of_span_range
    (I : Ideal A) (H : RHomPkg)
    {r : ℕ} (f : Fin r → A) (hI : I = Ideal.span (Set.range f))
    (K : DMod) :
    ∃ η : K ⟶ RHom[H](extendedAlternatingCechDerivedObject f, K),
      ∀ E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory,
        Function.Bijective
          (fun φ : RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E.obj ↦ η ≫ φ) := by
  refine ⟨cech_completion_unit H f K, ?_⟩
  intro E
  -- Proof comment: the remaining universal property is the dedicated Čech-unit bijectivity
  -- statement, rewritten from `I` to the span of the chosen generators.
  simpa [hI] using
    (cech_completion_unit_bijective_of_isDerivedComplete
      (A := A) (H := H) (f := f) (K := K) (E := E.obj) E.property)

-- Proof sketch: choose a finite generating family `f` for `I`. The companion completion functor
-- `K ↦ RHom_A(\check C(f), K)` lands in the full subcategory of derived-complete objects by
-- `derivedCompletionObj_isDerivedComplete_of_span_range`, and
-- `exists_derivedCompletionMap_of_span_range` supplies the universal property showing that it is
-- left adjoint to the inclusion.
/-- Lemma 15.92.10: if `I` is a finitely generated ideal of `A`, then the inclusion of the full
subcategory of derived-complete objects of `D(A)` into `D(A)` has a left adjoint; for a chosen
finite generating family of `I`, this reflector is realized by the derived internal Hom from the
extended alternating Čech complex on those generators. -/
theorem derivedCompleteInclusion_isRightAdjoint_of_fg
    (I : Ideal A) (hI : I.FG) :
    Functor.IsRightAdjoint ((DerivedCategory.derivedCompleteObjectProperty I).ι) := by
  classical
  obtain ⟨s, hs⟩ := hI
  let r : ℕ := s.card
  let f : Fin r → A := fun i ↦ (s.equivFin.symm i : A)
  have hspan' : Ideal.span (Set.range f) = I := by
    -- Reindex the finite generating set by `Fin r` so the earlier span-range results apply.
    rw [← hs]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [f]⟩
  have hspan : I = Ideal.span (Set.range f) := hspan'.symm
  let H : RHomPkg := inferInstance
  let completionObj : DMod → DMod :=
    fun K ↦ RHom[H](extendedAlternatingCechDerivedObject f, K)
  let completionSubobj :
      DMod → (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory :=
    fun K ↦
      ⟨completionObj K,
        derivedCompletionObj_isDerivedComplete_of_span_range I H f hspan K⟩
  let η : ∀ K : DMod, K ⟶ completionObj K :=
    fun K ↦ Classical.choose (exists_derivedCompletionMap_of_span_range I H f hspan K)
  let homEquiv :
      ∀ K : DMod,
        ∀ E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory,
          (completionObj K ⟶ E.obj) ≃ (K ⟶ E.obj) :=
    fun K E ↦
      Equiv.ofBijective
        (fun φ : completionObj K ⟶ E.obj ↦ η K ≫ φ)
        ((Classical.choose_spec
          (exists_derivedCompletionMap_of_span_range I H f hspan K)) E)
  let completionMap :
      ∀ {K L : DMod}, (K ⟶ L) → (completionObj K ⟶ completionObj L) :=
    fun {K L} a ↦ (homEquiv K (completionSubobj L)).symm (a ≫ η L)
  have h_completionMap :
      ∀ {K L : DMod} (a : K ⟶ L), η K ≫ completionMap a = a ≫ η L := by
    intro K L a
    -- The defining universal property characterizes `completionMap a` by the commutative square.
    exact (homEquiv K (completionSubobj L)).apply_symm_apply (a ≫ η L)
  let completionFunctor :
      DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory where
    obj := completionSubobj
    map := fun {K L} a ↦ completionMap a
    map_id := by
      intro K
      -- Uniqueness in the universal property identifies the induced endomorphism with the identity.
      apply (homEquiv K (completionSubobj K)).injective
      simpa using (h_completionMap (K := K) (L := K) (𝟙 K))
    map_comp := by
      intro K L M a b
      -- Compare both composites after precomposing with the universal map `η K`.
      apply (homEquiv K (completionSubobj M)).injective
      calc
        η K ≫ completionMap (a ≫ b)
            = (a ≫ b) ≫ η M := h_completionMap (K := K) (L := M) (a ≫ b)
        _ = η K ≫ (completionMap a ≫ completionMap b) := by
          rw [Category.assoc, h_completionMap (K := K) (L := L) a]
          rw [Category.assoc, h_completionMap (K := L) (L := M) b]
          simp [Category.assoc]
  let completionAdjunction :
      completionFunctor ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι :=
    Adjunction.mkOfHomEquiv
      { homEquiv := fun K E ↦ by
          -- Morphisms in the full subcategory are the underlying morphisms in `D(A)`.
          change (completionObj K ⟶ E.obj) ≃ (K ⟶ E.obj)
          exact homEquiv K E
        homEquiv_naturality_left_symm := by
          intro K₁ K₂ E a g
          -- Both sides correspond to the same map `a ≫ g : K₁ ⟶ E`.
          apply (homEquiv K₁ E).injective
          calc
            η K₁ ≫ (homEquiv K₁ E).symm (a ≫ g)
                = a ≫ g := (homEquiv K₁ E).apply_symm_apply (a ≫ g)
            _ = a ≫ (η K₂ ≫ (homEquiv K₂ E).symm g) := by
                rw [(homEquiv K₂ E).apply_symm_apply g]
            _ = (η K₁ ≫ completionMap a) ≫ (homEquiv K₂ E).symm g := by
                rw [h_completionMap (K := K₁) (L := K₂) a]
                simp [Category.assoc]
            _ = η K₁ ≫ (completionMap a ≫ (homEquiv K₂ E).symm g) := by
                simp [Category.assoc]
        homEquiv_naturality_right := by
          intro K E₁ E₂ g h
          -- Right naturality is just associativity of postcomposition.
          change η K ≫ (g ≫ h) = (η K ≫ g) ≫ h
          simp [Category.assoc] }
  exact completionAdjunction.isRightAdjoint

end

end DerivedCategory

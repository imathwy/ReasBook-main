import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_59_7
import StacksProject_2024.Chap15.Lemma_15_67_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "KModA" => HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ)
local notation "KModB" => HomotopyCategory (ModuleCat B) (ComplexShape.up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QhB" => (DerivedCategory.Qh : KModB ⥤ DModB)

/-- Helper for Lemma 15.67.13: the cochain-level scalar-extension functor along `A → B`. -/
private abbrev ExtCpx :
    CochainComplex (ModuleCat A) ℤ ⥤ CochainComplex (ModuleCat B) ℤ :=
  (ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)

/- Domain-style sampling for Lemma 15.67.13:
- primary domain: tor-amplitude in derived categories under derived scalar extension;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[A]^L[B]`,
  `ModuleCat.extendScalars`;
- best owner abstraction: this theorem is `source-facing`, while the core/canonical owners are the
  tor-amplitude predicate `HasTorAmplitudeIn` and the derived scalar-extension owner
  `derivedTensorWithAlgebra (algebraMap A B)`;
- primitive vs. derived:
  primitive data are the derived `A`-complex `K` and its tor-amplitude interval `[a, b]`;
  the base-changed object `K ⊗[A]^L[B]` is derived API through the canonical owner notation, so
  this file should depend directly on the owner file `15_60_1_1` rather than the later
  change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: preservation of tor-amplitude under base change along `A → B`;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

-- Proof sketch: choose a flat representative of `K` concentrated in degrees `[a, b]` using
-- Lemma `15.67.3`; after tensoring termwise with `B`, the resulting complex is still concentrated
-- in `[a, b]`, and its terms are flat over `B` by flat base change. This new flat representative
-- computes `K ⊗_A^L B`, so Lemma `15.67.3` gives the claimed tor-amplitude interval over `B`.
/-- Helper for Lemma 15.67.13: termwise scalar extension preserves the lower support bound of a
cochain complex. -/
lemma extendScalarsComplex_isStrictlyGE
    {E : CochainComplex (ModuleCat A) ℤ} {a : ℤ}
    (hE : E.IsStrictlyGE a) :
    ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyGE a := by
  -- Read the lower bound degreewise and transport zero objects through scalar extension.
  rw [CochainComplex.isStrictlyGE_iff] at hE ⊢
  intro i hi
  change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (E.X i) : ModuleCat B))
  simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hE i hi)

/-- Helper for Lemma 15.67.13: termwise scalar extension preserves the upper support bound of a
cochain complex. -/
lemma extendScalarsComplex_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ} {b : ℤ}
    (hE : E.IsStrictlyLE b) :
    ((ExtCpx (A := A) (B := B)).obj E).IsStrictlyLE b := by
  -- Read the upper bound degreewise and transport zero objects through scalar extension.
  rw [CochainComplex.isStrictlyLE_iff] at hE ⊢
  intro i hi
  change IsZero (((ModuleCat.extendScalars (algebraMap A B)).obj (E.X i) : ModuleCat B))
  simpa [ExtCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using
    (ModuleCat.extendScalars (algebraMap A B)).map_isZero (hE i hi)

/-- Helper for Lemma 15.67.13: termwise scalar extension carries flat terms to flat terms. -/
lemma extendScalarsComplex_isTermwiseFlat
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) :
    ((ExtCpx (A := A) (B := B)).obj E).IsTermwiseFlat := by
  -- Proof comment: termwise flatness is an objectwise statement, and ordinary scalar extension of
  -- a flat module is flat over the target ring.
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

/-- Helper for Lemma 15.67.13: a bounded-above termwise-flat complex is K-flat. -/
private theorem isKFlat_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    E.IsKFlat := by
  -- Proof comment: package the strict upper bound as the canonical `minus` owner, then invoke
  -- the bounded-above flat-to-K-flat theorem from Lemma `15.59.7`.
  have hminus : CochainComplex.minus (ModuleCat A) E :=
    (CochainComplex.minus_iff (ModuleCat A) E).2 ⟨b, hLE⟩
  exact CochainComplex.isKFlat_of_boundedAbove_of_flat E hminus hE

/-- Helper for Lemma 15.67.13: this is the explicit total-left-derived counit comparison from the
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
  -- Proof comment: conjugate the total-left-derived counit by `quotientCompQhIso` on the source
  -- and by `mapHomotopyCategoryFactors` plus `quotientCompQhIso` on the target.
  (derivedTensorWithAlgebra (algebraMap A B)).map
      ((DerivedCategory.quotientCompQhIso (ModuleCat A)).app E).inv ≫
    (F.totalLeftDerivedCounit QhA QisA).app
      ((HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).obj E) ≫
    QhB.map
      ((Functor.mapHomotopyCategoryFactors
        (ModuleCat.extendScalars (algebraMap A B)) (ComplexShape.up ℤ)).inv.app E) ≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat B)).app
      ((ExtCpx (A := A) (B := B)).obj E)).hom

/-- Helper for Lemma 15.67.13: a bounded-above termwise-flat representative computes derived
scalar extension through the canonical counit comparison. -/
private theorem derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) := by
  -- Route correction: use the source-faithful representative comparison morphism itself and prove
  -- its middle counit component is invertible because the chosen bounded-above flat model is
  -- K-flat.
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
  -- Proof comment: the remaining factors are maps of canonical isomorphisms, so the displayed
  -- comparison inherits invertibility from the counit component.
  simpa [derivedTensorWithAlgebra_complexComparison, F, F₀, qE]

/-- Helper for Lemma 15.67.13: a bounded-above termwise-flat cochain model should compute derived
scalar extension by the canonical total-left-derived counit comparison. -/
noncomputable def derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
    {E : CochainComplex (ModuleCat A) ℤ}
    (hE : E.IsTermwiseFlat) {b : ℤ} (hLE : E.IsStrictlyLE b) :
    ((DerivedCategory.Q.obj E) ⊗[A]^L[B]) ≅
      DerivedCategory.Q.obj ((ExtCpx (A := A) (B := B)).obj E) :=
  -- Proof comment: once the explicit representative comparison is known to be an isomorphism, the
  -- public comparison is just `asIso` of that morphism.
  letI :
      IsIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E) :=
    derivedTensorWithAlgebra_complexComparison_isIso_of_termwiseFlat_of_isStrictlyLE
      (A := A) (B := B) hE hLE
  asIso (derivedTensorWithAlgebra_complexComparison (A := A) (B := B) E)

/-- Lemma 15.67.13: if an object `K^•` of `D(A)` has tor-amplitude in `[a, b]`, then its derived
base change `K^• \otimes_A^{\mathbf L} B` has tor-amplitude in `[a, b]` as an object of
`D(B)`. -/
@[stacks 066L]
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra
    (K : DModA) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn (K ⊗[A]^L[B]) a b := by
  -- Route correction: discard the earlier direct change-of-rings test-object route and follow the
  -- source proof literally through bounded flat representatives from Lemma `15.67.3`.
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
    -- Reapply the representative criterion over `B` to the scalar-extended flat model.
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
    -- The remaining bridge is the representative-level comparison between derived scalar
    -- extension and termwise scalar extension of the chosen bounded-above flat model.
    exact
      (hasTorAmplitudeIn_of_iso_local
        (R := B)
        (a := a) (b := b)
        (derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
          (A := A) (B := B) hEFlat hELE)).2
        hModel
  -- Transport the result from the chosen representative `Q.obj E` back to the original `K`.
  exact
    (hasTorAmplitudeIn_of_iso_local
      (R := B)
      (a := a) (b := b)
      ((derivedTensorWithAlgebra (algebraMap A B)).mapIso eE)).2
      hBaseChangeModel

end

end CategoryTheory

import Mathlib.Data.List.TFAE
import stacks_proof.stacks_project.Chap10.Lemma_10_23_1
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Lemma_15_60_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)

/-- Helper for Lemma 15.67.15: the additive lift to homotopy categories induced by a functor to a
derived category. -/
private abbrev mapHomotopyCategoryToDerived
    {C : Type u} {E : Type u} [Category C] [Category E] [Preadditive C] [Abelian E]
    [HasDerivedCategory E] (F : C ⥤ E) [F.Additive] :
    HomotopyCategory C (up ℤ) ⥤ DerivedCategory E :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

local instance extendScalars_additive_atPrime (q : PrimeSpectrum B) :
    (ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (Localization.AtPrime q.asIdeal))).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap B (Localization.AtPrime q.asIdeal))).left_adjoint_additive

local instance extendScalars_preservesFiniteLimits_atPrime (q : PrimeSpectrum B) :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap B (Localization.AtPrime q.asIdeal))) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr <|
      IsLocalization.flat (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl)

/-- Helper for Lemma 15.67.15: the prime-local map `A_(q ∩ A) → B_q` supplies the canonical
localized algebra structure on `B_q`. -/
private noncomputable instance localizationAtPrime_over_base_algebra
    (q : PrimeSpectrum B) :
    Algebra (Localization.AtPrime (q.asIdeal.under A)) (Localization.AtPrime q.asIdeal) :=
  (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl).toAlgebra

/-- Helper for Lemma 15.67.15: the localized map `A_(q ∩ A) → B_q` extends the direct map
`A → B_q`. -/
lemma localizationAtPrime_over_base_comp_eq
    (q : PrimeSpectrum B) :
    (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl).comp
        (algebraMap A (Localization.AtPrime (q.asIdeal.under A))) =
      algebraMap A (Localization.AtPrime q.asIdeal) := by
  -- Both maps send `x` to the same localized numerator, so they agree by extensionality.
  ext x
  simpa [RingHom.comp_apply] using
    congrArg
      (fun f : A →+* Localization.AtPrime q.asIdeal => f x)
      (IsScalarTower.algebraMap_eq A B (Localization.AtPrime q.asIdeal))

/-- Helper for Lemma 15.67.15: after forgetting `B` to `A`, the regular `B`-module is still just
`B`, so the tensor presentation of `extendScalars` uses the identity linear equivalence on the
target ring. -/
private noncomputable def restrictScalars_self_linearEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.67.15: the restricted regular `B`-module still carries the expected
scalar-tower structure over `A → B`. -/
private instance restrictScalars_self_isScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun a b ↦ by
    rfl

/-- Helper for Lemma 15.67.15: the `ModuleCat.extendScalars` object is the honest tensor product
`B ⊗[A] M`. -/
private noncomputable def extendScalars_tensor_linearEquiv
    (M : ModuleCat A) :
    ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[B] TensorProduct A B M :=
  -- Unfold the owner-level scalar-extension object only once, then replace the left tensor factor
  -- by the regular `B`-module through the identity equivalence above.
  TensorProduct.AlgebraTensorModule.congr
    restrictScalars_self_linearEquiv
    (LinearEquiv.refl A M)

/- Domain sampling pass:
* primary domain: tor-amplitude in derived categories of module categories under restriction of
  scalars and prime localization;
* sampled owner declarations:
  - `HasTorAmplitudeIn` from `Definition_15_67_1`, the chapter owner for tor-amplitude;
  - `(ModuleCat.extendScalars f).mapDerivedCategory`, the canonical exact derived localization
    functor for flat scalar extension;
  - `(ModuleCat.restrictScalars f).mapDerivedCategory`, the canonical derived restriction functor;
  - `Localization.localRingHom`, the canonical owner for the localized map
    `A_(q ∩ A) → B_q`;
  - `hasTorAmplitudeIn_restrictScalars_of_flat` from `Lemma_15_67_11`, the chapter-local reuse
    point for passing tor-amplitude across flat restriction of scalars.

Source/core/bridge triage:
* `source-facing`: `hasTorAmplitudeIn_over_base_tfae_of_localizations`;
* `core/canonical`: `HasTorAmplitudeIn`, `ModuleCat.extendScalars`,
  `Localization.localRingHom`, and `mapDerivedCategory`;
* `bridge/view`: the localized restricted derived object over the contracted prime, written
  directly from those canonical owners in the prime-local and maximal-local clauses.

Primitive data is only the derived object `K : DModB` together with the canonical localization and
restriction functors. The public theorem below is kept source-facing as a `TFAE`, and its local
clauses are stated directly from those owners, using only theorem-local names to avoid repeating
the same dependent-type expression in every clause.
-/

/-- Helper for Lemma 15.67.15: the honest global `B`-linear test object used in the source proof
for tor-amplitude over the base ring `A`. -/
noncomputable def overBaseTest
    (K : DModB) (M : ModuleCat A) : DModB :=
  -- This is the global object whose localization is meant to compare with the local
  -- `A_(q ∩ A)`-test object.
  K ⊗[B]^L
    ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A B)).obj
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))

/-- Helper for Lemma 15.67.15: mapping the test object isomorphism through homology gives the
comparison used to transport tor-amplitude across isomorphic derived complexes. -/
noncomputable def torAmplitude_test_homology_iso
    {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat R)}
    (e : K ≅ L) (M : ModuleCat R) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        (K ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
        (L ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) :=
  (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
    ((derivedTensorProduct
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).mapIso e)

/-- Helper for Lemma 15.67.15: tor-amplitude in a fixed interval is invariant under isomorphism in
the derived category. -/
lemma hasTorAmplitudeIn_iff_of_iso
    {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat R)} {a b : ℤ}
    (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro hK
    intro M i hi
    -- Transport the tested homology object across the comparison isomorphism on the source
    -- derived complex.
    let eH := torAmplitude_test_homology_iso e M i
    exact eH.isZero_iff.1 (hK M i hi)
  · intro hL
    intro M i hi
    -- Apply the same comparison in the reverse direction.
    let eH := torAmplitude_test_homology_iso e.symm M i
    exact eH.isZero_iff.1 (hL M i hi)

/-- Helper for Lemma 15.67.15: if a `B`-module becomes zero after restricting scalars to `A`,
then it was already zero as a `B`-module. -/
lemma isZero_of_restrictScalars_obj
    (M : ModuleCat B)
    (hM : IsZero ((ModuleCat.restrictScalars (algebraMap A B)).obj M)) :
    IsZero M := by
  -- Restriction of scalars leaves the underlying additive group unchanged, so zero objects reflect.
  letI : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap A B)).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap A B)).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.67.15: restricting scalars from `B` to `A` commutes with homology on the
derived category of modules. -/
noncomputable def restrictScalars_homology_iso
    (L : DModB) (i : ℤ) :
    (HA i).obj (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj ((HB i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj K
  let eB : (HB i).obj L ≅ K.homology i :=
    ((HB i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Pass to a chosen complex model of `L`, compare homology before and after restriction, and
  -- then return to the derived-category homology objects.
  (HA i).mapIso
      (((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap A B)) ≪≫
      (ModuleCat.restrictScalars (algebraMap A B)).mapIso eB.symm

/-- Helper for Lemma 15.67.15: exact localization at a prime commutes with homology. -/
noncomputable def extendScalars_homology_iso_atPrime
    (q : PrimeSpectrum B) (L : DModB) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat (Localization.AtPrime q.asIdeal)) i).obj
        (((ModuleCat.extendScalars
            (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).obj L) ≅
      (ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).obj ((HB i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapHomologicalComplex (up ℤ)).obj K
  let eB : (HB i).obj L ≅ K.homology i :=
    ((HB i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Pass to a chosen complex model of `L`, compare homology before and after exact localization,
  -- and then return to the derived-category homology objects.
  (DerivedCategory.homologyFunctor (ModuleCat (Localization.AtPrime q.asIdeal)) i).mapIso
      (((((ModuleCat.extendScalars
            (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.extendScalars
          (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat (Localization.AtPrime q.asIdeal)) i).app FK ≪≫
    (K.sc i).mapHomologyIso
      (ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q.asIdeal))) ≪≫
      (ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapIso eB.symm

/-- Helper for Lemma 15.67.15: exact restriction of scalars sends a degree-zero complex to the
degree-zero complex of the restricted module. -/
noncomputable def restrictScalars_single_iso
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (M : ModuleCat S) :
    ((ModuleCat.restrictScalars σ).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars σ).obj M) := by
  -- Restriction of scalars is exact, so the standard `singleFunctor` comparison computes its
  -- image on a degree-zero complex without introducing any derived ambiguity.
  exact
    ((((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars σ)
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
        ((ModuleCat.restrictScalars σ).obj M)).symm)

/-- Helper for Lemma 15.67.15: exact localization at a prime sends a degree-zero complex to the
degree-zero complex of the localized module. -/
noncomputable def extendScalars_single_iso_atPrime
    (q : PrimeSpectrum B) (M : ModuleCat B) :
    (((ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor
        (ModuleCat (Localization.AtPrime q.asIdeal)) (0 : ℤ)).obj
        ((ModuleCat.extendScalars
          (algebraMap B (Localization.AtPrime q.asIdeal))).obj M) := by
  -- The localization functor is exact, so the same degree-zero comparison applies after
  -- extending scalars to `B_q`.
  exact
    ((((ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.extendScalars
            (algebraMap B (Localization.AtPrime q.asIdeal)))
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ
        (ModuleCat (Localization.AtPrime q.asIdeal)) (0 : ℤ)).app
          ((ModuleCat.extendScalars
            (algebraMap B (Localization.AtPrime q.asIdeal))).obj M)).symm)

local instance extendScalars_additive
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R R')).left_adjoint_additive

local instance extendScalars_preservesFiniteLimits_of_flat
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R R' from inferInstance))

/-- Helper for Lemma 15.67.15: exact flat scalar extension agrees with the owner
`derivedTensorWithAlgebra` functor on the derived category. -/
noncomputable def extendScalars_mapDerivedCategory_iso_of_flat
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] :
    (ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory ≅
      derivedTensorWithAlgebra (algebraMap R R') := by
  let F₀ : ModuleCat R ⥤ ModuleCat R' := ModuleCat.extendScalars (algebraMap R R')
  let F :
      HomotopyCategory (ModuleCat R) (up ℤ) ⥤
        DerivedCategory (ModuleCat R') :=
    mapHomotopyCategoryToDerived F₀
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)) := by
    -- The owner `derivedTensorWithAlgebra` is the total left-derived functor of exact scalar
    -- extension.
    simpa [F, F₀, mapHomotopyCategoryToDerived] using
      (extendScalarsToDerived_hasLeftDerivedFunctor
        (R := R) (A := R') (algebraMap R R'))
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)) := by
    -- Exact flat scalar extension already inverts quasi-isomorphisms, so it computes its own
    -- left derived functor.
    simpa [F₀] using
      (Functor.isLeftDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ))
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactorsh)
  -- Compare exact derived scalar extension with the canonical owner
  -- `derivedTensorWithAlgebra`.
  simpa [derivedTensorWithAlgebra, F, F₀, mapHomotopyCategoryToDerived] using
    (Functor.leftDerivedNatIso
      F₀.mapDerivedCategory
      (F.totalLeftDerived
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat R) (up ℤ) ⥤
            DerivedCategory (ModuleCat R))
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)))
      F₀.mapDerivedCategoryFactorsh.hom
      (Functor.totalLeftDerivedCounit
        F
        (DerivedCategory.Qh :
          HomotopyCategory (ModuleCat R) (up ℤ) ⥤
            DerivedCategory (ModuleCat R))
        (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)))
      (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ))
      (Iso.refl F))

/-- Helper for Lemma 15.67.15: exact scalar extension sends a degree-zero complex to the
degree-zero complex of the scalar-extended module. -/
noncomputable def extendScalars_single_iso
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (M : ModuleCat R) :
    (((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj
        ((ModuleCat.extendScalars (algebraMap R R')).obj M) := by
  -- Exact flat scalar extension can be computed on the cochain-level degree-zero complex.
  exact
    ((((ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.extendScalars (algebraMap R R')).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.extendScalars (algebraMap R R'))
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R') (0 : ℤ)).app
        ((ModuleCat.extendScalars (algebraMap R R')).obj M)).symm)

/-- Helper for Lemma 15.67.15: flat derived scalar extension carries a degree-zero module to the
degree-zero scalar-extended module. -/
noncomputable def derivedTensorWithAlgebra_single_iso_of_flat
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    (M : ModuleCat R) :
    (derivedTensorWithAlgebra (algebraMap R R')).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj
        ((ModuleCat.extendScalars (algebraMap R R')).obj M) := by
  -- First identify the owner `derivedTensorWithAlgebra` with exact scalar extension, then use
  -- the explicit degree-zero comparison for exact scalar extension.
  exact
    (extendScalars_mapDerivedCategory_iso_of_flat (R := R) (R' := R')).symm.app
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≪≫
      extendScalars_single_iso (R := R) (R' := R') M

/-- Helper for Lemma 15.67.15: zero homology remains zero after restricting scalars from `B` to
`A`. -/
lemma isZero_homology_restrictScalars_of_isZero
    (L : DModB) (i : ℤ)
    (hL : IsZero ((HB i).obj L)) :
    IsZero
      ((HA i).obj
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L)) := by
  -- Move the vanishing statement across the canonical homology comparison for restriction of
  -- scalars.
  exact (restrictScalars_homology_iso L i).isZero_iff.2 <|
    (ModuleCat.restrictScalars (algebraMap A B)).map_isZero hL

/-- Helper for Lemma 15.67.15: zero homology remains zero after localizing a `B`-complex at a
prime of `B`. -/
lemma isZero_homology_localized_atPrime_of_isZero
    (q : PrimeSpectrum B) (L : DModB) (i : ℤ)
    (hL : IsZero ((HB i).obj L)) :
    IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat (Localization.AtPrime q.asIdeal)) i).obj
        (((ModuleCat.extendScalars
            (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).obj L)) := by
  -- Move the vanishing statement across the canonical homology comparison for exact localization.
  exact (extendScalars_homology_iso_atPrime q L i).isZero_iff.2 <|
    (ModuleCat.extendScalars
      (algebraMap B (Localization.AtPrime q.asIdeal))).map_isZero hL

/-- Helper for Lemma 15.67.15: after restricting scalars from `Localization M` to `R`, the
identity map on a `Localization M`-module is already a localization map for `M`. -/
private theorem localized_restrictScalars_id_isLocalizedModule
    {R : Type u} [CommRing R]
    (M : Submonoid R) (N : ModuleCat (Localization M)) :
    let _ : Module R N := Module.compHom N (algebraMap R (Localization M))
    let _ : IsScalarTower R (Localization M) N :=
      RestrictScalars.isScalarTower R (Localization M) N
    IsLocalizedModule M (LinearMap.id : N →ₗ[R] N) := by
  let _ : Module R N := Module.compHom N (algebraMap R (Localization M))
  let _ : IsScalarTower R (Localization M) N :=
    RestrictScalars.isScalarTower R (Localization M) N
  -- The target is already an `M⁻¹R`-module, so the identity map satisfies the owner localization
  -- axioms over the source ring.
  simpa using (isLocalizedModule_id M N (Localization M))

/-- Helper for Lemma 15.67.15: over the source ring `R`, localizing a module already defined over
`Localization M` recovers the same module. -/
private noncomputable def localized_restrictScalars_base_linearEquiv
    {R : Type u} [CommRing R]
    (M : Submonoid R) (N : ModuleCat (Localization M)) :
    let _ : Module R N := Module.compHom N (algebraMap R (Localization M))
    LocalizedModule M ((ModuleCat.restrictScalars (algebraMap R (Localization M))).obj N) ≃ₗ[R] N :=
  let _ : Module R N := Module.compHom N (algebraMap R (Localization M))
  let _ : IsScalarTower R (Localization M) N :=
    RestrictScalars.isScalarTower R (Localization M) N
  let g :
      ((ModuleCat.restrictScalars (algebraMap R (Localization M))).obj N) →ₗ[R] N :=
    LinearMap.id
  letI : IsLocalizedModule M g :=
    localized_restrictScalars_id_isLocalizedModule M N
  -- Compare the canonical localization map of the restricted module with the identity
  -- localization map on the already localized target module.
  IsLocalizedModule.linearEquiv M
    (LocalizedModule.mkLinearMap M ((ModuleCat.restrictScalars (algebraMap R (Localization M))).obj N))
    g

/-- Helper for Lemma 15.67.15: for the canonical localization type `Localization M`, localizing a
module after forgetting to `R` recovers the original localized module. -/
noncomputable def localized_restrictScalars_linearEquiv
    {R : Type u} [CommRing R]
    (M : Submonoid R) (N : ModuleCat (Localization M)) :
    LocalizedModule M ((ModuleCat.restrictScalars (algebraMap R (Localization M))).obj N) ≃ₗ[Localization M] N :=
  let _ : Module R N := Module.compHom N (algebraMap R (Localization M))
  let _ : IsScalarTower R (Localization M) N :=
    RestrictScalars.isScalarTower R (Localization M) N
  -- First build the owner equivalence over `R`, then upgrade it to the localized ring.
  LinearEquiv.extendScalarsOfIsLocalization M (Localization M)
    (localized_restrictScalars_base_linearEquiv M N)

/-- Helper for Lemma 15.67.15: the previous localization comparison packaged as an isomorphism in
`ModuleCat (Localization M)`. -/
noncomputable def localized_restrictScalars_iso
    {R : Type u} [CommRing R]
    (M : Submonoid R) (N : ModuleCat (Localization M)) :
    ModuleCat.of (Localization M)
      (LocalizedModule M ((ModuleCat.restrictScalars (algebraMap R (Localization M))).obj N)) ≅
      N where
  hom := ModuleCat.ofHom (localized_restrictScalars_linearEquiv M N).toLinearMap
  inv := ModuleCat.ofHom (localized_restrictScalars_linearEquiv M N).symm.toLinearMap
  hom_inv_id := by
    -- The forward and backward maps are inverse because they come from a linear equivalence.
    ext x
    simpa using (localized_restrictScalars_linearEquiv M N).left_inv x
  inv_hom_id := by
    -- The reverse composite is the same identity-on-elements check.
    ext x
    simpa using (localized_restrictScalars_linearEquiv M N).right_inv x

/-- Helper for Lemma 15.67.15: after the raw comparison over `A`, one rewrites the tensor base to
`A_(q ∩ A)` using the canonical localization tensor equivalence. -/
noncomputable def localized_global_base_factor_changeBase_base_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    TensorProduct (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime (q.asIdeal.under A) M) ≃ₗ[
          Localization.AtPrime (q.asIdeal.under A)]
      TensorProduct A (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime (q.asIdeal.under A) M) :=
  -- Over the contracted local ring, the source proof's base rewrite is exactly the owner
  -- localization/tensor comparison `moduleTensorEquiv`.
  IsLocalization.moduleTensorEquiv (q.asIdeal.under A).primeCompl
    (Localization.AtPrime (q.asIdeal.under A))
    (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime (q.asIdeal.under A) M)

/-- Helper for Lemma 15.67.15: replacing `M` by its contracted-prime localization inside the
localized tensor product factors through the usual cancellation equivalence and the owner
identification `A_(q ∩ A) ⊗[A] M ≃ M_(q ∩ A)`. -/
noncomputable def tensor_localizedModule_atPrime_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    TensorProduct A (Localization.AtPrime q.asIdeal) M ≃ₗ[Localization.AtPrime q.asIdeal]
      TensorProduct (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime (q.asIdeal.under A) M) :=
  -- First factor the direct tensor through `A_(q ∩ A) ⊗[A] M`, then replace that middle tensor
  -- factor by the contracted-prime localization of `M`.
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      A (Localization.AtPrime (q.asIdeal.under A))
      (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) M).symm).trans
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal))
      (LocalizedModule.equivTensorProduct (q.asIdeal.under A).primeCompl M).symm)

/-- Helper for Lemma 15.67.15: the direct tensor/localization bridge above, recorded under the
name used by the later source-faithful comparison. -/
noncomputable def localized_global_base_factor_changeBase_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    TensorProduct A (Localization.AtPrime q.asIdeal)
        M ≃ₗ[Localization.AtPrime q.asIdeal]
      TensorProduct (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime (q.asIdeal.under A) M) :=
  -- Reuse the dedicated bridge so later arguments refer to a single canonical comparison.
  tensor_localizedModule_atPrime_linearEquiv q M

/-- Helper for Lemma 15.67.15: before replacing `M` by its contracted-prime localization, the raw
`(B ⊗[A] M)_q` comparison is the owner-level cancellation of the middle `B`-tensor factor. -/
noncomputable def localized_tensor_assoc_over_base_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    TensorProduct B (Localization.AtPrime q.asIdeal)
      (TensorProduct A B M) ≃ₗ[Localization.AtPrime q.asIdeal]
      TensorProduct A (Localization.AtPrime q.asIdeal) M :=
  -- The mixed-base tensor product is exactly the owner cancellation from iterated base change
  -- `A → B → B_q`.
  TensorProduct.AlgebraTensorModule.cancelBaseChange
    A B (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) M

/-- Helper for Lemma 15.67.15: localizing the honest global degree-zero base-change factor over
`B` first identifies it with the unreduced tensor product `B_q ⊗[A] M`. -/
noncomputable def localized_global_base_factor_overA_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    LocalizedModule.AtPrime q.asIdeal ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[Localization.AtPrime q.asIdeal]
      TensorProduct A (Localization.AtPrime q.asIdeal)
        M :=
  -- Identify the localization of `B ⊗[A] M` with `B_q ⊗[A] M` by first expanding scalar
  -- extension as the honest tensor product and then cancelling the middle `B`-factor.
  (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)).trans
    ((TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal))
        (extendScalars_tensor_linearEquiv M)).trans
      (localized_tensor_assoc_over_base_linearEquiv q M))

local instance extendScalars_additive_atMaximal (m : MaximalSpectrum B) :
    (ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (Localization.AtPrime m.asIdeal))).Additive :=
  extendScalars_additive_atPrime m.toPrimeSpectrum

local instance extendScalars_preservesFiniteLimits_atMaximal (m : MaximalSpectrum B) :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u}
        (algebraMap B (Localization.AtPrime m.asIdeal))) :=
  extendScalars_preservesFiniteLimits_atPrime m.toPrimeSpectrum

/-- Helper for Lemma 15.67.15: localizing the honest global degree-zero base-change factor over
`B` identifies it with the raw tensor product `B_q ⊗[A_(q ∩ A)] M_(q ∩ A)`. -/
noncomputable def localized_global_base_factor_linearEquiv
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    LocalizedModule.AtPrime q.asIdeal ((ModuleCat.extendScalars (algebraMap A B)).obj M) ≃ₗ[Localization.AtPrime q.asIdeal]
      TensorProduct (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime (q.asIdeal.under A) M) :=
  -- Compose the raw `⊗[A]` comparison with the isolated replacement of `M` by `M_(q ∩ A)`.
  (localized_global_base_factor_overA_linearEquiv q M).trans
    (localized_global_base_factor_changeBase_linearEquiv q M)

/-- Helper for Lemma 15.67.15: scalar extension to the contracted-prime localization agrees with
the canonical localized module. -/
noncomputable def extendScalars_to_localizedModule_iso
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    (ModuleCat.extendScalars
      (algebraMap A (Localization.AtPrime (q.asIdeal.under A)))).obj M ≅
      ModuleCat.of (Localization.AtPrime (q.asIdeal.under A))
        (LocalizedModule.AtPrime (q.asIdeal.under A) M) := by
  let Ap := Localization.AtPrime (q.asIdeal.under A)
  let eTensor :
      (ModuleCat.extendScalars (algebraMap A Ap)).obj M ≅
        ModuleCat.of Ap (TensorProduct A Ap M) :=
    (extendScalars_tensor_linearEquiv (A := A) (B := Ap) M).toModuleIso
  let eLocal :
      ModuleCat.of Ap (TensorProduct A Ap M) ≅
        ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M) :=
    ((LocalizedModule.equivTensorProduct (q.asIdeal.under A).primeCompl M).symm).toModuleIso
  -- Expand scalar extension into the honest tensor product and then collapse that tensor product
  -- to the canonical localization module.
  exact eTensor ≪≫ eLocal

/-- Helper for Lemma 15.67.15: if the degree-`i` homology of a derived `B`-complex becomes zero
after localizing at every maximal ideal of `B`, then the original homology object is already
zero. -/
lemma isZero_homology_of_localized_maximals
    (L : DModB) (i : ℤ)
    (hmax :
      ∀ m : MaximalSpectrum B,
        IsZero
          ((DerivedCategory.homologyFunctor
              (ModuleCat (Localization.AtPrime m.asIdeal)) i).obj
            (((ModuleCat.extendScalars
                (algebraMap B (Localization.AtPrime m.asIdeal))).mapDerivedCategory).obj L))) :
    IsZero ((HB i).obj L) := by
  have hsub_local :
      ∀ m : MaximalSpectrum B,
        Subsingleton (LocalizedModule.AtPrime m.asIdeal ((HB i).obj L)) := by
    intro m
    -- Move the maximal-local vanishing back to the honest localized module and read it as a
    -- subsingleton statement.
    have htensor :
        IsZero
          ((ModuleCat.extendScalars
              (algebraMap B (Localization.AtPrime m.asIdeal))).obj ((HB i).obj L)) := by
      let q : PrimeSpectrum B := m.toPrimeSpectrum
      exact (extendScalars_homology_iso_atPrime q L i).isZero_iff.1 (hmax m)
    have hlocal :
        IsZero
          (ModuleCat.of (Localization.AtPrime m.asIdeal)
            (LocalizedModule.AtPrime m.asIdeal ((HB i).obj L))) := by
      let eTensor :
          (ModuleCat.extendScalars
              (algebraMap B (Localization.AtPrime m.asIdeal))).obj ((HB i).obj L) ≅
            ModuleCat.of (Localization.AtPrime m.asIdeal)
              (TensorProduct B (Localization.AtPrime m.asIdeal) ((HB i).obj L)) := by
        -- Expand scalar extension once into the tensor-product owner.
        simpa using
          (extendScalars_tensor_linearEquiv
            (A := B) (B := Localization.AtPrime m.asIdeal) ((HB i).obj L)).toModuleIso
      let eLocal :
          ModuleCat.of (Localization.AtPrime m.asIdeal)
            (TensorProduct B (Localization.AtPrime m.asIdeal) ((HB i).obj L)) ≅
              ModuleCat.of (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal ((HB i).obj L)) :=
        ((LocalizedModule.equivTensorProduct m.asIdeal.primeCompl ((HB i).obj L)).symm).toModuleIso
      exact IsZero.of_iso htensor (eTensor ≪≫ eLocal).symm
    exact ModuleCat.subsingleton_of_isZero hlocal
  have hglobalSub :
      Subsingleton ↑((HB i).obj L) := by
    -- Detect vanishing from the maximal localizations using Lemma `10.23.1`.
    have hmaxIdeal :
        ∀ (P : Ideal B) [P.IsMaximal],
          Subsingleton (LocalizedModule.AtPrime P ↑((HB i).obj L)) := by
      intro P _
      let m : MaximalSpectrum B := ⟨P, inferInstance⟩
      simpa using hsub_local m
    exact
      ((module_zero_localization_tfae
        (R := B) (M := ↑((HB i).obj L))).out 2 0).mp hmaxIdeal
  letI : Subsingleton ↑((HB i).obj L) := hglobalSub
  exact ModuleCat.isZero_of_subsingleton ((HB i).obj L)

/-- Helper for Lemma 15.67.15: the previous raw tensor comparison packaged as an isomorphism in
`ModuleCat (Localization.AtPrime q.asIdeal)`. -/
noncomputable def localized_global_base_factor_iso
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    ModuleCat.of (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal ((ModuleCat.extendScalars (algebraMap A B)).obj M)) ≅
    ModuleCat.of (Localization.AtPrime q.asIdeal)
      (TensorProduct (Localization.AtPrime (q.asIdeal.under A))
        (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime (q.asIdeal.under A) M)) where
  hom := ModuleCat.ofHom (localized_global_base_factor_linearEquiv q M).toLinearMap
  inv := ModuleCat.ofHom (localized_global_base_factor_linearEquiv q M).symm.toLinearMap
  hom_inv_id := by
    -- The categorical inverse is the underlying inverse of the linear equivalence.
    ext x
    simpa using (localized_global_base_factor_linearEquiv q M).left_inv x
  inv_hom_id := by
    -- The reverse composite is checked on elements in the same way.
    ext x
    simpa using (localized_global_base_factor_linearEquiv q M).right_inv x

/-- Helper for Lemma 15.67.15: after localizing the global base-change factor of `overBaseTest`,
the right tensor factor becomes the prime-local test module over `A_(q ∩ A)`. -/
noncomputable def localized_over_base_factor_iso
    (q : PrimeSpectrum B) (M : ModuleCat A) :
    let Ap := Localization.AtPrime (q.asIdeal.under A)
    let Bq := Localization.AtPrime q.asIdeal
    let sigma := Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
    (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
      ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A B)).obj
        ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M))) ≅
      ((CategoryTheory.derivedTensorWithAlgebra sigma).obj
        ((DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj
          (ModuleCat.of Ap
            (LocalizedModule.AtPrime (q.asIdeal.under A) M)))) := by
  let Ap := Localization.AtPrime (q.asIdeal.under A)
  let Bq := Localization.AtPrime q.asIdeal
  let sigma : Ap →+* Bq :=
    Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
  letI : Module.Flat B Bq :=
    IsLocalization.flat Bq q.asIdeal.primeCompl
  letI : Module.Flat A Ap :=
    IsLocalization.flat Ap (q.asIdeal.under A).primeCompl
  let singleM :=
    (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M
  let eLocal :
      (DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj
          ((ModuleCat.extendScalars (algebraMap A Ap)).obj M) ≅
        (DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj
          (ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M)) :=
    (DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).mapIso
      (extendScalars_to_localizedModule_iso (A := A) (B := B) q M)
  -- Route correction: compare the localized right factor by first replacing exact localization
  -- with flat derived scalar extension, then reassociate `A → B → B_q` to
  -- `A → A_(q ∩ A) → B_q`, and finally collapse `A → A_(q ∩ A)` on `M[0]`.
  calc
    (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
        ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A B)).obj singleM)) ≅
      ((CategoryTheory.derivedTensorWithAlgebra (algebraMap B Bq)).obj
        ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A B)).obj singleM)) :=
      (extendScalars_mapDerivedCategory_iso_of_flat
        (R := B) (R' := Bq)).app _
    _ ≅ (CategoryTheory.derivedTensorWithAlgebra (algebraMap A Bq)).obj singleM :=
      (derivedTensorWithAlgebraCompIso
        (algebraMap A B)
        (algebraMap B Bq)
        (algebraMap A Bq)
        (by
          ext x
          simpa [RingHom.comp_apply] using
            congrArg (fun f : A →+* Bq => f x)
              (IsScalarTower.algebraMap_eq A B Bq))).app singleM
    _ ≅
        ((CategoryTheory.derivedTensorWithAlgebra (algebraMap A Ap) ⋙
          CategoryTheory.derivedTensorWithAlgebra sigma).obj singleM) :=
      ((derivedTensorWithAlgebraCompIso
        (algebraMap A Ap)
        sigma
        (algebraMap A Bq)
        (localizationAtPrime_over_base_comp_eq (A := A) (B := B) q)).symm.app singleM)
    _ ≅
        ((CategoryTheory.derivedTensorWithAlgebra sigma).obj
          ((DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj
            ((ModuleCat.extendScalars (algebraMap A Ap)).obj M))) :=
      (CategoryTheory.derivedTensorWithAlgebra sigma).mapIso
        (derivedTensorWithAlgebra_single_iso_of_flat
          (R := A) (R' := Ap) M)
    _ ≅
        ((CategoryTheory.derivedTensorWithAlgebra sigma).obj
          ((DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj
            (ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M)))) :=
      (CategoryTheory.derivedTensorWithAlgebra sigma).mapIso eLocal

/-- Helper for Lemma 15.67.15: specializing the raw localization/base-change comparison to a
test module already defined over `A_(q ∩ A)` identifies the localized global tensor factor with
the direct scalar extension of that local test module. -/
noncomputable def over_base_tensor_single_localized_module_iso
    (q : PrimeSpectrum B)
    (N : ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :
    ModuleCat.of (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal
        ((ModuleCat.extendScalars (algebraMap A B)).obj
          ((ModuleCat.restrictScalars
            (algebraMap A (Localization.AtPrime (q.asIdeal.under A)))).obj N))) ≅
      (ModuleCat.extendScalars
        (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)).obj N := by
  let Ap := Localization.AtPrime (q.asIdeal.under A)
  let Bq := Localization.AtPrime q.asIdeal
  let M : ModuleCat A :=
    (ModuleCat.restrictScalars (algebraMap A Ap)).obj N
  let eFactor :
      ModuleCat.of Bq
          (LocalizedModule.AtPrime q.asIdeal ((ModuleCat.extendScalars (algebraMap A B)).obj M)) ≅
        ModuleCat.of Bq
          (TensorProduct Ap Bq (LocalizedModule.AtPrime (q.asIdeal.under A) M)) :=
    localized_global_base_factor_iso q M
  let eTensor :
      ModuleCat.of Bq
          (TensorProduct Ap Bq (LocalizedModule.AtPrime (q.asIdeal.under A) M)) ≅
        (ModuleCat.extendScalars (algebraMap Ap Bq)).obj
          (ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M)) :=
    ((extendScalars_tensor_linearEquiv
      (A := Ap) (B := Bq)
      (ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M))).toModuleIso).symm
  let eLocal :
      (ModuleCat.extendScalars (algebraMap Ap Bq)).obj
          (ModuleCat.of Ap (LocalizedModule.AtPrime (q.asIdeal.under A) M)) ≅
        (ModuleCat.extendScalars (algebraMap Ap Bq)).obj N :=
    (ModuleCat.extendScalars (algebraMap Ap Bq)).mapIso
      (localized_restrictScalars_iso (q.asIdeal.under A).primeCompl N)
  -- First rewrite the localized global tensor factor into the raw `B_q ⊗[A_p] -` form, then
  -- identify that tensor with scalar extension and finally collapse the localized `N|_A` term.
  simpa [Ap, Bq, M] using eFactor ≪≫ eTensor ≪≫ eLocal

/-- Helper for Lemma 15.67.15: the previous module comparison upgraded to the corresponding
degree-zero complexes after exact localization at `q`. -/
noncomputable def over_base_tensor_single_localized_complex_iso
    (q : PrimeSpectrum B)
    (N : ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :
    (((ModuleCat.extendScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj
          ((ModuleCat.restrictScalars
            (algebraMap A (Localization.AtPrime (q.asIdeal.under A)))).obj N)))) ≅
      ((DerivedCategory.singleFunctor
        (ModuleCat (Localization.AtPrime q.asIdeal)) (0 : ℤ)).obj
        ((ModuleCat.extendScalars
          (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)).obj N)) :=
  let Bq := Localization.AtPrime q.asIdeal
  let M : ModuleCat B :=
    (ModuleCat.extendScalars (algebraMap A B)).obj
      ((ModuleCat.restrictScalars
        (algebraMap A (Localization.AtPrime (q.asIdeal.under A)))).obj N)
  let eLocal :
      (ModuleCat.extendScalars (algebraMap B Bq)).obj M ≅
        ModuleCat.of Bq (LocalizedModule.AtPrime q.asIdeal M) :=
    extendScalars_to_localizedModule_iso (A := B) (B := B) q M
  -- Exact localization computes on the degree-zero complex. After rewriting the localized module
  -- as the honest localized carrier, the specialized global/local tensor comparison applies.
  extendScalars_single_iso_atPrime q _ ≪≫
    (DerivedCategory.singleFunctor
      (ModuleCat (Localization.AtPrime q.asIdeal)) (0 : ℤ)).mapIso
        (eLocal ≪≫ over_base_tensor_single_localized_module_iso q N)

/-- Helper for Lemma 15.67.15: mapping the global test-object comparison through homology gives
the canonical bridge from the `A`-test homology to the restricted homology of `overBaseTest`. -/
noncomputable def over_base_test_restrict_iso
    (K : DModB) (M : ModuleCat A) :
    ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj K) ⊗[A]^L
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) ≅
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
        (overBaseTest (A := A) (B := B) K M)) := by
  -- Route correction: isolate the source-faithful object-level change-of-rings comparison first,
  -- so the homology-level lemma below only applies functoriality of homology and the canonical
  -- restriction-of-scalars/homology comparison.
  -- TODO: normalize both sides to explicit `DerivedCategory.Q.obj` tensor models, apply
  -- `DerivedCategory.Q.mapIso (restrictScalars_tensorObj_extendScalars_iso ...)` to the chosen
  -- model of the right test factor, and then fold back to `overBaseTest`.
  sorry

/-- Helper for Lemma 15.67.15: mapping the global test-object comparison through homology gives
the canonical bridge from the `A`-test homology to the restricted homology of `overBaseTest`. -/
noncomputable def over_base_test_homology_iso
    (K : DModB) (M : ModuleCat A) (i : ℤ) :
    (HA i).obj
        ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj K) ⊗[A]^L
          ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        ((HB i).obj (overBaseTest (A := A) (B := B) K M)) := by
  -- Route correction: once the object-level comparison is isolated, the homology bridge is only
  -- functoriality of `(HA i)` followed by the canonical comparison for restricting homology.
  exact
    (HA i).mapIso (over_base_test_restrict_iso (A := A) (B := B) K M) ≪≫
      restrictScalars_homology_iso (A := A) (B := B)
        (overBaseTest (A := A) (B := B) K M) i

/-- Helper for Lemma 15.67.15: after exact localization at `q`, the honest global `B`-linear test
object becomes the honest `B_q`-linear local test object attached to `N`. -/
noncomputable def localized_over_base_test_factorized_iso
    (K : DModB) (q : PrimeSpectrum B)
    (N : ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :
    let Ap := Localization.AtPrime (q.asIdeal.under A)
    let Bq := Localization.AtPrime q.asIdeal
    let sigma : Ap →+* Bq :=
      Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
    (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
      (overBaseTest (A := A) (B := B) K
        ((ModuleCat.restrictScalars (algebraMap A Ap)).obj N))) ≅
      overBaseTest (A := Ap) (B := Bq)
        (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj K) N :=
  -- TODO: first commute exact localization past the tensor product on the explicit `Q.obj`
  -- model of `overBaseTest`, then replace the localized right factor by
  -- `localized_over_base_factor_iso`, and finally rewrite back to the local honest test object.
  sorry

/-- Helper for Lemma 15.67.15: the local test homology over `A_(q ∩ A)` identifies with the
restricted homology of the localized global test object. -/
noncomputable def localized_over_base_test_homology_iso
    (K : DModB) (q : PrimeSpectrum B)
    (N : ModuleCat (Localization.AtPrime (q.asIdeal.under A))) (i : ℤ) :
    let Ap := Localization.AtPrime (q.asIdeal.under A)
    let Bq := Localization.AtPrime q.asIdeal
    let sigma : Ap →+* Bq :=
      Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
    (DerivedCategory.homologyFunctor (ModuleCat Ap) i).obj
        ((((ModuleCat.restrictScalars sigma).mapDerivedCategory).obj
            (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj K)) ⊗[Ap]^L
          ((DerivedCategory.singleFunctor (ModuleCat Ap) (0 : ℤ)).obj N)) ≅
      (ModuleCat.restrictScalars sigma).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Bq) i).obj
          (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
            (overBaseTest (A := A) (B := B) K
              ((ModuleCat.restrictScalars (algebraMap A Ap)).obj N)))) := by
  let Ap := Localization.AtPrime (q.asIdeal.under A)
  let Bq := Localization.AtPrime q.asIdeal
  let sigma : Ap →+* Bq :=
    Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
  let eObj :
      (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
        (overBaseTest (A := A) (B := B) K
          ((ModuleCat.restrictScalars (algebraMap A Ap)).obj N))) ≅
        overBaseTest (A := Ap) (B := Bq)
          (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj K) N :=
    localized_over_base_test_factorized_iso (A := A) (B := B) K q N
  -- First rewrite the localized honest global test object into the honest local one, then apply
  -- the already isolated global-over-base homology bridge over `A_(q ∩ A) → B_q`.
  simpa [Ap, Bq, sigma] using
    over_base_test_homology_iso
      (A := Ap) (B := Bq)
      (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj K) N i ≪≫
      (ModuleCat.restrictScalars sigma).mapIso
        ((DerivedCategory.homologyFunctor (ModuleCat Bq) i).mapIso eObj.symm)

/-- Helper for Lemma 15.67.15: maximal-local tor-amplitude over the contracted local base kills
the corresponding homology of the honest global `B`-linear test object. -/
lemma isZero_over_base_test_homology_of_localized_maximals
    (K : DModB)
    (hmax :
      ∀ m : MaximalSpectrum B,
        HasTorAmplitudeIn
          (((ModuleCat.restrictScalars
              (Localization.localRingHom (m.asIdeal.under A) m.asIdeal (algebraMap A B) rfl)).mapDerivedCategory).obj
            (((ModuleCat.extendScalars
                (algebraMap B (Localization.AtPrime m.asIdeal))).mapDerivedCategory).obj K))
          a b)
    (M : ModuleCat A) (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((HB i).obj (overBaseTest (A := A) (B := B) K M)) := by
  -- TODO: localize the honest global test object, transport the maximal-local tor-amplitude
  -- hypothesis through `localized_over_base_test_homology_iso`, and then reflect zero from every
  -- maximal localization using `isZero_homology_of_localized_maximals`.
  sorry

-- Proof sketch: the implication from the global statement to the prime-local and maximal-local
-- statements comes from exactness of derived localization and restriction of scalars. For the
-- converse, test the homology modules of `K ⊗_A^L M` at maximal ideals of `B`; by the localized
-- hypotheses these stalks vanish outside `[a, b]`, so Lemma `10.23.1` forces the global homology
-- modules to vanish.
/-- Lemma 15.67.15: for a derived `B`-complex `K`, the following are equivalent: `K`, viewed over
`A`, has tor-amplitude in `[a, b]`; for every prime `q` of `B`, the localization `K_q` has
tor-amplitude in `[a, b]` over `A_(q ∩ A)`; and it is enough to check this only at maximal ideals
of `B`. -/
@[stacks 0B67]
theorem hasTorAmplitudeIn_over_base_tfae_of_localizations (K : DModB) :
    let restrictedK : DerivedCategory (ModuleCat A) :=
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K
    let localizedOverBase :
        (q : PrimeSpectrum B) →
          DerivedCategory (ModuleCat (Localization.AtPrime (q.asIdeal.under A))) :=
      fun q ↦
        (ModuleCat.restrictScalars
            (Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl)).mapDerivedCategory.obj
          ((ModuleCat.extendScalars
              (algebraMap B (Localization.AtPrime q.asIdeal))).mapDerivedCategory.obj K)
    List.TFAE [
      HasTorAmplitudeIn restrictedK a b,
      ∀ q : PrimeSpectrum B, HasTorAmplitudeIn (localizedOverBase q) a b,
      ∀ m : MaximalSpectrum B,
        HasTorAmplitudeIn (localizedOverBase m.toPrimeSpectrum) a b
    ] := by
  dsimp
  tfae_have 1 → 2 := by
    intro hrestricted q
    let Ap := Localization.AtPrime (q.asIdeal.under A)
    let Bq := Localization.AtPrime q.asIdeal
    let sigma : Ap →+* Bq :=
      Localization.localRingHom (q.asIdeal.under A) q.asIdeal (algebraMap A B) rfl
    intro N i hi
    let underlyingN : ModuleCat A :=
      (ModuleCat.restrictScalars (algebraMap A Ap)).obj N
    have hGlobalTest :
        IsZero
          ((HA i).obj
            ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj K) ⊗[A]^L
              ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj underlyingN))) :=
      hrestricted underlyingN i hi
    have hOverBaseRestricted :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap A B)).obj
            ((HB i).obj (overBaseTest (A := A) (B := B) K underlyingN))) := by
      -- Move from the `A`-test homology to the restricted homology of the honest `B`-test
      -- object.
      exact (over_base_test_homology_iso (A := A) (B := B) K underlyingN i).isZero_iff.1
        hGlobalTest
    have hOverBase :
        IsZero ((HB i).obj (overBaseTest (A := A) (B := B) K underlyingN)) :=
      isZero_of_restrictScalars_obj
        (A := A) (B := B)
        ((HB i).obj (overBaseTest (A := A) (B := B) K underlyingN))
        hOverBaseRestricted
    have hLocalized :
        IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat Bq) i).obj
            (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
              (overBaseTest (A := A) (B := B) K underlyingN))) :=
      isZero_homology_localized_atPrime_of_isZero
        q
        (overBaseTest (A := A) (B := B) K underlyingN) i
        hOverBase
    have hLocalizedRestricted :
        IsZero
          ((ModuleCat.restrictScalars sigma).obj
            ((DerivedCategory.homologyFunctor (ModuleCat Bq) i).obj
              (((ModuleCat.extendScalars (algebraMap B Bq)).mapDerivedCategory).obj
                (overBaseTest (A := A) (B := B) K underlyingN)))) := by
      -- Restrict the localized homology along `A_(q ∩ A) → B_q` so it matches the local test
      -- comparison.
      exact (ModuleCat.restrictScalars sigma).map_isZero hLocalized
    -- The packaged local homology bridge now transports the vanishing statement to the local
    -- test object over `A_(q ∩ A)`.
    simpa [Ap, Bq, sigma, underlyingN] using
      (localized_over_base_test_homology_iso (A := A) (B := B) K q N i).isZero_iff.2
        hLocalizedRestricted
  tfae_have 2 → 3 := by
    intro hprime m
    -- Specialize the prime-local statement to maximal ideals.
    exact hprime m.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro hmax
    intro M i hi
    have hOverBase :=
      -- The source proof first shows the honest global `B`-linear test homology vanishes by
      -- checking all maximal localizations over the contracted base.
      isZero_over_base_test_homology_of_localized_maximals
        (A := A) (B := B) (a := a) (b := b) K hmax M i hi
    have hOverBaseRestricted :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap A B)).obj
            ((HB i).obj (overBaseTest K M))) := by
      -- Restrict the vanishing `B`-module so it matches the codomain of the test-homology
      -- comparison.
      exact (ModuleCat.restrictScalars (algebraMap A B)).map_isZero hOverBase
    -- Move the vanishing statement back across the global over-base homology bridge.
    exact (over_base_test_homology_iso (A := A) (B := B) K M i).isZero_iff.2
      hOverBaseRestricted
  tfae_finish

end

end CategoryTheory

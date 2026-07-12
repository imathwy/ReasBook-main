import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_65_15
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct DerivedTensorProduct DerivedTensorWithAlgebra
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "KModA" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "KModB" => HomotopyCategory (ModuleCat B) (up ℤ)
local notation "HR" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "HA" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "HB" => DerivedCategory.homologyFunctor (ModuleCat B)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QhB" => (DerivedCategory.Qh : KModB ⥤ DModB)
local notation "single₀R" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "single₀A" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)
local notation "single₀B" => DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)

/-- Helper for Lemma 15.67.18: extension of scalars is additive on module categories. -/
local instance extendScalars_additive_local
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap S T)).left_adjoint_additive

/-- Helper for Lemma 15.67.18: flat scalar extension preserves finite limits on module
categories. -/
local instance extendScalars_preservesFiniteLimits
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T] :
    Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap S T)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (show Module.Flat S T from inferInstance))

/- Domain-style sampling for Lemma 15.67.18:
- primary domain: relative tor-amplitude in derived categories under faithfully flat base change
  of the ambient algebra;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `(ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement is an `iff` about the canonical owner
  `HasTorAmplitudeIn` after applying the two exact derived restriction functors, so the theorem
  should speak directly in that owner language instead of rebuilding a local wrapper around the
  restricted complexes;
- primitive vs. derived:
  primitive data are the scalar tower `R → A → B`, the faithfully flat hypothesis on `A → B`, and
  the derived `A`-complex `K`;
  the restricted objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))` are
  derived API obtained by viewing the same source-facing complex over `R` before and after base
  change.

Source/core/bridge triage:
- `source-facing`: faithful-flat invariance of tor-amplitude over the base ring `R`;
- `core/canonical`: `HasTorAmplitudeIn` on derived module categories;
- `bridge/view`: the exact derived restriction objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))`,
  together with the derived base-change object `K ⊗[A]^L[B]`. -/

/-- Helper for Lemma 15.67.18: the honest test object over an intermediate `R`-algebra `S`
used to test tor-amplitude over the base ring `R`. -/
noncomputable def overBaseTest
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DerivedCategory (ModuleCat S)) (M : ModuleCat R) :
    DerivedCategory (ModuleCat S) :=
  K ⊗[S]^L
    ((derivedTensorWithAlgebra (algebraMap R S)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))

/-- Helper for Lemma 15.67.18: if the restriction of scalars of a module is zero, then the
original module is zero. -/
lemma isZero_of_restrictScalars_obj
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (M : ModuleCat T)
    (hM : IsZero ((ModuleCat.restrictScalars (algebraMap S T)).obj M)) :
    IsZero M := by
  -- Restriction of scalars does not change the underlying additive group, so zero objects reflect
  -- back to the original module.
  letI : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap S T)).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars (algebraMap S T)).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.67.18: the `R`-linear tor-amplitude test for the restricted complex
agrees with the restricted homology of the honest test object over an intermediate `R`-algebra
`S`. -/
-- Route correction: the source proof compares homology after choosing a chain model of `K`; the
-- old object-level restriction-side comparison overshot that route and led to transport failures.
-- TODO(Lemma 15.67.18): choose the source-faithful `Q.objPreimage`/tensor model for `K`,
-- compare it with `restrictScalars_tensorObj_extendScalars_iso`, and only then pass to homology
-- and `restrictScalars_homology_iso`.
noncomputable def over_base_test_homology_iso
    {S : Type u} [CommRing S] [Algebra R S]
    (K : DerivedCategory (ModuleCat S)) (M : ModuleCat R) (i : ℤ) :
    (HR i).obj
        ((((ModuleCat.restrictScalars (algebraMap R S)).mapDerivedCategory).obj K) ⊗[R]^L
          ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) ≅
      (ModuleCat.restrictScalars (algebraMap R S)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
          (overBaseTest (R := R) (S := S) K M)) := sorry

/-- Helper for Lemma 15.67.18: restricting scalars commutes with homology on derived module
categories. -/
noncomputable def restrictScalars_homology_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (L : DerivedCategory (ModuleCat T)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars (algebraMap S T)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let eT :
      (DerivedCategory.homologyFunctor (ModuleCat T) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K
  -- Pass to a chosen complex representative and compare homology before and after restriction.
  (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
      (((((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T)) ≪≫
      (ModuleCat.restrictScalars (algebraMap S T)).mapIso eT.symm

/-- Helper for Lemma 15.67.18: exact scalar extension sends a degree-zero complex to the
degree-zero complex of the scalar-extended module. -/
noncomputable def extendScalars_single_iso
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T] [Module.Flat S T]
    (M : ModuleCat S) :
    (((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor (ModuleCat S) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat T) (0 : ℤ)).obj
        ((ModuleCat.extendScalars (algebraMap S T)).obj M) := by
  -- Exact flat scalar extension can be computed on the cochain-level single complex.
  exact
    ((((ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat S) (0 : ℤ)).app M)) ≪≫
      (ModuleCat.extendScalars (algebraMap S T)).mapDerivedCategoryFactors.app
        ((CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M) ≪≫
      DerivedCategory.Q.mapIso
        ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.extendScalars (algebraMap S T))
          (0 : ℤ)).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat T) (0 : ℤ)).app
        ((ModuleCat.extendScalars (algebraMap S T)).obj M)).symm)

/-- Helper for Lemma 15.67.18: exact flat scalar extension of the right over-base test factor
agrees with direct derived scalar extension from `R` to `B`. -/
noncomputable def over_base_factor_baseChange_iso
    [Module.Flat A B] (M : ModuleCat R) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory).obj
      ((derivedTensorWithAlgebra (algebraMap R A)).obj (Functor.obj single₀R M))) ≅
      ((derivedTensorWithAlgebra (algebraMap R B)).obj (Functor.obj single₀R M)) := by
  -- First identify exact scalar extension over `A` with the owner `derivedTensorWithAlgebra`,
  -- then collapse the iterated-vs-direct derived base change.
  exact
    ((extendScalars_mapDerivedCategory_iso_of_flat (R := A) (R' := B)).app
      ((derivedTensorWithAlgebra (algebraMap R A)).obj (Functor.obj single₀R M))) ≪≫
      ((derivedTensorWithAlgebraCompIso
        (algebraMap R A) (algebraMap A B) (algebraMap R B)
        (by
          ext x
          simpa [RingHom.comp_apply, IsScalarTower.algebraMap_eq R A B])).app
        (Functor.obj single₀R M))

/-- Helper for Lemma 15.67.18: exact flat scalar extension carries the honest `A`-linear test
object to the honest `B`-linear test object of the base-changed complex. -/
noncomputable def over_base_test_baseChange_iso
    [Module.Flat A B] (K : DModA) (M : ModuleCat R) :
    (((ModuleCat.extendScalars (algebraMap A B)).mapDerivedCategory).obj
      (overBaseTest (R := R) (S := A) K M)) ≅
      overBaseTest (R := R) (S := B) (K ⊗[A]^L[B]) M := by
  -- TODO(Lemma 15.67.18): after installing the monoidal structure on exact scalar extension,
  -- rewrite the right test factor by `over_base_factor_baseChange_iso`, use `Functor.Monoidal.μIso`,
  -- and then return to the honest `overBaseTest` owner.
  sorry

/-- Helper for Lemma 15.67.18: after flat base change, the homology of the honest `A`-linear test
object identifies with the homology of the honest `B`-linear test object. -/
noncomputable def over_base_test_homology_baseChange_iso
    [Module.Flat A B] (K : DModA) (M : ModuleCat R) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        ((HA i).obj (overBaseTest (R := R) (S := A) K M)) ≅
      (HB i).obj (overBaseTest (R := R) (S := B) (K ⊗[A]^L[B]) M) := by
  -- Proof comment: once the honest test object itself is compared across `A → B`, the homology
  -- comparison is the formal composition of flat homology base change with that object isomorphism.
  exact
    (extendScalars_homology_iso_of_flat (R := A) (R' := B)
      (overBaseTest (R := R) (S := A) K M) i) ≪≫
      (HB i).mapIso (over_base_test_baseChange_iso (R := R) (A := A) (B := B) K M)

/-- Helper for Lemma 15.67.18: faithful flatness along `A → B` reflects and preserves the
vanishing of the homology of the honest over-base test object. -/
lemma isZero_over_base_test_homology_iff_of_faithfullyFlat
    (hff : RingHom.FaithfullyFlat (algebraMap A B))
    (K : DModA) (M : ModuleCat R) (i : ℤ) :
    IsZero ((HA i).obj (overBaseTest K M)) ↔
      IsZero ((HB i).obj (overBaseTest (K ⊗[A]^L[B]) M)) := by
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hff.flat
  constructor
  · intro hA
    -- Proof comment: preserve zero under exact scalar extension and transport it to the honest
    -- `B`-test homology through the flat base-change isomorphism.
    have hA_ext :
        IsZero
          ((ModuleCat.extendScalars (algebraMap A B)).obj
            ((HA i).obj (overBaseTest (R := R) (S := A) K M))) :=
      (ModuleCat.extendScalars (algebraMap A B)).map_isZero hA
    exact
      (over_base_test_homology_baseChange_iso (R := R) (A := A) (B := B) K M i).isZero_iff.1
        hA_ext
  · intro hB
    -- Proof comment: transport zero back to exact scalar extension of the `A`-test homology, then
    -- reflect it along faithful flatness.
    have hA_ext :
        IsZero
          ((ModuleCat.extendScalars (algebraMap A B)).obj
            ((HA i).obj (overBaseTest (R := R) (S := A) K M))) :=
      (over_base_test_homology_baseChange_iso (R := R) (A := A) (B := B) K M i).isZero_iff.2 hB
    exact
      isZero_of_extendScalars_of_faithfullyFlat
        ((HA i).obj (overBaseTest (R := R) (S := A) K M))
        hff
        hA_ext

/-- Lemma 15.67.18: for ring maps `R → A → B` with `A → B` faithfully flat, an object `K` of
`D(A)` has tor-amplitude in `[a, b]` over `R` if and only if its derived base change
`K \otimes_A^{\mathbf L} B`, regarded as an object of `D(R)`, has tor-amplitude in `[a, b]`
over `R`. -/
@[stacks 0DJF]
theorem hasTorAmplitudeIn_restrictScalars_iff_of_faithfullyFlat_baseChange
    (K : DModA) (a b : ℤ)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).obj K) a b ↔
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory).obj (K ⊗[A]^L[B]))
        a b := by
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hff.flat
  constructor
  · intro hK
    intro M i hi
    -- Proof comment: rewrite the `R`-linear tor-amplitude test for `K` as the honest
    -- `A`-linear test object, move vanishing across faithful-flat base change, and then rewrite
    -- back to the `R`-linear test for `K ⊗[A]^L[B]`.
    have hA_restrict := (over_base_test_homology_iso K M i).isZero_iff.1 (hK M i hi)
    have hA :=
      isZero_of_restrictScalars_obj
        (S := R) (T := A)
        ((HA i).obj (overBaseTest K M))
        hA_restrict
    have hB :=
      (isZero_over_base_test_homology_iff_of_faithfullyFlat
        (R := R) (A := A) (B := B) hff K M i).1 hA
    have hB_restrict := (ModuleCat.restrictScalars (algebraMap R B)).map_isZero hB
    exact
      (over_base_test_homology_iso (K ⊗[A]^L[B]) M i).isZero_iff.2 hB_restrict
  · intro hKB
    intro M i hi
    -- Proof comment: the reverse direction follows from the same test-object comparison, using
    -- faithful flatness to reflect the vanishing of the `A`-test homology from the `B`-test
    -- homology.
    have hB_restrict := (over_base_test_homology_iso (K ⊗[A]^L[B]) M i).isZero_iff.1 (hKB M i hi)
    have hB :=
      isZero_of_restrictScalars_obj
        (S := R) (T := B)
        ((HB i).obj (overBaseTest (K ⊗[A]^L[B]) M))
        hB_restrict
    have hA :=
      (isZero_over_base_test_homology_iff_of_faithfullyFlat
        (R := R) (A := A) (B := B) hff K M i).2 hB
    have hA_restrict := (ModuleCat.restrictScalars (algebraMap R A)).map_isZero hA
    exact
      (over_base_test_homology_iso K M i).isZero_iff.2 hA_restrict

end

end CategoryTheory

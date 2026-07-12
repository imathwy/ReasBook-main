import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_67_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped DerivedTensorProduct
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')
local notation "KModR" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "KModR'" => HomotopyCategory (ModuleCat R') (up ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "H'" => DerivedCategory.homologyFunctor (ModuleCat R')
local notation "QhR" => (DerivedCategory.Qh : KModR ⥤ DModR)
local notation "QhR'" => (DerivedCategory.Qh : KModR' ⥤ DModR')
local notation "QisR" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
local notation "single₀" => (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ) : ModuleCat R ⥤ DModR)
local notation "single₀'" =>
  (DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ) : ModuleCat R' ⥤ DModR')

/-- Helper for Lemma 15.67.17: faithful-flat base change detects tor-amplitude after restricting
scalars along the base ring. -/
theorem hasTorAmplitudeIn_restrictScalars_iff_of_faithfullyFlat_baseChange
    [Algebra R R']
    (K : DModR) (a b : ℤ)
    (hff : RingHom.FaithfullyFlat (algebraMap R R')) :
    HasTorAmplitudeIn K a b ↔
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory).obj
          ((derivedTensorWithAlgebra (algebraMap R R')).obj K)) a b := by
  sorry

/-- Lemma 15.67.17: if the derived base change of a derived `R`-complex `K` along a faithfully
flat ring map `R → R'` has tor-amplitude in `[a, b]`, then `K` already has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR) (a b : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : HasTorAmplitudeIn ((derivedTensorWithAlgebra f).obj K) a b) :
    HasTorAmplitudeIn K a b := by
  letI : Algebra R R' := f.toAlgebra
  letI : Module.Flat R R' := hff.flat
  have hK' : HasTorAmplitudeIn ((derivedTensorWithAlgebra (algebraMap R R')).obj K) a b := by
    simpa using hK
  have hRestrict :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory).obj
          ((derivedTensorWithAlgebra (algebraMap R R')).obj K)) a b := by
    -- First forget the `R'`-linear structure on the base-changed object.
    simpa using
      (hasTorAmplitudeIn_restrictScalars_of_flat
        (A := R) (B := R') (a := a) (b := b)
        ((derivedTensorWithAlgebra (algebraMap R R')).obj K)
        hK')
  have hiff :
      HasTorAmplitudeIn K a b ↔
        HasTorAmplitudeIn
          (((ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory).obj
            ((derivedTensorWithAlgebra (algebraMap R R')).obj K)) a b := by
    -- Then apply the faithful-flat base-change equivalence over the base ring `R`.
    simpa using
      (hasTorAmplitudeIn_restrictScalars_iff_of_faithfullyFlat_baseChange
        (R := R) (R' := R') K a b (by simpa using hff))
  exact hiff.2 hRestrict

end

end CategoryTheory

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.QuasiAffine
import StacksProject_2024.stacks_project.Chap28.Lemma_28_29_6
import StacksProject_2024.stacks_project.Chap31.Definition_31_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open Modules

-- Semantic recall: `lean_leansearch` found the mathlib owner `Scheme.IsQuasiAffine`; local
-- precedent expands ampleness through `TensorPowerSectionAffineNonvanishingAt` when the packaged
-- `Scheme.Modules.IsAmple` owner is not dependency-closed in item-file checking, and Chapter 31
-- uses `IsEffectiveCartierDivisor` for effective Cartier divisor closed immersions.

variable {X Z Z' : Scheme}
variable [MonoidalCategory X.Modules]
variable [SymmetricCategory X.Modules]
variable [MonoidalClosed X.Modules]

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/-- A dependency-closed spelling of “`X` has an ample invertible sheaf”: there is an invertible
module `L`, `X` is quasi-compact, and every point lies in an affine nonvanishing open of a
positive tensor power of `L`. -/
abbrev HasAmpleInvertibleSheaf (X : Scheme) [MonoidalCategory X.Modules] : Prop :=
  letI : MonoidalCategory (SheafOfModules X.toRingedSpace.ringCatSheaf) :=
    inferInstanceAs (MonoidalCategory X.Modules)
  ∃ L : X.Modules,
    Functor.IsEquivalence (tensorRight L) ∧
      IsCompact (Set.univ : Set X) ∧
        ∀ x : X, ∃ n : ℕ+,
          ∃ s : Γ(RingedSpace.tensorPowerSheaf L n, ⊤),
            ∃ U : X.Opens, TensorPowerSectionAffineNonvanishingAt L n s U x

/-- The ideal sheaf `\mathcal I_D` of an effective Cartier divisor closed immersion
`D ⟶ X`, viewed as an `\mathcal O_X`-module. -/
noncomputable abbrev effectiveCartierDivisorIdealSheaf (i : Z ⟶ X) : ModX :=
  RingedSpace.closedImmersionIdealSheaf i.toShHom

/-- The sheaf `\mathcal O_X(D - D')`, written as
`\mathcal Hom_{\mathcal O_X}(\mathcal I_D, \mathcal O_X) \otimes \mathcal I_{D'}` for two
effective Cartier divisor closed immersions `D ⟶ X` and `D' ⟶ X`. -/
noncomputable abbrev effectiveCartierDivisorDifferenceModule
    (i : Z ⟶ X) (i' : Z' ⟶ X) : ModX :=
  ((ihom (effectiveCartierDivisorIdealSheaf i)).obj 𝒪X) ⊗ₘ
    effectiveCartierDivisorIdealSheaf i'

/-- A simultaneous presentation of an invertible module as
`\mathcal O_X(D - D')`, with both effective Cartier divisors avoiding a finite set. -/
@[stacks 0AYM]
structure EffectiveCartierDivisorDifferencePresentation
    (X : Scheme.{u}) [MonoidalCategory X.Modules] [SymmetricCategory X.Modules]
    [MonoidalClosed X.Modules] [MonoidalCategory X.toRingedSpace.Modules]
    (L : X.Modules) (E : Finset X) where
  /-- The numerator divisor scheme. -/
  left : Scheme.{u}
  /-- The denominator divisor scheme. -/
  right : Scheme.{u}
  /-- The numerator effective Cartier divisor closed immersion. -/
  leftMap : left ⟶ X
  /-- The denominator effective Cartier divisor closed immersion. -/
  rightMap : right ⟶ X
  /-- The numerator is an effective Cartier divisor. -/
  leftIsEffective : IsEffectiveCartierDivisor leftMap
  /-- The denominator is an effective Cartier divisor. -/
  rightIsEffective : IsEffectiveCartierDivisor rightMap
  /-- The finite set avoids the numerator divisor. -/
  leftAvoids : ∀ x : X, x ∈ E → x ∉ Set.range leftMap.base
  /-- The finite set avoids the denominator divisor. -/
  rightAvoids : ∀ x : X, x ∈ E → x ∉ Set.range rightMap.base
  /-- The given module is isomorphic to the divisor-difference module. -/
  moduleIso : Nonempty (L ≅ effectiveCartierDivisorDifferenceModule leftMap rightMap)

/-- A simultaneous presentation of an invertible module as `\mathcal O_X(D - D')` in which the
denominator effective Cartier divisor is empty. -/
@[stacks 0AYM]
structure EffectiveCartierDivisorDifferencePresentationWithEmptyDenominator
    (X : Scheme.{u}) [MonoidalCategory X.Modules] [SymmetricCategory X.Modules]
    [MonoidalClosed X.Modules] [MonoidalCategory X.toRingedSpace.Modules]
    (L : X.Modules) (E : Finset X)
    extends EffectiveCartierDivisorDifferencePresentation X L E where
  /-- The denominator divisor has empty support. -/
  denominatorEmpty : Set.range rightMap.base = (∅ : Set X)

/-- Lemma 31.15.12 (1): on a Noetherian scheme admitting an ample invertible sheaf, every
invertible `\mathcal O_X`-module is isomorphic to `\mathcal O_X(D - D')` for effective Cartier
divisors `D` and `D'`, and the two divisors may be chosen to avoid any prescribed finite subset
of `X`. -/
@[stacks 0AYM]
theorem exists_effectiveCartierDivisor_differenceModule_iso_of_isNoetherian_exists_isAmple
    {X : Scheme} [MonoidalCategory X.Modules] [SymmetricCategory X.Modules]
    [MonoidalClosed X.Modules] [MonoidalCategory X.toRingedSpace.Modules]
    [IsNoetherian X]
    (hample : HasAmpleInvertibleSheaf X)
    (L : X.Modules) [Functor.IsEquivalence (tensorRight L)] (E : Finset X) :
    Nonempty (EffectiveCartierDivisorDifferencePresentation X L E) := sorry

/-- Lemma 31.15.12 (2): in the quasi-affine case, the denominator effective Cartier divisor
`D'` in Lemma 31.15.12 (1) may be chosen empty, while still avoiding the prescribed finite
subset. -/
@[stacks 0AYM]
theorem exists_effectiveCartierDivisor_differenceModule_iso_with_empty_denominator_of_isQuasiAffine
    {X : Scheme} [MonoidalCategory X.Modules] [SymmetricCategory X.Modules]
    [MonoidalClosed X.Modules] [MonoidalCategory X.toRingedSpace.Modules]
    [IsNoetherian X] [X.IsQuasiAffine]
    (hample : HasAmpleInvertibleSheaf X)
    (L : X.Modules) [Functor.IsEquivalence (tensorRight L)] (E : Finset X) :
    Nonempty
      (EffectiveCartierDivisorDifferencePresentationWithEmptyDenominator X L E) := sorry

end AlgebraicGeometry.Scheme

import Mathlib
import StacksProject_2024.Chap20.Definition_20_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

variable [CategoryWithHomology (Modules Y)]
variable [HasCountableCoproducts (Modules Y)]
variable [MonoidalCategory (Modules Y)]
variable [MonoidalPreadditive (Modules Y)]
variable [HasColimits (Modules Y)]
variable [(curriedTensor (Modules Y)).Additive]
variable [∀ ℱ : Modules Y, ((curriedTensor (Modules Y)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules Y))]

-- Proof sketch: by Lemma `20.48.3`, choose a representative of `E` by a complex of flat
-- `\mathcal O_Y`-modules concentrated in degrees `[a,b]`. Pull it back termwise along `f`; the
-- pulled-back terms stay flat by Lemma `17.17.4`, and the degree support is unchanged. Apply
-- Lemma `20.48.3` again to identify this pulled-back flat complex with `Lf^*E`.
/-- Lemma 20.48.4: if `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `E` is an object of `D(\mathcal O_Y)` with tor-amplitude in `[a, b]`, then the
derived pullback `Lf^*E` has tor-amplitude in `[a, b]`. -/
theorem modulePullbackDerived_hasTorAmplitudeIn
    (f : X ⟶ Y) [(modulePullback f).Additive] (E : ModuleDerived Y) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((modulePullbackDerived f).obj E) a b := sorry

end

end AlgebraicGeometry.RingedSpace

import StacksProject_2024.Chap20.Definition_20_48_1_Core
import StacksProject_2024.Chap20.Lemma_20_27_1
import StacksProject_2024.Chap20.Tor_amplitude_on_opens_ringed_site
import StacksProject_2024.Chap21.Lemma_21_46_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 20.48.4:
- primary domain: tor-amplitude in derived categories of module sheaves under derived pullback;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `AlgebraicGeometry.RingedSpace.modulePullbackDerived`,
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `RingedSite.Hom.modulePullbackDerived_hasTorAmplitudeIn`,
  `RingedSite.ofCommRingSheaf`,
  `RingedSite.Hom.ModuleDerived`;
- best owner abstraction:
  `source-facing`: the ringed-space tor-amplitude statement for `Lf^*`;
  `core/canonical`: the ringed-site tor-amplitude predicate
    `SheafOfModules.RingedSite.HasTorAmplitudeIn` together with the bundled pullback-preservation
    theorem `RingedSite.Hom.modulePullbackDerived_hasTorAmplitudeIn`;
  `bridge/view`: the opens ringed site of a ringed space, used only to identify the Chapter 20
    owner `HasTorAmplitudeIn` and the ringed-space derived pullback `L(f)^*` with the Chapter 21
    ringed-site owners.
- primitive data: the morphism `f`, the derived object `E`, the interval bounds `a, b`, and the
  tor-amplitude witness on `E`;
- derived API: preservation of that tor-amplitude witness under derived pullback.

This file should keep the source-facing ringed-space owner in the public theorem statement. The
opens-ringed-site comparison remains only private bridge machinery for the proof.
-/

local notation "DModY" => DerivedCategory (Modules Y)

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules X))]

variable [CategoryWithHomology (Modules Y)]
variable [HasCountableCoproducts (Modules Y)]
variable [MonoidalCategory (Modules Y)]
variable [MonoidalPreadditive (Modules Y)]
variable [HasColimits (Modules Y)]
variable [(curriedTensor (Modules Y)).Additive]
variable [∀ ℱ : Modules Y, ((curriedTensor (Modules Y)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules Y))]
variable [MonoidalCategory (DerivedCategory (Modules Y))]

local instance opensRingedSiteDerived_monoidalCategoryStruct (Z : RingedSpace.{u})
    [MonoidalCategory (DerivedCategory (Modules Z))] :
    MonoidalCategoryStruct (RingedSite.Hom.ModuleDerived (opensRingedSite Z)) := by
  change MonoidalCategoryStruct (DerivedCategory (Modules Z))
  exact
    (inferInstance : MonoidalCategory (DerivedCategory (Modules Z))).toMonoidalCategoryStruct

/-- Lemma 20.48.4: if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a morphism of ringed
spaces and `E` is an object of `D(𝒪_Y)` with tor-amplitude in `[a, b]`, then the
derived pullback `L(f)^* E` has tor-amplitude in `[a, b]`. -/
@[stacks 09U8]
theorem modulePullbackDerived_hasTorAmplitudeIn
    (f : X ⟶ Y) [(f^*).Additive] (E : DModY) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((L(f)^*).obj E) a b := by
  rw [hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn]
  let E' : RingedSite.Hom.ModuleDerived (opensRingedSite Y) := E
  have hE' : SheafOfModules.RingedSite.HasTorAmplitudeIn E' a b :=
    (hasTorAmplitudeIn_iff_opensRingedSiteHasTorAmplitudeIn E' a b).1 <| by
      simpa [E'] using hE
  change SheafOfModules.RingedSite.HasTorAmplitudeIn
      ((RingedSite.Hom.modulePullbackDerived (opensRingedSiteHom f)).obj E') a b
  exact RingedSite.Hom.modulePullbackDerived_hasTorAmplitudeIn (opensRingedSiteHom f) E' a b hE'

end

end AlgebraicGeometry.RingedSpace

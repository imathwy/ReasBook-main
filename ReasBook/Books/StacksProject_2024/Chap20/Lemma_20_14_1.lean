import Mathlib
import StacksProject_2024.Chap20.«20_3_0_4»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(RingedSpace.Hom.pushforward f).Additive]
variable [(RingedSpace.Hom.pushforward (𝟙 X)).Additive]
variable [(RingedSpace.Hom.pushforward (𝟙 Y)).Additive]
variable [Functor.IsLocalization
  (mapBoundedBelowHomotopyToDerivedBelow (𝟭 (SheafOfModules ((RingedSpace.ringCatSheaf X)))))
  (boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X))))]
variable [Functor.HasRightDerivedFunctor
  (mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward f))
  (boundedBelowHomotopyQuasiIso (SheafOfModules ((RingedSpace.ringCatSheaf X))))]

local notation "ModX" => SheafOfModules ((RingedSpace.ringCatSheaf X))
local notation "ModY" => SheafOfModules ((RingedSpace.ringCatSheaf Y))
local notation "QX" => mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModX)
local notation "QY" => mapBoundedBelowHomotopyToDerivedBelow (𝟭 ModY)
local notation "pushfToDplus" => mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Hom.pushforward f)

/-- Lemma 20.14.1: a morphism of bounded-below complexes
`\mathcal G^\bullet \to f_*\mathcal F^\bullet` induces the canonical morphism
`\mathcal G^\bullet \to Rf_*(\mathcal F^\bullet)` in `D^+(Y)`. -/
noncomputable def ringedSpaceBoundedBelowDerivedPushforwardComparison
    {𝒢 : CochainComplex.Plus ModY}
    {ℱ : CochainComplex.Plus ModX}
    (φ : 𝒢 ⟶ ((RingedSpace.Hom.pushforward f).mapCochainComplexPlus.obj ℱ)) :
    (QY.obj (cochainComplexPlusToBoundedBelowHomotopy.obj 𝒢)) ⟶
      ((Functor.totalRightDerived
          pushfToDplus
          QX
          (boundedBelowHomotopyQuasiIso ModX)).obj
        (QX.obj (cochainComplexPlusToBoundedBelowHomotopy.obj ℱ))) :=
  QY.map (cochainComplexPlusToBoundedBelowHomotopy.map φ) ≫
    ((pushfToDplus.totalRightDerivedUnit
      QX
      (boundedBelowHomotopyQuasiIso ModX)).app
        (cochainComplexPlusToBoundedBelowHomotopy.obj ℱ))

-- Proof sketch: apply the functoriality of the bounded-below homotopy quotient `Q`, the
-- localization functor to `D^+`, and the derived pushforward functor to the commutative square
-- of complexes, then use naturality of the total right derived unit.
/-- The canonical comparison morphism to `Rf_*` is natural in the triple
`(\mathcal G^\bullet, \mathcal F^\bullet, \varphi)`. -/
theorem ringedSpaceBoundedBelowDerivedPushforwardComparison_natural
    {𝒢₁ 𝒢₂ : CochainComplex.Plus ModY}
    {ℱ₁ ℱ₂ : CochainComplex.Plus ModX}
    (φ₁ : 𝒢₁ ⟶ ((RingedSpace.Hom.pushforward f).mapCochainComplexPlus.obj ℱ₁))
    (φ₂ : 𝒢₂ ⟶ ((RingedSpace.Hom.pushforward f).mapCochainComplexPlus.obj ℱ₂))
    (α : 𝒢₁ ⟶ 𝒢₂)
    (β : ℱ₁ ⟶ ℱ₂)
    (hcomm :
      φ₁ ≫ (RingedSpace.Hom.pushforward f).mapCochainComplexPlus.map β =
        α ≫ φ₂) :
    QY.map (cochainComplexPlusToBoundedBelowHomotopy.map α) ≫
        ringedSpaceBoundedBelowDerivedPushforwardComparison f φ₂ =
      ringedSpaceBoundedBelowDerivedPushforwardComparison f φ₁ ≫
        ((Functor.totalRightDerived
            pushfToDplus
            QX
            (boundedBelowHomotopyQuasiIso ModX)).map
          (QX.map (cochainComplexPlusToBoundedBelowHomotopy.map β))) := sorry

end AlgebraicGeometry

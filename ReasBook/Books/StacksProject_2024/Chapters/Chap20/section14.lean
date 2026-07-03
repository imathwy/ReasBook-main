import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_14_1 (from Chap20) -/
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

/-! ### Remark_20_14_2 (from Chap20) -/
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (𝒢 : (RingedSpace.Modules Y)) (ℱ : (RingedSpace.Modules X))

local notation "singleX" => CochainComplex.single₀ (RingedSpace.Modules X)
local notation "singleY" => CochainComplex.single₀ (RingedSpace.Modules Y)
local notation "pushf" => (RingedSpace.Hom.pushforward f).mapHomologicalComplex (up ℤ)
local notation "ΓY" => (moduleGlobalSectionsFunctor Y).mapHomologicalComplex (up ℤ)
local notation "ModΓY" => ModuleCat (globalSectionsRing Y)
local notation "QΓY" =>
  (DerivedCategory.Q : CochainComplex ModΓY ℤ ⥤ DerivedCategory ModΓY)

/-- Remark 20.14.2: after choosing an injective resolution `\mathcal F \to \mathcal I^\bullet`,
an injective resolution `\mathcal G \to \mathcal J^\bullet`, a complex of injectives
`(\mathcal J')^\bullet` quasi-isomorphic to `f_*\mathcal I^\bullet`, and a lift
`\beta : \mathcal J^\bullet \to (\mathcal J')^\bullet`, the morphism
`R\Gamma(Y, \mathcal G) \to R\Gamma(X, \mathcal F)` is represented on the chosen global-sections
complexes by the horizontal map induced by `\beta`, followed by the inverse of the vertical
quasi-isomorphism. -/
abbrev moduleDerivedGlobalSectionsMapOnChosenResolutions
    (I : CochainComplex.InjectiveResolution ((singleX).obj ℱ))
    (J : CochainComplex.InjectiveResolution ((singleY).obj 𝒢))
    (J' : CochainComplex.InjectiveResolution (pushf.obj I))
    (β : J ⟶ J')
    (γ : ΓY.obj (pushf.obj I) ⟶ ΓY.obj J')
    [QuasiIso γ] :
    QΓY.obj (ΓY.obj J) ⟶
      QΓY.obj (ΓY.obj (pushf.obj I)) :=
  QΓY.map (ΓY.map β) ≫ inv (QΓY.map γ)

-- Proof sketch: unfold the definition. The chosen-resolution representative is, by construction,
-- the morphism obtained by first applying global sections to the lift `β` and then composing with
-- the inverse of the chosen vertical quasi-isomorphism `γ`.
/-- The chosen-resolution representative is exactly the horizontal global-sections map followed by
the inverse of the vertical quasi-isomorphism. -/
theorem moduleDerivedGlobalSectionsMapOnChosenResolutions_def
    (I : CochainComplex.InjectiveResolution ((singleX).obj ℱ))
    (J : CochainComplex.InjectiveResolution ((singleY).obj 𝒢))
    (J' : CochainComplex.InjectiveResolution (pushf.obj I))
    (β : J ⟶ J')
    (γ : ΓY.obj (pushf.obj I) ⟶ ΓY.obj J')
    [QuasiIso γ] :
    moduleDerivedGlobalSectionsMapOnChosenResolutions f 𝒢 ℱ I J J' β γ =
      QΓY.map (ΓY.map β) ≫ inv (QΓY.map γ) :=
  rfl

end AlgebraicGeometry.RingedSpace

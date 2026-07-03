import StacksProject_2024.Chap13.Definition_13_18_1
import StacksProject_2024.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

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

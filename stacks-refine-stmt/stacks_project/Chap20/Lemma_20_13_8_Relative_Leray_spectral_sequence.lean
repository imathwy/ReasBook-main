import Mathlib
import stacks_project.Chap20.«20_3_0_4»
import stacks_project.Chap20.Lemma_20_11_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}}

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on a ringed
space. -/
abbrev ModuleDerivedPlus (X : RingedSpace.{u}) :=
  AlgebraicGeometry.boundedBelowDerivedCategory (RingedSpace.Modules X)

/-- The bounded-below right derived direct-image functor on module sheaves over ringed
spaces. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  Functor.totalRightDerived
    (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
    (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
    (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    (RingedSpace.Modules Y) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Y)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The degree-`n` cohomology sheaf of the bounded-below derived direct image
`R(g \circ f)_* K`. -/
abbrev moduleCompositePushforwardDerivedPlusCohomology
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) (n : ℕ) :
    (RingedSpace.Modules Z) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Z)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Z) n).obj
    ((modulePushforwardDerivedPlus (f ≫ g)).obj K))

/-- A functorial package for the relative Leray spectral sequence attached to composable
morphisms of ringed spaces. -/
structure RelativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially in
  the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    (RingedSpace.Modules X) ⥤ E₂CohomologicalSpectralSequenceNat (RingedSpace.Modules Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (R^q f_* \mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        ((modulePushforward g).rightDerived p).obj
          (((modulePushforward f).rightDerived q).obj ℱ)
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : (RingedSpace.Modules X) → ℕ → (RingedSpace.Modules Z)
  /-- The abutment identifies with the higher direct images of the composite morphism
  `(g \circ f)_*`. -/
  targetIso :
    ∀ (ℱ : (RingedSpace.Modules X)) (n : ℕ),
      abutment ℱ n ≅ ((modulePushforward (f ≫ g)).rightDerived n).obj ℱ

/-- A bounded-below-complex version of the relative Leray spectral sequence for composable
morphisms of ringed spaces. -/
structure RelativeLeraySpectralSequenceBoundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) where
  /-- The cohomological spectral sequence attached to the bounded-below complex `K`, starting on
  the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat (RingedSpace.Modules Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (H^q(Rf_* K))`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        ((modulePushforward g).rightDerived p).obj
          (modulePushforwardDerivedPlusCohomology f K q)
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℕ → (RingedSpace.Modules Z)
  /-- The abutment identifies with the cohomology sheaves of `R(g \circ f)_* K`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleCompositePushforwardDerivedPlusCohomology f g K n

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite
-- of the two direct-image functors on sheaves of modules. Lemma `20.13.7` identifies the right
-- derived direct image of the composite with the composite of the right derived direct images, so
-- the `E₂`-page becomes `R^p g_* (R^q f_* \mathcal F)`. Naturality of the Grothendieck
-- construction yields functoriality in `\mathcal F`.
/-- Lemma 20.13.8 (Relative Leray spectral sequence): for composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z`, there is a cohomological spectral sequence functorial in an
`\mathcal O_X`-module `\mathcal F` whose `E_2^{p,q}`-term is
`R^p g_* (R^q f_* \mathcal F)` and whose abutment is `R^{p + q} (g \circ f)_* \mathcal F`. -/
theorem exists_relativeLeraySpectralSequence
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules X)]
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive] :
    Nonempty (RelativeLeraySpectralSequence f g) := sorry

-- Proof sketch: apply the bounded-below Grothendieck spectral sequence to the composable
-- direct-image functors `f_*` and `g_*` on sheaves of modules. The same comparison from Lemma
-- `20.13.7` identifies the abutment with the cohomology sheaves of `R(g \circ f)_* K`, and the
-- `E₂`-page is obtained by taking higher direct images of the cohomology sheaves of `Rf_* K`.
/-- A bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed spaces. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInjectiveResolutions (RingedSpace.Modules Y)]
    [(modulePushforward f).Additive]
    [(modulePushforward g).Additive]
    [(modulePushforward (f ≫ g)).Additive]
    [(modulePushforward (𝟙 X)).Additive]
    [Functor.IsLocalization
      (AlgebraicGeometry.ringedSpaceModuleBoundedBelowDerivedLocalization X)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow f)
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    [Functor.HasRightDerivedFunctor
      (AlgebraicGeometry.ringedSpaceModuleMapBoundedBelowHomotopyToDerivedBelow (f ≫ g))
      (AlgebraicGeometry.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))]
    (K : ModuleDerivedPlus X) :
    Nonempty (RelativeLeraySpectralSequenceBoundedBelow f g K) := sorry

end AlgebraicGeometry.RingedSpace

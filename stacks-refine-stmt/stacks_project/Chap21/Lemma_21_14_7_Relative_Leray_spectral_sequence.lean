import Mathlib
import stacks_project.Chap13.Lemma_13_20_3
import stacks_project.Chap18.Definition_18_31_1
import stacks_project.Chap21.Lemma_21_7_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe w u v

namespace RingedSite.Hom

variable {X Y Z : RingedSite.{u, v}}

local instance (X : RingedSite.{u, v}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (ModuleCat X)

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerivedPlus (X : RingedSite.{u, v})
    [HasDerivedCategory.{w} (ModuleCat X)] :=
  CategoryTheory.boundedBelowDerivedCategory (ModuleCat X)

/-- The bounded-below right derived direct-image functor on module sheaves. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : RingedSite.Hom X Y)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    ModuleCat Y :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (ModuleCat Y)))) ⋙
      DerivedCategory.homologyFunctor (ModuleCat Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The degree-`n` cohomology sheaf of the bounded-below derived direct image
`R(g \circ f)_* K`. -/
abbrev moduleCompositePushforwardDerivedPlusCohomology
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) (n : ℕ) :
    ModuleCat Z :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (ModuleCat Z)))) ⋙
      DerivedCategory.homologyFunctor (ModuleCat Z) n).obj
    ((modulePushforwardDerivedPlus (RingedSite.Hom.comp f g)).obj K))

/-- A functorial package for the relative Leray spectral sequence attached to a composable pair of
morphisms of ringed topoi, formalized here by ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`.
-/
structure RelativeLeraySpectralSequence
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasInjectiveResolutions (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))] where
  /-- The cohomological spectral sequence attached to each `\mathcal O_X`-module, functorially in
  the module and starting on the `E₂`-page. -/
  spectralSequenceFunctor :
    ModuleCat X ⥤ E₂CohomologicalSpectralSequenceNat (ModuleCat Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (R^q f_* \mathcal F)`. -/
  pageTwoIso :
    ∀ (ℱ : ModuleCat X) (p q : ℕ),
      ((spectralSequenceFunctor.obj ℱ).page 2).X (p, q) ≅
        higherDirectImageModule g (higherDirectImageModule f ℱ q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ModuleCat X → ℕ → ModuleCat Z
  /-- The abutment identifies with the higher direct images of the composite morphism
  `(g \circ f)_*`. -/
  targetIso :
    ∀ (ℱ : ModuleCat X) (n : ℕ),
      abutment ℱ n ≅ higherDirectImageModule (RingedSite.Hom.comp f g) ℱ n

/-- A bounded-below-complex version of the relative Leray spectral sequence attached to a
composable pair of morphisms of ringed topoi, formalized here by ringed-site morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`. -/
structure RelativeLeraySpectralSequenceBoundedBelow
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) where
  /-- The cohomological spectral sequence attached to the bounded-below complex `K`, starting on
  the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat (ModuleCat Z)
  /-- The `E₂`-page identifies with the iterated higher direct images
  `R^p g_* (H^q(Rf_* K))`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        higherDirectImageModule g (modulePushforwardDerivedPlusCohomology f K q) p
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℕ → ModuleCat Z
  /-- The abutment identifies with the cohomology sheaves of `R(g \circ f)_* K`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleCompositePushforwardDerivedPlusCohomology f g K n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `SheafOfModules.pushforward f.structureSheafMap ⋙ SheafOfModules.pushforward g.structureSheafMap`.
-- Lemma `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on
-- the intermediate ringed topos, and Lemma `21.14.3` upgrades total acyclicity to right
-- acyclicity for the second pushforward. The Chapter `13` Grothendieck spectral sequence then
-- produces the desired `E₂`-page and abutment, while naturality of the construction gives
-- functoriality in `\mathcal F`.
/-- Lemma 21.14.7 (Relative Leray spectral sequence): for composable morphisms of ringed topoi,
formalized here by ringed-site morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, there is a cohomological
spectral sequence functorial in an `\mathcal O_X`-module `\mathcal F` whose
`E_2^{p,q}`-term is `R^p g_* (R^q f_* \mathcal F)` and whose abutment is
`R^{p + q} (g \circ f)_* \mathcal F`. -/
theorem exists_relativeLeraySpectralSequence
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasInjectiveResolutions (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))] :
    Nonempty (RelativeLeraySpectralSequence f g) := sorry

-- Proof sketch: apply Lemma `13.22.2` directly to the bounded-below derived categories of module
-- sheaves and to the composable direct-image functors `f_*` and `g_*`. The acyclicity input comes
-- from the module-sheaf form of the Leray acyclicity lemmas `21.14.1` and `21.14.3`, now used on
-- representatives of bounded-below complexes.
/-- The bounded-below derived version of the relative Leray spectral sequence for module sheaves on
ringed sites. -/
theorem exists_relativeLeraySpectralSequence_boundedBelow
    (f : RingedSite.Hom X Y) (g : RingedSite.Hom Y Z)
    [HasDerivedCategory.{w} (ModuleCat X)]
    [HasDerivedCategory.{w} (ModuleCat Y)]
    [HasDerivedCategory.{w} (ModuleCat Z)]
    [EnoughInjectives (ModuleCat X)]
    [HasInjectiveResolutions (ModuleCat Y)]
    [Functor.Additive (modulePushforward f)]
    [Functor.Additive (modulePushforward g)]
    [Functor.Additive (modulePushforward (RingedSite.Hom.comp f g))]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [AdditiveFunctorDerivedLocalizationSituation
      (modulePushforward (RingedSite.Hom.comp f g))]
    (K : ModuleDerivedPlus X) :
    Nonempty (RelativeLeraySpectralSequenceBoundedBelow f g K) := sorry

end RingedSite.Hom

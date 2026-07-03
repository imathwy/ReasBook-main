import Mathlib
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap20.«20_3_0_4»
import StacksProject_2024.Chap20.Lemma_20_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

local instance (X : RingedSpace.{u}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Modules X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (RingedSpace.Modules X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (RingedSpace.Modules X)

/-- The underlying additive sheaf of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleUnderlyingSheaf {X : RingedSpace.{u}} (ℱ : (RingedSpace.Modules X)) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).obj ℱ

/-- The degree-`p` global sheaf cohomology of an `\mathcal O_X`-module on a ringed space. -/
abbrev moduleGlobalCohomology {X : RingedSpace.{u}}
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (ℱ : (RingedSpace.Modules X)) (p : ℕ) :
    AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf ℱ).H' p (⊤ : Opens X.carrier)

/-- The bounded-below derived category `D^+(\mathcal O_X)` of `\mathcal O_X`-modules on a
ringed space. -/
abbrev ModuleDerivedPlus (X : RingedSpace.{u}) :=
  CategoryTheory.boundedBelowDerivedCategory (RingedSpace.Modules X)

/-- A bounded-below complex of `\mathcal O_X`-modules defines an object of `D^+(\mathcal O_X)`.
-/
abbrev moduleComplexToDerivedPlus (X : RingedSpace.{u})
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))] :
    CochainComplex.Plus (RingedSpace.Modules X) ⥤ ModuleDerivedPlus X :=
  CategoryTheory.boundedBelowCochainComplexToDerivedBelow (𝟭 (RingedSpace.Modules X))

/-- The bounded-below right derived direct-image functor on `\mathcal O_X`-modules. -/
abbrev modulePushforwardDerivedPlus {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (modulePushforward f))
    (mapBoundedBelowHomotopyToDerivedBelow (RingedSpace.Modules X))
    (boundedBelowHomotopyQuasiIso (RingedSpace.Modules X))

/-- The degree-`q` cohomology sheaf of the bounded-below derived direct image `Rf_* K`. -/
abbrev modulePushforwardDerivedPlusCohomology
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    (K : ModuleDerivedPlus X) (q : ℕ) :
    (RingedSpace.Modules Y) :=
  (((ObjectProperty.ι (t.plus : ObjectProperty (DerivedCategory (RingedSpace.Modules Y)))) ⋙
      DerivedCategory.homologyFunctor (RingedSpace.Modules Y) q).obj
    ((modulePushforwardDerivedPlus f).obj K))

/-- The `E_2^{p,q}` term in the Leray spectral sequence of a bounded-below complex, written as the
global degree-`p` cohomology of the `q`-th cohomology sheaf of `Rf_* K`. -/
abbrev leraySpectralSequencePageTwoTerm
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) (p q : ℕ) :
    AddCommGrpCat.{u} :=
  moduleGlobalCohomology
    (modulePushforwardDerivedPlusCohomology f ((moduleComplexToDerivedPlus X).obj K) q) p

/-- A packaged Leray spectral sequence for a bounded-below complex of `\mathcal O_X`-modules on a
morphism of ringed spaces `f : X ⟶ Y`. -/
structure LeraySpectralSequenceBoundedBelow
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) where
  /-- The chosen cohomological spectral sequence, starting on the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{u}
  /-- The `E₂`-page identifies with `H^p(Y, R^q f_* K)`. -/
  pageTwoIso :
    ∀ p q : ℕ,
      (spectralSequence.page 2).X (p, q) ≅
        leraySpectralSequencePageTwoTerm f K p q
  /-- The chosen abutment additive groups of the spectral sequence. -/
  abutment : ℕ → AddCommGrpCat.{u}
  /-- The abutment identifies with the hypercohomology of `K` on `X`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅ moduleDerivedGlobalSectionsCohomology X K (Int.ofNat n)

-- Proof sketch: apply the Grothendieck spectral sequence of Lemma `13.22.2` to the composite of
-- `modulePushforward f` with the additive global-sections functor on `Y`. The comparison from
-- Lemma `20.13.1`, together with the global-sections identification of Remark `20.13.2`, rewrites
-- the abutment as the hypercohomology of `K` on `X`, and the `E₂`-page becomes
-- `H^p(Y, R^q f_* K)`.
/-- Lemma 20.13.4 (Leray spectral sequence): for a morphism of ringed spaces `f : X ⟶ Y` and a
bounded-below complex `K` of `\mathcal O_X`-modules, there is a cohomological spectral sequence
with `E_2^{p,q} = H^p(Y, R^q f_* K)` converging to the hypercohomology `H^{p + q}(X, K)`. -/
theorem exists_leraySpectralSequence_boundedBelow
    (f : X ⟶ Y)
    [EnoughInjectives (RingedSpace.Modules X)]
    [AdditiveFunctorDerivedLocalizationSituation (𝟭 (RingedSpace.Modules X))]
    [(modulePushforward f).Additive]
    [AdditiveFunctorDerivedLocalizationSituation (modulePushforward f)]
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})]
    [AdditiveFunctorDerivedLocalizationSituation (moduleGlobalSectionsAdditiveFunctor X)]
    (K : CochainComplex.Plus (RingedSpace.Modules X)) :
    Nonempty (LeraySpectralSequenceBoundedBelow f K) := sorry

end AlgebraicGeometry.RingedSpace

import Mathlib
import StacksProject_2024.Chap12.Definition_12_24_7
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DerivedCategory.TStructure
open CategoryTheory.Limits

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/-- The abelian category of sheaves of modules on the ringed site `X`. -/
abbrev ModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

/-- The bounded-below derived category `D^+(\mathcal O_X)` of module sheaves on `X`. -/
abbrev ModuleDerivedPlus (X : RingedSite.{u, v}) :=
  CategoryTheory.boundedBelowDerivedCategory (ModuleCat X)

/-- The direct-image functor on module sheaves attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    ModuleCat X ⥤ ModuleCat Y :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The global-sections functor on `\mathcal O_X`-modules, computed on the underlying abelian
sheaf. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    ModuleCat X ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

/-- The `q`-th cohomology module sheaf of a bounded-below derived `\mathcal O_X`-complex. -/
abbrev moduleDerivedCohomology (X : RingedSite.{u, v})
    (K : ModuleDerivedPlus X) (q : ℤ) :
    ModuleCat X :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory (ModuleCat X)))) ⋙
        DerivedCategory.homologyFunctor (ModuleCat X) q).obj K)

local instance (X : RingedSite.{u, v}) :
    CategoryTheory.Functor.IsLocalization
      (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
      (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X)) :=
  CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization (ModuleCat X)

/-- The bounded-below right derived direct-image functor on module sheaves. -/
abbrev modulePushforwardDerivedPlus
    {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
    [EnoughInjectives (ModuleCat X)]
    [f.modulePushforward.Additive]
    [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward] :
    ModuleDerivedPlus X ⥤ ModuleDerivedPlus Y :=
  CategoryTheory.Functor.totalRightDerived
    (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow f.modulePushforward)
    (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
    (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}]
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [EnoughInjectives (ModuleCat X)]
variable [EnoughInjectives (ModuleCat Y)]
variable [f.modulePushforward.Additive]
variable [(moduleGlobalSectionsFunctor X).Additive]
variable [(moduleGlobalSectionsFunctor Y).Additive]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation f.modulePushforward]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation
  (moduleGlobalSectionsFunctor X)]
variable [CategoryTheory.AdditiveFunctorDerivedLocalizationSituation
  (moduleGlobalSectionsFunctor Y)]

/-- The `E_2^{p,q}` term `H^p(\mathcal D, R^q f_*(K))` of the Leray spectral sequence attached
to a bounded-below derived `\mathcal O_{\mathcal C}`-complex `K`. -/
abbrev leraySpectralSequencePageTwoTerm
    (K : ModuleDerivedPlus X) (p : ℕ) (q : ℤ) :
    AddCommGrpCat.{max u v} :=
  ((moduleGlobalSectionsFunctor Y).rightDerived p).obj
    (moduleDerivedCohomology Y
      ((modulePushforwardDerivedPlus f).obj K) q)

/-- The abutment `H^n(\mathcal C, K)` of the Leray spectral sequence, computed as the `n`-th
cohomology of the bounded-below derived global sections of `K`. -/
abbrev leraySpectralSequenceAbutment
    (K : ModuleDerivedPlus X) (n : ℤ) :
    AddCommGrpCat.{max u v} :=
  (((ObjectProperty.ι
      (t.plus : ObjectProperty (DerivedCategory AddCommGrpCat.{max u v}))) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} n).obj
      ((CategoryTheory.Functor.totalRightDerived
          (CategoryTheory.mapBoundedBelowHomotopyCategoryToDerivedBelow
            (moduleGlobalSectionsFunctor X))
          (CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow (ModuleCat X))
          (CategoryTheory.boundedBelowHomotopyQuasiIso (ModuleCat X))).obj K))

/-- A cohomological spectral sequence realizing the Leray spectral sequence for a morphism of
ringed topoi presented by a morphism of ringed sites `f` and a bounded-below derived
`\mathcal O_{\mathcal C}`-complex `K`. -/
structure LeraySpectralSequence
    (K : ModuleDerivedPlus X) where
  /-- The chosen cohomological spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 0
  /-- The `E_2`-page identifies with `H^p(\mathcal D, R^q f_*(K))`. -/
  pageTwoIso :
    ∀ p : ℕ, ∀ q : ℤ,
      (spectralSequence.page 2).X (Int.ofNat p, q) ≅
        leraySpectralSequencePageTwoTerm f K p q
  /-- The Leray spectral sequence is bounded. -/
  bounded : CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat.{max u v}
  /-- The abutment identifies with the hypercohomology `H^n(\mathcal C, K)`. -/
  targetIso :
    ∀ n : ℤ,
      abutment n ≅ leraySpectralSequenceAbutment K n

-- Proof sketch: apply the Grothendieck spectral sequence to the composite
-- `Γ(\mathcal C, -) = Γ(\mathcal D, -) ∘ f_*` on sheaves of `\mathcal O`-modules. Lemma
-- `21.14.1` shows that the pushforward of an injective module sheaf is totally acyclic on the
-- target, and Lemma `21.14.3` upgrades total acyclicity to right acyclicity for global sections.
-- Therefore the hypotheses of Lemma `13.22.2` hold for the pair
-- `f_* : Mod(\mathcal O_{\mathcal C}) ⥤ Mod(\mathcal O_{\mathcal D})` and
-- `Γ(\mathcal D, -)`, yielding the stated `E₂`-page and abutment.
/-- Lemma 21.14.5 (Leray spectral sequence): for a morphism of ringed topoi, formalized here by a
morphism of ringed sites `f`, and a bounded-below complex `K` of `\mathcal O_{\mathcal C}`-modules,
there is a cohomological spectral sequence whose `E_2^{p,q}`-term is
`H^p(\mathcal D, R^q f_*(K))` and whose abutment is `H^{p+q}(\mathcal C, K)`. -/
theorem exists_leraySpectralSequence
    (K : ModuleDerivedPlus X) :
    Nonempty (LeraySpectralSequence f K) := sorry

end

end RingedSite.Hom

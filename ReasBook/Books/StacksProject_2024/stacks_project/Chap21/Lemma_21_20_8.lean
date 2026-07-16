import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_1_Owner

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
variable [HasSheafify (J.over U) AddCommGrpCat.{u}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "ModU" => ringedSiteModuleCategory (J.over U) (𝒪.over U)
local notation "QMod" => (DerivedCategory.Q : CochainComplex Mod ℤ ⥤ DerivedCategory Mod)
local notation "QModU" => (DerivedCategory.Q : CochainComplex ModU ℤ ⥤ DerivedCategory ModU)
local notation "QisMod" => HomologicalComplex.quasiIso Mod (up ℤ)
local notation "QisModU" => HomologicalComplex.quasiIso ModU (up ℤ)

variable [Abelian Mod]
variable [Abelian ModU]

/- Domain-style sampling for Lemma 21.20.8:
- primary domain: derived adjunctions for localized lower shriek and localized restriction on
  sheaves of modules over a ringed site;
- sampled owner declarations:
  `ringedSiteLocalizedLowerShriek`,
  `ringedSiteLocalizedRestriction`,
  `ringedSiteLocalizedLowerShriek_adjunction`,
  `Functor.mapDerivedCategory`,
  `CategoryTheory.Adjunction.derived`;
- best owner abstraction: the source-facing derived localization adjunction should be stated
  directly on the Chapter 21 lower-shriek owner
  `(ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory` and the Chapter 18 restriction owner
  `(ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory`;
- primitive data: the underived localized adjunction
  `ringedSiteLocalizedLowerShriek J 𝒪 U ⊣ ringedSiteLocalizedRestriction J 𝒪 U`;
- derived API: the induced adjunction on derived categories supplied by
  `CategoryTheory.Adjunction.derived`.

Source/core/bridge triage:
- `source-facing`: the localized derived adjunction between
  `(ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory` and
  `(ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory`;
- `core/canonical`: `Functor.mapDerivedCategory` and `CategoryTheory.Adjunction.derived`;
- `bridge/view`: the Chapter 21 lower-shriek owner and the Chapter 18 localized restriction owner.
-/

/-- Lemma 21.20.8: the derived localized lower shriek on `D(ModU)` is left adjoint to the derived
localized restriction functor on `D(Mod)`. This is the canonical derived adjunction attached to
`ringedSiteLocalizedLowerShriek_adjunction`. -/
@[stacks 08FJ]
noncomputable def ringedSiteLocalizedLowerShriek_mapDerivedCategory_adjunction :
    ((ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory) ⊣
      ((ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory) := by
  let L := (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory
  let R := (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory
  let _ : Preadditive Mod := Abelian.toPreadditive
  let _ : Preadditive ModU := Abelian.toPreadditive
  let _ : Functor.IsLocalization QMod QisMod :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let _ : Functor.IsLocalization QModU QisModU :=
    DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp
  let _ :
      L.IsLeftDerivedFunctor
        (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategoryFactors.hom
        QisModU := by
    simpa using
      (Functor.isLeftDerivedFunctor_of_inverts
        QisModU
        ((ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory)
        (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategoryFactors)
  let _ :
      R.IsRightDerivedFunctor
        (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategoryFactors.inv
        QisMod := by
    simpa using
      (Functor.isRightDerivedFunctor_of_inverts
        QisMod
        ((ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory)
        (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategoryFactors)
  let _ :
      (L ⋙ R).IsLeftDerivedFunctor
        ((Functor.associator QModU L R).inv ≫
          Functor.whiskerRight
            (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategoryFactors.hom
            R)
        QisModU := by
    let e :
        QModU ⋙ (L ⋙ R) ≅
          (((ringedSiteLocalizedLowerShriek J 𝒪 U).mapHomologicalComplex (up ℤ)) ⋙ QMod) ⋙ R :=
      (Functor.associator QModU L R).symm ≪≫
        Functor.isoWhiskerRight
          (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategoryFactors
          R
    simpa [L, R, e] using
      (Functor.isLeftDerivedFunctor_of_inverts QisModU (L ⋙ R) e)
  let _ :
      (R ⋙ L).IsRightDerivedFunctor
        (Functor.whiskerRight
            (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategoryFactors.inv
            L ≫
          (Functor.associator QMod R L).hom)
        QisMod := by
    let e :
        QMod ⋙ (R ⋙ L) ≅
          (((ringedSiteLocalizedRestriction J 𝒪 U).mapHomologicalComplex (up ℤ)) ⋙ QModU) ⋙ L :=
      (Functor.associator QMod R L).symm ≪≫
        Functor.isoWhiskerRight
          (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategoryFactors
          L
    simpa [L, R, e] using
      (Functor.isRightDerivedFunctor_of_inverts QisMod (R ⋙ L) e)
  let hAdj : L ⊣ R :=
    Adjunction.derived
      ((ringedSiteLocalizedLowerShriek_adjunction J 𝒪 U).mapHomologicalComplex (up ℤ))
      QisModU
      QisMod
      (ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategoryFactors.hom
      (ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategoryFactors.inv
  exact hAdj

instance ringedSiteLocalizedLowerShriek_mapDerivedCategory_isLeftAdjoint :
    ((ringedSiteLocalizedLowerShriek J 𝒪 U).mapDerivedCategory).IsLeftAdjoint := by
  exact
    (ringedSiteLocalizedLowerShriek_mapDerivedCategory_adjunction J 𝒪 U).isLeftAdjoint

/-- Companion to Lemma 21.20.8: the derived localized restriction functor on `D(Mod)` is the
right adjoint of the derived localized lower shriek on `D(ModU)`. -/
instance ringedSiteLocalizedRestriction_mapDerivedCategory_isRightAdjoint :
    ((ringedSiteLocalizedRestriction J 𝒪 U).mapDerivedCategory).IsRightAdjoint := by
  exact
    (ringedSiteLocalizedLowerShriek_mapDerivedCategory_adjunction J 𝒪 U).isRightAdjoint

end

end SheafOfModules.RingedSite

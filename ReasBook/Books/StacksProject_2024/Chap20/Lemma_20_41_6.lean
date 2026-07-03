import Mathlib
import stacks_project.Chap20.Lemma_20_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.DerivedCategory
open CochainComplex.HomComplex.CohomologyClass
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X.carrier}

/-- The `RingCat`-valued structure sheaf underlying a ringed space. -/
private abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X.carrier :=
  (sheafCompose (Opens.grothendieckTopology X.carrier) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
private abbrev ambientModuleCategory (X : RingedSpace.{u}) :=
  SheafOfModules (ringedSpaceRingCatSheaf X)

/-- The category of `\mathcal O_U`-modules on the open subspace defined by `U`. -/
private abbrev openSubspaceModuleCategory (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (ringedSpaceRingCatSheaf X))

/-- The restricted open-subspace module category has its standard derived category. -/
private instance openSubspaceModuleCategory_hasDerivedCategory :
    HasDerivedCategory (openSubspaceModuleCategory X U) :=
  HasDerivedCategory.standard (openSubspaceModuleCategory X U)

local notation "ModX" => ambientModuleCategory X
local notation "ModU" => openSubspaceModuleCategory X U
local notation "DModU" => DerivedCategory ModU

/-- Restriction of `\mathcal O_X`-modules from `X` to the open subspace `U`. -/
private abbrev moduleRestrictionToOpen (X : RingedSpace.{u}) (U : Opens X.carrier) :
    ambientModuleCategory X ⥤ openSubspaceModuleCategory X U :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (ringedSpaceRingCatSheaf X))

/-- The localization functor from restricted complexes to the derived category on the open
subspace `U`. -/
private abbrev openSubspaceDerivedQ (X : RingedSpace.{u}) (U : Opens X.carrier) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ ⥤
      DerivedCategory (openSubspaceModuleCategory X U) :=
  DerivedCategory.Q

/-- Restriction of a complex of `\mathcal O_X`-modules to the open subspace `U`. -/
private abbrev restrictModuleComplexToOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (ambientModuleCategory X) ℤ) :
    CochainComplex (openSubspaceModuleCategory X U) ℤ :=
  ((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj K

-- Proof sketch: restriction to an open subspace is pullback along an open immersion, and the
-- K-injective preservation statement is the module-sheaf version of the standard restriction
-- argument used in Lemma `20.32.1`.
/-- Restriction to an open subspace preserves K-injective complexes of `\mathcal O_X`-modules. -/
private theorem restrictModuleComplexToOpen_isKInjective
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    (K : CochainComplex (ambientModuleCategory X) ℤ) [K.IsKInjective] :
    (restrictModuleComplexToOpen X U K).IsKInjective := by
  simpa [restrictModuleComplexToOpen, moduleRestrictionToOpen] using
    (AlgebraicGeometry.RingedSpace.moduleRestrictionToOpen_isKInjective (X := X) U K)

-- Proof sketch: apply `20.41.0.1` with `n = 0` to the restricted complexes
-- `\mathcal L^\bullet|_U` and `\mathcal I^\bullet|_U`, giving morphisms in the homotopy
-- category `K(\mathcal O_U)`. By Lemma `20.32.1`, the restriction of the K-injective complex
-- `\mathcal I^\bullet` is again K-injective, so the localization functor identifies these
-- homotopy classes with morphisms in `D(\mathcal O_U)`. This is the restricted-representative
-- form of the textbook identification
-- `H^0(\Gamma(U, \mathcal H\!\mathit{om}^\bullet(\mathcal L^\bullet, \mathcal I^\bullet))) =
-- \operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`.
/-- Lemma 20.41.6: if `Lc` and `Ic` are complexes of `\mathcal O_X`-modules and `Ic` is
K-injective, then the degree-zero cohomology of the sections of the restricted internal-Hom
complex on an open subset `U` identifies with the morphisms in the derived category of
`\mathcal O_U`-modules between the restricted derived objects represented by `Lc` and `Ic`. -/
noncomputable def openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom
    (Lc Ic : CochainComplex ModX ℤ)
    [Ic.IsKInjective] :
    (CochainComplex.HomComplex (restrictModuleComplexToOpen X U Lc)
      (restrictModuleComplexToOpen X U Ic)).homology (0 : ℤ) ≃
      ((openSubspaceDerivedQ X U).obj (restrictModuleComplexToOpen X U Lc) ⟶
        (openSubspaceDerivedQ X U).obj (restrictModuleComplexToOpen X U Ic)) :=
  let LU := restrictModuleComplexToOpen X U Lc
  let IU := restrictModuleComplexToOpen X U Ic
  let KU := (HomotopyCategory.quotient ModU (up ℤ)).obj LU
  let J0Iso :
      (HomotopyCategory.quotient ModU (up ℤ)).obj (IU⟦(0 : ℤ)⟧) ≅
        (HomotopyCategory.quotient ModU (up ℤ)).obj IU :=
    (HomotopyCategory.quotient ModU (up ℤ)).mapIso
      ((CategoryTheory.shiftFunctorZero (CochainComplex ModU ℤ) ℤ).app IU)
  letI : IU.IsKInjective := restrictModuleComplexToOpen_isKInjective X U Ic
  ((CochainComplex.HomComplex.homologyAddEquiv LU IU (0 : ℤ)).trans homAddEquiv).toEquiv.trans
    ((Iso.homCongr (Iso.refl KU) J0Iso).trans
      ((Equiv.ofBijective
          (DerivedCategory.Qh.map :
            (KU ⟶ (HomotopyCategory.quotient ModU (up ℤ)).obj IU) →
              (DerivedCategory.Qh.obj KU ⟶
                DerivedCategory.Qh.obj ((HomotopyCategory.quotient ModU (up ℤ)).obj IU)))
          (CochainComplex.IsKInjective.Qh_map_bijective KU IU)).trans
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModU).app LU)
          ((DerivedCategory.quotientCompQhIso ModU).app IU))))

-- Proof sketch: unfold the definition. It first identifies
-- `H^0(\operatorname{Hom}^\bullet(L_U^\bullet, I_U^\bullet))` with cohomology classes in the
-- Hom complex, then uses K-injectivity of `I_U^\bullet` to pass from cohomology classes to
-- morphisms in the localized derived category, and finally removes the zero shift.
/-- The canonical equivalence is obtained by composing the standard homology, K-injective, and
zero-shift identifications. -/
theorem openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom_def
    (Lc Ic : CochainComplex ModX ℤ)
    [Ic.IsKInjective] :
    openSubspaceHomComplex_homology_zero_equiv_restrictedDerivedHom
        Lc Ic =
      let LU := restrictModuleComplexToOpen X U Lc
      let IU := restrictModuleComplexToOpen X U Ic
      let KU := (HomotopyCategory.quotient ModU (up ℤ)).obj LU
      let J0Iso :
          (HomotopyCategory.quotient ModU (up ℤ)).obj (IU⟦(0 : ℤ)⟧) ≅
            (HomotopyCategory.quotient ModU (up ℤ)).obj IU :=
        (HomotopyCategory.quotient ModU (up ℤ)).mapIso
          ((CategoryTheory.shiftFunctorZero (CochainComplex ModU ℤ) ℤ).app IU)
      letI : IU.IsKInjective :=
        restrictModuleComplexToOpen_isKInjective X U Ic
      ((CochainComplex.HomComplex.homologyAddEquiv LU IU (0 : ℤ)).trans homAddEquiv).toEquiv.trans
        ((Iso.homCongr (Iso.refl KU) J0Iso).trans
          ((Equiv.ofBijective
              (DerivedCategory.Qh.map :
                (KU ⟶ (HomotopyCategory.quotient ModU (up ℤ)).obj IU) →
                  (DerivedCategory.Qh.obj KU ⟶
                    DerivedCategory.Qh.obj ((HomotopyCategory.quotient ModU (up ℤ)).obj IU)))
              (CochainComplex.IsKInjective.Qh_map_bijective KU IU)).trans
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso ModU).app LU)
              ((DerivedCategory.quotientCompQhIso ModU).app IU)))) := sorry

end

end AlgebraicGeometry.RingedSpace

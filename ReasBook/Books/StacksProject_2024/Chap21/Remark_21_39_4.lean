import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section Generic

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{max u v} A] [Abelian A]
variable [HasColimitsOfShape Cᵒᵖ A]

local notation "PresheafCat" => Cᵒᵖ ⥤ A
local notation "QisPresheaf" => HomotopyCategory.quasiIso PresheafCat (up ℤ)

/-- Evaluation of an `A`-valued presheaf on `C` at an object `U`. -/
private abbrev evaluatePresheafAt (U : C) : PresheafCat ⥤ A :=
  (evaluation (Cᵒᵖ) A).obj (Opposite.op U)

/-- The functor from the homotopy category of presheaf complexes to the derived category of `A`
obtained by taking colimits termwise. -/
private abbrev colimitToDerived :
    HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A :=
  (colim : PresheafCat ⥤ A).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The total left derived functor of taking colimits of `A`-valued presheaf complexes. -/
private abbrev derivedColimit
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    DerivedCategory PresheafCat ⥤ DerivedCategory A :=
  colimitToDerived.totalLeftDerived DerivedCategory.Qh QisPresheaf

-- Proof sketch: this is the naturality relation for the universal colimit cocone, evaluated at
-- the vertex `op U`.
/-- The colimit cocone gives a natural transformation from evaluation at `U` to colimits. -/
private theorem evaluationToColimit_naturality (U : C)
    {𝒢 ℋ : PresheafCat} (τ : 𝒢 ⟶ ℋ) :
    (evaluatePresheafAt U).map τ ≫ colimit.ι ℋ (Opposite.op U) =
      colimit.ι 𝒢 (Opposite.op U) ≫ (colim : PresheafCat ⥤ A).map τ := sorry

/-- The natural transformation from evaluation at `U` to presheaf colimits. -/
private abbrev evaluationToColimitNatTrans (U : C) :
    evaluatePresheafAt U ⟶ (colim : PresheafCat ⥤ A) where
  app 𝒢 := colimit.ι 𝒢 (Opposite.op U)
  naturality := fun {_ _} τ ↦ evaluationToColimit_naturality U τ

/-- The comparison from derived evaluation at `U` to the underived colimit functor on homotopy
categories. -/
private abbrev evaluationDerivedComparison (U : C) :
    DerivedCategory.Qh ⋙ (evaluatePresheafAt U).mapDerivedCategory ⟶
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A) :=
  (evaluatePresheafAt U).mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (evaluationToColimitNatTrans U) (up ℤ))
      DerivedCategory.Qh

/-- The natural transformation from derived evaluation at `U` to the derived colimit functor. -/
private abbrev evaluationMapToDerivedColimit (U : C)
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    (evaluatePresheafAt U).mapDerivedCategory ⟶
      (derivedColimit : DerivedCategory PresheafCat ⥤ DerivedCategory A) :=
  let F : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A := colimitToDerived
  let LF : DerivedCategory PresheafCat ⥤ DerivedCategory A := derivedColimit
  LF.leftDerivedLift
    (F.totalLeftDerivedCounit DerivedCategory.Qh QisPresheaf)
    QisPresheaf
    ((evaluatePresheafAt U).mapDerivedCategory)
    (evaluationDerivedComparison U)

/-- The canonical morphism from the complex of sections over `U` to the derived colimit of a
complex of `A`-valued presheaves. -/
private abbrev sectionComplexToDerivedColimit (U : C) (K : CochainComplex PresheafCat ℤ)
    [Functor.HasLeftDerivedFunctor
      (colimitToDerived : HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
      QisPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (derivedColimit : DerivedCategory PresheafCat ⥤ DerivedCategory A).obj
        (DerivedCategory.Q.obj K) :=
  (asIso ((evaluatePresheafAt U).mapDerivedCategoryFactors.hom.app K)).inv ≫
    (evaluationMapToDerivedColimit U).app (DerivedCategory.Q.obj K)

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "AbelianColimitToDerived" =>
  (colimitToDerived : HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- Specialized derived colimit functor for abelian presheaves. -/
private abbrev abelianDerivedColimit
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf] :
    DerivedCategory AbPresheaf ⥤ DerivedCategory AddCommGrpCat :=
  derivedColimit

/-- Remark 21.39.4: for an object `U` of `\mathcal C`, assuming the total left derived colimit
functor on complexes of abelian presheaves is defined, there is a canonical morphism from the
complex of sections `\mathcal F^\bullet(U)` to `L\pi_!(\mathcal F^\bullet)` in `D(\textit{Ab})`.
-/
noncomputable abbrev sectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex AbPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor
      AbelianColimitToDerived
      QisAbPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (abelianDerivedColimit).obj (DerivedCategory.Q.obj K) :=
  let _ : Functor.HasLeftDerivedFunctor
      AbelianColimitToDerived QisAbPresheaf := hLeft
  sectionComplexToDerivedColimit U K

-- Proof sketch: after inserting the supplied left-derived-functor instance, this is exactly the
-- specialized generic construction of `sectionComplexToDerivedColimit`.
/-- The abelian-presheaf construction is the specialization of the generic derived-colimit map. -/
theorem sectionComplexToLeftDerivedColimit_def (U : C)
    (K : CochainComplex AbPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf] :
    sectionComplexToLeftDerivedColimit U K = sectionComplexToDerivedColimit U K := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "ModuleColimitToDerived" =>
  (colimitToDerived : HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- Specialized derived colimit functor for module-valued presheaves. -/
private abbrev moduleDerivedColimit
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf] :
    DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  derivedColimit

/-- The same construction as `sectionComplexToLeftDerivedColimit`, now for complexes of
presheaves of `B`-modules, with target in the derived category `D(B)`. -/
noncomputable abbrev moduleSectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex BPresheaf ℤ)
    [hLeft : Functor.HasLeftDerivedFunctor
      ModuleColimitToDerived
      QisBPresheaf] :
    DerivedCategory.Q.obj (((evaluatePresheafAt U).mapHomologicalComplex (up ℤ)).obj K) ⟶
      (derivedColimit : DerivedCategory BPresheaf ⥤ DerivedCategory (ModuleCat B)).obj
        (DerivedCategory.Q.obj K) :=
  let _ : Functor.HasLeftDerivedFunctor
      ModuleColimitToDerived QisBPresheaf := hLeft
  sectionComplexToDerivedColimit U K

end Module

end CategoryTheory

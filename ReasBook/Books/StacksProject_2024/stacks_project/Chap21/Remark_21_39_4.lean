import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap21.Lemma_21_39_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Remark 21.39.4:
- primary domain: derived functors on homotopy/derived categories of presheaves, with the
  canonical section-to-colimit comparison induced by the colimit cocone;
- sampled owner declarations:
  `categoryOverPointColimitToDerived`,
  `categoryOverPointDerivedColimit`,
  `Functor.leftDerivedNatTrans`,
  `Functor.mapDerivedCategoryFactors`;
- best owner abstraction: the Chapter 21 lower-shriek owner is already
  `categoryOverPointColimitToDerived`, with total left derived functor
  `categoryOverPointDerivedColimit` and notation `Lπ![C, A]`. The comparison morphisms below are
  source-facing bridges into that owner, not parallel lower-shriek owners.

Source/core/bridge triage:
- `source-facing`: `sectionComplexToDerivedColimit` and its abelian/module specializations;
- `core/canonical`: `categoryOverPointColimitToDerived` and `categoryOverPointDerivedColimit`;
- `bridge/view`: the `AddCommGrpCat` and `ModuleCat` specializations below.

Primitive-vs-derived split:
- primitive data: the evaluation functor at `U` and the colimit cocone map to `colim`;
- derived API: the induced morphism on derived categories, built canonically from the owner-level
  left-derived-functor machinery.
-/

section Generic

variable {C : Type u} [Category.{v} C]
variable {A : Type w} [Category.{max u v} A] [Abelian A]
variable [HasColimitsOfShape Cᵒᵖ A]

local notation "PresheafCat" => Cᵒᵖ ⥤ A
local notation "QisPresheaf" => HomotopyCategory.quasiIso PresheafCat (up ℤ)
local notation "ColimitToDerived" =>
  (categoryOverPointColimitToDerived C A :
    HomotopyCategory PresheafCat (up ℤ) ⥤ DerivedCategory A)
local notation "DerivedColimit" =>
  (categoryOverPointDerivedColimit C A :
    DerivedCategory PresheafCat ⥤ DerivedCategory A)

-- Proof sketch: this is the naturality relation for the universal colimit cocone, evaluated at
-- the vertex `op U`.
omit [Abelian A] in
/-- The colimit cocone gives a natural transformation from evaluation at `U` to colimits. -/
private theorem evaluationToColimit_naturality (U : C)
    {𝒢 ℋ : PresheafCat} (τ : 𝒢 ⟶ ℋ) :
    ((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).map τ ≫ colimit.ι ℋ (Opposite.op U) =
      colimit.ι 𝒢 (Opposite.op U) ≫ (colim : PresheafCat ⥤ A).map τ := by
  -- This is exactly the colimit cocone compatibility for the map `τ`, evaluated at `op U`.
  exact (colimit.ι_map τ (Opposite.op U)).symm

/-- The natural transformation from evaluation at `U` to presheaf colimits. -/
private def evaluationToColimitNatTrans (U : C) :
    (evaluation (Cᵒᵖ) A).obj (Opposite.op U) ⟶ (colim : PresheafCat ⥤ A) where
  app 𝒢 := colimit.ι 𝒢 (Opposite.op U)
  naturality := fun {_ _} τ ↦ evaluationToColimit_naturality U τ

/-- The homotopy-to-derived comparison induced by the colimit cocone map on evaluation at `U`. -/
private def evaluationToColimitHomotopyComparison (U : C) :
    mapHomotopyCategoryToDerived ((evaluation (Cᵒᵖ) A).obj (Opposite.op U)) ⟶
      ColimitToDerived :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (evaluationToColimitNatTrans U) (up ℤ))
    DerivedCategory.Qh

omit [HasColimitsOfShape Cᵒᵖ A] in
/-- Helper for Remark 21.39.4: evaluation at a fixed object preserves quasi-isomorphisms
objectwise, so its derived-category lift is already a left derived functor. -/
private theorem evaluationMapDerivedCategory_isLeftDerivedFunctor (U : C) :
    (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategory).IsLeftDerivedFunctor
      (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategoryFactorsh.hom)
      QisPresheaf := by
  let F : PresheafCat ⥤ A := (evaluation (Cᵒᵖ) A).obj (Opposite.op U)
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      QisPresheaf
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

/-- The natural transformation from derived evaluation at `U` to the derived colimit functor. -/
private noncomputable def evaluationMapToDerivedColimit (U : C)
    [Functor.HasLeftDerivedFunctor ColimitToDerived QisPresheaf] :
    ((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategory ⟶
      DerivedColimit :=
  let _ :
      (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategory).IsLeftDerivedFunctor
        (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategoryFactorsh.hom)
        QisPresheaf :=
    evaluationMapDerivedCategory_isLeftDerivedFunctor U
  Functor.leftDerivedNatTrans
    (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategory)
    ((ColimitToDerived).totalLeftDerived DerivedCategory.Qh QisPresheaf)
    (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategoryFactorsh.hom)
    ((ColimitToDerived).totalLeftDerivedCounit DerivedCategory.Qh QisPresheaf)
    QisPresheaf
    (evaluationToColimitHomotopyComparison U)

/-- The canonical morphism from the complex of sections of `K` over `U` to the left derived
colimit of `K`, viewed in the Chapter 21 owner `Lπ![C, A]`. -/
noncomputable def sectionComplexToDerivedColimit (U : C) (K : CochainComplex PresheafCat ℤ)
    [Functor.HasLeftDerivedFunctor ColimitToDerived QisPresheaf] :
    (((evaluation (Cᵒᵖ) A).obj (Opposite.op U)).mapDerivedCategory).obj
        (DerivedCategory.Q.obj K) ⟶
      (Lπ![C, A]).obj (DerivedCategory.Q.obj K) :=
  (evaluationMapToDerivedColimit U).app (DerivedCategory.Q.obj K)

end Generic

section AddCommGrp

variable {C : Type u} [Category.{v} C]

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "AbelianColimitToDerived" =>
  (categoryOverPointColimitToDerived C AddCommGrpCat :
    HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

/-- Remark 21.39.4: for `U : C`, if the total left derived functor of presheaf colimits exists,
there is a canonical morphism from the complex of sections of `K` over `U` to its derived
colimit in `Lπ![C, AddCommGrpCat]`. -/
@[stacks 08Q6]
noncomputable abbrev sectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex AbPresheaf ℤ)
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf] :=
  sectionComplexToDerivedColimit U K

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "ModuleColimitToDerived" =>
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))

/-- The same comparison as `sectionComplexToLeftDerivedColimit`, for complexes of presheaves of
`B`-modules with target in `Lπ![C, ModuleCat B]`. -/
noncomputable abbrev moduleSectionComplexToLeftDerivedColimit (U : C)
    (K : CochainComplex BPresheaf ℤ)
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf] :=
  sectionComplexToDerivedColimit U K

end Module

end CategoryTheory

import StacksProject_2024.stacks_project.Chap21.CategoryOverPointDerivedColimit

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory Simplicial

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.39.7:
- primary domain: the derived lower shriek for the projection from a category over a point,
  computed via evaluation on a cosimplicial object;
- sampled owner declarations:
  `SimplicialObject.HomotopyEquiv`,
  `categoryOverPointColimitToDerived`,
  `categoryOverPointDerivedColimit`,
  `alternatingFaceMapComplex`;
- best owner abstraction: the generic cosimplicial-evaluation and `Lπ!` owner layer now lives in
  `CategoryOverPointDerivedColimit`, while this file keeps the two source-facing comparison
  theorems of Lemma `21.39.7`.

Source/core/bridge triage:
- `source-facing`: the two comparison theorems below;
- `core/canonical`: `SimplicialObject.HomotopyEquiv`,
  `categoryOverPointDerivedColimit`, and the generic evaluation owners from
  `CategoryOverPointDerivedColimit`;
- `bridge/view`: none beyond those theorem statements. -/

section AddCommGrp

variable {C : Type u} [Category.{v} C]
variable [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]

local notation "AbPresheaf" => Cᵒᵖ ⥤ AddCommGrpCat
local notation "QisAbPresheaf" => HomotopyCategory.quasiIso AbPresheaf (up ℤ)
local notation "AbelianColimitToDerived" =>
  (categoryOverPointColimitToDerived C AddCommGrpCat :
    HomotopyCategory AbPresheaf (up ℤ) ⥤ DerivedCategory AddCommGrpCat)

-- Proof sketch: resolve each abelian presheaf by sums of representables, evaluate the resolution
-- on `U_•`, and use the assumption that every simplicial set `Mor_C(U_•, U)` is homotopy
-- equivalent to `Δ[0]` to identify the resulting simplicial abelian groups with the corresponding
-- representable resolutions of the colimit. This yields a functorial isomorphism in the derived
-- category.
/-- Lemma 21.39.7 (1): in the category-over-a-point situation of Example 21.39.1, if every
simplicial set of maps from `U_•` to `U` is homotopy equivalent to the singleton simplicial set
`Δ[0]`, then the derived lower shriek of a degree-zero abelian presheaf is functorially
isomorphic to the derived object represented by the simplicial abelian group obtained by
evaluating the presheaf on `U_•`. -/
@[stacks 08Q9]
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_abelianCosimplicialEvaluation
    [Functor.HasLeftDerivedFunctor AbelianColimitToDerived QisAbPresheaf]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObjectHasPointlikeHomSpaces Ubullet) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor AbPresheaf (0 : ℤ)) ⋙ Lπ![C, AddCommGrpCat])
      (cosimplicialEvaluationToDerived AddCommGrpCat Ubullet) := sorry

end AddCommGrp

section Module

variable {C : Type u} [Category.{v} C]
variable (B : Type w) [Ring B]
variable [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]

local notation "BPresheaf" => Cᵒᵖ ⥤ ModuleCat B
local notation "QisBPresheaf" => HomotopyCategory.quasiIso BPresheaf (up ℤ)
local notation "ModuleColimitToDerived" =>
  (categoryOverPointColimitToDerived C (ModuleCat B) :
    HomotopyCategory BPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B))

-- Proof sketch: apply the abelian-sheaf argument objectwise to the underlying additive presheaf of
-- a `B`-module presheaf, use the compatibility of `Lπ!` for modules with the abelian version,
-- and transport the resulting functorial comparison back to `D(B)`.
/-- Lemma 21.39.7 (2): under the same hypothesis on `U_•`, the derived lower shriek of a
degree-zero presheaf of `B`-modules is functorially isomorphic to the derived object represented
by the simplicial `B`-module object obtained by evaluating the presheaf on `U_•`. -/
@[stacks 08Q9]
theorem categoryOverPointDerivedLowerShriek_singleFunctor_isIsomorphic_moduleCosimplicialEvaluation
    [Functor.HasLeftDerivedFunctor ModuleColimitToDerived QisBPresheaf]
    (Ubullet : CosimplicialObject C)
    (hUbullet : CosimplicialObjectHasPointlikeHomSpaces Ubullet) :
    IsIsomorphic
      ((DerivedCategory.singleFunctor BPresheaf (0 : ℤ)) ⋙ Lπ![C, (ModuleCat B)])
      (cosimplicialEvaluationToDerived (ModuleCat B) Ubullet) := sorry

end Module

end CategoryTheory

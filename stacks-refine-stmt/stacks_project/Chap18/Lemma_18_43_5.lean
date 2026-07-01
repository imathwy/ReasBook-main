import Mathlib
import stacks_project.Chap12.Definition_12_10_1
import stacks_project.Chap18.Definition_18_43_1
import stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v w u₁

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Sets

variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

-- Proof sketch: work locally on the site and use the local triviality criterion from the previous
-- lemma to reduce a finite diagram of finite locally constant sheaves to a diagram of constant
-- finite sets. Finite limits of finite sets are finite, and the associated constant sheaf computes
-- the ambient sheaf limit locally.
/-- Lemma 18.43.5 (1): finite locally constant sheaves of sets are closed under finite limits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under limits of that shape. -/
theorem isFiniteLocallyConstant_isClosedUnderFiniteLimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K := sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderLimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderLimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderLimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteLimits K

-- Proof sketch: after local trivialization, a finite diagram becomes a diagram of constant sheaves
-- attached to finite sets. Finite colimits of finite sets are finite, so the ambient sheaf colimit
-- is again locally a constant finite sheaf.
/-- Lemma 18.43.5 (2): finite locally constant sheaves of sets are closed under finite colimits in
`Sh(\mathcal C)`, i.e. for every finite indexing category the corresponding object property is
stable under colimits of that shape. -/
theorem isFiniteLocallyConstant_isClosedUnderFiniteColimits
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K := sorry

/-- Finite locally constant sheaves of sets carry the canonical
`ObjectProperty.IsClosedUnderColimitsOfShape` instance for every finite indexing category. -/
instance isFiniteLocallyConstant_isClosedUnderColimitsOfShape
    (K : Type u₁) [SmallCategory K] [FinCategory K] :
    IsClosedUnderColimitsOfShape
      (fun F : Sheaf J (Type w) ↦ IsFiniteLocallyConstant F) K :=
  isFiniteLocallyConstant_isClosedUnderFiniteColimits K

end Sets

section AddCommGroups

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]

-- Proof sketch: apply the weak-Serre criterion recorded in the imported owner abstraction.
-- Kernels and cokernels are handled locally by trivializing maps, and extensions are checked after
-- refining to a cover where the end terms are constant finite abelian sheaves.
/-- Lemma 18.43.5 (3): finite locally constant abelian sheaves form a weak Serre subcategory of
`Ab(\mathcal C)`. -/
theorem isFiniteLocallyConstantAddCommGrp_isWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J AddCommGrpCat.{w} ↦ IsFiniteLocallyConstantAddCommGrp F) :=
  sorry

/-- Finite locally constant abelian sheaves carry their canonical weak-Serre instance. -/
instance isFiniteLocallyConstantAddCommGrp_instWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J AddCommGrpCat.{w} ↦ IsFiniteLocallyConstantAddCommGrp F) :=
  isFiniteLocallyConstantAddCommGrp_isWeakSerreClass

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

-- Proof sketch: again use the weak-Serre criterion. After local trivialization, kernels and
-- cokernels are kernels and cokernels of maps of finite type `\Lambda`-modules; the Noetherian
-- hypothesis guarantees these remain finite type, and the extension argument follows from the
-- pushout description in the source text.
/-- Lemma 18.43.5 (4): for a Noetherian ring `\Lambda`, locally constant sheaves of finite type
`\Lambda`-modules form a weak Serre subcategory of `Mod(\mathcal C, \Lambda)`. -/
theorem isFiniteTypeLocallyConstantModule_isWeakSerreClass :
    IsWeakSerreClass (fun F : Sheaf J (ModuleCat.{w} Λ) ↦ IsFiniteTypeLocallyConstantModule F) :=
  sorry

/-- Finite type locally constant module sheaves carry their canonical weak-Serre instance. -/
instance isFiniteTypeLocallyConstantModule_instWeakSerreClass :
    IsWeakSerreClass
      (fun F : Sheaf J (ModuleCat.{w} Λ) ↦ IsFiniteTypeLocallyConstantModule F) :=
  isFiniteTypeLocallyConstantModule_isWeakSerreClass

end Modules

end

end Sheaf
end CategoryTheory

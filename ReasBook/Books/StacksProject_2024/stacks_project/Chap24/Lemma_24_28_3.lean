import StacksProject_2024.stacks_project.Chap24.«24_28_0_1»
import StacksProject_2024.stacks_project.Chap24.Lemma_24_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uB vB uA vA uA' vA'

namespace DifferentialGradedModule

section

variable {ModB : Type uB} [Category.{vB} ModB] [Abelian ModB] [CategoryWithHomology ModB]
variable {ModA : Type uA} [Category.{vA} ModA] [Abelian ModA] [CategoryWithHomology ModA]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Abelian ModAprime]
variable [CategoryWithHomology ModAprime]
variable (pullback : ModB ⥤ ModA) [pullback.Additive]
variable (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]

local notation "KModB" => HomotopyCategory ModB (up ℤ)
local notation "KModA" => HomotopyCategory ModA (up ℤ)
local notation "KModAprime" => HomotopyCategory ModAprime (up ℤ)
local notation "DModB" => DerivedCategory ModB
local notation "DModA" => DerivedCategory ModA
local notation "DModAprime" => DerivedCategory ModAprime
local notation "QhB" => (DerivedCategory.Qh : KModB ⥤ DModB)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QisB" => HomotopyCategory.quasiIso ModB (up ℤ)
local notation "QisA" => HomotopyCategory.quasiIso ModA (up ℤ)

-- Semantic search note: `lean_leansearch` recalled `Functor.totalLeftDerived` and the
-- `Functor.HasLeftDerivedFunctor` owner. Nearby Chapter 24 files use
-- `pullbackTensorToDerived` and `leftDerivedPullback`, so this item states the identification at
-- that total-left-derived functor layer.

/-- The homotopy-category tensor-with-`\mathcal N` functor followed by localization to
`D(\mathcal A', \mathrm d)`. -/
abbrev tensorToDerived : KModA ⥤ DModAprime :=
  tensorWithN.mapHomotopyCategory (up ℤ) ⋙
    (DerivedCategory.Qh : KModAprime ⥤ DModAprime)

/-- The fixed-right-factor left derived tensor functor
`- \otimes_{\mathcal A}^{\mathbf L} \mathcal N`. -/
abbrev leftDerivedTensor
    [Functor.HasLeftDerivedFunctor (tensorToDerived tensorWithN) QisA] :
    DModA ⥤ DModAprime :=
  (tensorToDerived tensorWithN).totalLeftDerived QhA QisA

/-- Lemma 24.28.3: the left derived functor supplied by Lemma 24.28.1 for
`\mathcal M \mapsto f^*\mathcal M \otimes_{\mathcal A}\mathcal N` is the composite
`\mathcal M \mapsto Lf^*\mathcal M \otimes_{\mathcal A}^{\mathbf L}\mathcal N`. -/
@[stacks 0FTH]
theorem pullbackTensorLeftDerived_eq_leftDerivedPullback_comp_leftDerivedTensor
    [Functor.HasLeftDerivedFunctor (pullbackTensorToDerived pullback tensorWithN) QisB]
    [Functor.HasLeftDerivedFunctor (pullbackToDerived pullback) QisB]
    [Functor.HasLeftDerivedFunctor (tensorToDerived tensorWithN) QisA] :
    (pullbackTensorToDerived pullback tensorWithN).totalLeftDerived QhB QisB =
      leftDerivedPullback pullback ⋙ leftDerivedTensor tensorWithN := sorry

end

end DifferentialGradedModule

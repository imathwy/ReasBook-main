import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_15
import StacksProject_2024.stacks_project.Chap24.«24_28_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uB vB uA vA uA' vA'

namespace DifferentialGradedModule

section

variable {ModB : Type uB} [Category.{vB} ModB] [Abelian ModB] [CategoryWithHomology ModB]
variable {ModA : Type uA} [Category.{vA} ModA] [Preadditive ModA]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Abelian ModAprime]
variable [CategoryWithHomology ModAprime]
variable (pullback : ModB ⥤ ModA) [pullback.Additive]
variable (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]

local notation "KModB" => HomotopyCategory ModB (up ℤ)
local notation "QisB" => HomotopyCategory.quasiIso ModB (up ℤ)

-- Semantic search note: `lean_leansearch` recalled the canonical
-- `Functor.HasLeftDerivedFunctor`, `Functor.totalLeftDerived`, and
-- `Functor.ComputesLeftDerivedAt` owners. The Chapter 24 source-facing homotopy-category
-- composite and its localization-valued extension are owned by `24_28_0_1`, and this item
-- applies the Chapter 13 good-object criterion to that canonical owner.

/-- Lemma 24.28.1 (1): in the derived-pullback situation, if every object of
`K(\textit{Mod}(\mathcal B, \mathrm d))` admits a quasi-isomorphism from a good object and the
functor
`\mathcal P \mapsto f^*\mathcal P \otimes_{\mathcal A} \mathcal N` sends quasi-isomorphisms
between good objects to isomorphisms after localization in
`D(\mathcal A', \mathrm d)`, then its localization-valued homotopy functor has a left derived
extension `D(\mathcal B, \mathrm d) \to D(\mathcal A', \mathrm d)`. -/
@[stacks 0FTF]
theorem pullbackTensorToDerived_hasLeftDerivedFunctor_of_goodResolutions
    [(HomotopyCategory.quasiIso ModB (up ℤ)).IsSaturatedMultiplicativeSystem]
    (good : ObjectProperty KModB)
    (hgood_resolves : ∀ M : KModB, ∃ (P : KModB) (s : P ⟶ M), good P ∧ QisB s)
    (hgood_inverts :
      ∀ {P P' : KModB} (s : P ⟶ P'), good P → good P' → QisB s →
        IsIso ((pullbackTensorToDerived pullback tensorWithN).map s)) :
    (pullbackTensorToDerived pullback tensorWithN).HasLeftDerivedFunctor QisB := sorry

/-- Lemma 24.28.1 (2): under the same good-resolution and good-object invariance hypotheses, a
good right differential graded `\mathcal B`-module `\mathcal P` computes the left derived
extension of
`\mathcal P \mapsto f^*\mathcal P \otimes_{\mathcal A} \mathcal N`; equivalently, the derived
value at `\mathcal P` is represented by the ordinary object
`f^*\mathcal P \otimes_{\mathcal A} \mathcal N` in `D(\mathcal A', \mathrm d)`. -/
@[stacks 0FTF]
theorem pullbackTensorToDerived_computesLeftDerivedAt_of_good
    [(HomotopyCategory.quasiIso ModB (up ℤ)).IsSaturatedMultiplicativeSystem]
    (good : ObjectProperty KModB)
    (hgood_resolves : ∀ M : KModB, ∃ (P : KModB) (s : P ⟶ M), good P ∧ QisB s)
    (hgood_inverts :
      ∀ {P P' : KModB} (s : P ⟶ P'), good P → good P' → QisB s →
        IsIso ((pullbackTensorToDerived pullback tensorWithN).map s))
    {P : KModB} (hP : good P) :
    (pullbackTensorToDerived pullback tensorWithN).ComputesLeftDerivedAt QisB P := sorry

end

end DifferentialGradedModule

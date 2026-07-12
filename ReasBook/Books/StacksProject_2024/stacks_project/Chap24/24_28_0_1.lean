import Mathlib.CategoryTheory.IsomorphismClasses
import StacksProject_2024.Chap13.Lemma_13_14_16_Homotopy

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe uB vB uA vA uA' vA'

namespace DifferentialGradedModule

section

variable {ModB : Type uB} [Category.{vB} ModB] [Preadditive ModB]
variable {ModA : Type uA} [Category.{vA} ModA] [Preadditive ModA]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Preadditive ModAprime]

local notation "KModB" => HomotopyCategory ModB (up ℤ)
local notation "KModAprime" => HomotopyCategory ModAprime (up ℤ)

-- Owner choice: this is the source-facing Chapter 24 homotopy-category composite used directly by
-- `Lemma_24_28_1` and `Definition_24_28_2`. The public owner is the composite of the canonical
-- homotopy-category lifts of pullback and tensor; the comparison with the single lift of the
-- composite functor is the canonical Chapter 13 bridge `Functor.mapHomotopyCategoryCompIso`.

/-- 24.28.0.1: the homotopy-category pullback-then-tensor functor
`K(\textit{Mod}(\mathcal B, d)) ⥤ K(\textit{Mod}(\mathcal A', d))`,
`\mathcal M ↦ f^* \mathcal M \otimes_{\mathcal A} \mathcal N`,
attached to a chosen pullback functor and a chosen tensor-with-`\mathcal N` functor. -/
@[stacks 0FTE]
def pullbackTensorHomotopyFunctor
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive] :
    KModB ⥤ KModAprime :=
  pullback.mapHomotopyCategory (up ℤ) ⋙ tensorWithN.mapHomotopyCategory (up ℤ)

@[simp] theorem pullbackTensorHomotopyFunctor_obj
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]
    (M : KModB) :
    (pullbackTensorHomotopyFunctor pullback tensorWithN).obj M =
      (tensorWithN.mapHomotopyCategory (up ℤ)).obj
        ((pullback.mapHomotopyCategory (up ℤ)).obj M) :=
  rfl

@[simp] theorem pullbackTensorHomotopyFunctor_map
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]
    {M M' : KModB} (f : M ⟶ M') :
    (pullbackTensorHomotopyFunctor pullback tensorWithN).map f =
      (tensorWithN.mapHomotopyCategory (up ℤ)).map
        ((pullback.mapHomotopyCategory (up ℤ)).map f) :=
  rfl

/- Bridge/view: `pullbackTensorHomotopyFunctor` is the Chapter 24 source-facing owner, while the
single homotopy-category lift of `pullback ⋙ tensorWithN` is the canonical core owner provided by
Chapter 13. Since the Chapter 13 comparison isomorphism is presently proof-backed, this file keeps
the bridge at the proposition-level owner `IsIsomorphic` rather than exporting `Iso` data. -/
theorem pullbackTensorHomotopyFunctor_isIsomorphic
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive] :
    IsIsomorphic
      (pullbackTensorHomotopyFunctor pullback tensorWithN)
      ((pullback ⋙ tensorWithN).mapHomotopyCategory (up ℤ)) :=
by
  exact ⟨(Functor.mapHomotopyCategoryCompIso pullback tensorWithN).symm⟩

end

section

variable {ModB : Type uB} [Category.{vB} ModB] [Preadditive ModB]
variable {ModA : Type uA} [Category.{vA} ModA] [Preadditive ModA]
variable {ModAprime : Type uA'} [Category.{vA'} ModAprime] [Abelian ModAprime]
variable [CategoryWithHomology ModAprime]

local notation "KModB" => HomotopyCategory ModB (up ℤ)
local notation "KModAprime" => HomotopyCategory ModAprime (up ℤ)
local notation "DModAprime" => DerivedCategory ModAprime
local notation "QhAprime" => (DerivedCategory.Qh : KModAprime ⥤ DModAprime)

/-- The localization-valued extension of `pullbackTensorHomotopyFunctor`, obtained by composing
with the canonical functor `K(\textit{Mod}(\mathcal A', \mathrm d)) \to
D(\textit{Mod}(\mathcal A', \mathrm d))`. -/
def pullbackTensorToDerived
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive] :
    KModB ⥤ DModAprime :=
  pullbackTensorHomotopyFunctor pullback tensorWithN ⋙ QhAprime

omit [CategoryWithHomology ModAprime] in
@[simp] theorem pullbackTensorToDerived_obj
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]
    (M : KModB) :
    (pullbackTensorToDerived pullback tensorWithN).obj M =
      DerivedCategory.Qh.obj ((pullbackTensorHomotopyFunctor pullback tensorWithN).obj M) :=
  rfl

omit [CategoryWithHomology ModAprime] in
@[simp] theorem pullbackTensorToDerived_map
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive]
    {M M' : KModB} (f : M ⟶ M') :
    (pullbackTensorToDerived pullback tensorWithN).map f =
      DerivedCategory.Qh.map ((pullbackTensorHomotopyFunctor pullback tensorWithN).map f) :=
  rfl

/- Bridge/view: whiskering the Chapter 13 composition comparison with localization identifies the
source-facing localization-valued owner with the localization of the single composite lift. As
above, this remains a theorem-level `IsIsomorphic` bridge rather than public `Iso` data. -/
omit [CategoryWithHomology ModAprime] in
theorem pullbackTensorToDerived_isIsomorphic
    (pullback : ModB ⥤ ModA) [pullback.Additive]
    (tensorWithN : ModA ⥤ ModAprime) [tensorWithN.Additive] :
    IsIsomorphic
      (pullbackTensorToDerived pullback tensorWithN)
      (((pullback ⋙ tensorWithN).mapHomotopyCategory (up ℤ)) ⋙ QhAprime) :=
by
  exact
    ⟨Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso pullback tensorWithN).symm
      QhAprime⟩

end

end DifferentialGradedModule

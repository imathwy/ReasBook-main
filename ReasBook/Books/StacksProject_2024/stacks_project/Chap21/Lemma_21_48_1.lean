import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap15.Lemma_15_58_1
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)] [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ringedSiteModuleCategory J 𝒪),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X)]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  PreservesColimit (Functor.empty.{0} (ringedSiteModuleCategory J 𝒪))
    ((curriedTensor (ringedSiteModuleCategory J 𝒪)).flip.obj X)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

/- Domain-style sampling for Lemma 21.48.1:
- primary domain: the symmetric monoidal structure on cochain complexes of sheaves of
  `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  the Chapter 15 owner instance `SymmetricCategory (CochainComplex C ℤ)`,
  `SymmetricCategory`,
  `SymmetricCategory.symmetry`;
- best owner abstraction: `SymmetricCategory Cpx`;
- primitive data: the ambient owner category `ringedSiteModuleCategory J 𝒪` and the monoidal
  symmetric/additive tensor data on it required by the Chapter 15 cochain-complex owner;
- derived API: the canonical braiding `β_` and its symmetry theorem
  `SymmetricCategory.symmetry`.

Source/core/bridge triage:
- `source-facing`: cochain complexes of sheaves of `𝒪`-modules on a ringed site form a
  symmetric monoidal category for total-complex tensor product;
- `core/canonical`: `SymmetricCategory Cpx`;
- `bridge/view`: the canonical braiding symmetry equation on `Cpx`.

This item is recall-only. The previous local `RingedSiteModules` alias, braiding wrapper, and
renamed symmetry theorem duplicated the chapter owner and mathlib owner API without adding new
mathematics, so they are removed in favor of direct recall of the chapter owner
`cochainComplexSymmetricCategory`, specialized to `Cpx`.
-/

/- Lemma 21.48.1: the statement that cochain complexes of sheaves of `𝒪`-modules on a
ringed site form a symmetric monoidal category for total-complex tensor product is the
Chapter 15 owner `cochainComplexSymmetricCategory`, specialized in this file to
`Cpx = CochainComplex Mod ℤ`. -/
recall cochainComplexSymmetricCategory

/- Specialized check for Lemma 21.48.1 on cochain complexes of sheaves of `𝒪`-modules. -/
#check (inferInstance : SymmetricCategory Cpx)

end

end SheafOfModules.RingedSite

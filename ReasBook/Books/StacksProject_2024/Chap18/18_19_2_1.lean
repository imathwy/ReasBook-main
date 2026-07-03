import Mathlib
import stacks_project.Chap18.Lemma_18_27_9
import stacks_project.Chap18.Lemma_18_28_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u}) (U : C)
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for 18.19.2.1:
- primary domain: extension by zero and restriction for sheaves of modules on a localized ringed
  site;
- sampled owner declarations:
  `localizedStructureModuleExtensionByZero`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `SheafOfModules.unitHomEquiv`;
- best owner abstraction: the chapter-standard summand
  `localizedStructureModuleExtensionByZero 𝒪 U = j_{U!}\mathcal O_U`, with the source-facing
  bijection derived from the core adjunction
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- primitive data: the ringed site `(\mathcal C, J, \mathcal O)`, the object `U : C`, the
  localized structure module `\mathcal O_U`, and the module sheaf `\mathcal F`;
- derived API: the source-facing bijection
  `Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)`.

Source/core/bridge triage:
- `source-facing`: the canonical bijection
  `Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)`;
- `core/canonical`: the owner adjunction
  `SheafOfModules.pullbackPushforwardAdjunction
    (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))`;
- `bridge/view`: the standard summand owner `localizedStructureModuleExtensionByZero 𝒪 U` and
  the canonical identification of global sections of `ℱ.over U` with evaluation at the terminal
  object `(\mathrm{id}_U : U \to U)` of `C/U`.

This file therefore reuses the chapter owner `localizedStructureModuleExtensionByZero` for
`j_{U!}\mathcal O_U` and derives the source-facing bijection from the localized adjunction rather
than keeping a second public wrapper for the same module. -/

private noncomputable def localizedSectionsEquivEvaluation (ℱ : Mod) :
    (SheafOfModules.over ℱ U).sections ≃
      (SheafOfModules.evaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) (op U)).obj ℱ where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
  invFun m :=
    (SheafOfModules.over ℱ U).val.sectionsMk
      (fun X ↦ (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from X.unop).op) m)
      (fun (X Y : (Over U)ᵒᵖ) (f : X ⟶ Y) ↦ by
        have h :
            (Over.mkIdTerminal.from X.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from X.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    ext X
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from X.unop).op)
  right_inv m := by
    change
      (SheafOfModules.over ℱ U).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using
      (SheafOfModules.over ℱ U).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/- Lemma 18.19.2.1, owner form: the source-facing bijection is the composite of the localized
adjunction Hom-equivalence, `SheafOfModules.unitHomEquiv` on `ℱ.over U`, and the terminal-object
identification of localized global sections with evaluation at `U`. -/
/-- 18.19.2.1: for a ringed site `(\mathcal C, \mathcal O)`, an object `U : \mathcal C`, and an
`\mathcal O`-module sheaf `\mathcal F`, there is a canonical bijection
`Hom_{\mathcal O}(j_{U!}\mathcal O_U, \mathcal F) ≃ \mathcal F(U)`. -/
noncomputable def localizedStructureModuleExtensionByZero_homEquiv
    (ℱ : Mod) :
    (localizedStructureModuleExtensionByZero 𝒪 U ⟶ ℱ) ≃
    (SheafOfModules.evaluation ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪) (op U)).obj ℱ :=
  (((SheafOfModules.pullbackPushforwardAdjunction
      (𝟙 (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U))).homEquiv
      (SheafOfModules.unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪).over U)) ℱ).trans
    (SheafOfModules.over ℱ U).unitHomEquiv).trans
    (localizedSectionsEquivEvaluation J 𝒪 U ℱ)

end SheafOfModules.RingedSite

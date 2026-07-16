import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v}) (U : C)

/- Domain-style sampling for Lemma 18.19.2:
- primary domain: localized restriction and extension by zero for sheaves of modules on a ringed
  site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `ringSheaf`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardOver`,
  `SheafOfModules.overPushforwardOverAdj`;
- best owner abstraction: the canonical localized adjunction
  `SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U`;
- primitive data: the ringed site `((C, J), \mathcal O)` and the object `U : C`;
- derived API: the source-facing localized restriction and extension-by-zero functors.

Source/core/bridge triage:
- `core/canonical`: the owner module `stacks_project.Chap18.RingedSiteModuleCategory` together
  with `SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U`;
- `source-facing`: the localized functors `j_U^*` and `j_{U!}`;
- `bridge/view`: the chapter owner names below.

This file reuses the canonical owner declarations `ringSheaf` and `ringedSiteModuleCategory`
from `RingedSiteModuleCategory` and adds only the source-facing localized functors. -/

/-- Restriction from the ambient ringed site `((C, J), \mathcal O)` to the localized ringed site
`((C/U, J.over U), \mathcal O_U)`. -/
abbrev ringedSiteLocalizedRestriction :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory (J.over U) (𝒪.over U) :=
  SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))

instance : (ringedSiteLocalizedRestriction J 𝒪 U).IsLeftAdjoint := by
  exact (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U).isLeftAdjoint

/-- Extension by zero from the localized ringed site `((C/U, J.over U), \mathcal O_U)` back to
the ambient ringed site `((C, J), \mathcal O)`. -/
abbrev ringedSiteLocalizedExtensionByZero :
    ringedSiteModuleCategory (J.over U) (𝒪.over U) ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := ringSheaf J 𝒪) U)

instance :
    (ringedSiteLocalizedExtensionByZero J 𝒪 U).PreservesZeroMorphisms := by
  refine ⟨fun A B ↦ ?_⟩
  rfl

instance : (ringedSiteLocalizedExtensionByZero J 𝒪 U).IsRightAdjoint := by
  exact (SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U).isRightAdjoint

/- Lemma 18.19.2: on the localized ringed site `(C/U, J.over U, \mathcal O_U)`, the restriction
and extension-by-zero functors are the left and right sides of the canonical localized adjunction
`SheafOfModules.overPushforwardOverAdj (R := ringSheaf J 𝒪) U`. -/

end

end SheafOfModules.RingedSite

export SheafOfModules.RingedSite
  (ringedSiteLocalizedExtensionByZero ringedSiteLocalizedRestriction)

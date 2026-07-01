import Mathlib
import stacks_project.Chap18.Definition_18_28_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.28.6:
- primary domain: flat sheaves of modules on a ringed site and their localized restrictions;
- sampled owner declarations:
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero_isFlat`,
  `PresheafOfModules.sheafification_isFlat`,
  `SheafOfModules.RingedSite.pullback_isFlat_of_isFlat`;
- best owner abstraction: the chapter owner `SheafOfModules.RingedSite.IsFlat`; the restriction
  `ℱ.over U` should be expressed by the same owner on `𝒪.over U`, not by a parallel exactness
  predicate on `tensorLeft`;
- primitive data: the sheaf of rings `𝒪`, the sheaf of modules `ℱ`, and the localized object
  `U : C`;
- derived API: flatness of the localized restriction `ℱ.over U`.

Source/core/bridge triage:
- `source-facing`: flatness of the restriction `ℱ|_U`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat`;
- `bridge/view`: the restriction operation `ℱ ↦ ℱ.over U`. -/
-- Proof sketch: let `𝒢₁ ⟶ 𝒢₂ ⟶ 𝒢₃` be an exact short complex of `\mathcal O_U`-modules. Apply
-- extension by zero `j_{U!}`, which is exact by Lemma `18.19.3`, identify
-- `j_{U!} (𝒢ᵢ ⊗ ℱ|_U)` with `j_{U!} 𝒢ᵢ ⊗ ℱ` using Lemma `18.27.9`, use flatness of `ℱ`, and
-- then reflect exactness back to the localized site by Lemma `18.19.4`.
/-- Lemma 18.28.6: if `ℱ` is a flat `\mathcal O`-module on a ringed site
`(\mathcal C, \mathcal O)`, then for every object `U : \mathcal C` the restricted module
`ℱ|_U`, written `ℱ.over U`, is flat on the localized ringed site
`(\mathcal C/U, \mathcal O_U)`, expressed in the chapter's canonical owner
`SheafOfModules.RingedSite.IsFlat`. -/
theorem isFlat_over
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) (ℱ : SheafOfModules (ringSheaf J 𝒪))
    [IsFlat 𝒪 ℱ] :
    IsFlat (𝒪.over U) (ℱ.over U) := sorry

end SheafOfModules.RingedSite

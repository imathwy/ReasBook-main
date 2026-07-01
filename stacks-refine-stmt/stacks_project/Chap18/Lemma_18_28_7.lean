import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Over
import stacks_project.Chap18.Definition_18_28_1
import stacks_project.Chap18.Lemma_18_28_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u

/-- The localized ring presheaf on the slice category `C/U`. -/
abbrev localizedRingPresheaf {C : Type u} [Category.{u} C]
    (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C) :
    (Over U)ᵒᵖ ⥤ RingCat.{u} :=
  (Over.forget U).op ⋙ 𝒪

/-- Extension by zero from presheaves of modules over the localized ring presheaf on `C/U`. -/
abbrev presheafLocalizedExtensionByZero {C : Type u} [Category.{u} C]
    (𝒪 : Cᵒᵖ ⥤ RingCat.{u}) (U : C) :
    PresheafOfModules (localizedRingPresheaf 𝒪 U) ⥤ PresheafOfModules 𝒪 :=
  PresheafOfModules.pullback (𝟙 (localizedRingPresheaf 𝒪 U))

namespace PresheafOfModules

variable {C : Type u} [Category.{u} C]

/-- The localized structure module `\mathcal O_U` on the slice category `C/U`, regarded as a
module over the localized ring presheaf. -/
abbrev localizedStructureModule
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (localizedRingPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat) U) :=
  PresheafOfModules.unit (localizedRingPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat) U)

/-- The presheaf `j_{U!}\mathcal O_U` obtained by extending the localized structure module by zero
from `C/U` back to `C`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat) :=
  (presheafLocalizedExtensionByZero (𝒪 ⋙ forget₂ CommRingCat RingCat) U).obj
    (localizedStructureModule 𝒪 U)

-- Proof sketch: evaluate `j_{U!}\mathcal O_U` at an object `V`. By Remark `18.19.7` this section
-- module is the coproduct over all arrows `V ⟶ U` of copies of `\mathcal O(V)`, hence is a free,
-- in particular flat, `\mathcal O(V)`-module. Then apply Lemma `18.28.2`.
/-- Lemma 18.28.7 (1): for a presheaf of commutative rings `\mathcal O` on a category
`\mathcal C` and an object `U : \mathcal C`, the lower-shriek module `j_{U!}\mathcal O_U` is flat
as a presheaf of `\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (U : C) :
    IsFlat (localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end PresheafOfModules

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

/-- The localized structure module `\mathcal O_U` on the slice site `(C/U, J.over U)`, extended
by zero to a sheaf of `\mathcal O`-modules on `(C, J)`. -/
abbrev localizedStructureModuleExtensionByZero
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    SheafOfModules (ringSheaf J 𝒪) :=
  (SheafOfModules.pullback (𝟙 ((ringSheaf J 𝒪).over U))).obj
    (SheafOfModules.unit ((ringSheaf J 𝒪).over U))

-- Proof sketch: on the localized site, tensoring with `\mathcal O_U` is the identity functor.
-- Lemma `18.27.9` identifies tensoring with `j_{U!}\mathcal O_U` on `(C, J)` with extension by
-- zero `j_{U!}`, and Lemma `18.19.3` shows that extension by zero is exact. Hence tensoring with
-- `j_{U!}\mathcal O_U` is exact, i.e. `j_{U!}\mathcal O_U` is flat.
/-- Lemma 18.28.7 (2): if `(\mathcal C, J)` is a site and `\mathcal O` is a sheaf of
commutative rings on it, then the lower-shriek module `j_{U!}\mathcal O_U` is a flat sheaf of
`\mathcal O`-modules. -/
theorem localizedStructureModuleExtensionByZero_isFlat
    (𝒪 : Sheaf J CommRingCat.{u}) (U : C) :
    IsFlat 𝒪 (localizedStructureModuleExtensionByZero 𝒪 U) := sorry

end SheafOfModules.RingedSite

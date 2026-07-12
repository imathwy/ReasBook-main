import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)
local notation "𝒪X" => SheafOfModules.unit (RingedSpace.ringCatSheaf X)

/- Domain-style sampling for Definition 17.23.1:
- primary domain: annihilator sheaves of modules on a ringed space, expressed through the
  monoidal closed structure on `SheafOfModules (RingedSpace.ringCatSheaf X)`;
- sampled owner declarations:
  `AlgebraicGeometry.ringedSpaceRingCatSheaf`,
  `(RingedSpace.ringCatSheaf AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.unit`,
  `PresheafOfModules.sheafificationAdjunction`,
  `MonoidalClosed.id`,
  `kernel`;
- best owner abstraction:
  the ambient owner is the existing chapter ringed-space coefficient sheaf `(RingedSpace.ringCatSheaf X)`, and
  the source-facing annihilator object should be the categorical kernel in
  `ModX` of the canonical map from the structure sheaf `𝒪X` to `(ihom ℱ).obj ℱ`;
- primitive data: a module sheaf `ℱ`;
- derived API: the canonical comparison isomorphism `unitIsoTensorUnit`, the action map
  `selfInternalHomUnitMap ℱ`, the canonical inclusion `annihilatorι ℱ : annihilator ℱ ⟶ 𝒪X`,
  and the sectionwise bridge `annihilatorSectionImage`.

Source/core/bridge triage:
- `source-facing`: the annihilator sheaf `annihilator ℱ`;
- `core/canonical`: the ambient module category `ModX`, `𝒪X`, `ihom`, and categorical kernels;
- `bridge/view`: the canonical comparison isomorphism `unitIsoTensorUnit : 𝒪X ≅ 𝟙_ ModX`,
  obtained from the sheafification counit for the presheaf-side unit model of the tensor unit;
  this yields the action map `selfInternalHomUnitMap ℱ`, the resulting inclusion
  `annihilatorι ℱ`, and the sectionwise inclusion `annihilatorSectionImage`.

This file therefore keeps `annihilator` as the source-facing owner and reuses the chapter owner
`(RingedSpace.ringCatSheaf X)` from Definition `17.4.1`, together with the canonical internal-hom
identity map `MonoidalClosed.id ℱ`. The bridge to the ambient tensor unit is the canonical
sheafification-counit comparison, not an equality identification with `𝒪X`. -/

section

variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

/-- The canonical map `\mathcal O_X \to
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)` whose kernel is the annihilator
sheaf. -/
noncomputable def selfInternalHomUnitMap (ℱ : ModX) : 𝒪X ⟶ (ihom ℱ).obj ℱ :=
  unitIsoTensorUnit.hom ≫ MonoidalClosed.id ℱ

/-- Definition 17.23.1: the annihilator of an `\mathcal O_X`-module `\mathcal F` is the kernel
of the canonical map `\mathcal O_X \to \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F,
\mathcal F)`. -/
abbrev annihilator (ℱ : ModX) : ModX :=
  kernel (selfInternalHomUnitMap ℱ)

namespace AnnihilatorSheaf

scoped notation:max "Ann(" ℱ ")" => SheafOfModules.annihilator ℱ

end AnnihilatorSheaf

open scoped AnnihilatorSheaf

/-- The annihilator sheaf carries its canonical inclusion into the structure sheaf. -/
noncomputable abbrev annihilatorι (ℱ : ModX) : Ann(ℱ) ⟶ 𝒪X :=
  kernel.ι (selfInternalHomUnitMap ℱ)

/-- A local section of the annihilator sheaf, regarded as a section of the structure sheaf via the
kernel inclusion. -/
abbrev annihilatorSectionImage (ℱ : ModX) (U : Opens X)
    (s : (Ann(ℱ)).val.obj (op U)) : X.presheaf.obj (op U) :=
  unitSectionToRingSection U ((annihilatorι ℱ).val.app (op U) s)

end

end SheafOfModules

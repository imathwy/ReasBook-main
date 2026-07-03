import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.Definition_17_4_1

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
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

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
- derived API: the canonical inclusion `annihilatorι ℱ : annihilator ℱ ⟶ 𝒪X`, and the
  sectionwise bridge `annihilatorSectionImage`.

Source/core/bridge triage:
- `source-facing`: the annihilator sheaf `annihilator ℱ`;
- `core/canonical`: the ambient module category `ModX`, `𝒪X`, `ihom`, and categorical kernels;
- `bridge/view`: the canonical comparison isomorphism `unitIsoTensorUnit : 𝒪X ≅ 𝟙_ ModX`,
  obtained from the sheafification counit for the presheaf-side unit model of the tensor unit;
  this yields the comparison morphism `unitToTensorUnit`, the resulting inclusion
  `annihilatorι ℱ`, and the sectionwise inclusion `annihilatorSectionImage`.

This file therefore keeps `annihilator` as the source-facing owner and reuses the chapter owner
`(RingedSpace.ringCatSheaf X)` from Definition `17.4.1`, together with the canonical internal-hom
identity map `MonoidalClosed.id ℱ`. The bridge to the ambient tensor unit is the canonical
sheafification-counit comparison, not an equality identification with `𝒪X`. -/

private abbrev tensorUnitModel : ModX :=
  ((SheafOfModules.forget (RingedSpace.ringCatSheaf X) ⋙
      PresheafOfModules.restrictScalars (𝟙 (RingedSpace.ringCatSheaf X).obj)) ⋙
    PresheafOfModules.sheafification (𝟙 (RingedSpace.ringCatSheaf X).obj)).obj 𝒪X

-- Proof sketch: the chosen tensor unit in the ambient monoidal structure on `ModX` is the
-- sheafification of the presheaf-side free rank-one module. This is the same owner as the object
-- underlying the counit comparison below.
private theorem tensorUnitModel_eq_tensorUnit :
    tensorUnitModel = (𝟙_ ModX : ModX) := by
  sorry

/-- The canonical comparison isomorphism from the structure sheaf owner `\mathcal O_X` to the
ambient tensor unit in `SheafOfModules (RingedSpace.ringCatSheaf X)`. -/
noncomputable def unitIsoTensorUnit : 𝒪X ≅ 𝟙_ ModX :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (RingedSpace.ringCatSheaf X).obj)).counit.app 𝒪X)).symm ≪≫
    eqToIso tensorUnitModel_eq_tensorUnit

/-- The canonical comparison morphism from the structure sheaf owner `\mathcal O_X` to the
ambient tensor unit in `SheafOfModules (RingedSpace.ringCatSheaf X)`. -/
noncomputable abbrev unitToTensorUnit : 𝒪X ⟶ 𝟙_ ModX :=
  unitIsoTensorUnit.hom

/-- The canonical map `\mathcal O_X \to
\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)` whose kernel is the annihilator
sheaf. -/
noncomputable def selfInternalHomUnitMap (ℱ : ModX) : 𝒪X ⟶ (ihom ℱ).obj ℱ :=
  unitToTensorUnit ≫ MonoidalClosed.id ℱ

/-- Definition 17.23.1: the annihilator of an `\mathcal O_X`-module `\mathcal F` is the kernel
of the canonical map `\mathcal O_X \to \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F,
\mathcal F)`. -/
abbrev annihilator (ℱ : ModX) : ModX :=
  kernel (selfInternalHomUnitMap ℱ)

/-- The annihilator sheaf is definitionally the kernel of the canonical action map
`\mathcal O_X \to \mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal F)`. -/
theorem annihilator_eq_kernel (ℱ : ModX) :
    annihilator ℱ = kernel (selfInternalHomUnitMap ℱ) :=
  rfl

/-- The annihilator sheaf carries its canonical inclusion into the structure sheaf. -/
noncomputable abbrev annihilatorι (ℱ : ModX) : annihilator ℱ ⟶ 𝒪X :=
  kernel.ι (selfInternalHomUnitMap ℱ)

/-- The annihilator sheaf, viewed canonically as a subobject of the structure sheaf. -/
noncomputable abbrev annihilatorSubobject (ℱ : ModX) : Subobject 𝒪X :=
  Subobject.mk (annihilatorι ℱ)

/-- A local section of the annihilator sheaf, regarded as a section of the structure sheaf via the
kernel inclusion. -/
abbrev annihilatorSectionImage (ℱ : ModX) (U : Opens X)
    (s : (annihilator ℱ).val.obj (op U)) : X.presheaf.obj (op U) :=
  unitSectionToRingSection U ((annihilatorι ℱ).val.app (op U) s)

end SheafOfModules

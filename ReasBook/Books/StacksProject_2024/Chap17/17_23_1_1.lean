import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import StacksProject_2024.Chap17.Definition_17_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open Opposite
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

/- Domain-style sampling for 17.23.1.1:
- primary domain: annihilator sheaves of `\mathcal O_X`-modules and their stalkwise action;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.stalkModuleCat`,
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`,
  `SheafOfModules.annihilator`,
  `SheafOfModules.annihilatorι`;
- best owner abstraction:
  the source-facing annihilator sheaf should reuse `SheafOfModules.annihilator`, while the stalk
  module should be expressed through `AlgebraicGeometry.RingedSpace.stalkModuleCat`, the
  structure-sheaf stalk should be reached through the owner bridge
  `AlgebraicGeometry.RingedSpace.unitStalkLinearMap`; the stalk-side source item should therefore
  be packaged as the ideal cut out by the stalk map induced by `SheafOfModules.annihilatorι`;
- primitive data:
  a module sheaf `ℱ` and a point `x`;
- derived API:
  stalk-element and germwise membership statements obtained from the stalk-ideal inclusion.

Source/core/bridge triage:
- `source-facing`: the stalk-ideal inclusion
  `(Ann_{\mathcal O_X}(\mathcal F))_x \subset Ann_{\mathcal O_{X, x}}(\mathcal F_x)`;
- `core/canonical`: `SheafOfModules.annihilator`, `RingedSpace.stalkModuleCat`, and
  `RingedSpace.unitStalkLinearMap`;
- `bridge/view`: `SheafOfModules.annihilatorSectionImage`,
  `SheafOfModules.unitStalkLinearMap_germ`, and the elementwise/germwise membership lemmas, which
  turn the stalk-ideal inclusion into local-section statements. -/

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]
variable [MonoidalClosed (SheafOfModules.{u} (RingedSpace.ringCatSheaf X))]

local notation "ModX" => SheafOfModules (RingedSpace.ringCatSheaf X)

/-- The ideal of the stalk ring `\mathcal O_{X, x}` cut out by the stalk of the annihilator sheaf
of `\mathcal F`. -/
noncomputable def annihilatorStalkIdeal (ℱ : ModX) (x : X) : Ideal (X.presheaf.stalk x) :=
  show Ideal (X.presheaf.stalk x) from
    LinearMap.range ((RingedSpace.moduleStalkHom x (annihilatorι ℱ) ≫
      RingedSpace.unitStalkLinearMap x).hom)

-- Proof sketch: first pass from the stalk of `annihilator ℱ` to the stalk of the unit
-- `\mathcal O_X`-module via `RingedSpace.moduleStalkHom x (annihilatorι ℱ)`, then identify that
-- stalk with `\mathcal O_{X,x}` through `RingedSpace.unitStalkLinearMap x`. Because sections of
-- `annihilator ℱ` lie in the kernel of the action map, the resulting stalk scalar acts by zero on
-- every element of `ℱ_x`, hence lies in `Module.annihilator (\mathcal O_{X,x}) (ℱ_x)`.
/-- Companion bridge: the canonical image of a stalk element of
`\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` in `\mathcal O_{X, x}` lies in the annihilator
ideal of the stalk `\mathcal F_x`. -/
theorem stalk_annihilatorImage_mem_stalk_annihilator
    (ℱ : ModX) (x : X)
    (t : RingedSpace.stalkModuleCat (annihilator ℱ) x) :
    RingedSpace.unitStalkLinearMap x (RingedSpace.moduleStalkHom x (annihilatorι ℱ) t) ∈
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := sorry

/-- 17.23.1.1: the ideal of the stalk ring `\mathcal O_{X, x}` cut out by the stalk of the
annihilator sheaf `\operatorname{Ann}_{\mathcal O_X}(\mathcal F)` is contained in the annihilator
ideal of the stalk module `\mathcal F_x`. This is the stalkwise inclusion
`(\operatorname{Ann}_{\mathcal O_X}(\mathcal F))_x \subset
\operatorname{Ann}_{\mathcal O_{X, x}}(\mathcal F_x)`. -/
theorem annihilatorStalkIdeal_le_module_annihilator (ℱ : ModX) (x : X) :
    annihilatorStalkIdeal ℱ x ≤
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  rintro _ ⟨t, rfl⟩
  exact stalk_annihilatorImage_mem_stalk_annihilator ℱ x t

/-- Companion bridge: if `s` is a local section of the annihilator sheaf near `x`, then its germ
in `\mathcal O_{X, x}` lies in the annihilator ideal of the stalk `\mathcal F_x`. -/
theorem germ_annihilator_mem_stalk_annihilator (ℱ : ModX) (x : X)
    (U : Opens X) (hx : x ∈ U) (s : (annihilator ℱ).val.obj (op U)) :
    X.presheaf.germ U x hx (annihilatorSectionImage ℱ U s) ∈
      Module.annihilator (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x) := by
  have hmap :
      RingedSpace.moduleStalkHom x (annihilatorι ℱ)
          (TopCat.Presheaf.germ (annihilator ℱ).val.presheaf U x hx s) =
        TopCat.Presheaf.germ (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).val.presheaf U x
          hx ((annihilatorι ℱ).val.app (op U) s) := by
    simpa [RingedSpace.moduleStalkHom] using
      (RingedSpace.moduleStalkMap_germ x (annihilatorι ℱ) U hx s)
  have hmem :=
    stalk_annihilatorImage_mem_stalk_annihilator ℱ x
      (TopCat.Presheaf.germ (annihilator ℱ).val.presheaf U x hx s)
  rw [hmap, unitStalkLinearMap_germ] at hmem
  simpa [annihilatorSectionImage] using hmem

end SheafOfModules

import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.Lemma_18_32_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.25.8:
- primary domain: categorical smallness of invertible `\mathcal O_X`-modules on a ringed space,
  expressed as a set of representatives up to isomorphism;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.invertibleModuleProperty_essentiallySmall`,
  `CategoryTheory.ObjectProperty.EssentiallySmall.exists_small`;
- best owner abstraction: the object property
  `(IsInvertible : ObjectProperty (RingedSpace.Modules X))` on the canonical ringed-space module
  category;
- primitive data: a ringed space `X` and the canonical invertibility owner `IsInvertible` on
  `RingedSpace.Modules X`;
- derived API: a set of representatives extracted from the canonical
  `ObjectProperty.EssentiallySmall.exists_small` skeleton construction.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertion that invertible `\mathcal O_X`-modules admit a
  set of invertible representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.EssentiallySmall
    ((IsInvertible : ObjectProperty (RingedSpace.Modules X)))`;
- `bridge/view`: the opens-site specialization from the Chapter 18 ringed-site owner theorem to
  the canonical ringed-space module category.
-/

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦
    Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))
local notation "PInv" => (IsInvertibleX : ObjectProperty ModX)

variable [MonoidalCategory (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf)]

/- Lemma 17.25.8: on a ringed space `X`, there is a set of invertible `\mathcal O_X`-modules
containing exactly one representative of each isomorphism class of invertible modules. This is the
opens-site specialization of the Chapter 18 owner theorem. -/
theorem exists_set_of_invertible_module_representatives :
    ∃ S : Set ModX,
      (∀ 𝒩 ∈ S, IsInvertibleX 𝒩) ∧
      ∀ (ℒ : ModX) [IsInvertibleX ℒ],
        ∃! 𝒩 : ModX, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℒ) := by
  simpa using
    (SheafOfModules.RingedSite.exists_set_of_invertible_module_representatives
      (J := Opens.grothendieckTopology X) X.sheaf)

end AlgebraicGeometry.RingedSpace

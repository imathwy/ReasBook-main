import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap04.Lemma_4_43_3
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : ModX)
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦
    Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

/- Domain-style sampling for Definition 17.25.1:
- primary domain: invertible sheaves of modules on a ringed space, with the textbook left-tensor
  criterion and the triviality predicate;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`,
  `RingedSpace.Modules`;
- best owner abstraction: the canonical owner is
  `SheafOfModules.RingedSite.IsInvertible`, specialized to the opens site of `X`; the textbook
  left-tensor criterion is a companion bridge theorem, not a second owner;
- primitive data: a module sheaf `ℒ : ModX`;
- derived API: the left-tensor equivalence reformulation and the source-facing triviality
  predicate `IsTrivial ℒ`.

Layer triage:
- `source-facing`: invertible and trivial `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`;
- `bridge/view`: the equivalence between the canonical owner and the textbook left-tensor
  criterion on `RingedSpace.Modules X`.
-/

section Invertible

variable [MonoidalCategory (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf)]

/-- On a ringed space, the canonical invertibility owner is equivalent to the source-facing
criterion that left tensoring by `\mathcal L` is an autoequivalence of
`\mathrm{Mod}(\mathcal O_X)`. -/
theorem isInvertible_iff_tensorLeft_isEquivalence
    (ℒ : ModX) :
    IsInvertibleX ℒ ↔ (tensorLeft ℒ).IsEquivalence := by
  constructor
  · intro hℒ
    let _ : IsInvertibleX ℒ := hℒ
    exact (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance
  · intro hℒ
    let _ : Functor.IsEquivalence (tensorRight ℒ) :=
      (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).1 hℒ
    infer_instance

end Invertible

/-- Definition 17.25.1 (2): an invertible `\mathcal O_X`-module is trivial if it is isomorphic,
as an `\mathcal O_X`-module, to the structure sheaf. -/
@[stacks 01CS]
abbrev IsTrivial (ℒ : ModX) : Prop :=
  Nonempty (ℒ ≅ 𝒪X)

/-- The structure sheaf is trivial as an `\mathcal O_X`-module. -/
theorem unit_isTrivial :
    IsTrivial 𝒪X :=
  ⟨Iso.refl _⟩

end AlgebraicGeometry.RingedSpace

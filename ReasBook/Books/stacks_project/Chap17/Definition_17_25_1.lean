import Mathlib
import stacks_project.Chap04.Lemma_4_43_3
import stacks_project.Chap06.Definition_6_26_1
import stacks_project.Chap17.Definition_17_23_1
import stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/- Domain-style sampling for Definition 17.25.1:
- primary domain: invertible sheaves of modules on a ringed space, as the ringed-space
  specialization of the ringed-site module theory;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `ringedSiteModuleCategory`,
  `tensorLeft`,
  `CategoryTheory.tensorLeft_isEquivalence_iff_tensorRight_isEquivalence`,
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.unit_isInvertible`;
- best owner abstraction: the canonical owner is the Chapter 18 ringed-site class
  `SheafOfModules.RingedSite.IsInvertible`, specialized to the ringed-space owner
  `X.Modules`; the left-tensor equivalence is the source-facing companion bridge;
- primitive data: a module sheaf `ℒ : ModX`;
- derived API: the bridge theorem `isInvertible_iff_tensorLeft_isEquivalence` and the
  source-facing triviality predicate `IsTrivial ℒ`.

Layer triage:
- `source-facing`: the textbook bridge from invertibility to the left-tensor criterion, and
  trivial `\mathcal O_X`-modules;
- `core/canonical`: `SheafOfModules.RingedSite.IsInvertible`;
- `bridge/view`: the equivalence between left and right tensor criteria on `ModX`.
-/

section Invertible

variable [MonoidalCategory ModX]

/- Definition 17.25.1 (1): on a ringed space, an invertible `\mathcal O_X`-module is the
canonical ringed-site owner `SheafOfModules.RingedSite.IsInvertible`, specialized to `ModX`. -/
recall SheafOfModules.RingedSite.IsInvertible

variable (ℒ : ModX)

/-- On a ringed space, the canonical owner `IsInvertible` is equivalent to the source-facing
left-tensor criterion. -/
theorem isInvertible_iff_tensorLeft_isEquivalence :
    IsInvertible ℒ ↔ (tensorLeft ℒ).IsEquivalence :=
  ⟨fun hℒ ↦
      let _ : IsInvertible ℒ := hℒ
      (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).2 inferInstance,
    fun hℒ ↦
      let _ : Functor.IsEquivalence (tensorRight ℒ) :=
        (tensorLeft_isEquivalence_iff_tensorRight_isEquivalence ℒ).1 hℒ
      inferInstance⟩

end Invertible

/-- Definition 17.25.1 (2): an invertible `\mathcal O_X`-module is trivial if it is isomorphic,
as an `\mathcal O_X`-module, to the structure sheaf. -/
abbrev IsTrivial (ℒ : ModX) : Prop :=
  Nonempty (ℒ ≅ 𝒪X)

-- Proof sketch: the structure sheaf is trivially isomorphic to itself via the identity
-- isomorphism.
/-- The structure sheaf is trivial as an `\mathcal O_X`-module. -/
theorem unit_isTrivial :
    IsTrivial 𝒪X :=
  ⟨Iso.refl _⟩

end AlgebraicGeometry.RingedSpace

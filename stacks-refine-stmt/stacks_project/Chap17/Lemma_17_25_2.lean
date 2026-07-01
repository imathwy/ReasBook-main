import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_14_1
import stacks_project.Chap17.Definition_17_25_1
import stacks_project.Chap18.Lemma_18_32_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]

local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)
local notation "IsInvertible" =>
  @SheafOfModules.RingedSite.IsInvertible _ _ (Opens.grothendieckTopology X) X.sheaf _ _
/- Domain-style sampling for Lemma 17.25.2:
- primary domain: invertible `\mathcal O_X`-modules on a ringed space, viewed through the
  canonical ringed-site owner and its source-facing tensor-inverse consequences;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.isInvertible_iff_tensorLeft_isEquivalence`,
  `SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`,
  `SheafOfModules.RingedSite.isLocallyDirectSummandOfFiniteFree_of_isInvertible`,
  `SheafOfModules.RingedSite.nonempty_iso_ringedSiteModuleDual_of_tensor_inverse`,
  `SheafOfModules.RingedSite.ringedSiteModuleDual`;
- best owner abstraction: `SheafOfModules.RingedSite.IsInvertible`, specialized to `ModX`; the
  tensor-left equivalence and tensor-inverse statements are source-facing bridge/view results;
- primitive data: a module `ℒ : ModX`, and when needed an explicit tensor trivialization
  `e : ℒ ⊗ₘ 𝒩 ≅ 𝒪X`;
- derived API: the existence of a tensor inverse, the local direct-summand consequence, and the
  comparison of any tensor inverse with the source-facing internal Hom
  `\mathcal{H}\!\mathit{om}_{\mathcal O_X}(ℒ, \mathcal O_X)`.

Source/core/bridge triage:
- `source-facing`: the textbook one-sided tensor-trivialization and internal-Hom comparison on a
  ringed space;
- `core/canonical`: `IsInvertible` and the ringed-site theorems listed above;
- `bridge/view`: the ringed-space specialization of the Chapter 18 invertibility theorems.
-/

/- Lemma 17.25.2: for a ringed space, the tensor-inverse criterion for invertibility is exactly
the Chapter 18 owner theorem
`SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse`, specialized to the site of
opens of `X`. -/
recall SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse

-- Proof sketch: combine the canonical owner bridge from Definition `17.25.1` with the main
-- tensor-inverse criterion above.
/-- Companion form of Lemma 17.25.2: tensoring with `ℒ` is an auto-equivalence exactly when `ℒ`
admits a tensor inverse. -/
theorem tensorLeft_isEquivalence_iff_exists_tensor_inverse
    (ℒ : ModX) :
    (tensorLeft ℒ).IsEquivalence ↔
      ∃ 𝒩 : ModX, Nonempty ((ℒ ⊗ₘ 𝒩) ≅ 𝒪X) := by
  exact
    (AlgebraicGeometry.RingedSpace.isInvertible_iff_tensorLeft_isEquivalence ℒ).symm.trans
      (SheafOfModules.RingedSite.isInvertible_iff_exists_tensor_inverse ℒ)

-- Proof sketch: choose a tensor inverse `𝒩`, use the main equivalence to obtain that `ℒ` is
-- invertible, and then apply the local duality argument of Lemma `17.18.2` to deduce that `ℒ` is
-- locally a retract of a finite free module sheaf.
/-- If `ℒ` admits a tensor inverse, then locally `ℒ` is a direct summand of a finite free
`\mathcal O_X`-module. -/
theorem exists_tensor_inverse_locallyDirectSummandOfFiniteFree
    (ℒ : ModX)
    (hℒ : ∃ 𝒩 : ModX, Nonempty ((ℒ ⊗ₘ 𝒩) ≅ 𝒪X)) :
    ℒ.IsLocallyDirectSummandOfFiniteFree := by
  sorry

section InternalHom

variable [MonoidalClosed (RingedSpace.Modules X)]

-- Proof sketch: specialize the Chapter 18 comparison
-- `nonempty_iso_ringedSiteModuleDual_of_tensor_inverse` to `ModX` using the given explicit
-- trivialization `e`, then compose with the canonical tensor-unit identification
-- `(ihom ℒ).mapIso unitIsoTensorUnit.symm : ringedSiteModuleDual ℒ ≅ (ihom ℒ).obj 𝒪X`.
/-- Lemma 17.25.2 (internal-Hom clause): any tensor inverse `𝒩` of `ℒ` is isomorphic to
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(ℒ, \mathcal O_X)`. -/
theorem tensor_inverse_iso_internalHom_unit
    (ℒ 𝒩 : ModX)
    (e : (ℒ ⊗ₘ 𝒩) ≅ 𝒪X) :
    Nonempty (𝒩 ≅ (ihom ℒ).obj 𝒪X) := by
  sorry

end InternalHom

end SheafOfModules

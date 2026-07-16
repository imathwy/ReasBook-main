import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap17.Lemma_17_18_2
import stacks_proof.stacks_project.Chap18.Example_18_29_1

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "ModX" => X.Modules
local notation "𝒪X" => (𝟙_ X.Modules : X.Modules)

variable [MonoidalCategory X.Modules]
variable [MonoidalClosed X.Modules]

/- Domain-style sampling for Example 17.18.1:
- primary domain: duality for `\mathcal O_X`-modules on a ringed space, via the canonical
  tensor/internal-Hom comparison and its left-duality consequence;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree`,
  `SheafOfModules.RingedSite.unitInternalHomTensorToEnd`,
  `SheafOfModules.RingedSite.isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree`,
  `CategoryTheory.ExactPairing`;
- best owner abstraction: the source-facing owner category is `X.Modules`, with the Chapter 18
  local-direct-summand owner
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree ℱ`; the comparison morphism and
  isomorphism theorem remain the canonical core declarations specialized to the opens site of `X`;
- primitive data: a sheaf `ℱ : X.Modules` and the chapter owner predicate
  `SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree ℱ`;
- derived API: direct recall of the canonical tensor/internal-Hom comparison and isomorphism
  owners on the ringed-space surface, together with the induced left-duality datum.

Source/core/bridge triage:
- `source-facing`: Example 17.18.1 on `X.Modules`;
- `core/canonical`: the Chapter 18 ringed-site owner declarations and `ExactPairing`;
- `bridge/view`: direct recall of those owners on the opens site of `X`, plus the specialized
  `#synth` consequence below.
-/

/-
Example 17.18.1: on a ringed space, the canonical tensor-to-endomorphism morphism
`\mathcal F \otimes_{\mathcal O_X} \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,
\mathcal O_X) \to \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal F)` is exactly the
Chapter 18 owner `SheafOfModules.RingedSite.unitInternalHomTensorToEnd`, specialized to the opens
site of `X`.
-/
recall SheafOfModules.RingedSite.unitInternalHomTensorToEnd

/-
Example 17.18.1: if `\mathcal F` is locally a direct summand of a finite free
`\mathcal O_X`-module, then the canonical tensor/internal-Hom comparison is an isomorphism by
direct specialization of the Chapter 18 owner theorem.
-/
recall SheafOfModules.RingedSite.isIso_unitInternalHomTensorToEnd_of_locallyDirectSummandOfFiniteFree

variable [BraidedCategory X.Modules]
variable (ℱ : X.Modules)
variable
  [@SheafOfModules.RingedSite.IsLocallyDirectSummandOfFiniteFree _ _
    (Opens.grothendieckTopology X) _ X.sheaf ℱ]

/- Example 17.18.1 also yields that
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal O_X)` is a left dual of
`\mathcal F`; on the ringed-space surface this is the canonical specialized instance
`ExactPairing ((ihom ℱ).obj (𝟙_ X.Modules)) ℱ`. -/
#synth ExactPairing ((ihom ℱ).obj 𝒪X) ℱ

end

end AlgebraicGeometry.RingedSpace

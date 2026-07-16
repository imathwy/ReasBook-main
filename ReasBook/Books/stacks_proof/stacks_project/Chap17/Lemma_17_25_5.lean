import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap18.Lemma_18_32_4

open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 17.25.5:
- primary domain: invertible `\mathcal O_X`-modules and their duality in the symmetric monoidal
  closed category `RingedSpace.Modules X`;
- inspected owner declarations:
  `SheafOfModules.RingedSite.IsInvertible`,
  `SheafOfModules.RingedSite.isInvertible_tensor_of_isInvertible`,
  `SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible`,
  `SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible`;
- best owner abstraction: the Chapter 18 ringed-site theorems above, specialized to the opens site
  of a ringed space;
- primitive data: invertible modules `ℒ`, `𝒩 : X.Modules`;
- derived API: invertibility of `ℒ ⊗ 𝒩`, invertibility of the internal-Hom dual of `ℒ`, and the
  evaluation-isomorphism statement at the unit object.

Source/core/bridge triage:
- `source-facing`: the three clauses of Stacks Lemma 17.25.5 for ringed spaces;
- `core/canonical`: the Chapter 18 ringed-site owner theorems;
- `bridge/view`: the opens-site specialization from a ringed site to a ringed space.

This file is therefore a canonical-recall item: the ringed-space statements add no new
mathematics beyond the already-owned ringed-site theorems, so the duplicate local theorem shells
should be deleted rather than preserved under parallel names.
-/

/- Lemma 17.25.5 (1): on a ringed space, the tensor product of two invertible
`\mathcal O_X`-modules is invertible. This is the opens-site specialization of the Chapter 18
owner theorem. -/
recall SheafOfModules.RingedSite.isInvertible_tensor_of_isInvertible

/- Lemma 17.25.5 (2): on a ringed space, the internal-Hom dual
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L, \mathcal O_X)` of an invertible
`\mathcal O_X`-module is invertible. This is the same opens-site specialization. -/
recall SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible

/- Lemma 17.25.5 (3): on a ringed space, the evaluation morphism
`\mathcal L \otimes_{\mathcal O_X} \mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal L,
\mathcal O_X) \to \mathcal O_X` is an isomorphism for invertible `\mathcal O_X`-modules. This is
again the opens-site specialization of the Chapter 18 owner theorem. -/
recall SheafOfModules.RingedSite.isIso_internalHom_unit_evaluation_of_isInvertible

end AlgebraicGeometry.RingedSpace

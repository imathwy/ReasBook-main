import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_17_12

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Source/core/bridge triage:
- `source-facing`: Lemma 20.26.13 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the Chapter 21 ringed-site owner
  `SheafOfModules.RingedSite.quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat`;
- `bridge/view`: the opens-site specialization
  `Modules X = ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf`.

This file should expose only the ringed-space statement and transport it to the existing
ringed-site owner, not reprove a parallel tensor-quasi-isomorphism theorem. -/

/- Lemma 20.26.13: if `α : P ⟶ Q` is a quasi-isomorphism between K-flat complexes of
`𝒪_X`-modules on a ringed space `(X, 𝒪_X)`, then for every complex `F` the induced map
`tensorHom (𝟙 F) α` is a quasi-isomorphism. This is exactly the opens-site specialization of the
canonical ringed-site theorem
`SheafOfModules.RingedSite.quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat`. -/
recall SheafOfModules.RingedSite.quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat

end AlgebraicGeometry.RingedSpace

import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 20.41.2:
- primary domain: composition pairing for internal-Hom complexes of `𝒪_X`-module cochain
  complexes;
- inspected owner declarations:
  `SheafOfModules.RingedSite.internalHomComplexComposition`,
  `(ihom K).obj L`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction:
  `SheafOfModules.RingedSite.internalHomComplexComposition`, whose source is already the canonical
  tensor product of the two ringed-site internal-Hom complexes;
- primitive data:
  the ambient ringed site and the three cochain complexes;
- derived API:
  the assembled composition morphism and its degreewise formula.

Source/core/bridge triage:
- `source-facing`: Lemma 20.41.2 for complexes of `𝒪_X`-modules on a ringed space;
- `core/canonical`: the ringed-site owner
  `SheafOfModules.RingedSite.internalHomComplexComposition`;
- `bridge/view`: the specialization from the canonical site of opens of `X` to ringed spaces.

This file should therefore stay at the `bridge/view` layer and directly recall the ringed-site
owner declaration instead of introducing a second ringed-space wrapper with the same interface. -/

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.41.2: for a ringed space `(X, 𝒪_X)` and complexes `K`, `L`, and `M` of
`𝒪_X`-modules, there is a canonical morphism
`Tot (ℋom^•(L, M) ⊗[𝒪_X] ℋom^•(K, L)) ⟶ ℋom^•(K, M)`.
This is the canonical ringed-site composition morphism specialized to the site of opens of `X`. -/
recall internalHomComplexComposition

end AlgebraicGeometry.RingedSpace

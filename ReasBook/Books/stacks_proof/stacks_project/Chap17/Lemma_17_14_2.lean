import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_14_1

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}} (ℱ : X.Modules) [ℱ.IsLocallyFree]

/-
Domain-style sampling for Lemma 17.14.2:
- primary domain: locally free and quasi-coherent sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsQuasicoherent`,
  `RingedSpace.Modules`,
  the canonical instance `(ℱ : X.Modules) [ℱ.IsLocallyFree] : ℱ.IsQuasicoherent`
  from `Definition_17_14_1`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with
  `ℱ.IsLocallyFree` as primitive source-facing data and `ℱ.IsQuasicoherent` as derived API;
- primitive data: a module sheaf `ℱ` on `X` together with its local-freeness owner instance;
- derived API: the canonical quasi-coherence instance attached to a locally free module.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that a locally free `\mathcal O_X`-module is
  quasi-coherent;
- `core/canonical`: the owner predicates `SheafOfModules.IsLocallyFree` and
  `SheafOfModules.IsQuasicoherent` on `RingedSpace.Modules X`;
- `bridge/view`: the owner-level instance in `Definition_17_14_1`; this file should therefore be
  a canonical-use item rather than a second parallel owner-level declaration.
-/

/- Lemma 17.14.2: if `\mathcal F` is a locally free sheaf of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)`, then `\mathcal F` is quasi-coherent. This is the canonical instance
from `Definition_17_14_1`. -/
#check (inferInstance : ℱ.IsQuasicoherent)

end AlgebraicGeometry

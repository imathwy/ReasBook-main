import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Definition_17_14_1

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.14.2:
- primary domain: locally free and quasi-coherent sheaves of modules on a ringed space;
- inspected owner declarations:
  `SheafOfModules.IsLocallyFree`,
  `SheafOfModules.IsQuasicoherent`,
  `RingedSpace.Modules`,
  `SheafOfModules.free`;
- best owner abstraction: the ambient owner category `RingedSpace.Modules X`, with
  `ℱ.IsLocallyFree` as primitive source-facing data and `ℱ.IsQuasicoherent` as derived API;
- primitive data: a module sheaf `ℱ` on `X` together with its local trivializations by free
  sheaves from `Definition_17_14_1`;
- derived API: the quasi-coherence instance attached to a locally free module.

Source/core/bridge triage:
- `source-facing`: the Stacks assertion that a locally free `\mathcal O_X`-module is
  quasi-coherent;
- `core/canonical`: the owner predicates `SheafOfModules.IsLocallyFree` and
  `SheafOfModules.IsQuasicoherent` on `RingedSpace.Modules X`;
- `bridge/view`: this file should expose the result directly as the canonical instance rather than
  as a separate theorem plus an anonymous wrapper instance.
-/

-- Proof sketch: a local trivialization by free modules gives a local presentation on the same
-- neighbourhood, since free sheaves are quasi-coherent and quasi-coherence is local on the base.
/-- Lemma 17.14.2: if `\mathcal F` is a locally free sheaf of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)`, then `\mathcal F` is quasi-coherent. -/
instance ringedSpaceModule_isQuasicoherent_of_isLocallyFree
    (ℱ : RingedSpace.Modules X) [ℱ.IsLocallyFree] :
    ℱ.IsQuasicoherent := sorry

end AlgebraicGeometry.RingedSpace

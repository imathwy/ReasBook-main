import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

/- 
Domain-style sampling for Lemma 17.11.2:
- primary domain: finite-presentation and quasi-coherence predicates for sheaves of modules on a
  ringed space;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsQuasicoherent`,
  the canonical mathlib instance
  `(M : SheafOfModules R) [M.IsFinitePresentation] : M.IsQuasicoherent`;
- best owner abstraction: the upstream owner class `SheafOfModules.IsFinitePresentation`, with
  quasi-coherence as derived API supplied by the canonical instance;
- primitive data: a sheaf of modules on `X` together with its finite-presentation instance;
- derived API: the resulting quasi-coherence instance;

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of Stacks Project Lemma 17.11.2;
- `core/canonical`: the upstream instance `[M.IsFinitePresentation] → M.IsQuasicoherent`;
- `bridge/view`: the chapter owner alias `RingedSpace.Modules X`.

This item is a canonical-use item: the mathematical content is already owned upstream, so the
file should reuse that owner directly instead of introducing a parallel local theorem wrapper.
-/

variable {X : RingedSpace.{u}}
variable (𝒢 : RingedSpace.Modules X) [𝒢.IsFinitePresentation]

/- Lemma 17.11.2: any `\mathcal O_X`-module of finite presentation on a ringed space
`(X, \mathcal O_X)` is quasi-coherent. This is the canonical instance from
`SheafOfModules.IsFinitePresentation` to `SheafOfModules.IsQuasicoherent`. -/
#check (inferInstance : 𝒢.IsQuasicoherent)

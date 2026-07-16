import Mathlib
import stacks_proof.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

/- 
Domain-style sampling for Lemma 17.12.2:
- primary domain: coherent sheaves of modules on ringed spaces and their canonical downstream
  finiteness predicates;
- sampled owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsCoherent` from `Definition_17_12_1`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.IsQuasicoherent`,
  the canonical instance `[M.IsFinitePresentation] → M.IsQuasicoherent`;
- best owner abstraction: the ambient owner category `(RingedSpace.Modules X)`,
  with `SheafOfModules.IsCoherent` as the source-facing hypothesis and
  `SheafOfModules.IsFinitePresentation` / `SheafOfModules.IsQuasicoherent` as derived owner-level
  properties;
- primitive data: the sheaf `ℱ` together with the coherence structure;
- derived API: finite presentation and quasi-coherence, both supplied canonically by instances.

Source/core/bridge triage:
- `source-facing`: coherence of an `\mathcal O_X`-module;
- `core/canonical`: the owner predicates `SheafOfModules.IsFinitePresentation` and
  `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: instance search from coherence to finite presentation, then to quasi-coherence.

This item is a canonical-use item, not a new owner: the chapter-local coherence class already owns
the input data, while the conclusions are canonical downstream instances, so the file should reuse
those instances directly instead of introducing theorem wrappers with duplicate interfaces.
-/

variable {X : RingedSpace.{u}}
variable (ℱ : RingedSpace.Modules X) [ℱ.IsCoherent]

/- Lemma 17.12.2: a coherent `\mathcal O_X`-module on a ringed space `(X, \mathcal O_X)` is
finitely presented. This is the canonical instance provided by
`Definition_17_12_1`. -/
#check (inferInstance : ℱ.IsFinitePresentation)

/- Lemma 17.12.2: a coherent `\mathcal O_X`-module is therefore quasi-coherent, via the canonical
instance from finite presentation to quasi-coherence. -/
#check (inferInstance : ℱ.IsQuasicoherent)

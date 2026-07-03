import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for coherence versus finite presentation on a ringed space:
- inspected owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsCoherent`,
  `SheafOfModules.IsFinitePresentation`
- best owner abstraction:
  the ambient owner is `(RingedSpace.Modules X)`; coherence and finite presentation are object properties on
  that owner category
- primitive data:
  a ringed space `X`, a module sheaf `ℱ : (RingedSpace.Modules X)`, and coherence of the structure-sheaf
  module `SheafOfModules.unit ((RingedSpace.ringCatSheaf X))`
- derived API:
  the source-facing equivalence between coherence and finite presentation under the coherent
  structure-sheaf hypothesis

Source/core/bridge triage:
- `source-facing`: the textbook equivalence for `\mathcal O_X`-modules when `\mathcal O_X` is
  coherent
- `core/canonical`: the owner predicates `SheafOfModules.IsCoherent` and
  `SheafOfModules.IsFinitePresentation` on `(RingedSpace.Modules X)`
- `bridge/view`: this theorem, which relates the two owner predicates under the extra hypothesis on
  the unit module
-/

namespace SheafOfModules

variable {X : RingedSpace.{u}}

-- Proof sketch: finite presentation gives local exact sequences by finite free modules. Under
-- coherence of the structure sheaf module, the kernels in such local presentations are of finite
-- type, so the defining coherence condition holds.
/-- If the structure sheaf `\mathcal O_X`, viewed as an `\mathcal O_X`-module, is coherent, then
a finitely presented `\mathcal O_X`-module is coherent. -/
theorem isCoherent_of_isFinitePresentation
    [hOX : (unit (RingedSpace.ringCatSheaf X)).IsCoherent]
    (ℱ : RingedSpace.Modules X) [ℱ.IsFinitePresentation] :
    ℱ.IsCoherent := sorry

instance (ℱ : RingedSpace.Modules X)
    [hOX : (unit (RingedSpace.ringCatSheaf X)).IsCoherent] [ℱ.IsFinitePresentation] :
    ℱ.IsCoherent :=
  isCoherent_of_isFinitePresentation ℱ

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Lemma 17.12.5: if the structure sheaf `\mathcal O_X`, regarded as an `\mathcal O_X`-module,
is coherent, then an `\mathcal O_X`-module `\mathcal F` is coherent if and only if it is of
finite presentation. -/
theorem isCoherent_iff_isFinitePresentation_of_structureSheaf_isCoherent
    [hOX : (SheafOfModules.unit (RingedSpace.ringCatSheaf X)).IsCoherent]
    (ℱ : (RingedSpace.Modules X)) :
    ℱ.IsCoherent ↔ ℱ.IsFinitePresentation := by
  constructor <;> intro <;> infer_instance

end AlgebraicGeometry.RingedSpace

import Mathlib
import StacksProject_2024.Chap05.Definition_5_11_4
import StacksProject_2024.Chap05.Definition_5_20_1
import StacksProject_2024.Chap05.Definition_5_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [TopologicalSpace.LocallyNoetherianSpace X]
  [QuasiSober X] [T0Space X] [CatenarySpace X]

/- Domain-style sampling for local existence of dimension functions:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived codimension owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood owner: `TopologicalSpace.LocallyNoetherianSpace.exists_open`
- open-subspace locality owners: `IsLocallyClosed.sober` and `IsLocallyClosed.catenarySpace`

Layer triage:
- `source-facing`: Lemma 5.20.4, asserting existence of a local dimension function near a point
- `core/canonical`: `IsDimensionFunction`, `LocallyNoetherianSpace`, `QuasiSober`, and
  `CatenarySpace`
- `bridge/view`: restriction to a suitable open neighborhood, then construction of an
  integer-valued function on that open subspace

Primitive data versus derived API:
- primitive data already belongs to the owner abstractions `IsDimensionFunction`,
  `LocallyNoetherianSpace`, and `CatenarySpace`
- this file should therefore keep only the source-facing existential theorem on an open subspace,
  rather than introducing a local wrapper for a neighborhood together with its function
-/

-- Proof sketch: choose a Noetherian open neighbourhood of `x` using local Noetherianity, shrink it
-- along the irreducible components and their pairwise intersections as in Lemma `5.20.3`, and
-- define the local codimension function relative to `x`; catenarity and sobriety ensure this
-- function is well defined and satisfies the immediate-specialization axiom on the resulting open
-- subspace.
/-- Lemma 5.20.4: in a locally Noetherian, sober, catenary space, every point has an open
neighbourhood whose induced topology admits a dimension function. -/
theorem exists_open_neighborhood_with_dimensionFunction (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := sorry

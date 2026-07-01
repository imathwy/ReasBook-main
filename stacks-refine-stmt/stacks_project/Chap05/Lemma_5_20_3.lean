import Mathlib
import stacks_project.Chap05.Definition_5_20_1
import stacks_project.Chap05.Definition_5_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

/- Domain-style sampling for Lemma 5.20.3:
- project owner for dimension functions: `IsDimensionFunction`
- derived codimension comparison owner: `IsDimensionFunction.sub_eq_codimBetween_pointClosure`
- local Noetherian neighborhood bridge: `LocallyNoetherianSpace.exists_mem_nhds_subset`
- canonical irreducible-component owner on Noetherian neighborhoods: `irreducibleComponents`

Layer triage:
- `source-facing`: the difference of two dimension functions is locally constant
- `core/canonical`: `IsDimensionFunction`, `IsLocallyConstant`, `LocallyNoetherianSpace`,
  `QuasiSober`
- `bridge/view`: shrink to a Noetherian open neighborhood, then compare both functions on each
  irreducible component through the common codimension formula from Lemma `5.20.2`

Primitive data versus derived API:
- primitive data already lives upstream in `IsDimensionFunction` and `LocallyNoetherianSpace`
- this file should contribute only the derived locally constant theorem under the owner namespace,
  not a new wrapper around local dimension data
-/

namespace IsDimensionFunction

section

variable {X : Type u} [TopologicalSpace X] [LocallyNoetherianSpace X] [QuasiSober X]
  {δ δ' : X → ℤ}

-- Proof sketch: around each point, choose a Noetherian open neighbourhood using local
-- Noetherianity. In that neighbourhood, the finitely many irreducible components through the
-- point have generic points by sobriety, and Lemma 5.20.2 identifies both dimension functions
-- with the same codimension formula on each component, forcing `δ - δ'` to be constant there.
/-- Lemma 5.20.3: on a locally Noetherian sober topological space, the difference `δ - δ'` of two
dimension functions is locally constant; `T₀` is derived canonically from either dimension
function, so only quasi-sobriety remains ambient. -/
theorem isLocallyConstant_sub (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := sorry

end

end IsDimensionFunction

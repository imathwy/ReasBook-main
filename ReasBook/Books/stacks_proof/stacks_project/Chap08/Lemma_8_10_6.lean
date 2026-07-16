import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_35_14
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Definition_8_5_1
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_10_3

-- Declarations for this item will be appended below by the statement pipeline.

universe uC uY vC vY

namespace CategoryTheory

open FibredCategoryOver

section

variable {C : Type uC} {Y : Type uY}
variable [Category.{vC} C] [Category.{vY} Y]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 8.10.6:
- primary domain: stacks over a site, stacks in groupoids over a site, and the inherited topology
  on the total category of a fibred category.
- inspected owner-level declarations:
  `StackOver`,
  `StackInGroupoidsOver`,
  `IsStackInGroupoids`,
  `Functor.isFibredInGroupoids_comp`.
- best owner abstraction available in the current compiled closure: the two source clauses are
  best exposed as canonical instance-level consequences on the bundled owners `StackOver J` and
  `StackInGroupoidsOver J`, with no local wrapper API.
- primitive data: clause `(1)` needs only `Xₛ : StackOver J`, `q : Y ⥤ Xₛ.S`, and the
  inherited-topology stack hypothesis on `q`.
- derived API: clause `(2)` is obtained by combining clause `(1)` with the composition instance
  `Functor.isFibredInGroupoids_comp` and the canonical constructor
  `[IsFibredInGroupoids _] [IsStackOnSite _ _] → IsStackInGroupoids _ _`.

Source/core/bridge triage:
- `source-facing`: the two clause-specific consequences of Stacks Project Lemma 8.10.6.
- `core/canonical`: `StackOver`, `StackInGroupoidsOver`, `IsStackOnSite`, `IsStackInGroupoids`,
  and the Chapter 4 composition owner `Functor.isFibredInGroupoids_comp`.
- `bridge/view`: the inherited-topology passage `IsStackOnSite (inheritedTopology J Xₛ) q` to
  `IsStackOnSite J (q ⋙ Xₛ.p)` in clause `(1)`, and the corresponding stack-in-groupoids
  strengthening in clause `(2)`. -/

/-- Lemma 8.10.6 (1): if `Xₛ : StackOver J` is a stack over `(C, J)` and
`q : Y ⥤ Xₛ.S` is a stack for the topology on `Xₛ` inherited from `(C, J)`, then the composite
projection `q ⋙ Xₛ.p : Y ⥤ C` is a stack over `(C, J)`. -/
@[stacks 09WX]
instance composite_isStackOnSite_of_inheritedTopology
    (Xₛ : StackOver J) (q : Y ⥤ Xₛ.S)
    [IsStackOnSite (inheritedTopology J Xₛ) q] :
    IsStackOnSite J (q ⋙ Xₛ.p) := by
  -- The intended owner-level conclusion is the canonical stack structure on the composite
  -- projection, so first ask instance search for an existing transitivity bridge.
  infer_instance

/-- Lemma 8.10.6 (2): if `Xₛ : StackInGroupoidsOver J` is a stack in groupoids over `(C, J)` and
`q : Y ⥤ Xₛ.S` is a stack in groupoids for the topology on `Xₛ` inherited from `(C, J)`, then
the composite projection `q ⋙ Xₛ.p : Y ⥤ C` is a stack in groupoids over `(C, J)`. -/
@[stacks 09WX]
instance composite_isStackInGroupoids_of_inheritedTopology
    (Xₛ : StackInGroupoidsOver J) (q : Y ⥤ Xₛ.S)
    [IsStackInGroupoids (inheritedTopology J Xₛ) q] :
    IsStackInGroupoids J (q ⋙ Xₛ.p) := by
  -- Once the composite projection is recognized as a stack in groupoids, the target instance is
  -- the canonical owner on that composite functor.
  infer_instance

end

end CategoryTheory

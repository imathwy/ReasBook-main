import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4

noncomputable section

universe u v w x

namespace OrdinaryConvexProgram

section

variable {𝕜 : Type x} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E] [TopologicalSpace E]
variable [AddCommMonoid β] [LinearOrder β] [SMul 𝕜 β] [TopologicalSpace β]
variable {r s : ℕ}

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.5 says that the bifunction associated with an ordinary convex
  program is closed once the constraint set is closed, the objective and inequality branches are
  closed on that set, and the equality branches satisfy a closedness bridge for equality slices.
- `core/canonical`: Definition 6.29.5 already identifies bifunction closedness with lower
  semicontinuity of the graph function `Function.uncurry F`, and the Chapter 6 owner is
  `P.perturbedProblem`.
- `bridge/view`: `P.perturbedProblem` is the canonical `+∞`-extension of the source objective to
  the perturbed feasible slices. The source data of `OrdinaryConvexProgram` already lives on the
  closed constraint set, so the closedness assumptions stay on the primitive branch data; equality
  slices are handled by a two-sided semicontinuity bridge (`LowerSemicontinuous` and
  `UpperSemicontinuous`) rather than being left implicit in affine data.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `LowerSemicontinuous (Function.uncurry F)` from `Definition_6_29_5`;
- `Function.toWithBotTopOn` from `Chap01.Remark_4_4_5`;
- `LowerSemicontinuous` / `UpperSemicontinuous` as the canonical closedness owners for
  inequality/equality branches.

Primitive data vs derived API:
- primitive source-facing data: the program `P`;
- primitive source-facing closedness assumptions: closedness of `P.constraintSet`, lower
  semicontinuity of `P.objective`, lower semicontinuity of each `P.inequality i`, and two-sided
  semicontinuity for each equality branch `P.equality j`;
- derived conclusion: lower semicontinuity of the graph function of `P.perturbedProblem`.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

variable (P : OrdinaryConvexProgram 𝕜 E β r s)

-- Proof sketch: the perturbed feasible set is cut out inside the closed set `P.constraintSet` by
-- lower-semicontinuous inequality branches and equality slices controlled by both lower and upper
-- semicontinuity, hence it is closed. The perturbed problem is then the canonical `+∞`-extension
-- of the lower-semicontinuous objective branch to that closed feasible slice, so its graph
-- function is lower semicontinuous.
/-- Lemma 6.29.5: if the constraint set of an ordinary convex program is closed, the objective
and inequality branches are lower semicontinuous on that set, and each equality branch has both
lower and upper semicontinuity (so equality slices have an explicit closedness bridge), then the
graph function of the perturbed problem is lower semicontinuous. -/
theorem uncurry_perturbedProblem_lowerSemicontinuous
    (hconstraintSet : IsClosed P.constraintSet)
    (hobjective : LowerSemicontinuous P.objective)
    (hineq : ∀ i, LowerSemicontinuous (P.inequality i))
    (heq_lower : ∀ j, LowerSemicontinuous (P.equality j))
    (heq_upper : ∀ j, UpperSemicontinuous (P.equality j)) :
    LowerSemicontinuous (Function.uncurry P.perturbedProblem) := sorry

end

end OrdinaryConvexProgram

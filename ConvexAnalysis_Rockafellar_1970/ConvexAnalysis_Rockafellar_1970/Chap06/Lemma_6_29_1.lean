import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_4

noncomputable section

universe u v w

namespace OrdinaryConvexProgram

section

open scoped Rockafellar

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.1 says that the bifunction associated with an ordinary convex
  program is convex in the joint perturbation/decision variables.
- `core/canonical`: Chapter 6 already owns that bifunction as `P.perturbedProblem`, and Chapter 1
  already owns bifunction convexity as `Function.IsConvex 𝕜 (Function.uncurry F)`.
- `bridge/view`: this file should therefore state the lemma on the source-facing bifunction
  convexity notation `convᵇ[𝕜](P.perturbedProblem)` (definitionally
  `Function.IsConvex 𝕜 (Function.uncurry P.perturbedProblem)`); the explicit source constraint set
  and the split inequality/equality data stay in the owner `OrdinaryConvexProgram`, rather than
  being rebuilt as a second full-space wrapper API.

Domain-style sampling used here:
- `OrdinaryConvexProgram` from `Definition_6_28_1`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Function.IsConvex` from `Chap01.Theorem_4_2` (via the Chapter 6 owner imports);
- `convᵇ[𝕜](·)` from `Definition_6_29_4`;
- `Function.toWithBotTopOn` as the canonical extended-value owner already used by
  `P.perturbedProblem`.

Primitive data vs derived API:
- primitive source data: the program `P`, which already packages the source constraint set, the
  objective on that set, the convex inequality family, and the affine equality family;
- derived API: bifunction convexity of `P.perturbedProblem`, written in source form
  `convᵇ[𝕜](P.perturbedProblem)`.

Layer target: `source-facing`, stated directly on the existing Chapter 6 owner.
-/

-- Proof sketch: unfold `P.perturbedProblem` as the canonical `+∞`-extension of the objective to
-- each perturbed feasible set. The base constraint set is convex by `P.constraintSet_convex`; the
-- perturbed inequality slices are convex by the convexity fields of `P`, and the perturbed
-- equality slices are affine by the affine fields of `P`. The graph-function decomposition into
-- the objective branch and the corresponding indicator terms is therefore convex termwise, and so
-- is their sum.
/-- Lemma 6.29.1: the graph function of the perturbed problem associated with an ordinary convex
program is convex on the product of perturbation parameters and decision variables. -/
theorem uncurry_perturbedProblem_isConvex :
    convᵇ[𝕜](P.perturbedProblem) := sorry

end

end OrdinaryConvexProgram

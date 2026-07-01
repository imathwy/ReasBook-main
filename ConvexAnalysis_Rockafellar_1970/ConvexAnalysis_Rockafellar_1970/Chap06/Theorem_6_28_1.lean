import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] [Top β]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.1 fixes a Kuhn--Tucker multiplier pair `(lam, μ)` for an ordinary
  convex program `P`, forms the weighted objective
  `f₀ + Σ λᵢ fᵢ + Σ μⱼ hⱼ`, and characterizes the optimal solutions of `P`.
- `core/canonical`: the Chapter 6 owners already present are `P.feasibleSet`,
  `P.feasibleObjective`, `P.optimalValue`, `P.weightedObjective`, the Kuhn--Tucker owner
  `P.IsKuhnTuckerVector`, and `Function.IsProper` together with the effective-domain notation
  `dom(·)`.
- `bridge/view`: the theorem is kept source-facing as a set equality between the ambient points
  satisfying the weighted-objective minimizer and complementary-slackness conditions and the
  ambient optimal-solution set.

Domain-style sampling used here:

- `IsMinOn` from mathlib's order-extrema API as the canonical attained-minimum owner;
- `Function.IsProper` and `dom(·)` from Chapter 1;
- `OrdinaryConvexProgram`, `extendZero`, `P.feasibleSet`, `P.feasibleObjective`,
  `P.optimalValue`, `P.weightedObjective`, and `P.IsKuhnTuckerVector` from
  Definitions 6.28.1--6.28.3.

Primitive data vs derived API:

- primitive data: the program `P` and the multiplier blocks `(lam, μ)`;
- primitive owner-side objects: the feasible region, the feasible objective, and the ambient
  extension of the weighted objective;
- derived source-facing sets: the canonical minimum set
  `minimumSet (P.weightedObjective lam μ)`, the complementary minimizer subset, and the
  ambient optimal-solution set.

Layer target: `source-facing`. The numbered item is a direct optimal-solution characterization, so
the theorem is stated directly about sets of points in `E` rather than through a surrogate data
package.
-/

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-- The subset `D₀` from Theorem 6.28.1: weighted-objective minimizers whose inequality
constraints satisfy the zero-multiplier weak inequalities, whose nonzero-multiplier inequality
constraints are active, and whose equality constraints vanish. -/
def weightedObjectiveComplementaryMinimizerSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) : Set E :=
  {x | x ∈ minimumSet (P.weightedObjective lam μ) ∧
      (∀ i, lam i = 0 → extendZero (P.inequality i) x ≤ 0) ∧
      (∀ i, lam i ≠ 0 → extendZero (P.inequality i) x = 0) ∧
      (∀ j, extendZero (P.equality j) x = 0)}

-- Proof sketch: unfold `weightedObjectiveComplementaryMinimizerSet`; the four conjuncts record
-- exactly the ambient minimizer condition, the weak inequalities attached to zero multipliers, the
-- active-constraint equalities attached to nonzero multipliers, and the equality constraints.
/-- Membership in `weightedObjectiveComplementaryMinimizerSet` is the conjunction of the
weighted-objective minimizer condition with the side conditions defining `D₀` in Theorem 6.28.1.
-/
@[simp] theorem mem_weightedObjectiveComplementaryMinimizerSet
    (lam : ι → 𝕜) (μ : κ → 𝕜) (x : E) :
    x ∈ P.weightedObjectiveComplementaryMinimizerSet lam μ ↔
      x ∈ minimumSet (P.weightedObjective lam μ) ∧
        (∀ i, lam i = 0 → extendZero (P.inequality i) x ≤ 0) ∧
        (∀ i, lam i ≠ 0 → extendZero (P.inequality i) x = 0) ∧
        (∀ j, extendZero (P.equality j) x = 0) := sorry

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

variable {r s : ℕ} {ι : Type} {κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: use the Kuhn--Tucker owner fields for `(lam, μ)` to obtain properness of the
-- weighted objective, effective-domain identification with `P.constraintSet`, strict lower
-- boundedness of the weighted-objective infimum, and equality of that infimum with the feasible
-- optimal value. Compare weighted and feasible objectives on feasible points, and characterize the
-- equality case by the zero/nonzero multiplier side conditions together with the equality
-- constraints. This identifies `D₀` with the ambient image of the minimizer set of
-- `P.feasibleObjective`.
/-- Theorem 6.28.1: if `(lam, μ)` satisfies the Kuhn--Tucker conditions for an ordinary convex
program `P`, then the points where the weighted objective attains its ambient infimum and the
zero/nonzero multiplier side conditions hold are exactly the optimal solutions of `P`. -/
theorem weightedObjectiveComplementaryMinimizerSet_eq_optimalSolutionSet
    (lam : ι → 𝕜) (μ : κ → 𝕜)
    (hKT : P.IsKuhnTuckerVector lam μ) :
    P.weightedObjectiveComplementaryMinimizerSet lam μ = P.optimalSolutionSet := sorry

end OrdinaryConvexProgram

end

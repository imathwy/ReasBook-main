import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_28_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.4 is the linear-constraint specialization of the Kuhn--Tucker
  existence theorem for ordinary convex programs.
- `core/canonical`: the existing Chapter 6 owners are `OrdinaryConvexProgram`, `P.optimalValue`,
  `P.feasibleSet`, and `P.IsKuhnTuckerVector`.
- `bridge/view`: the source phrase “only linear constraints” is expressed canonically by requiring
  each inequality constraint to be affine on `P.constraintSet`, now at the intrinsic
  owner `affOn[𝕜](·, ·)` on the canonical ambient extension `extendZero (P.inequality i)`; the
  equality block is already affine by the defining data of `OrdinaryConvexProgram`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `affOn[𝕜](·, ·)` (on `extendZero` realizations) from
  `Definition_6_28_1`;
- `P.feasibleSet`, `P.optimalValue`, and `P.IsKuhnTuckerVector` from
  `Definition_6_28_3`;
- `P.HasStrictlyFeasiblePointOnNonaffineInequalities` and
  `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` from `Theorem_6_28_3`;
- the relative-interior owner notation `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source-facing data: an ordinary convex program `P`, affine inequality constraints,
  and a feasible point;
- derived qualification: nonaffine strict feasibility (vacuous when every inequality is affine);
- derived conclusion: existence of a Kuhn--Tucker multiplier pair for `P`.

Layer target: `source-facing`, with the canonical intrinsic constrained-data affine owner on the
theorem surface.
-/

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: if every inequality is affine on the constraint-set owner layer, there are no
-- nonaffine inequalities. Hence any feasible point witnesses
-- `HasStrictlyFeasiblePointOnNonaffineInequalities`.
/-- If all inequality constraints are affine on `P.constraintSet`, then any feasible point of `P`
induces the nonaffine strict-feasibility qualification from Theorem 6.28.3. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hfeas : ∃ x : E, x ∈ P.feasibleSet) :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities := by
  rcases hfeas with ⟨x, hxFeas⟩
  refine ⟨⟨x, hxFeas⟩, ?_⟩
  intro i hnonaffine
  exact False.elim (hnonaffine (haffine i))

-- Proof sketch: affine inequalities and a feasible point give the nonaffine strict-feasibility
-- qualification via
-- `hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint`,
-- then apply `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility`.
/-- Primitive owner form of Corollary 6.28.4: if every inequality of `P` is affine on
`P.constraintSet`, `P.optimalValue ≠ ⊥`, and `P.feasibleSet` is nonempty, then `P` admits a
Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint
    (hopt : P.optimalValue ≠ ⊥)
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hfeas : ∃ x : E, x ∈ P.feasibleSet) :
    ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerVector lam μ := by
  have hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities :=
    P.hasStrictlyFeasiblePointOnNonaffineInequalities_of_affine_inequalities_and_feasiblePoint
      haffine hfeas
  exact P.exists_kuhnTuckerVector_of_nonaffine_strict_feasibility hopt hstrict

end OrdinaryConvexProgram

end

section

variable {𝕜 : Type v} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

namespace OrdinaryConvexProgram

variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: `hri` immediately yields a feasible point, so the primitive owner theorem
-- `exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint` applies directly.
/-- Corollary 6.28.4 (source-facing form): if an ordinary convex program has only linear
constraints, formalized by the intrinsic affineness of every inequality on `P.constraintSet`, its
optimal value is not `-∞`, and the feasible set meets `ri[𝕜](P.constraintSet)`, then a Kuhn--Tucker
vector exists. The equality constraints are already affine by the defining data of
`OrdinaryConvexProgram`. -/
theorem exists_kuhnTuckerVector_of_affine_inequalities_and_ri_feasiblePoint
    (hopt : P.optimalValue ≠ ⊥)
    (haffine : ∀ i, affOn[𝕜](extendZero (P.inequality i), P.constraintSet))
    (hri : ∃ x : E, x ∈ P.feasibleSet ∩ ri[𝕜](P.constraintSet)) :
    ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerVector lam μ := by
  refine P.exists_kuhnTuckerVector_of_affine_inequalities_and_feasiblePoint hopt haffine ?_
  rcases hri with ⟨x, hx, -⟩
  exact ⟨x, hx⟩

end OrdinaryConvexProgram

end

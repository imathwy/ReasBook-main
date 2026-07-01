import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_28_3

noncomputable section

universe u v

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.3 is the pure-inequality specialization of the Kuhn--Tucker
  existence theorem: there are no equality constraints, and the Slater-type hypothesis is a point
  of the constraint set where every inequality is strict.
- `core/canonical`: the existing Chapter 6 owners are `P.optimalValue` and
  `P.IsKuhnTuckerVector`.
- `bridge/view`: in the case `s = 0`, the textbook Kuhn--Tucker vector is expressed by the
  existing split owner with the unique empty equality block `Fin.elim0`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerVector` from `Definition_6_28_3`;
- `OrdinaryConvexProgram.optimalValue` from `Definition_6_28_3`;
- `OrdinaryConvexProgram` from `Definition_6_28_1`, via `Definition_6_28_3`;
- `OrdinaryConvexProgram.exists_kuhnTuckerVector_of_nonaffine_strict_feasibility`
  from `Theorem_6_28_3`;
- the canonical empty-index function `Fin.elim0` from mathlib's `Fin` API.

Primitive data vs derived API:
- primitive source data: a program `P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0`, a feasible
  optimal value, and a point of `P.constraintSet` where every inequality is strict;
- derived API: existence of a Kuhn--Tucker vector with no equality multiplier block.

Layer target: `source-facing`, stated directly on the existing ordinary-convex-program owners.
-/

section StrictFeasibility

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {m : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0 (Fin m) (Fin 0))

-- Proof sketch: in the pure-inequality case `s = 0`, weak feasibility is immediate from strict
-- inequalities, the equality block is vacuous, and strictness on all inequalities implies
-- strictness on the nonaffine subfamily.
/-- A point of `P.constraintSet` satisfying all inequalities strictly yields the nonaffine
strict-feasibility qualification used in Theorem 6.28.3. -/
theorem hasStrictlyFeasiblePointOnNonaffineInequalities_of_exists_strict_inequality_point
    (hstrict : ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0) :
    P.HasStrictlyFeasiblePointOnNonaffineInequalities := by
  rcases hstrict with ⟨x, hxstrict⟩
  have hxFeasible : x.1 ∈ P.feasibleSet := by
    refine (P.mem_feasibleSet x.1).2 ⟨x.2, ?_, ?_⟩
    · intro i
      exact (hxstrict i).le
    · intro j
      exact Fin.elim0 j
  refine ⟨⟨x.1, hxFeasible⟩, ?_⟩
  intro i _
  simpa [extendZero_apply] using hxstrict i

end StrictFeasibility

section Existence

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {m : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) m 0 (Fin m) (Fin 0))

-- Proof sketch: first convert the source hypothesis to
-- the corresponding strict-feasibility hypothesis in the pure-inequality case of
-- Theorem 6.28.3. Then specialize the resulting Kuhn--Tucker vector to the unique empty equality
-- multiplier block (written as `0` at the theorem surface).
/-- Corollary 6.28.3: if an ordinary convex program has only inequality constraints, its optimal
value is not `-∞`, and some point of the constraint set satisfies every inequality strictly, then
the program admits a Kuhn--Tucker vector. -/
theorem exists_kuhnTuckerVector_of_strict_inequality_point
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : ∃ x : P.constraintSet, ∀ i, P.inequality i x < 0) :
    ∃ lam : Fin m → 𝕜, P.IsKuhnTuckerVector lam 0 := by
  have hstrict_nonaffine : P.HasStrictlyFeasiblePointOnNonaffineInequalities :=
    P.hasStrictlyFeasiblePointOnNonaffineInequalities_of_exists_strict_inequality_point hstrict
  rcases exists_kuhnTuckerVector_of_nonaffine_strict_feasibility
      (P := P) hopt hstrict_nonaffine with ⟨lam, μ, hKT⟩
  have hμ : μ = 0 := Subsingleton.elim _ _
  refine ⟨lam, ?_⟩
  cases hμ
  exact hKT

end Existence

end OrdinaryConvexProgram

end

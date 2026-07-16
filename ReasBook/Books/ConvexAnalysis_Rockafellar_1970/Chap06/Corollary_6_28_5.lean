import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_28_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_28_4

noncomputable section

universe u

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.28.5 is the Kuhn--Tucker optimality criterion for an ordinary
  convex program under the qualification hypothesis used in Theorem 6.28.3.
- `core/canonical`: the Chapter 6 owners already present are `P.IsOptimalSolution`,
  `P.HasStrictlyFeasiblePointOnNonaffineInequalities`, `P.IsKuhnTuckerPoint`,
  `multiplierSet`, and the source-order saddle-point owner `Bifunction.IsSaddlePointOn` applied to
  `saddleLagrangian P`.
- `bridge/view`: the source writes a single multiplier vector `u⋆`; in the local API this is the
  split multiplier data `(lam, μ)` with `lam : Fin r → 𝕜` for inequality constraints and
  `μ : Fin s → 𝕜` for equality constraints.

Domain-style sampling used here:
- `OrdinaryConvexProgram.HasStrictlyFeasiblePointOnNonaffineInequalities` and
  `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` from `Theorem_6_28_3`;
- `OrdinaryConvexProgram.IsOptimalSolution` and `OrdinaryConvexProgram.saddleLagrangian` from
  `Definition_6_28_3`;
- `OrdinaryConvexProgram.multiplierSet` from `Definition_6_28_6` through `Theorem_6_28_4`;
- `OrdinaryConvexProgram.IsKuhnTuckerPoint`,
  `isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian`, and
  `isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint` from `Theorem_6_28_4`;
- `Bifunction.IsSaddlePointOn` from `Definition_6_28_7` via `Theorem_6_28_4`.

Primitive data vs derived API:
- primitive source data: a program `P`, the qualification hypotheses from Theorem 6.28.3, and a
  candidate point `x`;
- main source-facing criterion: existence of multiplier blocks making `(lam, μ, x)` a saddle point
  of the source-order Lagrangian;
- derived equivalent criterion: existence of multiplier blocks making `x` a Kuhn--Tucker point.

Layer target: `source-facing`. This corollary stays on the existing Chapter 6 owners for optimal
solutions, saddle points, and Kuhn--Tucker points, without introducing a second optimality or
multiplier wrapper.
-/

section Saddle

variable {𝕜 : Type*} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: for the forward direction, apply
-- `exists_kuhnTuckerVector_of_nonaffine_strict_feasibility` to obtain multipliers `(lam, μ)`, and
-- then use `isKuhnTuckerVector_and_isOptimalSolution_iff_isSaddlePoint_saddleLagrangian` to turn
-- the Kuhn--Tucker vector together with optimality of `x` into a saddle-point statement. For the
-- reverse direction, a saddle point gives both a Kuhn--Tucker vector and optimality of `x` by the
-- same equivalence, so project the optimality component.
/-- Corollary 6.28.5: under the nonaffine strict-feasibility hypothesis of Theorem 6.28.3, a
point `x` is an optimal solution of an ordinary convex program `P` if and only if there exist
multiplier blocks `(lam, μ)` representing the source multiplier vector `u⋆` such that
`((lam, μ), x)` is a saddle-point of the `WithBotTop 𝕜`-valued Lagrangian used in
Theorem 6.28.4, with
the dual variable constrained to the multiplier set `Eᵣ = multiplierSet`. -/
theorem isOptimalSolution_iff_exists_isSaddlePoint_saddleLagrangian
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities)
    (x : E) :
    P.IsOptimalSolution x ↔
      ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜,
        Bifunction.IsSaddlePointOn multiplierSet (Set.univ : Set E)
          (saddleLagrangian P) (lam, μ) x := sorry

end Saddle

section KuhnTuckerPoint

variable {𝕜 : Type*} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s)

-- Proof sketch: combine
-- `isOptimalSolution_iff_exists_isSaddlePoint_saddleLagrangian` with
-- `isSaddlePoint_saddleLagrangian_iff_isKuhnTuckerPoint`; this rewrites the existential
-- saddle-point criterion as an existential Kuhn--Tucker point criterion with the same multiplier
-- blocks.
/-- Under the hypotheses of Theorem 6.28.3, optimality of `x` is equivalently the existence of
Lagrange multipliers `(lam, μ)` such that `x` is a Kuhn--Tucker point of `P`. -/
theorem isOptimalSolution_iff_exists_isKuhnTuckerPoint
    (hopt : P.optimalValue ≠ ⊥)
    (hstrict : P.HasStrictlyFeasiblePointOnNonaffineInequalities)
    (x : E) :
    P.IsOptimalSolution x ↔
      ∃ lam : Fin r → 𝕜, ∃ μ : Fin s → 𝕜, P.IsKuhnTuckerPoint lam μ x := sorry

end KuhnTuckerPoint

end OrdinaryConvexProgram

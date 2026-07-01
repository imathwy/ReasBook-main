import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]

namespace OrdinaryConvexProgram

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.28.6 identifies Kuhn-Tucker multipliers by the source minimax formula
  for the Lagrangian and records the optimal-value interpretation of the resulting saddle value.
- `core/canonical`: the existing Chapter 6 owners are `P.IsKuhnTuckerMultiplier`,
  `P.IsKuhnTuckerVector`, `P.optimalValue`,
  `P.IsOptimalSolution`, and the Lagrangian `P.saddleLagrangian`.
- `bridge/view`: the already built owners `P.IsOptimalSolution` and `P.saddleLagrangian`,
  matching the bridge used in Theorem 6.28.4, connect the Kuhn-Tucker data to the displayed
  row-infimum / maximin / minimax formulas on the canonical extended-order codomain
  `WithBotTop 𝕜`.

Domain-style sampling used here:
- `OrdinaryConvexProgram.IsKuhnTuckerMultiplier`, `OrdinaryConvexProgram.IsKuhnTuckerVector`,
  `OrdinaryConvexProgram.optimalValue`, and `OrdinaryConvexProgram.saddleLagrangian` from the
  preceding Section 28 items;
- the source bridge owner `OrdinaryConvexProgram.IsOptimalSolution`, sampled from the nearby
  Section 28 development;
- `IsSaddlePointOn` and the row/column extremum API sampled through the Chapter 7 minimax files.
-/

variable (P : OrdinaryConvexProgram 𝕜 E (WithBotTop 𝕜) r s ι κ)

-- Proof sketch: Theorem 6.28.4 turns the Kuhn-Tucker and primal-optimality hypotheses into a
-- saddle-point of `P.saddleLagrangian`. Evaluating that saddle-point at the distinguished pair
-- `(u, x)` identifies the saddle value with the program's optimal value.
/-- The saddle value of the Lagrangian at a Kuhn-Tucker multiplier and an optimal solution equals
the optimal value of the ordinary convex program. -/
theorem saddleLagrangian_value_eq_optimalValue_of_isKuhnTuckerMultiplier_of_isOptimalSolution
    (u : (ι → 𝕜) × (κ → 𝕜)) (x : E)
    (hKT : P.IsKuhnTuckerMultiplier u) (hx : P.IsOptimalSolution x) :
    P.saddleLagrangian u x = P.optimalValue := sorry

-- Proof sketch: combine Theorem 6.28.4 with the preceding saddle-value lemma. The saddle-point
-- inequalities identify the row infimum at `u` with the global maximin value, and the
-- pointwise primal supremum of the Lagrangian gives the minimax value; all three then coincide
-- with `P.optimalValue`.
/-- For a Kuhn-Tucker multiplier, the row infimum at that multiplier pair, the global maximin
value, and the global minimax value of the Lagrangian all coincide with the optimal value of
`P`. -/
theorem saddleLagrangian_rowInf_maximin_minimax_eq_optimalValue_of_isKuhnTuckerMultiplier
    (u : (ι → 𝕜) × (κ → 𝕜)) (hKT : P.IsKuhnTuckerMultiplier u) :
    (⨅ x, P.saddleLagrangian u x) = P.optimalValue ∧
      (⨆ u, ⨅ x, P.saddleLagrangian u x) = P.optimalValue ∧
      (⨅ x, ⨆ u, P.saddleLagrangian u x) = P.optimalValue := sorry

-- Proof sketch: if `u` is Kuhn-Tucker, the previous theorem identifies the row infimum at
-- `u` with the common maximin/minimax value and gives the strict lower bound `⊥ < ...`
-- from the finiteness built into `P.IsKuhnTuckerMultiplier`. Conversely, strict lower boundedness
-- together with equality of both extremal values to that row infimum rules out the inadmissible
-- `⊥` branch of the
-- Lagrangian and recovers the defining Kuhn-Tucker conditions.
/-- Theorem 6.28.6: a multiplier pair `u = (lam, μ)` is a Kuhn-Tucker multiplier for an ordinary
convex program `P` exactly when the row infimum of the Lagrangian at `u` is strictly above
`⊥`, with both global values `sup_u inf_x L(u, x)` and `inf_x sup_u L(u, x)` equal to that row
infimum. -/
theorem isKuhnTuckerMultiplier_iff_saddleLagrangian_rowInf_finite_eq_maximin_eq_minimax
    (u : (ι → 𝕜) × (κ → 𝕜)) :
    P.IsKuhnTuckerMultiplier u ↔
      ⊥ < (⨅ x, P.saddleLagrangian u x) ∧
        (⨆ u, ⨅ x, P.saddleLagrangian u x) =
          (⨅ x, P.saddleLagrangian u x) ∧
        (⨅ x, ⨆ u, P.saddleLagrangian u x) =
          (⨅ x, P.saddleLagrangian u x) := sorry

end OrdinaryConvexProgram

end

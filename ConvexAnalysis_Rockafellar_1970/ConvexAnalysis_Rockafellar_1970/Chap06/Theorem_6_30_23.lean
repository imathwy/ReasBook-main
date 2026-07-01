import Mathlib.Analysis.Calculus.Gradient.Basic
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Corollary_6_28_2

noncomputable section

open scoped BigOperators Gradient RealInnerProductSpace

universe u

namespace Function

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}
variable (f₀ : E → ℝ) (f : Fin m → E → ℝ)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.23 characterizes feasible dual multipliers for a pure-inequality
  Lagrange dual by the existence of a point where the weighted objective has zero gradient, and
  then identifies the dual value with the attained primal weighted value.
- `core/canonical`: the project already owns the weighted objective as the finite Lagrange
  combination `L[Finset.univ](f₀, f, uStar)` together with the Chapter 6 minimizer owner
  `minimumSet`, so the theorem should be stated on that owner layer rather than through a new
  dual-feasibility wrapper or repeated `IsMinOn _ Set.univ _` packaging.
- `bridge/view`: the textbook dual-feasibility phrase is expressed here by the bounded-below
  condition from the preceding dual-feasibility criterion, while the Euclidean gradient surface is
  kept directly through `∇`.

Domain-style sampling used here:
- the finite weighted-objective notation `L[s](f₀, f, lam)` from `Corollary_6_28_2`;
- `minimumSet` from `Definition_6_27_3`;
- the Euclidean gradient owner `∇` from `Mathlib.Analysis.Calculus.Gradient.Basic`;
- the Chapter 25 singleton-subdifferential/gradient bridge used later to relate first-order
  conditions to minimizers;
- the Chapter 6 zero-subgradient minimizer criterion that turns vanishing first-order data into
  minimum-set membership for convex functions.

Primitive data vs derived API:
- primitive source data: the ambient space `E`, the objective `f₀`, the constraint family `f`,
  and the multiplier vector `uStar`;
- primitive owner object: the weighted Lagrange combination
  `L[Finset.univ](f₀, f, uStar)` and its minimum-set owner `minimumSet`;
- derived API: bounded-below versus critical-point existence for nonnegative multipliers, the
  minimum-set consequence of vanishing gradient, and the resulting value identity.

Layer target: `bridge/view`, keeping the theorem on the canonical weighted-objective owner rather
than introducing a second public owner for the dual feasible set.
-/

-- Proof sketch: for a nonnegative multiplier vector, the weighted Lagrange combination remains
-- convex. If its infimum is finite, the attainment hypothesis yields a minimizer `x`; the
-- Chapter 25 gradient/subdifferential bridge together with the Chapter 6 zero-subgradient
-- criterion then gives `∇ (L[Finset.univ](f₀, f, uStar)) x = 0`. Conversely, a vanishing
-- gradient gives the zero-subgradient condition at `x`, hence `x` is a global minimizer of the
-- convex weighted objective and its infimum is therefore strictly above `-∞`.
/-- Theorem 6.30.23: under convexity, differentiability, and attainment of every finite infimum
for nonnegative multipliers, the bounded-below condition for the weighted Lagrange combination is
equivalent to the existence of a point where its gradient vanishes. This is the gradient form of
the dual-feasibility criterion for the pure-inequality dual program. -/
theorem boundedBelow_lagrangeCombination_iff_exists_zero_gradient_of_nonneg
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    (hattain :
      ∀ uStar : Fin m → ℝ, 0 ≤ uStar →
        (⊥ : WithBotTop ℝ) < ⨅ x : E, (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ) →
          ∃ x : E, x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)))
    (uStar : Fin m → ℝ) (huStar : 0 ≤ uStar) :
    ((⊥ : WithBotTop ℝ) < ⨅ x : E, (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ)) ↔
      ∃ x : E, ∇ (L[Finset.univ](f₀, f, uStar)) x = 0 := sorry

-- Proof sketch: when `uStar ≥ 0`, the weighted Lagrange combination is convex. A vanishing
-- gradient at `x` yields the zero-subgradient condition there, so `x` is a global minimizer.
-- This owner-level conclusion is the canonical Chapter 6 minimizer statement; the value identity
-- below is a direct companion extracted from it.
/-- For a nonnegative multiplier vector, any point where the gradient of the weighted Lagrange
combination vanishes belongs to the canonical minimum set of that weighted objective. -/
theorem mem_minimumSet_lagrangeCombination_of_nonneg_of_zero_gradient
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    {uStar : Fin m → ℝ} (huStar : 0 ≤ uStar) {x : E}
    (hx : ∇ (L[Finset.univ](f₀, f, uStar)) x = 0) :
    x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)) := sorry

-- Proof sketch: first pass from the zero-gradient hypothesis to the minimum-set owner above.
-- Then rewrite minimum-set membership as pointwise domination of the weighted objective and
-- identify the corresponding `WithBotTop ℝ` infimum value.
/-- Companion value formula: for a nonnegative multiplier vector, any point where the gradient of
the weighted Lagrange combination vanishes realizes its infimum. -/
theorem lagrangeCombination_eq_iInf_of_nonneg_of_zero_gradient
    (hf₀_convex : ConvexOn ℝ Set.univ f₀)
    (hf_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (f i))
    (hf₀_diff : Differentiable ℝ f₀)
    (hf_diff : ∀ i : Fin m, Differentiable ℝ (f i))
    {uStar : Fin m → ℝ} (huStar : 0 ≤ uStar) {x : E}
    (hx : ∇ (L[Finset.univ](f₀, f, uStar)) x = 0) :
    (((L[Finset.univ](f₀, f, uStar)) x : ℝ) : WithBotTop ℝ) =
      ⨅ y : E, (((L[Finset.univ](f₀, f, uStar)) y : ℝ) : WithBotTop ℝ) := by
  have hxMin : x ∈ minimumSet (L[Finset.univ](f₀, f, uStar)) :=
    mem_minimumSet_lagrangeCombination_of_nonneg_of_zero_gradient
      f₀ f hf₀_convex hf_convex hf₀_diff hf_diff huStar hx
  refine le_antisymm ?_ (iInf_le _ x)
  refine le_iInf fun y ↦ ?_
  exact WithBotTop.coe_le_coe.mpr (mem_minimumSet_iff.mp hxMin y)

end

end Function

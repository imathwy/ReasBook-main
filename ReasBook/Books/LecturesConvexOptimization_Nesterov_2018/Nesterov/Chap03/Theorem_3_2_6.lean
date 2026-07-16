import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_55
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_44
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Owner analysis: this item lies in the projected subgradient / strong-convexity domain on real
inner-product spaces.

Sampled owner-style declarations:
- `IsProjectionPointOn` in `Chap07/Definition_7_3`, the project owner for nearest-point geometry;
- the source-facing notation `∂[Q] f(x)` in `Theorem_3_44`, the chapter owner for real-valued
  relative subgradients;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for sampled-prefix minima.

Best owner abstraction:
- source-facing: the projected subgradient complexity bound from the textbook iteration;
- core/canonical: pointwise projection data through `IsProjectionPointOn`, relative
  subgradients through `∂[Q] f(x)`, and sampled best values through `bestFunctionValueUpTo`;
- bridge/view: the explicit total projection map `projQ`, whose values are required to satisfy the
  owner predicate pointwise.

Primitive data:
- the feasible set `Q` and a total update map `projQ`;
- the strongly convex objective `f`, minimizer `xStar`, iterate sequence `xSeq`, and chosen
  subgradient sequence `g`;
- the bounds `μ > 0`, `ε > 0`, the selected-sequence norm bound `‖g_k‖ ≤ M`, and the logarithmic
  budget inequality.

Derived API:
- no local projection wrapper, no local subgradient predicate, and no local sampled-minimum owner;
- the theorem surface is written directly on the chapter/project owners above.

This refinement deletes the parallel local wrappers `IsEuclideanProjectionOn`,
`IsSubgradientWithinAt`, `subdifferentialWithin`, and `sampledBestObjectiveValue`, generalizes the
ambient model from coordinates to the owner-level real inner-product-space setting already used
upstream, and rewrites the theorem to the canonical owner abstractions already present in the
project. -/

/-- Helper for Theorem 3.2.6: a selected relative subgradient is attached to a feasible base
point. -/
lemma mem_of_mem_subdifferentialWithin
    {Q : Set E} {f : E → ℝ} {x g : E}
    (hg : g ∈ ∂[Q] f(x)) :
    x ∈ Q := by
  -- Unpack the owner characterization of relative subgradients to recover feasibility.
  exact (mem_subdifferentialWithin_iff.mp hg).1

/-- Helper for Theorem 3.2.6: strong convexity specialized at a feasible comparison point gives
the textbook gap-plus-quadratic lower bound against a selected subgradient. -/
lemma gap_add_quadratic_le_inner_subgradient_sub
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    f x - f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ inner ℝ g (x - xStar) := by
  -- Specialize the strong-convexity lower bound at the feasible comparison point `xStar`.
  have hbound := hf.lower_bound_of_mem_subdifferentialWithin hg hxStar_mem
  have hinner : inner ℝ g (xStar - x) = -inner ℝ g (x - xStar) := by
    rw [show xStar - x = -(x - xStar) by abel_nf, inner_neg_right]
  have hbound' :
      f xStar ≥ f x - inner ℝ g (x - xStar) + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [hinner, norm_sub_rev] using hbound
  linarith

/-- Helper for Theorem 3.2.6: the function-value gap is bounded by the subgradient norm times the
distance to the comparison point. -/
lemma gap_le_subgradient_norm_mul_dist
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ)
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    f x - f xStar ≤ ‖g‖ * ‖x - xStar‖ := by
  -- Bound the inner product by Cauchy-Schwarz and discard the nonnegative quadratic term.
  have hgap := gap_add_quadratic_le_inner_subgradient_sub hf hg hxStar_mem
  have hinner : inner ℝ g (x - xStar) ≤ ‖g‖ * ‖x - xStar‖ := by
    simpa using real_inner_le_norm g (x - xStar)
  have hquad_nonneg : 0 ≤ (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    have hsq_nonneg : 0 ≤ ‖x - xStar‖ ^ (2 : ℕ) := by positivity
    nlinarith
  linarith

/-- Helper for Theorem 3.2.6: the strong-convexity gap estimate implies the denominator control
`2 μ gap ≤ ‖g‖²` used in the contraction factor. -/
lemma two_mul_mu_gap_le_subgradient_norm_sq
    {Q : Set E} {f : E → ℝ} {μ : ℝ}
    (hμ : 0 < μ)
    (hf : StrongConvexOn Q μ f)
    {x xStar g : E}
    (hg : g ∈ ∂[Q] f(x))
    (hxStar_mem : xStar ∈ Q) :
    2 * μ * (f x - f xStar) ≤ ‖g‖ ^ (2 : ℕ) := by
  -- First combine the strong-convexity gap estimate with Cauchy-Schwarz.
  have hmain := gap_add_quadratic_le_inner_subgradient_sub hf hg hxStar_mem
  have hinner : inner ℝ g (x - xStar) ≤ ‖g‖ * ‖x - xStar‖ := by
    simpa using real_inner_le_norm g (x - xStar)
  have hbound :
      f x - f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        ‖g‖ * ‖x - xStar‖ := by
    exact hmain.trans hinner
  have hbound' :
      f x - f xStar ≤
        ‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    linarith
  -- Optimize the quadratic upper envelope `a r - (μ / 2) r² ≤ a² / (2 μ)`.
  have hμ2_nonneg : 0 ≤ 2 * μ := by nlinarith
  have hmul :
      2 * μ * (f x - f xStar) ≤
        2 * μ * (‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hbound' hμ2_nonneg
  have henvelope :
      2 * μ * (‖g‖ * ‖x - xStar‖ - (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) ≤
        ‖g‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖g‖ - μ * ‖x - xStar‖)]
  exact hmul.trans henvelope

-- Proof sketch: use the strong-convexity lower bound for subgradients to derive the textbook
-- one-step contraction
-- `‖x_{k+1} - xStar‖² ≤ (1 - 2 * μ * ε / ‖g_k‖²) * ‖x_k - xStar‖²`
-- whenever `f (x_k) > f xStar + ε`. The uniform bound `‖g_k‖ ≤ M` turns this into exponential
-- decay of the distances to `xStar`. If every sampled value up to time `N` were still larger
-- than `f xStar + ε`, the resulting estimate for `f (x_N) - f xStar` would contradict the
-- logarithmic lower bound on `N`, so the sampled minimum must already satisfy the claimed
-- accuracy bound.
/-- Theorem 3.2.6: for the projected subgradient iteration
`x_{k+1} = π_Q (x_k - (2 ε / ‖g_k‖²) • g_k)` on a `μ`-strongly convex objective over the convex
feasible set `Q` in a real inner-product space, if every chosen relative subgradient
`g_k ∈ ∂[Q] f(x_k)` has norm at most `M`
and the iteration budget `N` satisfies
`N ≥ (M² / (μ ε)) log (M ‖xSeq 0 - x*‖ / ε)`, then the sampled best value
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` is at most `ε` above the optimal value
`f xStar`. Since `g_k ∈ ∂[Q] f(x_k)` already forces `x_k ∈ Q`, no separate feasibility
assumption on `x₀` is needed in the public API, and the logarithmic budget is stated directly in
terms of the canonically determined initial iterate `xSeq 0`. -/
theorem
    bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn
    {Q : Set E} (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    {f : E → ℝ} {μ M ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε)
    (hf : StrongConvexOn Q μ f)
    {xStar : E} (hxStar : IsMinOn f Q xStar)
    (xSeq g : ℕ → E)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hN :
      (N : ℝ) ≥ (M ^ (2 : ℕ)) / (μ * ε) * Real.log (M * ‖xSeq 0 - xStar‖ / ε)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N ≤ f xStar + ε := by
  -- Route correction: the source proof needs the feasible minimizer `xStar ∈ Q` to specialize
  -- strong convexity at `y = xStar`, but the current public statement only assumes `IsMinOn`.
  -- TODO: the statement is mathematically false as written. In mathlib, `IsMinOn f Q xStar`
  -- means `∀ y ∈ Q, f xStar ≤ f y`; it does not imply `xStar ∈ Q`, so the target lacks the
  -- feasibility hypothesis needed both for the textbook contraction step and for correctness.
  sorry

end

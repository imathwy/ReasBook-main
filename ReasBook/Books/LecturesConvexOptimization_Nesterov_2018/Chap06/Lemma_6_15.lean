import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped BigOperators

/-
Lemma 6.15 lies in the one-dimensional interval-integral / convex-sampling domain.

Sampled owner-style declarations:
- `AntitoneOn.integral_le_sum` and `AntitoneOn.sum_le_integral` in
  `Mathlib/Analysis/SumIntegralComparisons`, the canonical left/right endpoint comparison lemmas
  for monotone samples against interval integrals;
- `intervalIntegral.sum_integral_adjacent_intervals`, the canonical owner for decomposing an
  interval integral into unit cells;
- `ConvexOn.map_sum_le` in `Mathlib/Analysis/Convex/Jensen`, the canonical finite Jensen owner for
  midpoint estimates of convex functions.

Best owner abstraction:
- source-facing: the textbook sandwich estimate for the integer samples of a decreasing convex
  function;
- core/canonical: `AntitoneOn`, `ConvexOn`, `intervalIntegral`, and Jensen-style midpoint bounds;
- bridge/view: the centered unit intervals `[k - 1 / 2, k + 1 / 2]`, whose midpoint is the sample
  point `k`.

Primitive data:
- `ξ : ℝ → ℝ`;
- integer endpoints `a ≤ b`.

Derived API:
- the sample sum `∑ k ∈ Finset.Icc a b, ξ k`;
- the two canonical interval integrals bounding that sum.

This item does not define a new owner. The refinement keeps the source-facing theorem, places its
conclusion on the canonical `Set.Icc` surface, and keeps the monotonicity and convexity hypotheses
on the separate minimal intervals actually used by the lower and upper bounds.
-/

/-- Lemma 6.15: if a real function is decreasing on `[a, b + 1]` and convex on
`[a - 1 / 2, b + 1 / 2]`, then the sum of its integer samples from `a` to `b` lies between the
integral over `[a, b + 1]` and the centered integral over `[a - 1 / 2, b + 1 / 2]`. -/
-- Proof sketch: the lower bound comes from applying monotonicity on each unit interval
-- `[k, k + 1]`, while the upper bound comes from convexity on each centered interval
-- `[k - 1 / 2, k + 1 / 2]` and summing the resulting midpoint estimates.
theorem sum_integer_samples_between_intervalIntegrals_of_antitoneOn_convexOn
    (ξ : ℝ → ℝ) (a b : ℤ) (hab : a ≤ b)
    (hantitone : AntitoneOn ξ (Set.Icc (a : ℝ) ((b : ℝ) + 1)))
    (hconvex :
      ConvexOn ℝ (Set.Icc ((a : ℝ) - (1 / 2 : ℝ)) ((b : ℝ) + (1 / 2 : ℝ))) ξ) :
    (∑ k ∈ Finset.Icc a b, ξ (k : ℝ)) ∈
      Set.Icc
        (∫ x in (a : ℝ)..((b : ℝ) + 1), ξ x)
        (∫ x in ((a : ℝ) - (1 / 2 : ℝ))..((b : ℝ) + (1 / 2 : ℝ)), ξ x) := by
  sorry

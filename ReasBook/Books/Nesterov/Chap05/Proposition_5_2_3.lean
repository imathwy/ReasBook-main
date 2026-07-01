import Mathlib
import Nesterov.Chap05.Definition_5_2_8
import Nesterov.Chap05.Definition_5_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Proposition 5.2.3 lies in the Chapter 5 strongly-convex quadratic-regime entry-time domain on
real normed spaces.

Primary mathematical domain:
* strongly convex objectives together with the canonical strong-convexity specialization of the
  Chapter 4 global rate estimate, and the resulting Chapter 5 quadratic region
  `𝒬[f | f(x*), M_f]`

Sampled owner-style declarations:
* `selfConcordantQuadraticRegion` and the notation `𝒬[f | f*, M_f]` in `Definition_5_2_9`, the
  Chapter 5 source-facing quadratic-region owner;
* `strongConvexSelfConcordanceConstant` in `Definition_5_2_8`, the chapter owner for the
  canonical strong-convexity-induced self-concordance constant
  `M_f = L₃ / (2 σ₂^(3 / 2))`;
* `mem_selfConcordantQuadraticRegion_iff_mem_cubicNewtonQuadraticDecreaseRegion` in
  `Definition_5_2_9`, the canonical bridge to the older Chapter 4 comparison region;
* `cubicNewton_gap_le_inverse_square_rate_of_bounded_sublevel` in `Chap04/Theorem_4_2_2`, the
  nearby chapter theorem whose strong-convexity specialization produces the canonical
  coefficient `2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`;
* `StrongConvexOn.quadratic_growth_of_isMinOn` in `Chap02/Theorem_2_30`, the canonical
  quadratic-growth owner behind that specialization;
* `stronglyConvexHalfGapIndex` in `Definition_5_2_10`, the downstream owner showing that the
  natural strong-convexity scaling parameter is `Δ = M_f * √gap`, not a local wrapper.

Best owner abstraction:
* source-facing: the first index where the iterate enters the Chapter 5 region
  `𝒬[f | f(x*), M_f]`;
* core/canonical: the Chapter 5 region owner together with the canonical strong-convexity
  specialization of the Chapter 4 inverse-square rate;
* bridge/view: the comparison between the Chapter 5 threshold `1 / (8 M_f^2)`, the Chapter 4
  multiplication-form region `cubicNewtonQuadraticDecreaseRegion`, and the scaled gap
  `Δ = M_f * √gap`.

Primitive data:
* the strong-convexity parameter sign `0 < σ₂`;
* the iterate family `x`;
* the minimizer `x*` together with the canonical owner witness `IsMinOn f Set.univ x*`;
* the global-rate constants `c`, `p`;
* the canonical strong-convexity-specialized rate bound `hrate`;
* the least-entry witness `hN`.

Derived API:
* the Chapter 5 quadratic-region owner `𝒬[f | f(x*), M_f]`;
* the strong-convexity scaling `Δ M_f gap`.

This refinement keeps Proposition 5.2.3 source-facing while removing the noncanonical free radius
parameter `D`. The theorem surface now uses the canonical strong-convexity-specialized rate
coefficient that one obtains from the Chapter 4 inverse-square estimate via
`StrongConvexOn.quadratic_growth_of_isMinOn`, so the public statement no longer pretends that an
arbitrary bounded-sublevel witness is itself controlled by strong convexity. The entry condition
stays phrased directly with the Chapter 5 owner `𝒬[f | f(x*), M_f]` rather than the older
Chapter 4 comparison region. -/

/-- The strong-convex scaled gap `Δ = M_f * √gap` used in the textbook complexity estimate for
entering the quadratic-convergence region. In source-facing applications the gap is the
suboptimality `f(x) - f(x*)`, whose nonnegativity is supplied by `IsMinOn`. -/
def stronglyConvexScaledGap (Mf gap : ℝ) : ℝ :=
  Mf * Real.sqrt gap

/- Source-facing Lean notation for the textbook strongly-convex scaled gap owner `Δ`. -/
scoped[StronglyConvexScaledGap] notation:max "Δ" => stronglyConvexScaledGap

open scoped SelfConcordantQuadraticRegion StronglyConvexScaledGap

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section

variable {σ2 : ℝ} {L3 : NNReal}

-- Proof sketch: start from the canonical strong-convexity specialization of the Chapter 4 rate
-- bound,
-- `f(x_k) - f(x*) ≤ 2^(5/2) c M_f (f(x₀) - f(x*))^(3/2) / k^p`
-- with `M_f = L₃ / (2 * σ₂^(3 / 2))`, compare it to the defining threshold
-- `f(x) - f(x*) ≤ 1 / (8 M_f^2)` of `𝒬[f | f(x*), M_f]`, and choose the first positive integer
-- above the scalar root. Converting that natural-number rounding into a real inequality yields
-- the final `1 + ...` bound on the least entry index.
/-- Proposition 5.2.3: assume the iterate sequence `x_k` satisfies the global rate
`f(x_k) - f(x*) ≤ (2^(5/2) c M_f / k^p) * (f(x₀) - f(x*))^(3/2)`, where `x*` is a global
minimizer of `f`,
`M_f = L₃ / (2 * σ₂^(3 / 2))`, then `N` is bounded by the corresponding constant multiple of
`Δ_f(x₀)^(3 / p)`, with the natural-number rounding written as
`1 + (2^(11/2) c Δ_f(x₀)^3)^(1 / p)`. Here `N` is the least index for which `x_N` enters the
Chapter 5 quadratic region `𝒬[f | f(x*), M_f]`. Under `L₃ > 0`, the Chapter 5 threshold
`f(x_N) - f(x*) ≤ 1 / (8 M_f^2)` is equivalent to the older Chapter 4 comparison-region
condition `2 L₃² (f(x_N) - f(x*)) ≤ σ₂³`. -/
theorem stronglyConvex_firstSourceQuadraticConvergenceRegionEntryIndex_le
    {f : E → ℝ}
    (x : ℕ → E) (xStar : E) {c p : ℝ}
    (hσ2 : 0 < σ2)
    (hmin : IsMinOn f Set.univ xStar)
    (hc : 0 < c) (hp : 0 < p)
    (hrate :
      ∀ k : ℕ, 0 < k →
        f (x k) - f xStar ≤
          (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c *
            (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) *
            Real.rpow (f (x 0) - f xStar) (3 / 2 : ℝ)) /
            Real.rpow (k : ℝ) p)
    {N : ℕ}
    (hN :
      IsLeast
        {n : ℕ | x n ∈ 𝒬[f | f xStar, strongConvexSelfConcordanceConstant σ2 L3]}
        N) :
    (N : ℝ) ≤
      1 +
      Real.rpow
        (Real.rpow (2 : ℝ) (11 / 2 : ℝ) * c *
          (Δ (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) (f (x 0) - f xStar)) ^ (3 : ℕ))
        (1 / p) := sorry

end

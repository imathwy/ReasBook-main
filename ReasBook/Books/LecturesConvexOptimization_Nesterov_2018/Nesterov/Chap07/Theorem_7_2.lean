import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- Theorem 7.2 lies in the chapter's relative-accuracy / lower-level subgradient-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the scalar radius-parameter owner used in
  Chapter 7;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, whose lower-level scheme
  input has type `ℕ → ℝ → X`;
- `schemeSNRestartingStep` in `Algorithm_7_4.lean`, which uses the same scalar-parameter scheme
  surface;
- `direct_structure_iterate_value_le_one_add_delta_mul_optimal_value` in `Theorem_7_4.lean`, the
  sibling relative-error conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.2's conversion from a stagewise subgradient-approximation gap bound to
  a one-shot relative-value guarantee;
- core/canonical: a lower-level scheme `G : ℕ → ℝ → X` evaluated at a scalar radius parameter
  `rhoHat`;
- bridge/view: the specific floor-chosen index `⌊1 / (α⁴ δ²)⌋`.

Primitive data:
- `f`, `G`, `rhoHat`, `α`, `δ`, and `fStar`;
- the stagewise estimate for `G k rhoHat`.

Derived API:
- the chosen stage index `⌊1 / (α⁴ δ²)⌋`;
- the final relative-value inequality.

This file keeps the source-facing theorem directly, but it aligns the scheme input with the
chapter's canonical scalar-parameter owner surface and exposes the active scalar side conditions
instead of a stronger interval wrapper plus a hidden sign assumption on `fStar`.
-/

variable {X : Type u}

-- Proof sketch: apply the assumed estimate at
-- `N = Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))`, then use
-- `Nat.floor_lt_add_one` to deduce `1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)) ≤ N + 1` and hence
-- `1 / (α ^ (2 : ℕ) * Real.sqrt (N + 1 : ℝ)) ≤ δ` from `0 < α` and `0 < δ`, then multiply by
-- `fStar` using `0 ≤ fStar`.
/-- Theorem 7.2 [Chapter7_1.json:15]: if `α` and `δ` are positive, `fStar` is nonnegative, and every iterate
`G k rhoHat` satisfies the subgradient approximation estimate
`f (G k rhoHat) - fStar ≤ (1 / (α^2 * √(k + 1))) * fStar`, then the iterate with index
`⌊1 / (α^4 δ^2)⌋` satisfies `f (G_N rhoHat) ≤ (1 + δ) fStar`. -/
theorem subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value
    (f : X → ℝ) (G : ℕ → ℝ → X) (rhoHat α δ fStar : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hfStar_nonneg : 0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (G k rhoHat) - fStar ≤
          (1 / (α ^ (2 : ℕ) * Real.sqrt (k + 1 : ℝ))) * fStar) :
    f (G (Nat.floor (1 / (α ^ (4 : ℕ) * δ ^ (2 : ℕ)))) rhoHat) ≤ (1 + δ) * fStar := sorry

end

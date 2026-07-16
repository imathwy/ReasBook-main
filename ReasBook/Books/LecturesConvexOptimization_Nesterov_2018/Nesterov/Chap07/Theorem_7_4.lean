import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u}

/- Theorem 7.4 lies in the chapter's relative-accuracy / lower-level direct-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the Chapter 7 owner for the scalar radius
  parameter used by the lower-level scheme;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for relative-value accuracy;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, which uses the same
  lower-level scheme surface `ℕ → ℝ → X`;
- `subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value` in
  `Theorem_7_2.lean`, the sibling one-shot relative-value conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.4's conversion of the stagewise direct-structure gap estimate into a
  one-shot relative-value bound at a floor-chosen index;
- core/canonical: a lower-level scheme `S : ℕ → ℝ → X` evaluated at the Chapter 7 radius owner
  `aPrioriRadiusEstimate f γ0 x0`;
- bridge/view: the specific stage index `⌊2 / (α² δ)⌋`, with `IsRelativeAccuracy` remaining the
  ambient chapter owner for the stronger two-sided notion.

Primitive data:
- `f`, `S`, `x0`, `α`, `γ0`, `δ`, and `fStar`;
- the stagewise gap estimate for `f (S k (aPrioriRadiusEstimate f γ0 x0))`;
- the source proof's comparison `α * f x0 ≤ fStar`.

Derived API:
- the floor-chosen stage `⌊2 / (α² δ)⌋`;
- the final upper bound `f (S_N (aPrioriRadiusEstimate f γ0 x0)) ≤ (1 + δ) fStar`.

Source/core/bridge triage:
- source-facing: the theorem's upper-bound conclusion at the chosen stage;
- core/canonical: `aPrioriRadiusEstimate` and the lower-level scheme surface `ℕ → ℝ → X`;
- bridge/view: the arithmetic passage from the stagewise coefficient `2 / (α² (k + 1))` to the
  target coefficient `δ`.

The theorem is the Chapter 7 arithmetic conversion step, so it should expose the source proof's
primitive comparison `α * f x0 ≤ fStar` rather than hiding it inside an already-normalized
`fStar`-scaled estimate. The ambient Euclidean and convex-analytic setup belongs to the
construction of the direct-structure scheme and its gap bound, not to this conversion lemma
itself, so those stronger assumptions are omitted here.
-/

-- Proof sketch: evaluate the assumed gap estimate at
-- `N = Nat.floor (2 / (α ^ (2 : ℕ) * δ))`. The floor inequality implies
-- `2 / (α ^ (2 : ℕ) * (N + 1 : ℝ)) ≤ δ`, so the gap is at most `δ * (α * f x0)`. Then use the
-- source comparison `α * f x0 ≤ fStar` to get
-- `f (S N (aPrioriRadiusEstimate f γ0 x0)) - fStar ≤ δ * fStar`, which rearranges to the claimed
-- upper bound.
/-- Theorem 7.4 [Chapter7_1.json:27]: if `α` and `δ` are positive, the Chapter 7 normalization
`α * f(x₀) ≤ f*` holds, and every direct-structure iterate at radius
`aPrioriRadiusEstimate f γ0 x0 = (1 / γ₀(F)) f(x₀)` satisfies the gap estimate
`f (S_k ((1 / γ₀(F)) f(x₀))) - f* ≤ (2 / (α(F)^2 (k + 1))) * α(F) * f(x₀)`, then the iterate
with index `⌊2 / (α(F)^2 δ)⌋` satisfies
`f (S_N ((1 / γ₀(F)) f(x₀))) ≤ (1 + δ) f*`. -/
theorem direct_structure_iterate_value_le_one_add_delta_mul_optimal_value
    (f : X → ℝ) (S : ℕ → ℝ → X) (x0 : X) (α γ0 δ fStar : ℝ)
    (hα : 0 < α) (hδ : 0 < δ)
    (hOptimalValue_lower : α * f x0 ≤ fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (S k (aPrioriRadiusEstimate f γ0 x0)) - fStar ≤
          (2 / (α ^ (2 : ℕ) * (k + 1 : ℝ))) * (α * f x0)) :
    f (S (Nat.floor (2 / (α ^ (2 : ℕ) * δ))) (aPrioriRadiusEstimate f γ0 x0)) ≤
      (1 + δ) * fStar := sorry

end

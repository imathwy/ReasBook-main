import Nesterov.Chap05.Definition_5_2_10
import Nesterov.Chap05.Definition_5_2_11
import Nesterov.Chap05.Proposition_5_2_3

open scoped BigOperators SelfConcordantQuadraticRegion
open scoped StronglyConvexHalfGapIndex StronglyConvexMultiStageAccelerationNotation
open scoped StronglyConvexScaledGap

noncomputable section

universe u

/- Theorem 5.2.5 lies in the Chapter 5 multistage acceleration domain for strongly convex
self-concordant objectives.

Sampled declarations in this domain:
* `stronglyConvexHalfGapIndex` from `Definition_5_2_10`, the chapter owner for the source
  positive threshold index `k_p`;
* `stronglyConvexMultiStageAccelerationStageLength`,
  `stronglyConvexMultiStageAccelerationTotalLowerLevelIterations`,
  `stronglyConvexMultiStageAccelerationOrbit`, and
  `IsStronglyConvexMultiStageAccelerationStoppingStage` from `Definition_5_2_11`, the chapter
  owners for the stage schedule, cumulative lower-level work, multistage orbit `(5.2.28)`, and
  first stopping stage;
* `one_le_stronglyConvexHalfGapIndex` and
  `one_le_stronglyConvexMultiStageAccelerationStageLength`, the derived owner API ensuring that
  the source schedule uses positive stage lengths;
* `Nat.ceil` / `Nat.le_ceil`, the canonical mathlib owner for the ceiling schedule appearing in
  the source formula for `t_k`;
* `Real.logb`, the canonical base-`2` logarithm owner used in the stopping-stage estimate.

Source/core/bridge triage:
* source-facing: Theorem 5.2.5 itself, stated for the textbook multistage strategy with stopping
  region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* core/canonical: the chapter owner orbit
  `stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0` together with the canonical
  least-stage predicate `IsStronglyConvexMultiStageAccelerationStoppingStage ... T`;
* bridge/view: the arithmetic passage from the stagewise rate bound and the ceiling schedule to
  the logarithmic bound on the stopping stage and the geometric-series bound on the total work.

Primitive data:
* the canonical positive half-gap index `k_p`;
* the source stopping region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* the recursive outer orbit `y_k`;
* the source first-stopping-stage witness `T`;
* the stagewise rate estimate inherited from the lower-level method.

Derived API:
* the total number of lower-level iterations performed before the stopping stage;
* the stage bound `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`;
* the resulting total-work bound.

This refinement restores the source theorem surface. The previous version replaced the textbook
strategy by an abstract geometric-decay lemma over an auxiliary gap observable and by an extra
terminal-region bridge hypothesis. Here the main declarations speak directly about the source
ceiling schedule and the source stopping threshold. -/

section

variable {E : Type u} {f : E → ℝ}
variable {innerIterate : ℕ → E → E} {c p fStar : ℝ} {Mf : NNReal} {x0 : E}

private theorem stoppingStageSetup
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hTpos : 0 < T) (hp : 0 < p) :
    x0 ∉ 𝒬[f | fStar, Mf] ∧
      0 < Mf ∧
      0 < f x0 - fStar ∧
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty := by
  have hx0 : x0 ∉ 𝒬[f | fStar, Mf] := by
    simpa using
      stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage hT hTpos
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hgap : 0 < f x0 - fStar :=
    gap_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hkp :
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty :=
    stronglyConvexHalfGapAdmissibleIndices_nonempty hp hgap
  exact ⟨hx0, hMf, hgap, hkp⟩

-- Proof sketch: prove by induction that
-- `f (y[innerIterate | kp; p; x0] k) - f* ≤ (1 / 2)^k * (f x₀ - f*)` for all
-- `k ≤ T - 1`, using the source
-- stagewise estimate together with the ceiling lower bound
-- `((1 / 2 : ℝ) ^ (k / (2 * p))) * kp ≤ t[kp; p] k` and the defining property of `kp`. Since
-- the
-- initial point lies outside the source quadratic-convergence region, one first derives the
-- nondegenerate regime `0 < Mf` and `0 < f x₀ - f*`, hence the admissible-index set defining
-- `k_p` is automatically nonempty. Since the preterminal stage output lies outside the source
-- quadratic-convergence region, one has
-- `1 / (8 M_f^2) < f (y[innerIterate | kp; p; x0] (T - 1)) - f*`, which rearranges to
-- `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`.
/-- Theorem 5.2.5: let `k_p = k[c, M_f; p](f(x₀) - f*)`, and consider
the multistage strategy `(5.2.28)` whose `k`-th stage (`k ≥ 1`) runs the lower-level method for
`t_k = ⌈k_p / 2^((k - 1) / (2p))⌉` steps and stops once
`f(y_k) - f* ≤ 1 / (8 M_f^2)`. If each stage output satisfies the source rate estimate
`f(y_{k+1}) - f* ≤ (2^(5/2) c M_f / t_{k+1}^p) * (f(y_k) - f*)^(3/2)`, then the total
number of stages satisfies `T ≤ 4 + log₂ ((Δ M_f (f(x₀) - f*))^2)`, equivalently
`T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`, provided that `p > 0`. -/
theorem selfConcordantStronglyConvexStrategy_totalStages_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (T : ℝ) ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
  by_cases hzero : T = 0
  · sorry
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hzero
    rcases stoppingStageSetup hT hTpos hp with ⟨hx0, hMf, hgap, hkp⟩
    sorry

-- Proof sketch: write
-- `N = ∑_{k=0}^{T-1} t k`, use `Nat.ceil x ≤ x + 1` to bound each stage length by
-- `1 + kp / 2^{k / (2p)}`, sum the geometric series, and insert the stopping-stage estimate from
-- `selfConcordantStronglyConvexStrategy_totalStages_le`.
/-- Theorem 5.2.5 also bounds the total number `N` of lower-level iterations in the multistage
strategy `(5.2.28)` by
`4 + log₂ ((Δ M_f (f(x₀) - f*))^2) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, equivalently
`4 + log₂ (M_f^2 (f(x₀) - f*)) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, assuming
`p > 0`. -/
theorem selfConcordantStronglyConvexStrategy_totalLowerLevelIterations_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
        k[c, Mf; p](f x0 - fStar) p T : ℝ) ≤
      4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) +
        (Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
        (k[c, Mf; p](f x0 - fStar) : ℝ) := by
  by_cases hzero : T = 0
  · sorry
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hzero
    rcases stoppingStageSetup hT hTpos hp with ⟨hx0, hMf, hgap, hkp⟩
    sorry

end

import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap07.Algorithm_7_14
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_65
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_62
import LecturesConvexOptimization_Nesterov_2018.Chap07.Lemma_7_14
import LecturesConvexOptimization_Nesterov_2018.Chap07.Theorem_7_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient HessianDualLocalNorm

noncomputable section

universe u

section

variable {X : Type u}

/-- The explicit rate term
`δ_k = 2 (√(ν / (k + 1)) + ν / (k + 1))
  (1 + log (2 + (3 / 2) √(ν (k + 1))))`
from the relative-accuracy estimate for the barrier subgradient method. -/
def barrierSubgradientRelativeAccuracyDelta (ν : ℝ) (k : ℕ) : ℝ :=
  2 * (Real.sqrt (ν / ((k : ℝ) + 1)) + ν / ((k : ℝ) + 1)) *
    (1 + Real.log (2 + (3 / 2 : ℝ) * Real.sqrt (ν * ((k : ℝ) + 1))))

/-- The explicit relative-accuracy rate is positive whenever the barrier parameter `ν` is
positive. -/
theorem barrierSubgradientRelativeAccuracyDelta_pos {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    0 < barrierSubgradientRelativeAccuracyDelta ν k := sorry

/-- The geometric mean of the positive values `ψ(x₀), …, ψ(x_k)`. -/
def positiveIterateGeometricMean
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) : ℝ :=
  Real.rpow
    (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
    (1 / ((k : ℝ) + 1))

/-- Expanding `positiveIterateGeometricMean ψ x k` gives the geometric mean of the first `k + 1`
positive values along the iterate sequence. -/
@[simp] theorem positiveIterateGeometricMean_def
    (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X) (k : ℕ) :
    positiveIterateGeometricMean ψ x k =
      Real.rpow
        (Finset.prod (Finset.range (k + 1)) fun i ↦ (ψ (x i) : ℝ))
        (1 / ((k : ℝ) + 1)) :=
  rfl

section RelativeAccuracyBridge

variable (ψ : X → {r : ℝ // 0 < r}) (x : ℕ → X)
variable (ψStar : {r : ℝ // 0 < r}) {ν : ℝ} (k : ℕ)

-- Proof sketch: rewrite the arithmetic mean of the logarithms as the logarithm of the geometric
-- mean, then exponentiate the bound
-- `log ψ⋆ - (1 / (k + 1)) ∑_{i=0}^k log ψ(x_i) ≤ δ_k`.
/-- Exponentiating the logarithmic average estimate yields the geometric-mean lower bound
`[∏_{i=0}^k ψ(x_i)]^(1 / (k + 1)) ≥ ψ⋆ exp(-δ_k)`. This is the generic bridge/view step used in
Theorem 7.16 once the owner-level logarithmic estimate has been established. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
    (hlog_rate :
      Real.log (ψStar : ℝ) -
          (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (x i) : ℝ)) /
            ((k : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν k)
    :
    positiveIterateGeometricMean ψ x k ≥
      (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k) := sorry

/-- Once the geometric mean is known to lie between `ψ⋆ exp (-δ_k)` and `ψ⋆`, it is a
relative-scale `δ_k` approximation of `ψ⋆` in the sense of Definition 7.65. -/
theorem positiveIterateGeometricMean_isRelativeScaleDeltaApproximation_of_bounds
    (hexp_bound :
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k))
    (hmean_le : positiveIterateGeometricMean ψ x k ≤ (ψStar : ℝ))
    (hδ_pos : 0 < barrierSubgradientRelativeAccuracyDelta ν k) :
    IsRelativeScaleDeltaApproximation
      (ψStar : ℝ)
      (barrierSubgradientRelativeAccuracyDelta ν k)
      (positiveIterateGeometricMean ψ x k) := sorry

-- Proof sketch: combine the exponential estimate with the elementary inequality
-- `exp (-t) ≥ 1 - t`.
/-- The exponential lower bound implies the weaker linear lower bound obtained from
`exp (-δ_k) ≥ 1 - δ_k`. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_one_sub_rate_of_exp_bound
    (hexp_bound :
      positiveIterateGeometricMean ψ x k ≥
        (ψStar : ℝ) * Real.exp (-barrierSubgradientRelativeAccuracyDelta ν k)) :
    positiveIterateGeometricMean ψ x k ≥
      (ψStar : ℝ) * (1 - barrierSubgradientRelativeAccuracyDelta ν k) := sorry

end RelativeAccuracyBridge

section BarrierSubgradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/- Theorem 7.16 lies in Chapter 7's primal barrier-subgradient / relative-scale maximization
domain.

Mandatory domain-style sampling:
- `BarrierSubgradientMethod` in `Chap07/Algorithm_7_14`, the source-facing owner of the primal
  barrier-subgradient run `(7.3.33)`;
- `IsMaxOn`, the canonical maximizer predicate for the positive optimum `x⋆`;
- `logarithmicTransform_has_constrained_subgradient_norm_le_one_and_concaveOn` in
  `Chap07/Lemma_7_14`, the chapter bridge that turns positivity and concavity of `ψ` into the
  logarithmic barrier-subgradient hypotheses needed for the dual explicit-rate owner;
- `DualBarrierSubgradientMethod.maximalGap_le_explicit_rate` in `Chap07/Theorem_7_15`, the
  upstream explicit-rate owner whose scalar error term is recorded below as `δ_k`.

Best owner abstraction:
- source-facing: Theorem 7.16 for an actual `BarrierSubgradientMethod` and an actual maximizing
  point `x⋆`;
- core/canonical: `BarrierSubgradientMethod`, `IsMaxOn`, and the generic owner
  `positiveIterateGeometricMean`;
- bridge/view: the logarithmic average estimate and the generic exponentiation lemmas from the
  previous section.

Primitive data:
- the method owner `method : BarrierSubgradientMethod P₀ F ψ v x₀`;
- the maximizing feasible point `x⋆`;
- the maximizing property of `x⋆`;
- concavity of `ψ` on `P₀`;
- the Chapter 7 barrier assumptions on `F`;
- the canonical Hessian-dual local norm bound `‖∇ ψ(x)‖*ₓ ≤ ψ(x)` on `P₀`.

Derived API:
- the positive iterate geometric mean `method.iterateGeometricMean k`;
- the logarithmic average estimate for `log ψ`;
- the exponential and linear relative-scale lower bounds.
-/

namespace BarrierSubgradientMethod

variable {P0 : Set E} {F ψ : E → ℝ} {v : NNRealˣ} {x0 : P0}

/-- The geometric mean of the positive values `ψ(x₀), …, ψ(x_k)` along a barrier subgradient
method. -/
def iterateGeometricMean
    (method : BarrierSubgradientMethod P0 F ψ v x0) (k : ℕ) : ℝ :=
  positiveIterateGeometricMean
    (fun x : P0 ↦ ⟨ψ x, method.ψ_pos x.property⟩)
    method.iterate k

/-- If `x⋆` maximizes `ψ` on `P₀`, then the geometric mean of the positive iterate values of `ψ`
along `method` is bounded above by `ψ(x⋆)`. -/
theorem iterateGeometricMean_le_optimal
    (method : BarrierSubgradientMethod P0 F ψ v x0)
    (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar) (k : ℕ) :
    method.iterateGeometricMean k ≤ ψ xStar := sorry

section ExplicitRate

variable (method : BarrierSubgradientMethod P0 F ψ v x0)
variable (xStar : P0) (hoptimal : IsMaxOn ψ P0 xStar)
variable (ν : NNReal) (hν : 0 < (ν : ℝ))
variable [IsSelfConcordantBarrierOnWith P0 ν F]
variable [HasPositiveDefiniteHessianOn P0 F]
variable (hψ_concave : ConcaveOn ℝ P0 ψ)
variable
  (hψ_dual_bound :
    ∀ x : P0,
      HessianDualLocalNorm.ofPosDefMem F x.2
          (InnerProductSpace.toDualMap ℝ E (∇ ψ x)) ≤
        ψ x)

-- Proof sketch: apply Lemma 7.14 to `logarithmicTransform ψ`, using concavity of `ψ`, positivity
-- and differentiability from `method`, and the local Hessian-dual norm bound `‖∇ ψ(x)‖*ₓ ≤ ψ(x)`
-- to place `-log ψ` in the Chapter 7 barrier-subgradient class with bound `1`; then invoke the
-- explicit-rate owner from Theorem 7.15 for the resulting logarithmic barrier-subgradient run and
-- rewrite its normalized maximal-gap bound as the logarithmic average estimate below.
/-- Theorem 7.16 first yields the logarithmic average estimate for `log ψ` along the actual
barrier-subgradient run from Algorithm 7.14, under the source-facing Chapter 7 assumptions:
`x⋆` maximizes `ψ` on `P₀`, `ψ` is concave on `P₀`, `F` is a `ν`-self-concordant barrier on
`P₀`, and the gradient of `ψ` has Hessian-dual local norm at most `ψ(x)` at every feasible point.
-/
theorem logarithmicAverageGap_le_relativeAccuracyDelta
    (k : ℕ) :
    Real.log (ψ xStar) -
        (Finset.sum (Finset.range (k + 1)) fun i ↦ Real.log (ψ (method i))) /
          ((k : ℝ) + 1) ≤
      barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k := sorry

/-- Theorem 7.16 on the primal owner surface: under the same Chapter 7 source assumptions as the
preceding logarithmic-gap theorem, the geometric mean of the first `k + 1` iterate values of `ψ`
along the actual barrier-subgradient run is bounded below by `ψ(x⋆) exp (-δ_k)`. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate
    (k : ℕ) :
    method.iterateGeometricMean k ≥
      ψ xStar * Real.exp (-barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k) := sorry

/-- Theorem 7.16 expressed through the chapter owner
`IsRelativeScaleDeltaApproximation`: the upper bound by `ψ(x⋆)` and positivity of `δ_k` are
derived from the maximizing property of `x⋆`, the positivity of the barrier parameter `ν`, and
the logarithmic estimate above, so the public theorem stays on the primal source-facing owner
surface. -/
theorem positiveIterateGeometricMean_isRelativeScaleDeltaApproximation
    (k : ℕ) :
    IsRelativeScaleDeltaApproximation
      (ψ xStar)
      (barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k)
      (method.iterateGeometricMean k) := sorry

-- Proof sketch: combine the exponential estimate from Theorem 7.16 with the elementary
-- inequality `exp (-t) ≥ 1 - t`.
/-- The weaker linear lower bound obtained from Theorem 7.16 via `exp (-δ_k) ≥ 1 - δ_k`, again
derived from the same Chapter 7 bridge assumptions rather than from a separately supplied
logarithmic-rate hypothesis. -/
theorem positiveIterateGeometricMean_ge_optimal_mul_one_sub_rate
    (k : ℕ) :
    method.iterateGeometricMean k ≥
      ψ xStar * (1 - barrierSubgradientRelativeAccuracyDelta (ν : ℝ) k) := sorry

end ExplicitRate

end BarrierSubgradientMethod

end BarrierSubgradient

end

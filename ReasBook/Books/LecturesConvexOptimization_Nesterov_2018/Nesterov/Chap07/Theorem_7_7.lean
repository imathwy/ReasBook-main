import LecturesConvexOptimization_Nesterov_2018.Chap07.Algorithm_7_7
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Theorem 7.7 lies in Chapter 7's translated ellipsoid-rounding / determinant-growth domain.

Sampled owner-style declarations:
- `GeneralConvexRoundingAlgorithm.radius` and
  `GeneralConvexRoundingAlgorithm.oneSidedRoundingSigma` in `Algorithm_7_7`, the owner-level run
  API for Algorithm 7.7;
- `matrixEllipsoid` and the notation `W[r](v, G)` in `Definition_7_26`, the source-facing owner of
  translated ellipsoids;
- `_root_.oneSidedRoundingSigma` in `Lemma_7_5`, the chapter owner of the per-step scalar
  quantity `σ = (r - n) / (n + 1)`;
- `IsBetaRounding` in `Definition_7_27`, the chapter owner for the initial translated inner/outer
  ellipsoid containment data;
- `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6`, the nearby owner-style
  iteration bound organized as initial rounding data plus continuing-step hypotheses.

Best owner abstraction:
- source-facing: the iteration bound for a run of Algorithm 7.7 up to a terminal iterate `T`;
- core/canonical: `GeneralConvexRoundingAlgorithm` for the run data and `IsBetaRounding` for the
  initial translated ellipsoid containment;
- bridge/view: the terminal unit-ellipsoid containment and the theorem-level logarithmic
  determinant-growth inequalities.

Primitive data:
- the algorithm run;
- the initial outer radius `R`;
- the total number of performed updates `T`.

Derived API:
- the center sequence `vₖ = algorithm k` and the shape sequence `Gₖ = algorithm.shape k`;
- the initial translated rounding datum, packaged canonically by `IsBetaRounding`;
- the canonical per-step scalar `σₖ = algorithm.oneSidedRoundingSigma k`, derived from the current
  shape and maximizer displacement through the Chapter 7 owner `_root_.oneSidedRoundingSigma`;
- the initial and terminal positive-definiteness, derived from `algorithm.initial_shape_posDef`
  and `algorithm.shape_posDef` rather than stored as extra theorem inputs;
- the per-step logarithmic determinant increment estimate.

Source/core/bridge triage:
- source-facing: the theorem below;
- core/canonical: `GeneralConvexRoundingAlgorithm`, `IsBetaRounding`;
- bridge/view: the terminal comparison data and the stepwise logarithmic determinant inequalities.

The previous statement still left the source-defined per-step scalar `σₖ` as a primitive theorem
parameter. This refinement moves the theorem back to the owner layer of
`GeneralConvexRoundingAlgorithm`, reuses `IsBetaRounding` for the initial containment data, and
states both the continuation lower bound and the determinant-growth estimate directly in terms of
the canonical owner-side step quantity `algorithm.oneSidedRoundingSigma k`.
-/

-- Proof sketch: sum the lower bound
-- `2 σₖ² / ((1 + σₖ) (2 + σₖ))` over all continuing iterations, with
-- `σₖ = algorithm.oneSidedRoundingSigma k`, use
-- `σₖ ≥ (n / (n + 1)) (γ - 1)` to replace each increment by the uniform constant
-- `4 (γ - 1)² / ((1 + 2γ) (2 + γ))`, and compare the resulting lower bound for
-- `log det G_T - log det G₀` with the upper bound coming from the initial translated rounding
-- `W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`. The lower bound `1 ≤ R` is recovered internally from
-- `algorithm.initial_shape_posDef`, `hInitial`, and `n ≥ 1`, while the terminal inner
-- containment is supplied in the source-facing form `W₁(v_T,G_T) ⊆ C`.

namespace GeneralConvexRoundingAlgorithm

section IterationBounds

variable {C : Set E} {gamma R : ℝ} {v0 : E} {G0 : Mat}

/-- Theorem 7.7: if `n ≥ 1`, an Algorithm 7.7 run starts from an `R`-rounding
`W₁(v₀,G₀) ⊆ C ⊆ W_R(v₀,G₀)`, its terminal iterate satisfies `W₁(v_T,G_T) ⊆ C`, the
canonical per-step quantities `σₖ = algorithm.oneSidedRoundingSigma k` satisfy
`σₖ ≥ (n / (n + 1)) (γ - 1)` for `k < T`, and the logarithmic determinant gains satisfy
`log det Gₖ₊₁ - log det Gₖ ≥ 2 σₖ² / ((1 + σₖ) (2 + σₖ))` for `k < T`, then
`T ≤ ((1 + 2γ) (2 + γ) / (2 (γ - 1)²)) n log R`. -/
theorem iterations_le
    (algorithm : GeneralConvexRoundingAlgorithm C gamma v0 G0)
    (hn : 1 ≤ n)
    {T : ℕ}
    (hInitial : IsBetaRounding C R G0 v0)
    (hFinal : W[1]((algorithm.center T), (algorithm.shape T)) ⊆ C)
    (hsigma :
      ∀ k : ℕ, k < T →
        ((n : ℝ) / (n + 1 : ℝ)) * (gamma - 1) ≤ algorithm.oneSidedRoundingSigma k)
    (hlogDet :
      ∀ k : ℕ, k < T →
        Real.log (Matrix.det (algorithm.shape (k + 1))) ≥
          Real.log (Matrix.det (algorithm.shape k)) +
            (2 * (algorithm.oneSidedRoundingSigma k) ^ (2 : ℕ)) /
              ((1 + algorithm.oneSidedRoundingSigma k) *
                (2 + algorithm.oneSidedRoundingSigma k))) :
    (T : ℝ) ≤
      ((1 + 2 * gamma) * (2 + gamma)) / (2 * (gamma - 1) ^ (2 : ℕ)) *
        (n : ℝ) * Real.log R := sorry

end IterationBounds

end GeneralConvexRoundingAlgorithm

end

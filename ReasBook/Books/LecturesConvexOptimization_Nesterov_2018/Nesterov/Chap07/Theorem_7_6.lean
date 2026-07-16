import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Algorithm_7_5
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap07.Definition_7_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped EllipsoidNotation

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 7.6 lies in Chapter 7's centrally symmetric ellipsoid-rounding / stopping-index domain.

Sampled owner-style declarations:
- `CentralSymmetricRoundingMethod.stoppingCriterion` and
  `CentralSymmetricRoundingMethod.stoppingIndex` in `Algorithm_7_5`, the canonical first-hit
  stopping API for Algorithm 7.5;
- `CentralSymmetricRoundingMethod.threshold_lt_radius_of_lt_stoppingIndex` in `Algorithm_7_5`,
  the owner-level continuation inequality `γ √n < rₖ` before the first stopping index;
- `IsBetaRounding` in `Definition_7_27` and `IsInitialApproximation` in `Definition_7_29`, the
  chapter owners for centered initial ellipsoid data.

Best owner abstraction:
- source-facing: the iteration bound for the actual Algorithm 7.5 run, measured at its canonical
  first stopping index;
- core/canonical: `CentralSymmetricRoundingMethod`, its stopping API, and the centered
  ellipsoid-rounding owner `IsBetaRounding`;
- bridge/view: theorem-level invariance and log-determinant growth hypotheses attached only to
  genuinely continuing steps.

Primitive data:
- the centrally symmetric rounding method itself;
- the canonical termination witness for that method;
- the initial outer radius `R` appearing in the centered rounding datum.

Derived API:
- the stopping index `method.stoppingIndex hTerminate`;
- the continuation inequality `γ √n < rₖ` before stopping;
- the initial centered rounding data packaged by `IsBetaRounding`;
- the lower bound `1 ≤ R`, derived internally from the initial rounding data together with
  `method.one_le_dim`;
- the determinant-growth lower bound used in the complexity estimate.

The previous statement was organized around an arbitrary `N` and separate proof-bridge hypotheses
for `σₖ` and `log det`. This refinement moves the main theorem back to the owner layer of
Algorithm 7.5: the bound is stated for the canonical first stopping index, the lower bound on
`σₖ` is derived from the continuation inequality, the lower bound `1 ≤ R` is recovered internally
from the initial rounding datum, and the initial containment data are packaged by the chapter
rounding owner.
-/

namespace CentralSymmetricRoundingMethod

section StoppingBounds

variable (method : CentralSymmetricRoundingMethod n)
variable (hTerminate : method.Terminates)

local notation "s" => method.stoppingIndex hTerminate

-- Proof sketch: derive `1 ≤ R` from the initial centered rounding data and `method.one_le_dim`.
-- Sum the lower bound for `log det Gₖ₊₁ - log det Gₖ` over the genuinely continuing steps
-- `k < s`; for each such `k`, the continuation inequality `γ √n < rₖ` is supplied canonically by
-- `threshold_lt_radius_of_lt_stoppingIndex`. Compare the resulting lower bound for
-- `log det G_s - log det G₀` with the upper bound coming from the initial centered rounding
-- `W₁(G₀) ⊆ C ⊆ W_R(G₀)` and the persistent inner containments `W₁(Gₖ) ⊆ C`.
/-- Theorem 7.6: if an Algorithm 7.5 run starts from the centered `R`-rounding
`W₁(G₀) ⊆ C ⊆ W_R(G₀)`, if every post-update iterate before the first stopping index still
satisfies `W₁(Gₖ) ⊆ C`, and if every genuinely continuing step `k < s` gains at least
`2 log γ - (γ² - 1) / γ²` in `log det Gₖ`, then the canonical first stopping index `s` is
bounded by `2 n γ² / (γ - 1)² * log R`. -/
theorem stoppingIndex_le
    {R : ℝ}
    (hInitial : IsBetaRounding (method.body : Set E) R (method 0) (0 : E))
    (hinner :
      ∀ k : ℕ, k < s →
        W[1]((method (k + 1))) ⊆ (method.body : Set E))
    (hlogDet :
      ∀ k : ℕ, k < s →
        Real.log (Matrix.det (method (k + 1))) ≥
          Real.log (Matrix.det (method k)) +
            (2 * Real.log method.gamma -
              (method.gamma ^ (2 : ℕ) - 1) / method.gamma ^ (2 : ℕ))) :
    (s : ℝ) ≤
      2 * (n : ℝ) * method.gamma ^ (2 : ℕ) / (method.gamma - 1) ^ (2 : ℕ) * Real.log R := sorry

end StoppingBounds

end CentralSymmetricRoundingMethod

end

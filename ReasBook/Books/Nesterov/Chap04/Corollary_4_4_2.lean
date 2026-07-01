import Mathlib
import Nesterov.Chap04.Algorithm_4_4_1
import Nesterov.Chap04.Proposition_4_4_7
import Nesterov.Chap04.Theorem_4_1_2
import Nesterov.Chap04.Theorem_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped LevelSetNotation Manifold ModifiedGaussNewtonLocalDecreaseNotation Topology

noncomputable section

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 L : ℝ} {x0 : E₁}

/- Corollary 4.4.2 lies in the modified Gauss--Newton trajectory / cluster-point domain.

Sampled owner declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate sequence;
* `ModifiedGaussNewtonMethod.meritFunction_succ_le` in `Proposition_4_4_7`, the owner theorem
  keeping the trajectory inside its initial merit sublevel set;
* `ModifiedGaussNewtonMethod.gap_ge_residualSqTail` and
  `ModifiedGaussNewtonMethod.gap_ge_chiWeightedTail` in `Theorem_4_4_1`, the source-facing
  summability owners behind parts `(1)` and `(2)`;
* `cubicRegularization_limitPoints_isConnected` and
  `cubicRegularization_clusterPoint_value_eq_limit` in `Theorem_4_1_2`, the chapter owners for
  connectedness of cluster-point sets and for passing scalar sequence limits to cluster points;
* `modifiedGaussNewtonLocalDecrease` with notation `Δ[problem; φ; r](x)` in `Lemma_4_4_3`, the
  source-facing local-model decrease `Δ_r`.

Best owner abstraction:
* source-facing: the asymptotic consequences for a `ModifiedGaussNewtonMethod`;
* core/canonical: `ModifiedGaussNewtonMethod`, `MapClusterPt`, the initial sublevel set
  `𝓛[f]((f x0))`, and the generic Chapter 4 cluster-point bridge theorems;
* bridge/view: the local-model decrease `Δ[r](x)` and the initial sublevel set
  `𝓛[f]((f x0))`, used internally to pass from trajectory estimates to cluster-point
  consequences.

Primitive data:
* the trajectory `method`;
* the radius parameter `r`.
* for the connected-cluster-set layer, the bounded initial sublevel set `𝓛[f]((f x0))` in a
  proper ambient space;
* for the cluster-point identity layer, continuity of `Δ[r]` at the chosen cluster point.

Internal proof bridges:
* monotonicity of the merit values, confining the trajectory to `𝓛[f]((f x0))`;
* the generic Chapter 4 connected-cluster-set owner
  `cubicRegularization_limitPoints_isConnected`, used after supplying boundedness of `𝓛[f]((f x0))`;
* the scalar cluster-point bridge `cubicRegularization_clusterPoint_value_eq_limit`, used after
  supplying continuity of `Δ[r]` at the cluster point.

Derived API:
* vanishing successive differences;
* vanishing local-model decrease values along the trajectory;
* connectedness of the cluster-point set `X*` under boundedness of `𝓛[f]((f x0))` in a proper
  ambient space;
* the cluster-point identity `Δ_r(x̄) = 0` under continuity of `Δ[problem; φ; r]` at `x̄`.

This file keeps Corollary 4.4.2 source-facing on the intrinsic normed-space layer already used by
`ModifiedGaussNewtonMethod`, while exposing exactly the extra owner-side data needed by the
canonical Chapter 4 cluster-point bridges: boundedness of the initial merit sublevel set in a
proper ambient space for part `(3)`, and continuity of `Δ[r]` at the chosen cluster point for
part `(4)`.
-/

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

namespace ModifiedGaussNewtonMethod

-- Proof sketch: apply Theorem 4.4.1 with the canonical lower bound `0 ≤ f x` coming from the
-- sharp merit function, identify `x_{k+1} - x_k` with the residual of the chosen step at `x_k`,
-- and use that summable squared residuals force the residuals themselves to converge to `0`.
/-- Corollary 4.4.2 (1): along a modified Gauss--Newton method, the consecutive differences
`‖x_k - x_{k+1}‖` converge to `0`. -/
theorem stepDifferences_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ ‖method k - method (k + 1)‖) atTop (𝓝 0) := sorry

private theorem stepDistances_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0) :
    Tendsto (fun k ↦ dist (method (k + 1)) (method k)) atTop (𝓝 0) :=
  method.stepDifferences_tendsto_zero

-- Proof sketch: if `r = 0`, then `Metric.closedBall x 0 = {x}` and the source-facing local model
-- decrease collapses to `Δ_0(x) = 0`. For general `r`, use Theorem 4.4.1 to show that the
-- weighted chi-tail built from `Δ[problem; φ; r](method k)` is summable. Since `χ` is
-- nonnegative and
-- vanishes only at `0`, the summability of this tail forces `Δ_r(method k) → 0`.
/-- Corollary 4.4.2 (2): for every radius `r`, the local model decrease `Δ_r(x_k)` tends to `0`
along the modified Gauss--Newton iterates. -/
theorem localModelDecrease_tendsto_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal) :
    Tendsto (fun k ↦ Δ[problem; φ; r]((method k))) atTop (𝓝 0) := sorry

-- Proof sketch: use Proposition 4.4.7 to keep the entire trajectory inside the initial sublevel
-- set `𝓛0`, then apply the chapter owner theorem
-- `cubicRegularization_limitPoints_isConnected` to that bounded set in the proper ambient space,
-- with `stepDistances_tendsto_zero` supplying the canonical metric vanishing-step hypothesis.
/-- Corollary 4.4.2 (3): the set `X*` of limit points of the modified Gauss--Newton trajectory is
connected provided the initial merit sublevel set `𝓛[f]((f x₀))` is bounded in the proper
ambient space. -/
theorem limitPoints_isConnected
    [ProperSpace E₁]
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (hbounded : Bornology.IsBounded 𝓛0) :
    IsConnected {xBar : E₁ | MapClusterPt xBar atTop method} := sorry

-- Proof sketch: if `r = 0`, then `Δ_0 = 0` pointwise by the closed-ball singleton formula.
-- Otherwise apply part `(2)` to get `Δ_r(method k) → 0`, then invoke the chapter owner theorem
-- `cubicRegularization_clusterPoint_value_eq_limit` for the scalar function
-- `fun x ↦ Δ[problem; φ; r](x)`, using the explicit continuity hypothesis at the cluster point.
/-- Corollary 4.4.2 (4): every cluster point `x̄ ∈ X*` of the modified Gauss--Newton trajectory
satisfies `Δ_r(x̄) = 0` for each radius `r`, provided `Δ[problem; φ; r]` is continuous at `x̄`. -/
theorem clusterPoint_localModelDecrease_eq_zero
    (method : ModifiedGaussNewtonMethod problem φ L0 L x0)
    (r : NNReal)
    {xBar : E₁} (hxBar : MapClusterPt xBar atTop method)
    (hΔ_cont : ContinuousAt (fun x ↦ Δ[problem; φ; r](x)) xBar) :
    Δ[problem; φ; r](xBar) = 0 := sorry

end ModifiedGaussNewtonMethod

end

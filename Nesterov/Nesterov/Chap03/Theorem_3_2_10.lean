import Mathlib
import Nesterov.Chap03.Definition_3_55
import Nesterov.Chap03.Algorithm_3_7
import Nesterov.Chap03.Lemma_3_31
import Nesterov.Chap03.Theorem_3_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CenterOfGravityMethod

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

local notation "dim" => Module.finrank ℝ E

/-
Primary domain: center-of-gravity cutting-plane complexity bounds for bounded convex minimization
problems.

Relevant owner-style declarations sampled before refinement:
- `CenterOfGravityMethod.iterate` and `CenterOfGravityMethod.localizer` in `Algorithm_3_7`, the
  chapter owners for the centroid iterates `x_k` and localization sets `S_k`;
- `CenterOfGravityMethod.localizer_eq_localizationSets` in `Algorithm_3_7`, the bridge from the
  owner centroid recursion to the canonical recursive localization family;
- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior` in
  `Lemma_3_31`, the intrinsic owner centroid-cut volume estimate supplying the factor
  `1 - 1 / e`;
- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` in `Theorem_3_2_9`, the owner
  radius/volume comparison converting stagewise volume decay into the `k / dim` radius exponent.

Best owner abstraction:
- source-facing: the best sampled objective value along the chapter's center-of-gravity iterates;
- core/canonical: `ConvexMinimizationWithSeparationOracle E` together with
  `CenterOfGravityMethod.iterate`;
- bridge/view: the derived centroid-cut volume decay and localization-radius estimate.

Primitive data:
- the owner cutting-plane problem `problem`;
- the minimizer `xStar`, outer radius `D`, and Lipschitz constant `M`.

Derived API:
- the iterate sequence `iterate problem`;
- the best sampled value `bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k`;
- the geometric decay factor obtained by combining centroid-cut volume contraction with the owner
  radius/volume theorem.

Source/core/bridge triage:
- source-facing: the center-of-gravity complexity bound itself;
- core/canonical: `ConvexMinimizationWithSeparationOracle E` and `CenterOfGravityMethod.iterate`;
- bridge/view: centroid-cut volume decay and localization-radius comparison.

The previous version erased the center-of-gravity method and kept only a generic metric-space
recursion hypothesis. This refinement restores the actual source-facing theorem on the chapter's
owner method abstraction and leaves the geometric-decay recursion as a derived proof ingredient
rather than primitive public data. The centroid-cut ingredient now lives at the same intrinsic
finite-dimensional owner level as the localization-radius theorem, so the theorem no longer
over-generalizes the existing chapter owner graph.
-/

-- Proof sketch: `CenterOfGravityMethod.localizer_succ` identifies each update as the centroid cut
-- of the previous localization set. Apply the centroid-cut volume estimate
-- `centerOfGravityCut_volumeRatio_le_one_sub_inv_e_of_bounded_convex_nonemptyInterior` at every
-- step to obtain geometric decay of the localizer volumes. Then use
-- `localization_radius_le_outer_radius_mul_volume_ratio_rpow` together with
-- `CenterOfGravityMethod.localizer_eq_localizationSets` to bound the localization radius by
-- `D * (1 - 1 / e)^(k / dim)`. Finally, every iterate lies in the corresponding localization set,
-- so Lipschitz continuity on `B₂(xStar, D)` converts that radius estimate into the displayed
-- best-value gap bound.
/-- Theorem 3.2.10: at the chapter owner level, for the center-of-gravity cutting-plane method on
a bounded convex minimization problem, if `xStar` minimizes the objective on the feasible set
`Q = problem.feasibleSet`, if `Q ⊆ B₂(xStar, D)`, and if the objective is `M`-Lipschitz on that
ball, then the best sampled value
`f_k^* = bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k` along the centroid
iterates satisfies
`f_k^* - problem xStar ≤ M D (1 - 1 / e)^(k / dim)`, where `dim = Module.finrank ℝ E`. The
factor `(1 - 1 / e)^(k / dim)` is derived from the centroid-cut volume contraction and the
localization-radius/volume comparison, not assumed as primitive data. -/
theorem CenterOfGravityMethod.bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay
    (problem : ConvexMinimizationWithSeparationOracle E)
    {xStar : E} {D : ℝ} {M : NNReal}
    (hxStar : IsMinOn problem problem.feasibleSet xStar)
    (hQ_subset : problem.feasibleSet ⊆ Metric.closedBall xStar D)
    (hLip : LipschitzOnWith M problem (Metric.closedBall xStar D))
    (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ problem (iterate problem i)) k - problem xStar ≤
      (M : ℝ) * D * Real.rpow (1 - 1 / Real.exp 1) ((k : ℝ) / dim) := sorry

end

end

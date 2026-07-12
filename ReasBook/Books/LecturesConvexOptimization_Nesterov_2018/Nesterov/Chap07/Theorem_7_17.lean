import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_73
import LecturesConvexOptimization_Nesterov_2018.Chap07.Definition_7_74
import LecturesConvexOptimization_Nesterov_2018.Chap07.Theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {X : Type u}

/- Theorem 7.17 lies in the Chapter 7 finite-horizon geometric-mean / barrier-rate bridge
domain.

Mandatory domain-style sampling:
- `dynamicStrategyAverageRateOfGrowth` in `Chap07/Definition_7_74`, the source-facing owner for
  the realized dynamic geometric mean along a finite horizon;
- `staticProductionAverageEfficiency` in `Chap07/Definition_7_73`, the chapter owner for the
  static geometric mean on the same horizon;
- `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate` in
  `Chap07/Theorem_7_16`, the canonical exponentiation bridge from a logarithmic average estimate
  to a geometric-mean lower bound;
- `barrierSubgradientRelativeAccuracyDelta` in `Chap07/Theorem_7_16`, the owner of the explicit
  Chapter 7 rate term.

Best owner abstraction:
- source-facing: the dynamic-vs-static finite-horizon comparison from Theorem 7.17;
- core/canonical: `dynamicStrategyAverageRateOfGrowth`, `staticProductionAverageEfficiency`, and
  the generic bridge theorem
  `positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate`;
- bridge/view: the conversion between the chapter's finite-horizon `Fin`-indexed trace and the
  generic `ℕ`-indexed geometric-mean bridge, together with the asymptotic theorem for
  `barrierSubgradientRelativeAccuracyDelta`.

Primitive data:
- the feasible subtype `P`;
- the horizon `N`;
- the positive outputs `ψ`;
- the realized dynamic trace `x`;
- the comparison static point `xStatic`.

Derived API:
- the dynamic geometric mean `dynamicStrategyAverageRateOfGrowth ψ x`;
- the static geometric mean `staticProductionAverageEfficiency ψ xStatic`;
- the explicit error rate `barrierSubgradientRelativeAccuracyDelta`.

Source/core/bridge triage:
- source-facing: `dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta`,
  which compares the dynamic owner to the canonical optimal static efficiency;
- core/canonical: `IsMaxOn`, `sSup`, and the generic theorem from `Theorem_7_16`;
- bridge/view:
  `dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap`
  and the asymptotic vanishing statement for the explicit rate.
-/

-- Proof sketch: rewrite the logarithmic average of the dynamic outputs as the logarithm of
-- `dynamicStrategyAverageRateOfGrowth ψ x`, then exponentiate the assumed logarithmic comparison
-- with the static average efficiency at the supplied comparison point.
/-- Exponentiating a logarithmic comparison estimate at a fixed static strategy `xStatic` yields
the corresponding geometric-mean lower bound for the dynamic strategy. This is the bridge/view
step used in Theorem `7.17` after choosing an optimal static strategy via Definition `7.73`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      staticProductionAverageEfficiency ψ xStatic *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  let outputs : Fin (N + 1) → {r : ℝ // 0 < r} := fun k ↦ ψ k (x k)
  let indices : ℕ → Fin (N + 1) := fun i ↦ ⟨i % (N + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hStaticPos : 0 < staticProductionAverageEfficiency ψ xStatic := by
    rw [staticProductionAverageEfficiency_def, staticProductionTotalOutput_def]
    exact Real.rpow_pos_of_pos (Finset.prod_pos fun k _ ↦ (ψ k xStatic).property) _
  have hsum :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ)) =
        ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
    calc
      Finset.sum (Finset.range (N + 1)) (fun i ↦ Real.log (outputs (indices i) : ℝ))
          = ∑ k : Fin (N + 1), Real.log (outputs (indices k) : ℝ) := by
              simpa using
                (Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (outputs (indices i) : ℝ))
                  (N + 1)).symm
      _ = ∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        simp [outputs, indices, Nat.mod_eq_of_lt k.2]
  have hprod :
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ)) =
        Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
    calc
      (∏ k : Fin (N + 1), (ψ k (x k) : ℝ))
          = ∏ k : Fin (N + 1), (outputs (indices k) : ℝ) := by
              refine Finset.prod_congr rfl fun k _ ↦ ?_
              simp [outputs, indices, Nat.mod_eq_of_lt k.2]
      _ = Finset.prod (Finset.range (N + 1)) (fun i ↦ (outputs (indices i) : ℝ)) := by
        simpa using
          (Fin.prod_univ_eq_prod_range (fun i ↦ (outputs (indices i) : ℝ)) (N + 1))
  have hlog_rate' :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (Finset.sum (Finset.range (N + 1)) fun i ↦ Real.log (outputs (indices i) : ℝ)) /
            ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N := by
    simpa [hsum] using hlog_rate
  have hbridge :=
    positiveIterateGeometricMean_ge_optimal_mul_exp_neg_rate_of_log_rate
      outputs
      indices
      ⟨staticProductionAverageEfficiency ψ xStatic, hStaticPos⟩
      N
      hlog_rate'
  have hdynamic :
      dynamicStrategyAverageRateOfGrowth ψ x =
        Real.rpow
          (Finset.prod (Finset.range (N + 1)) fun i ↦ (outputs (indices i) : ℝ))
          ((1 : ℝ) / (N + 1 : ℝ)) := by
    rw [dynamicStrategyAverageRateOfGrowth_def, ← hprod]
  rw [positiveIterateGeometricMean_def] at hbridge
  simpa [hdynamic] using hbridge

/-- If `xStatic` maximizes the static cumulative output from Definition `7.73`, then it also
maximizes the derived static geometric-mean efficiency. -/
theorem staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic := by
  rw [isMaxOn_univ_iff] at hoptimal ⊢
  intro y
  rw [staticProductionAverageEfficiency_def, staticProductionAverageEfficiency_def]
  have hy_nonneg : 0 ≤ staticProductionTotalOutput ψ y := by
    rw [staticProductionTotalOutput_def]
    exact le_of_lt (Finset.prod_pos fun k _ ↦ (ψ k y).property)
  exact Real.rpow_le_rpow
    hy_nonneg
    (hoptimal y)
    (by positivity)

/-- An optimal static strategy realizes the canonical optimal static efficiency, expressed as the
supremum of all static geometric-mean efficiencies over the feasible subtype `P`. -/
theorem staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic) :
    sSup (Set.range (staticProductionAverageEfficiency ψ)) =
      staticProductionAverageEfficiency ψ xStatic := by
  have hoptimalEfficiency :
      IsMaxOn (staticProductionAverageEfficiency ψ) Set.univ xStatic :=
    staticProductionAverageEfficiency_isMaxOn_of_staticProductionTotalOutput_isMaxOn ψ xStatic
      hoptimal
  have hne : (Set.range (staticProductionAverageEfficiency ψ)).Nonempty :=
    ⟨_, xStatic, rfl⟩
  have hbdd : BddAbove (Set.range (staticProductionAverageEfficiency ψ)) := by
    refine ⟨staticProductionAverageEfficiency ψ xStatic, ?_⟩
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  apply le_antisymm
  · refine csSup_le hne ?_
    rintro y ⟨z, rfl⟩
    exact (isMaxOn_univ_iff.mp hoptimalEfficiency z)
  · exact le_csSup hbdd ⟨xStatic, rfl⟩

-- Proof sketch: use Definition `7.73` to identify the comparison point with an optimal static
-- strategy, rewrite its efficiency as the canonical supremum of all static efficiencies, and then
-- apply the one-point exponentiation bridge above.
/-- Theorem 7.17: if `xStatic` is an optimal static strategy in the sense of Definition `7.73`
and the barrier-subgradient logarithmic comparison estimate is available at that optimizer, then
the dynamic average rate of growth is at least the canonical optimal static efficiency times
`exp (-δ_N)`. -/
theorem dynamicStrategyAverageRateOfGrowth_ge_optimalStaticEfficiency_mul_exp_neg_delta
    {P : Set X} {N : ℕ}
    (ψ : Fin (N + 1) → P → {r : ℝ // 0 < r})
    (x : Fin (N + 1) → P)
    (xStatic : P)
    (hoptimal : IsMaxOn (staticProductionTotalOutput ψ) Set.univ xStatic)
    {ν : ℝ}
    (hlog_rate :
      Real.log (staticProductionAverageEfficiency ψ xStatic) -
          (∑ k : Fin (N + 1), Real.log (ψ k (x k) : ℝ)) / ((N : ℝ) + 1) ≤
        barrierSubgradientRelativeAccuracyDelta ν N) :
    dynamicStrategyAverageRateOfGrowth ψ x ≥
      sSup (Set.range (staticProductionAverageEfficiency ψ)) *
        Real.exp (-barrierSubgradientRelativeAccuracyDelta ν N) := by
  rw [staticProductionAverageEfficiency_eq_sSup_of_optimalStaticStrategy ψ xStatic hoptimal]
  exact
    dynamicStrategyAverageRateOfGrowth_ge_staticEfficiency_mul_exp_neg_delta_of_log_gap
      ψ x xStatic hlog_rate

-- Proof sketch: use that both `(N + 1)⁻¹/²` and `(N + 1)⁻¹` tend to `0` as `N → ∞`, the
-- logarithmic factor grows only like `log (√N)`, and then combine these asymptotics in the
-- owner `barrierSubgradientRelativeAccuracyDelta ν N`.
/-- The explicit barrier-subgradient relative-accuracy term tends to `0` as the horizon tends to
infinity. -/
theorem barrierSubgradientRelativeAccuracyDelta_tendsto_zero
    (ν : NNReal) :
    Filter.Tendsto
      (fun N : ℕ ↦ barrierSubgradientRelativeAccuracyDelta (ν : ℝ) N)
      Filter.atTop (nhds 0) := sorry

end

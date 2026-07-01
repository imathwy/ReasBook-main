import Nesterov.Chap03.Theorem_3_2_10
import Nesterov.Chap06.Algorithm_6_5
import Nesterov.Chap06.Definition_6_53
import Nesterov.Chap06.Definition_6_59
import Nesterov.Chap06.Theorem_6_14

noncomputable section

open scoped BigOperators WeightSequenceNotation TotalVariationNotation

universe u

namespace ConditionalGradientContraction

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 6.44 lies in the Chapter 6 conditional-gradient / total-variation / sampled-prefix
domain.

Sampled owner declarations:
- `bestFunctionValueUpTo` in `Chap03/Theorem_3_2_10`, the chapter owner for sampled prefix minima;
- `accumulatedWeights` with notation `A[a](t)` and `weightCoefficient` with notation `τ[a](t)`
  in `Definition_6_53`, the Chapter 6 owners for the accumulated weights and normalized
  coefficients;
- `ContractedFeasibleSetTrustRegionScheme` in `Algorithm_6_5`, the source-facing owner for the
  Chapter 6 conditional-gradient iterates `x_t`;
- `linearModelTotalVariationReal` in `Definition_6_59`, the canonical real-valued bridge for the
  Chapter 6 total variation `δ(x_t)`.

Best owner abstraction:
- source-facing: Proposition 6.44's bound on the sampled minimum total variation
  `δ_T^* = min_{0 ≤ t ≤ T} δ(x_t)` for the Chapter 6 method with the standard coefficients;
- core/canonical: `bestFunctionValueUpTo` together with the Chapter 6 owners
  `A[a](t)`, `τ[a](t)`, and `linearModelTotalVariationReal`;
- bridge/view: the internal weighted-prefix arithmetic lemma below.

Primitive data:
- the Chapter 6 standard weight sequence `a_t = t`;
- its derived owners `A_t = A[standardWeight](t)` and `τ_t = τ[standardWeight](t)`;
- the conditional-gradient iterate owner `method`;
- the weighted total-variation estimate along `method`.

Derived API:
- the closed forms for `A[standardWeight](t)` and `τ[standardWeight](t)`;
- the sampled minimum
  `bestFunctionValueUpTo
    (fun t ↦ linearModelTotalVariationReal ... ⟨method t, method.iterates_mem_feasibleSet t⟩) T`;
- Proposition 6.44's rate bound on that sampled minimum.

Source/core/bridge triage:
- source-facing: the standard-weight specialization of the Chapter 6 total-variation estimate;
- core/canonical: `bestFunctionValueUpTo`, `A[a](t)`, `τ[a](t)`,
  `ContractedFeasibleSetTrustRegionScheme`, and `linearModelTotalVariationReal`;
- bridge/view: the weighted-prefix estimate used internally to pass from the weighted bound to the
  sampled-prefix minimum.

The previous file kept only a free-floating arithmetic implication over arbitrary `x` and `δ`.
This refinement restores the actual Chapter 6 owners on the theorem surface: the standard weight
sequence, its accumulated weights and coefficients, the conditional-gradient iterate owner, and
the total-variation bridge consumed by later Chapter 6 estimates. The weighted-prefix estimate is
now kept as a chapter-facing companion theorem derived from those owners, while the sampled-
minimum statement remains the source-facing Proposition 6.44 surface.
-/

/-- The standard Chapter 6 coefficient sequence `a_t = t`. -/
def standardWeight : ℕ → ℝ :=
  fun t ↦ t

/-- Evaluating the standard Chapter 6 weights gives `a_t = t`. -/
@[simp] theorem standardWeight_apply (t : ℕ) :
    standardWeight t = t :=
  rfl

/-- For the standard Chapter 6 weights `a_t = t`, the accumulated weights satisfy
`A_t = A[standardWeight](t) = t (t + 1) / 2`. -/
theorem accumulatedWeights_standardWeight (t : ℕ) :
    A[standardWeight](t) = (t : ℝ) * (t + 1) / 2 := by
  rw [accumulatedWeights_apply]
  have hnat :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ k) * 2 = t * (t + 1) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Finset.sum_range_id_mul_two (t + 1)
  have hreal :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ (k : ℝ)) * 2 = (t : ℝ) * (t + 1) := by
    exact (by
      simpa [Nat.cast_sum, Nat.cast_mul] using
        congrArg (fun n : ℕ ↦ (n : ℝ)) hnat)
  have hsum :
      Finset.sum (Finset.range (t + 1)) (fun k ↦ (k : ℝ)) = (t : ℝ) * (t + 1) / 2 := by
    nlinarith
  simpa [standardWeight] using hsum

/-- For the standard Chapter 6 weights `a_t = t`, the normalized coefficients satisfy
`τ_t = τ[standardWeight](t) = 2 / (t + 2)`. -/
theorem weightCoefficient_standardWeight (t : ℕ) :
    τ[standardWeight](t) = 2 / ((t + 2 : ℕ) : ℝ) := by
  rw [weightCoefficient_apply, standardWeight_apply, accumulatedWeights_standardWeight (t + 1)]
  have ht1 : ((t + 1 : ℕ) : ℝ) ≠ 0 := by
    positivity
  have ht2 : ((t + 2 : ℕ) : ℝ) ≠ 0 := by
    positivity
  field_simp [ht1, ht2]
  rw [Nat.cast_add, Nat.cast_add]
  ring

private theorem bestFunctionValueUpTo_le_of_standardWeight_bound
    (values : ℕ → ℝ) {T : ℕ} {B : ℝ}
    (hweighted :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) ≤
        B * A[standardWeight]((T + 1)) / ((T + 1 : ℕ) : ℝ)) :
    bestFunctionValueUpTo values T ≤ B / ((T + 1 : ℕ) : ℝ) := by
  let vT : ℝ := bestFunctionValueUpTo values T
  have hv_le : ∀ t ∈ Finset.range (T + 1), vT ≤ values t := by
    intro t ht
    exact bestFunctionValueUpTo_le ⟨t, Finset.mem_range.mp ht⟩
  have hsum_lower :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * vT) ≤
        Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) := by
    refine Finset.sum_le_sum fun t ht ↦ ?_
    rw [standardWeight_apply]
    exact mul_le_mul_of_nonneg_left (hv_le t ht) (by positivity)
  have hsum_id :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) = (T : ℝ) * (T + 1) / 2 := by
    have hnat :
        Finset.sum (Finset.range (T + 1)) (fun t ↦ t) * 2 = T * (T + 1) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Finset.sum_range_id_mul_two (T + 1)
    have hreal :
        Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) * 2 = (T : ℝ) * (T + 1) := by
      exact (by
        simpa [Nat.cast_sum, Nat.cast_mul] using
          congrArg (fun n : ℕ ↦ (n : ℝ)) hnat)
    nlinarith
  have hsum_weights :
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) =
        accumulatedWeights standardWeight (T + 1) := by
    calc
      Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ) + 1) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            rw [standardWeight_apply]
            norm_num
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ (t : ℝ)) +
            Finset.sum (Finset.range (T + 1)) (fun _ ↦ (1 : ℝ)) := by
              simp [Finset.sum_add_distrib]
      _ = ((T : ℝ) * (T + 1)) / 2 + ((T + 1 : ℕ) : ℝ) := by
            rw [hsum_id]
            simp
      _ = accumulatedWeights standardWeight (T + 1) := by
            rw [accumulatedWeights_standardWeight]
            norm_num [Nat.cast_add]
            ring
  have hprefix :
      vT * accumulatedWeights standardWeight (T + 1) ≤
        Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) := by
    calc
      vT * accumulatedWeights standardWeight (T + 1) =
          vT * Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1)) := by
            rw [hsum_weights]
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ vT * standardWeight (t + 1)) := by
            rw [Finset.mul_sum]
      _ =
          Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * vT) := by
            refine Finset.sum_congr rfl fun t _ ↦ ?_
            ring
      _ ≤ Finset.sum (Finset.range (T + 1)) (fun t ↦ standardWeight (t + 1) * values t) :=
            hsum_lower
  have hmain :
      accumulatedWeights standardWeight (T + 1) * vT ≤
        accumulatedWeights standardWeight (T + 1) * (B / ((T + 1 : ℕ) : ℝ)) := by
    have :
        vT * accumulatedWeights standardWeight (T + 1) ≤
          B * accumulatedWeights standardWeight (T + 1) / ((T + 1 : ℕ) : ℝ) :=
      hprefix.trans hweighted
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hA_pos : 0 < accumulatedWeights standardWeight (T + 1) := by
    rw [accumulatedWeights_standardWeight]
    positivity
  nlinarith

-- Proof sketch: combine the Chapter 6 objective-drop owner from `Theorem_6_14` with the
-- standard-weight specialization `τ_t = τ[standardWeight](t) = 2 / (t + 2)`, rewrite the
-- resulting chosen-dual gap in terms of the canonical total-variation bridge
-- `linearModelTotalVariationReal`, and sum the per-step estimate to obtain the displayed weighted
-- prefix bound.
/-- Under the Chapter 6 `ν = 1` Hölder-gradient and diameter hypotheses, Algorithm 6.5 with the
standard coefficients `a_t = t` satisfies the weighted total-variation bound
`∑_{t=0}^T a_{t+1} δ_t ≤ (34 / (11 log 2)) G₁ D^2 A_{T+1} / (T + 1)`,
where
`δ_t = linearModelTotalVariationReal problem.feasibleSet problem.smoothPart
  (withTopRealPart problem.nonsmoothPart) ⟨method t, method.iterates_mem_feasibleSet t⟩`,
`A_t = A[standardWeight](t) = t (t + 1) / 2`, and
`τ_t = τ[standardWeight](t) = 2 / (t + 2)`. -/
theorem weighted_totalVariationReal_le_standard_weight_rate_nu_one
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ) {T : ℕ}
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤) :
      Finset.sum (Finset.range (T + 1))
        (fun t ↦
          standardWeight (t + 1) *
            linearModelTotalVariationReal
              problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
              ⟨method t, method.iterates_mem_feasibleSet t⟩) ≤
      (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) * A[standardWeight]((T + 1)) /
        ((T + 1 : ℕ) : ℝ) := by
  sorry

-- Proof sketch: apply the chapter-facing weighted-prefix bound above, then use the internal
-- weighted-prefix-to-sampled-minimum lemma for the standard weights.
/-- Proposition 6.44: along the Chapter 6 conditional-gradient scheme, if the step sizes are the
standard coefficients `τ_t = τ[standardWeight](t) = 2 / (t + 2)`, the smooth part has
`ν = 1` Hölder gradient on the feasible set with constant `G₁`, the feasible set has diameter
bounded by `D`, and the total variations along the first `T + 1` iterates are finite, then the
sampled minimum total variation
`δ_T^* = bestFunctionValueUpTo
  (fun t ↦
    linearModelTotalVariationReal problem.feasibleSet problem.smoothPart
      (withTopRealPart problem.nonsmoothPart) ⟨method t, method.iterates_mem_feasibleSet t⟩) T`
satisfies
`δ_T^* ≤ (34 / (11 log 2)) G₁ D^2 / (T + 1)`. -/
theorem bestFunctionValueUpTo_totalVariationReal_le_standard_weight_rate_nu_one
    {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}
    (method : ContractedFeasibleSetTrustRegionScheme problem x0) (G₁ : NNReal) (D : ℝ) {T : ℕ}
    (hstep : ∀ t : ℕ, method.stepSize t = τ[standardWeight](t))
    (hholder :
      HolderGradientOn 1 G₁ problem.feasibleSet problem.smoothPart method.gradient)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (hfinite :
      ∀ t : ℕ, t ≤ T →
        δ[problem.feasibleSet, problem.smoothPart, withTopRealPart problem.nonsmoothPart](⟨method t,
          method.iterates_mem_feasibleSet t⟩) ≠ ⊤) :
    bestFunctionValueUpTo
        (fun t ↦
          linearModelTotalVariationReal
            problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
            ⟨method t, method.iterates_mem_feasibleSet t⟩)
        T ≤
      (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) / ((T + 1 : ℕ) : ℝ) := by
  have hweighted :
      Finset.sum (Finset.range (T + 1))
          (fun t ↦
            standardWeight (t + 1) *
              linearModelTotalVariationReal
                problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
                ⟨method t, method.iterates_mem_feasibleSet t⟩) ≤
        (34 / (11 * Real.log 2)) * (G₁ : ℝ) * D ^ (2 : ℕ) *
          A[standardWeight]((T + 1)) /
          ((T + 1 : ℕ) : ℝ) :=
    weighted_totalVariationReal_le_standard_weight_rate_nu_one
      method G₁ D hstep hholder hdiam hfinite
  simpa using
    (bestFunctionValueUpTo_le_of_standardWeight_bound
      (fun t ↦
        linearModelTotalVariationReal
          problem.feasibleSet problem.smoothPart (withTopRealPart problem.nonsmoothPart)
          ⟨method t, method.iterates_mem_feasibleSet t⟩)
      hweighted)

end

end ConditionalGradientContraction

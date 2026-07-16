import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap02.Lemma_2_18
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_46

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

namespace MultipleConstraintFirstOrderProblem

private def subgradientNormFamily
    (problem : MultipleConstraintFirstOrderProblem E m) : Fin (m + 1) → E → ℝ :=
  Fin.cases
    (fun y ↦ ‖problem.oracle.subgradient y‖)
    (fun j y ↦ ‖(problem.constraintOracle j).subgradient y‖)

/-- The canonical finite-family maximum of the objective-subgradient norm together with all
constraint-subgradient norms at `x`. -/
def subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) : ℝ :=
  maxTypeObjective (subgradientNormFamily problem) x

/-- Each sampled objective-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem objectiveSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) :
    ‖problem.oracle.subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ 0))

/-- Each sampled constraint-subgradient norm is bounded by the problem-level maximum
`subgradientNormMaximum`. -/
theorem constraintSubgradientNorm_le_subgradientNormMaximum
    (problem : MultipleConstraintFirstOrderProblem E m) (x : E) (j : Fin m) :
    ‖(problem.constraintOracle j).subgradient x‖ ≤ problem.subgradientNormMaximum x := by
  rw [subgradientNormMaximum, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun i : Fin (m + 1) ↦ subgradientNormFamily problem i x)
      (Finset.mem_univ (Fin.succ j)))

end MultipleConstraintFirstOrderProblem

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/- Theorem 3.2.4 lies in the chapter's approximate-Lagrange-multiplier switching-method domain.

Sampled owner-style declarations:
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintIndices`
- `ApproximateLagrangeMultiplierSwitchingMethod.inactiveConstraintCount`
- `ApproximateLagrangeMultiplierSwitchingMethod.primalDualGapQuantity`
- `MultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- `maxTypeObjective` in `Chap02/Lemma_2_18`
- mathlib `Finset.sup'` on finite sampled scalar families

Best owner abstraction:
- a run `method : ApproximateLagrangeMultiplierSwitchingMethod problem`
- the project finite-family maximum owner `maxTypeObjective`

Primitive data:
- the switching-method run `method`
- the radius `R`, the stage `t`, the bounded-feasible-set hypothesis, and the
  large-iteration hypothesis

Derived API:
- the residual maximum `maxTypeObjective problem.constraints (method k)`, given directly by the
  Chapter 2 finite-family maximum owner
- the problem-owned norm envelope
  `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum`
- the sampled norm bound `M[method](t)`, owned by `sampleMaxSubgradientNorm` and derived as the
  finite operational maximum of that owner quantity along the sampled iterates `k = 0, ..., t`
- the source gap estimate written directly for the owner
  `primalDualGapQuantity`

Source/core/bridge triage:
- source-facing: the textbook residual bound, the positivity of `N(t)`, and the
  gap estimate for `δ_t` in the source regime `S_t > 0`
- core/canonical: `inactiveConstraintCount`, `normalizingFactor`,
  `approximateDualMultiplier`, `primalDualGapQuantity`, the finite-family maximum owner
  `maxTypeObjective`, and the finite-fold owner `Finset.sup'`
- bridge/view: the direct `Fin m` specialization `maxTypeObjective problem.constraints (method k)`

The old file duplicated the run data and left `δ_t` as arbitrary primitive data.
This refinement keeps the source-facing quantities, but derives them from the chapter owner run,
the chapter's canonical finite-family maximum surface for the constraint residual, the canonical
finite-fold sampled maximum for the textbook bound `M[method](t)`, and the existing gap owner
`primalDualGapQuantity`. -/

/-- Theorem 3.2.4: if `0 < h`, the feasible set is contained in the ball `‖x - x₀‖ ≤ R`, and
`t > R² / h²`, then the number `N(t)` of objective-step indices among `{0, ..., t}` is
positive. -/
theorem positive_inactiveConstraintCount_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    0 < N[method](t) := sorry

section ConstraintMaxima

/-- The sampled norm bound
`M = max_{0 ≤ k ≤ t} max {‖g(x_k)‖, ‖g₁(x_k)‖, ..., ‖g_m(x_k)‖}`. -/
def sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun k : Fin (t + 1) ↦
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)

/- Source-facing Lean notation for the textbook sampled norm bound `M`. -/
namespace ApproximateLagrangeMultiplierSwitchingNotation

scoped notation:max "M[" method:arg "](" t:arg ")" =>
  sampleMaxSubgradientNorm method t

end ApproximateLagrangeMultiplierSwitchingNotation

open scoped ApproximateLagrangeMultiplierSwitchingNotation

private theorem stageMax_le_sampleMaxSubgradientNorm
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) {t : ℕ} (k : Fin (t + 1)) :
    problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k) ≤
      M[method](t) := by
  unfold sampleMaxSubgradientNorm
  exact
    Finset.le_sup'
      (fun i : Fin (t + 1) ↦
        problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method i))
      (Finset.mem_univ k)

/-- Companion bridge for the textbook residual estimate: every objective-step iterate up to time
`t` satisfies the componentwise bound `f_j(x_k) ≤ M h` for each constraint index `j`, where
`0 < h` and `M = M[method](t)`. -/
-- Proof sketch: on indices in `A₀(t)`, the switching active set is empty, so each constraint
-- value is bounded by the corresponding threshold `h ‖g_j(x_k)‖`. The sampled norm bound
-- `M[method](t)` dominates the owner quantity
-- `problem.toMultipleConstraintFirstOrderProblem.subgradientNormMaximum (method k)` at every
-- sampled stage up to time `t`, hence every sampled constraint-subgradient norm, so the desired
-- inequality follows for each fixed `j`.
theorem constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) (j : Fin m) :
    problem.constraints j (method k) ≤ M[method](t) * method.h := by
  have hactive : method.activeSet k = ∅ :=
    (mem_inactiveConstraintIndices_iff method t).1 hk
  have hconstraint :
      problem.constraints j (method k) ≤
        method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := by
    exact le_of_not_gt fun hj ↦ by
      have hj_mem : j ∈ method.activeSet k := by
        simp [ApproximateLagrangeMultiplierSwitchingMethod.activeSet,
          ProjectedMultipleConstraintFirstOrderProblem.switchingActiveSet, hj]
      simp [hactive] at hj_mem
  have hnorm :
      ‖(problem.constraintOracle j).subgradient (method k)‖ ≤
        M[method](t) :=
    le_trans
      (MultipleConstraintFirstOrderProblem.constraintSubgradientNorm_le_subgradientNormMaximum
        problem.toMultipleConstraintFirstOrderProblem (method k) j)
      (stageMax_le_sampleMaxSubgradientNorm method k)
  calc
    problem.constraints j (method k)
      ≤ method.h * ‖(problem.constraintOracle j).subgradient (method k)‖ := hconstraint
    _ ≤ method.h * M[method](t) :=
      mul_le_mul_of_nonneg_left hnorm hh.le
    _ = M[method](t) * method.h := by rw [mul_comm]

/-- Every objective-step iterate up to time `t` satisfies the textbook residual-maximum bound
`max_{1 ≤ j ≤ m} f_j(x_k) ≤ M h`, written through the chapter owner
`maxTypeObjective problem.constraints (method k)`, where `0 < h` and `M = M[method](t)`. -/
theorem maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
    [NeZero m]
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (t : ℕ)
    (hh : 0 < method.h)
    {k : Fin (t + 1)} (hk : k ∈ A₀[method](t)) :
    maxTypeObjective problem.constraints (method k) ≤
      M[method](t) * method.h := by
  exact
    (maxTypeObjective_le_iff problem.constraints (method k)
      (M[method](t) * method.h)).2
      (fun j ↦
        constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices
          method t hh hk j)

/-- In the large-iteration regime, the textbook denominator regime needed by Definition 3.45 is
available: the objective and selected-constraint ratios are genuine, `h > 0`, and `N(t) > 0`. -/
theorem hasApproximateDualMultiplierDenominators_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    method.HasApproximateDualMultiplierDenominators t := by
  refine ⟨hobjective, hselected, hh, ?_⟩
  exact method.positive_inactiveConstraintCount_of_large_iteration_count R t hh hQ_bounded ht

/-- In the large-iteration regime of Theorem 3.2.4, the textbook gap quantity `δ_t` is bounded
above by `M h`, where `0 < h` and `M = M[method](t)`. The source denominator
regime needed for `δ_t` is assembled from the objective and selected-constraint nonvanishing
hypotheses together with the earlier positivity theorem for `N(t)`. -/
-- Proof sketch: combine the telescoping estimate `(3.2.36)` with the source positivity gate
-- `0 < S[method](t; hobjective)`, obtained from the earlier positivity theorem for `N(t)`,
-- hence `0 < σ[method](t; hobjective)`. After inserting `t > R² / h²`, divide by `σ_t`
-- to obtain `δ_t ≤ M h`.
theorem delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count
    (method : ApproximateLagrangeMultiplierSwitchingMethod problem) (R : NNReal) (t : ℕ)
    (hh : 0 < method.h)
    (hobjective : method.HasObjectiveDenominators t)
    (hselected : method.HasSelectedConstraintDenominators t)
    (hQ_bounded : ∀ x ∈ problem.feasibleSet, ‖x - method.x0‖ ≤ R)
    (ht : ((R : ℝ) ^ (2 : ℕ)) / (method.h ^ (2 : ℕ)) < (t : ℝ)) :
    δ[method](t;
        (method.hasApproximateDualMultiplierDenominators_of_large_iteration_count
          R t hh hobjective hselected hQ_bounded ht)) ≤ (M[method](t) * method.h : EReal) := sorry

end ConstraintMaxima

end ApproximateLagrangeMultiplierSwitchingMethod

end

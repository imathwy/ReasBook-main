import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Proposition_1_10_17
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_9_4
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_8_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/-
Definition 5.4.9.5 lies in the Chapter 5 box-constrained `ℓ_p` approximation / logarithmic
barrier domain.

Sampled owner declarations:
- `strictConstraintSet` and `logarithmicBarrier` in `Chap01/Proposition_1_10_17`, the project
  owner pattern for logarithmic barriers attached to finite continuous inequality families;
- `analyticBarrierDomain`, `AnalyticBarrierPoint`, and `analyticBarrier` in
  `Chap03/Definition_3_62`, the chapter precedent for keeping a logarithmic barrier on its strict
  domain and any ambient formula only as a bridge;
- `epigraphLogarithmicBarrier` and `StrictEpigraphFeasiblePoint` in
  `Chap05/Definition_5_4_3_5`, the adjacent Chapter 5 owner pattern for an epigraph barrier
  built from `strictConstraintSet` and `logarithmicBarrier`;
- `separableLogBarrierF4` in `Definition_5_4_8_12`, the Chapter 5 owner of the scalar barrier
  `f(y, t) = -log t - log (t^(2 / p) - y^2)`.

Best owner abstraction:
- source-facing: the strict barrier domain and logarithmic barrier attached to the box-constrained
  `ℓ_p` approximation barrier model;
- core/canonical: `strictConstraintSet` and `logarithmicBarrier` on the split continuous
  constraint family whose first two blocks recover the scalar owner `separableLogBarrierF4`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formula.

Primitive data:
- no new primitive data beyond `problem : LpApproximationBoxProblem n m`;
- the existing lifted decision variables `LpApproximationEpigraphPoint n m`.

Derived API:
- the internal split continuous constraint family;
- `problem.barrierModelBarrierDomain`;
- `problem.StrictBarrierModelPoint`;
- `problem.barrierModelBarrier`;
- the ambient evaluation theorems.

Source/core/bridge triage:
- source-facing: `problem.barrierModelBarrierDomain` and `problem.barrierModelBarrier`;
- core/canonical: the Chapter 1 owners `strictConstraintSet` and `logarithmicBarrier`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formulas.

The textbook barrier formula is only meaningful where every logarithmic argument is strictly
positive, so the public owner must live on that strict carrier rather than on all lifted points.
This refinement therefore keeps the same mathematical formula, but moves the public API to the
strict-domain logarithmic-barrier pattern already used elsewhere in the project.
-/

private abbrev residualArgument
    (problem : LpApproximationBoxProblem n m) (i : Fin m)
    (decision : LpApproximationEpigraphPoint n m) : ℝ :=
  ⟪problem.a i, decision.point⟫ - problem.b i

private def residualArgumentMap
    (problem : LpApproximationBoxProblem n m) (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := residualArgument problem i
  continuous_toFun := by
    simpa [residualArgument] using
      (((innerSL ℝ (problem.a i) : E →L[ℝ] ℝ).continuous.comp continuous_fst).sub
        continuous_const)

private def objectiveSlackMap :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := objectiveSlack
  continuous_toFun := continuous_snd.fst

private def residualSlackMap (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.residualSlack i
  continuous_toFun := (continuous_apply i).comp continuous_snd.snd

private def pointCoordinateMap (j : Fin n) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.point j
  continuous_toFun := by
    let hOfLp :
        Continuous (fun x : E ↦ x.ofLp) :=
      PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)
    have hcoord : Continuous fun x : E ↦ x j := (continuous_apply j).comp hOfLp
    simpa using hcoord.comp continuous_fst

private def barrierModelStrictConstraints
    (problem : LpApproximationBoxProblem n m) :
    Fin (m + (m + (1 + (n + n)))) → C(LpApproximationEpigraphPoint n m, ℝ) :=
  Fin.addCases
    (fun i ↦ -(residualSlackMap i))
    (Fin.addCases
      (fun i ↦
        { toFun := fun decision ↦
            (residualArgument problem i decision) ^ (2 : ℕ) -
              Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))
          continuous_toFun := by
            have harg :
                Continuous fun decision : LpApproximationEpigraphPoint n m ↦
                  residualArgument problem i decision :=
              (problem.residualArgumentMap i).continuous
            have hτ :
                Continuous fun decision : LpApproximationEpigraphPoint n m ↦
                  decision.residualSlack i :=
              (residualSlackMap i).continuous
            have hp : 0 ≤ 2 / (problem.p : ℝ) := by
              exact div_nonneg (by norm_num) (le_trans zero_lt_one.le problem.one_le_p)
            exact (harg.pow 2).sub <| hτ.rpow_const fun _ ↦ Or.inr hp })
      (Fin.addCases
        (fun _ ↦
          ∑ i : Fin m, residualSlackMap i - objectiveSlackMap)
        (Fin.addCases
          (fun j ↦ ContinuousMap.const _ (problem.α j) - pointCoordinateMap j)
          (fun j ↦ pointCoordinateMap j - ContinuousMap.const _ (problem.β j)))))

/-- The strict domain on which the box-constrained `ℓ_p` approximation barrier-model
logarithmic barrier is defined. -/
def barrierModelBarrierDomain
    (problem : LpApproximationBoxProblem n m) :
    Set (LpApproximationEpigraphPoint n m) :=
  strictConstraintSet problem.barrierModelStrictConstraints

/-- The subtype of points in the strict barrier-model barrier domain. This is the natural owner
carrier for the logarithmic barrier. -/
abbrev StrictBarrierModelPoint
    (problem : LpApproximationBoxProblem n m) :=
  {decision : LpApproximationEpigraphPoint n m // decision ∈ problem.barrierModelBarrierDomain}

/-- Membership in `problem.barrierModelBarrierDomain` means that every logarithmic argument in the
textbook barrier formula is strictly positive. -/
theorem mem_barrierModelBarrierDomain_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    decision ∈ problem.barrierModelBarrierDomain ↔
      (∀ i : Fin m,
        0 < decision.residualSlack i ∧
          (⟪problem.a i, decision.point⟫ - problem.b i) ^ (2 : ℕ) <
            Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))) ∧
        ∑ i : Fin m, decision.residualSlack i < decision.objectiveSlack ∧
        ∀ j : Fin n, problem.α j < decision.point j ∧ decision.point j < problem.β j := by
  sorry

/-- Definition 5.4.9.5: the logarithmic barrier attached to the box-constrained `ℓ_p`
approximation barrier model, kept on its strict domain and obtained by reusing the Chapter 1
owner `logarithmicBarrier` on the split continuous inequality family whose scalar blocks are the
Chapter 5 owner `separableLogBarrierF4 problem.p`. -/
def barrierModelBarrier
    (problem : LpApproximationBoxProblem n m) :
    C(problem.StrictBarrierModelPoint, ℝ) :=
  logarithmicBarrier problem.barrierModelStrictConstraints

/-- Evaluating `problem.barrierModelBarrier` on a strict-domain point recovers its ambient bridge
formula. -/
@[simp] theorem barrierModelBarrier_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierModelBarrier decision =
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i)) -
        Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (decision.1.point j - problem.α j) +
            Real.log (problem.β j - decision.1.point j)) := by
  sorry

/-- At a strict-domain tuple `(x, ξ, τ)`, the barrier-model logarithmic barrier is the textbook
formula
`F(x, ξ, τ) = \sum_i f(\langle a_i, x \rangle - b^{(i)}, τ_i)
  - \log (\xi - \sum_i τ_i)
  - \sum_j [\log (x_j - α_j) + \log (β_j - x_j)]`,
where `f = separableLogBarrierF4 problem.p`. -/
theorem barrierModelBarrier_apply_mk
    (problem : LpApproximationBoxProblem n m) (x : E) (ξ : ℝ) (τ : Fin m → ℝ)
    (h : (x, ξ, τ) ∈ problem.barrierModelBarrierDomain) :
    problem.barrierModelBarrier ⟨(x, ξ, τ), h⟩ =
      (∑ i : Fin m, separableLogBarrierF4 (problem.p : ℝ) (⟪problem.a i, x⟫ - problem.b i, τ i)) -
        Real.log (ξ - ∑ i : Fin m, τ i) -
        ∑ j : Fin n, (Real.log (x j - problem.α j) + Real.log (problem.β j - x j)) := by
  exact problem.barrierModelBarrier_apply ⟨(x, ξ, τ), h⟩

end LpApproximationBoxProblem

end

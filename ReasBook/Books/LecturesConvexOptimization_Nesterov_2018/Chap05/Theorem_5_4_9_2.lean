import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap04.Assumption_4_3_1
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_9_5
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_9_7
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_9_8
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_4_9_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LpApproximationBoxProblem
open LpApproximationEpigraphPoint
open scoped BigOperators Gradient RealInnerProductSpace LpBarrierNewtonSystem

variable {n m : ℕ}

/-- The Euclidean coordinate index for the private ambient bridge used to evaluate the Chapter 5
barrier gradient and Hessian. -/
private abbrev LpBarrierOracleAmbientIndex (n m : ℕ) :=
  Fin n ⊕ Option (Fin m)

/-- The Euclidean carrier for the private ambient bridge behind the public oracle on
`LpApproximationEpigraphPoint n m`. -/
private abbrev LpBarrierOracleAmbientPoint (n m : ℕ) :=
  EuclideanSpace ℝ (LpBarrierOracleAmbientIndex n m)

/-- Convert the chapter's canonical lifted decision point to the private Euclidean ambient bridge
used internally by `gradient` and `hessian`. -/
private def toLpBarrierOracleAmbientPoint
    (decision : LpApproximationEpigraphPoint n m) :
    LpBarrierOracleAmbientPoint n m :=
  (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).symm fun i ↦
    match i with
    | Sum.inl j => decision.point j
    | Sum.inr none => decision.objectiveSlack
    | Sum.inr (some j) => decision.residualSlack j

/-- Convert the private Euclidean ambient bridge point back to the chapter's canonical lifted
decision carrier. -/
private def ofLpBarrierOracleAmbientPoint
    (decision : LpBarrierOracleAmbientPoint n m) :
    LpApproximationEpigraphPoint n m :=
  let coords := EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ decision
  ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coords (Sum.inl i),
    coords (Sum.inr none),
    fun i ↦ coords (Sum.inr (some i)))

private def lpBarrierOracleAmbientLinearEquiv (n m : ℕ) :
    LpApproximationEpigraphPoint n m ≃ₗ[ℝ] LpBarrierOracleAmbientPoint n m where
  toFun := toLpBarrierOracleAmbientPoint
  invFun := ofLpBarrierOracleAmbientPoint
  map_add' x y := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j with
        | none =>
            rfl
        | some j =>
            rfl
  map_smul' c x := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j with
        | none =>
            rfl
        | some j =>
            rfl
  left_inv x := by
    ext
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
  right_inv x := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j <;> simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]

private abbrev lpBarrierOracleAmbientEquiv (n m : ℕ) :
    LpApproximationEpigraphPoint n m ≃L[ℝ] LpBarrierOracleAmbientPoint n m :=
  (lpBarrierOracleAmbientLinearEquiv n m).toContinuousLinearEquiv

/-- The canonical output type of the actual second-order oracle for the Chapter 5 barrier
`problem.barrierModelBarrier`: the barrier gradient together with the Hessian operator on the
canonical lifted decision carrier `LpApproximationEpigraphPoint n m`. -/
abbrev LpBarrierSecondOrderOracleOutput (n m : ℕ) :=
  LpApproximationEpigraphPoint n m ×
    (LpApproximationEpigraphPoint n m →L[ℝ] LpApproximationEpigraphPoint n m)

/-- A primitive evaluator for the Chapter 5 barrier second-order oracle across all box-constrained
`ℓ_p` approximation instances. -/
abbrev LpBarrierSecondOrderOracleEvaluator :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m),
    problem.StrictBarrierModelPoint → LpBarrierSecondOrderOracleOutput n m

/-- A primitive arithmetic-work model for evaluating the Chapter 5 barrier second-order oracle. -/
abbrev LpBarrierSecondOrderOracleWork :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m),
    problem.StrictBarrierModelPoint → ℕ

/-- The dense-model work bound for one second-order oracle call to the actual barrier
`problem.barrierModelBarrier`, written in terms of primitive per-index arithmetic costs for the
source-facing block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂`. -/
def barrierSecondOrderOracleDenseArithmeticWorkBound
    (m n : ℕ)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : ℕ :=
  m * (g1Work m n + n) +
    (m * g2Work m n + n) +
    (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n))

/-- Expanding `barrierSecondOrderOracleDenseArithmeticWorkBound m n g1Work g2Work h11Work h12Work
h22Work` recovers the dense-model arithmetic template for one second-order oracle call to the
barrier `problem.barrierModelBarrier`, expressed in terms of the primitive per-index block costs.
-/
theorem barrierSecondOrderOracleDenseArithmeticWorkBound_eq
    (m n : ℕ)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) :
    barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work =
      m * (g1Work m n + n) +
        (m * g2Work m n + n) +
        (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n)) :=
  rfl

/- Theorem 5.4.9.2 lies in the Chapter 5 box-constrained `ℓ_p` approximation / barrier-oracle
arithmetic-complexity domain.

Sampled owner declarations:
* `problem.barrierModelBarrier` and `problem.StrictBarrierModelPoint` in `Definition_5_4_9_5`,
  the chapter owners for the actual logarithmic barrier `F(x, ξ, τ)` and its strict barrier
  domain;
* `auxiliaryGradient` and `auxiliaryTimeDerivative` in `Definition_5_4_9_7`, the source-facing
  first-order block owners `g₁` and `g₂`;
* `secondOrderDerivativeBlock11`, `secondOrderDerivativeBlock12`, and
  `secondOrderDerivativeBlock22` in `Definition_5_4_9_8`, the source-facing second-order block
  owners `h₁₁`, `h₁₂`, and `h₂₂`;
* `κ[decision]`, `Λ₀[decision]`, `Λ₁[decision]`, `Λ₂[decision]`, and `D[decision]` in
  `Definition_5_4_9_9`, the chapter owners for the Hessian blocks of the actual barrier.

Best owner abstraction:
* source-facing: `decision.barrierSecondOrderOracleGradient` and `problem.barrierSecondOrderOracle`,
  the actual gradient/Hessian oracle for the barrier `problem.barrierModelBarrier`;
* core/canonical: the strict-domain owner `problem.StrictBarrierModelPoint` together with the
  existing Chapter 5 block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, `h₂₂`, `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`,
  `A`, and the canonical oracle predicate `HasSecondOrderOracleAt`;
* bridge/view: the Euclidean ambient formula `problem.barrierModelBarrierAmbient`, the dense block
  decomposition `problem.barrierSecondOrderOracleDenseBlocks`, and the dense-assembly work bound
  relating an arbitrary arithmetic-work model to that actual oracle.

Primitive data:
* the primitive per-index cost functions for evaluating `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂`.

Derived API:
* `decision.barrierSecondOrderOracleGradient`;
* `problem.barrierSecondOrderOracle`;
* `problem.barrierSecondOrderOracleDenseBlocks`;
* `EvaluatesLpBarrierSecondOrderOracle`;
* `LpBarrierSecondOrderOracleDenseAssemblyBound`;
* `HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound`;
* `hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound`;
* the theorem `barrierSecondOrderOracleDenseArithmeticComplexity_bound`.

This refinement keeps the asymptotic arithmetic statement `O(m n^2)`, but moves the public
source-facing layer onto the actual barrier oracle instead of leaving the file centered on five
ad hoc work functions and a point-ignored synthetic family. The concrete oracle now exposes the
actual gradient/Hessian data of `problem.barrierModelBarrier` at a strict point, while the dense
block decomposition and the abstract comparison from an arbitrary implementation to that oracle
remain only as bridges. -/

namespace LpApproximationBoxProblem

/-- The private ambient bridge formula whose restriction to the strict barrier domain is
`problem.barrierModelBarrier`. The public oracle stays on `LpApproximationEpigraphPoint n m`,
while this Euclidean realization is used internally for `gradient` and `hessian`. -/
private def barrierModelBarrierAmbient
    (problem : LpApproximationBoxProblem n m) :
    LpBarrierOracleAmbientPoint n m → ℝ :=
  fun decision ↦
    let lifted := ofLpBarrierOracleAmbientPoint decision
    (∑ i : Fin m,
      separableLogBarrierF4 (problem.p : ℝ)
        (⟪problem.a i, lifted.point⟫ - problem.b i, lifted.residualSlack i)) -
      Real.log (lifted.objectiveSlack - ∑ i : Fin m, lifted.residualSlack i) -
      ∑ j : Fin n,
        (Real.log (lifted.point j - problem.α j) +
          Real.log (problem.β j - lifted.point j))

/-- Evaluating `problem.barrierModelBarrierAmbient` gives the textbook ambient barrier formula in
the lifted coordinates `(x, ξ, τ)`. -/
@[simp] private theorem barrierModelBarrierAmbient_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : LpBarrierOracleAmbientPoint n m) :
    problem.barrierModelBarrierAmbient decision =
      let lifted := ofLpBarrierOracleAmbientPoint decision
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, lifted.point⟫ - problem.b i, lifted.residualSlack i)) -
        Real.log (lifted.objectiveSlack - ∑ i : Fin m, lifted.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (lifted.point j - problem.α j) +
            Real.log (problem.β j - lifted.point j)) :=
  rfl

/-- Restricting the ambient bridge formula `problem.barrierModelBarrierAmbient` to the strict
domain recovers the actual barrier owner `problem.barrierModelBarrier`. -/
private theorem barrierModelBarrier_eq_barrierModelBarrierAmbient
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierModelBarrier decision =
      problem.barrierModelBarrierAmbient (toLpBarrierOracleAmbientPoint decision.1) := by
  sorry

namespace StrictBarrierModelPoint

/-- The gradient of the actual barrier `problem.barrierModelBarrier` at a strict-domain point,
written in the Chapter 5 coordinates `(x, ξ, τ)` and assembled from the source-facing block
owners `g₁` and `g₂`. -/
def barrierSecondOrderOracleGradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    LpApproximationEpigraphPoint n m :=
  let barrierScalar := separableLogBarrierF4 problem.p
  let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
  let g1Vector : EuclideanSpace ℝ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
      auxiliaryGradient barrierScalar (decision.newtonSystemResidual i)
        (decision.1.residualSlack i)
  let g2Vector : Fin m → ℝ := fun i ↦
    auxiliaryTimeDerivative barrierScalar (decision.newtonSystemResidual i)
      (decision.1.residualSlack i)
  let boxGradient : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm fun j ↦
      -(1 / (decision.1.point j - problem.α j)) +
        1 / (problem.β j - decision.1.point j)
  ((A[problem]).toEuclideanLin g1Vector + boxGradient,
    -1 / gap,
    fun i ↦ g2Vector i + 1 / gap)

/-- Expanding `decision.barrierSecondOrderOracleGradient` recovers the Chapter 5 dense gradient
formula for `problem.barrierModelBarrier`, assembled from `g₁`, `g₂`, and the logarithmic box
terms. -/
theorem barrierSecondOrderOracleGradient_def
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient =
      let barrierScalar := separableLogBarrierF4 problem.p
      let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
      let g1Vector : EuclideanSpace ℝ (Fin m) :=
        (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
          auxiliaryGradient barrierScalar (decision.newtonSystemResidual i)
            (decision.1.residualSlack i)
      let g2Vector : Fin m → ℝ := fun i ↦
        auxiliaryTimeDerivative barrierScalar (decision.newtonSystemResidual i)
          (decision.1.residualSlack i)
      let boxGradient : EuclideanSpace ℝ (Fin n) :=
        (EuclideanSpace.equiv (Fin n) ℝ).symm fun j ↦
          -(1 / (decision.1.point j - problem.α j)) +
            1 / (problem.β j - decision.1.point j)
      ((A[problem]).toEuclideanLin g1Vector + boxGradient,
        -1 / gap,
        fun i ↦ g2Vector i + 1 / gap) :=
  rfl

/-- The `x`-component of `decision.barrierSecondOrderOracleGradient` is the dense sum of the
`g₁` evaluations and the box-logarithm gradient terms. -/
@[simp] theorem barrierSecondOrderOracleGradient_point
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient.point =
      (A[problem]).toEuclideanLin
          ((EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
            auxiliaryGradient (separableLogBarrierF4 problem.p) (decision.newtonSystemResidual i)
              (decision.1.residualSlack i)) +
        (EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun j ↦
            -(1 / (decision.1.point j - problem.α j)) +
              1 / (problem.β j - decision.1.point j)) :=
  rfl

/-- The `ξ`-component of `decision.barrierSecondOrderOracleGradient` is the derivative of the
coupling logarithm `- log (ξ - ∑ i, τ⁽ⁱ⁾)`. -/
@[simp] theorem barrierSecondOrderOracleGradient_objectiveSlack
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient.objectiveSlack =
      -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) :=
  rfl

/-- The `τ⁽ⁱ⁾`-component of `decision.barrierSecondOrderOracleGradient` is the sum of the
source-facing `g₂` contribution and the coupling-logarithm derivative. -/
@[simp] theorem barrierSecondOrderOracleGradient_residualSlack
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    decision.barrierSecondOrderOracleGradient.residualSlack i =
      auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
          (decision.newtonSystemResidual i) (decision.1.residualSlack i) +
        1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j) :=
  rfl

/-- At a strict barrier-model point, the explicit vector
`decision.barrierSecondOrderOracleGradient` is genuine gradient data for the ambient bridge
formula of `problem.barrierModelBarrier`. -/
private theorem hasGradientAt_barrierModelBarrierAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasGradientAt problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient)
      (toLpBarrierOracleAmbientPoint decision.1) := by
  sorry

/-- The explicit dense formula `decision.barrierSecondOrderOracleGradient` agrees with the
Euclidean gradient of the ambient bridge formula for `problem.barrierModelBarrier`. -/
private theorem barrierSecondOrderOracleGradient_eq_gradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    ∇ problem.barrierModelBarrierAmbient (toLpBarrierOracleAmbientPoint decision.1) =
      toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient := by
  sorry

/-- The ambient bridge formula for `problem.barrierModelBarrier` also carries genuine second-order
oracle data at every strict barrier-model point. -/
private theorem hasFDerivAt_barrierModelBarrierAmbient_gradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasFDerivAt (∇ problem.barrierModelBarrierAmbient)
      (hessian problem.barrierModelBarrierAmbient
        (toLpBarrierOracleAmbientPoint decision.1))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  sorry

end StrictBarrierModelPoint

/-- The Hessian part of the actual second-order oracle for `problem.barrierModelBarrier`,
transported from the private Euclidean ambient bridge back to the canonical lifted carrier
`LpApproximationEpigraphPoint n m`. -/
def StrictBarrierModelPoint.barrierSecondOrderOracleHessian
    {problem : LpApproximationBoxProblem n m}
    (decision : problem.StrictBarrierModelPoint) :
    LpApproximationEpigraphPoint n m →L[ℝ] LpApproximationEpigraphPoint n m :=
  let ambientEquiv := lpBarrierOracleAmbientEquiv n m
  ambientEquiv.symm.toContinuousLinearMap.comp
    ((hessian problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.1)).comp ambientEquiv.toContinuousLinearMap)

/-- Expanding `decision.barrierSecondOrderOracleHessian` recovers the Hessian of the private
ambient bridge formula, conjugated back to `LpApproximationEpigraphPoint n m`. -/
theorem StrictBarrierModelPoint.barrierSecondOrderOracleHessian_def
    {problem : LpApproximationBoxProblem n m}
    (decision : problem.StrictBarrierModelPoint) :
    decision.barrierSecondOrderOracleHessian =
      let ambientEquiv := lpBarrierOracleAmbientEquiv n m
      ambientEquiv.symm.toContinuousLinearMap.comp
        ((hessian problem.barrierModelBarrierAmbient
          (toLpBarrierOracleAmbientPoint decision.1)).comp ambientEquiv.toContinuousLinearMap) :=
  rfl

/-- The actual second-order oracle for the barrier `problem.barrierModelBarrier`: the explicit
gradient formula together with the Hessian operator on the canonical lifted decision carrier. -/
def barrierSecondOrderOracle
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    LpBarrierSecondOrderOracleOutput n m :=
  (decision.barrierSecondOrderOracleGradient,
    decision.barrierSecondOrderOracleHessian)

/-- Expanding `problem.barrierSecondOrderOracle decision` recovers the actual barrier gradient and
Hessian data at the strict point `decision`. -/
theorem barrierSecondOrderOracle_def
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierSecondOrderOracle decision =
      (decision.barrierSecondOrderOracleGradient,
        decision.barrierSecondOrderOracleHessian) :=
  rfl

/-- The dense block presentation of the Hessian part of `problem.barrierSecondOrderOracle`,
assembled from the Chapter 5 Newton blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, and `D`. -/
def barrierSecondOrderOracleDenseBlocks
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :=
  (decision.barrierSecondOrderOracleGradient,
    κ[decision],
    Λ₀[decision],
    Λ₁[decision],
    Λ₂[decision],
    D[decision])

/-- Expanding `problem.barrierSecondOrderOracleDenseBlocks decision` recovers the concrete dense
block data used to assemble the Hessian of `problem.barrierModelBarrier`. -/
theorem barrierSecondOrderOracleDenseBlocks_def
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierSecondOrderOracleDenseBlocks decision =
      (decision.barrierSecondOrderOracleGradient,
        κ[decision],
        Λ₀[decision],
        Λ₁[decision],
        Λ₂[decision],
        D[decision]) :=
  rfl

/-- The source-facing oracle `problem.barrierSecondOrderOracle` supplies genuine second-order
oracle data for the ambient bridge formula of `problem.barrierModelBarrier`. -/
private theorem barrierSecondOrderOracle_hasSecondOrderOracleAt
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    HasSecondOrderOracleAt problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.1) := by
  sorry

end LpApproximationBoxProblem

/-- A primitive oracle evaluator computes the actual Chapter 5 second-order oracle when it agrees
pointwise with `problem.barrierSecondOrderOracle`. -/
def EvaluatesLpBarrierSecondOrderOracle
    (oracle : LpBarrierSecondOrderOracleEvaluator) : Prop :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint),
      oracle problem decision = problem.barrierSecondOrderOracle decision

/-- The primitive dense-model hypothesis that every per-index evaluation of the source-facing
block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` has uniformly bounded arithmetic cost. -/
def HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : Prop :=
  ∃ C_eval : ℕ,
    ∀ m n : ℕ, 0 < m → 0 < n →
      g1Work m n ≤ C_eval ∧
        g2Work m n ≤ C_eval ∧
        h11Work m n ≤ C_eval ∧
        h12Work m n ≤ C_eval ∧
        h22Work m n ≤ C_eval

section OracleWork

variable
  (oracle : LpBarrierSecondOrderOracleEvaluator)
  (oracleWork : LpBarrierSecondOrderOracleWork)

/-- The dense-assembly cost bound for one second-order oracle call to the actual barrier
`problem.barrierModelBarrier`: the arithmetic work is accounted for by evaluating the
primitive block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` at each residual block and
assembling the resulting gradient and Hessian by dense vector and matrix bookkeeping. -/
def LpBarrierSecondOrderOracleDenseAssemblyBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : Prop :=
  EvaluatesLpBarrierSecondOrderOracle oracle ∧
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (decision : problem.StrictBarrierModelPoint),
        oracleWork problem decision ≤
          barrierSecondOrderOracleDenseArithmeticWorkBound m n
            g1Work g2Work h11Work h12Work h22Work

/-- The source-facing `O(m n^2)` arithmetic-complexity owner for the second-order oracle of the
actual barrier `problem.barrierModelBarrier`. -/
def HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound
    : Prop :=
  EvaluatesLpBarrierSecondOrderOracle oracle ∧
    ∃ C_oracle : ℝ,
      0 < C_oracle ∧
        ∀ m n : ℕ, 0 < m → 0 < n →
          ∀ (problem : LpApproximationBoxProblem n m) (decision : problem.StrictBarrierModelPoint),
            (oracleWork problem decision : ℝ) ≤
              C_oracle * (m : ℝ) * (n : ℝ) ^ (2 : ℕ)

/-- Unfolding
`HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracleWork`
recovers the explicit constant-factor form of the dense-model bound `O(m n^2)` for the
second-order oracle of `problem.barrierModelBarrier`. -/
theorem hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_iff
    :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracle oracleWork ↔
      EvaluatesLpBarrierSecondOrderOracle oracle ∧
        ∃ C_oracle : ℝ,
          0 < C_oracle ∧
            ∀ m n : ℕ, 0 < m → 0 < n →
              ∀ (problem : LpApproximationBoxProblem n m)
                (decision : problem.StrictBarrierModelPoint),
                (oracleWork problem decision : ℝ) ≤
                  C_oracle * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := by
  rfl

end OracleWork

private theorem barrierSecondOrderOracleDenseArithmeticWorkBound_le
    {m n C_eval : ℕ}
    {g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hg1 : g1Work m n ≤ C_eval)
    (hg2 : g2Work m n ≤ C_eval)
    (hh11 : h11Work m n ≤ C_eval)
    (hh12 : h12Work m n ≤ C_eval)
    (hh22 : h22Work m n ≤ C_eval) :
    barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work ≤
      (5 * C_eval + 5) * m * n ^ 2 := by
  rw [barrierSecondOrderOracleDenseArithmeticWorkBound_eq]
  let M := m * n ^ 2
  have hn_sq : n ≤ n ^ 2 := by
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left n hn
  have hn_sq_one : 1 ≤ n ^ 2 := le_trans hn hn_sq
  have hC_sq : C_eval ≤ C_eval * n ^ 2 := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left C_eval hn_sq_one
  have hmn_sq : m * n ≤ M := by
    simpa [M] using Nat.mul_le_mul_left m hn_sq
  have hm_sq : m ≤ m * n ^ 2 := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hn_sq_one
  have hnm_sq : n ≤ M := by
    calc
      n ≤ m * n := by
        simpa [Nat.one_mul, Nat.mul_comm] using Nat.mul_le_mul_right n hm
      _ ≤ M := hmn_sq
  have hterm1 :
      m * (g1Work m n + n) ≤ (C_eval + 1) * M := by
    calc
      m * (g1Work m n + n) ≤ m * (C_eval + n ^ 2) := by
        gcongr
      _ ≤ m * (C_eval * n ^ 2 + n ^ 2) := by
        gcongr
      _ = (C_eval + 1) * M := by
        dsimp [M]
        ring
  have hterm2 :
      m * g2Work m n + n ≤ (C_eval + 1) * M := by
    calc
      m * g2Work m n + n ≤ m * C_eval + M := by
        gcongr
      _ ≤ m * (C_eval * n ^ 2) + M := by
        gcongr
      _ = (C_eval + 1) * M := by
        dsimp [M]
        ring
  have hterm3_core :
      m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) ≤ 3 * C_eval * M := by
    have hh12' : n * h12Work m n ≤ n ^ 2 * C_eval := by
      calc
        n * h12Work m n ≤ n * C_eval := by
          gcongr
        _ ≤ n ^ 2 * C_eval := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.mul_le_mul_right C_eval hn_sq
    have hh22' : h22Work m n ≤ n ^ 2 * C_eval := by
      calc
        h22Work m n ≤ C_eval := hh22
        _ ≤ n ^ 2 * C_eval := by
          simpa [Nat.mul_comm] using hC_sq
    calc
      m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n)
        ≤ m * (n ^ 2 * C_eval + n ^ 2 * C_eval + n ^ 2 * C_eval) := by
          gcongr
      _ = 3 * C_eval * M := by
        dsimp [M]
        ring
  have hterm3_overhead :
      m * n + m + n ≤ 3 * M := by
    calc
      m * n + m + n ≤ M + m + n := by
        gcongr
      _ ≤ M + M + n := by
        gcongr
      _ ≤ M + M + M := by
        gcongr
      _ = 3 * M := by
        ring
  calc
    m * (g1Work m n + n) +
        (m * g2Work m n + n) +
        (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n))
      = (m * (g1Work m n + n) + (m * g2Work m n + n)) +
          (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n)) := by
            ring
    _ ≤ ((C_eval + 1) * M + (C_eval + 1) * M) + (3 * C_eval * M + 3 * M) := by
      gcongr
    _ = (5 * C_eval + 5) * M := by
      ring
    _ = (5 * C_eval + 5) * m * n ^ 2 := by
      simp [M, Nat.mul_assoc]

private theorem barrierSecondOrderOracleDenseArithmeticWorkBound_le_real
    {m n C_eval : ℕ}
    {g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hg1 : g1Work m n ≤ C_eval)
    (hg2 : g2Work m n ≤ C_eval)
    (hh11 : h11Work m n ≤ C_eval)
    (hh12 : h12Work m n ≤ C_eval)
    (hh22 : h22Work m n ≤ C_eval) :
    (barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work : ℝ) ≤
      (5 * C_eval + 5 : ℝ) * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := by
  exact_mod_cast
    barrierSecondOrderOracleDenseArithmeticWorkBound_le
      (Nat.succ_le_of_lt hm) (Nat.succ_le_of_lt hn) hg1 hg2 hh11 hh12 hh22

/-- If the arithmetic work of a second-order barrier oracle is bounded by the concrete dense
assembly template, then that work satisfies the source-facing owner
`HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound`. -/
theorem hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound
    (oracle : LpBarrierSecondOrderOracleEvaluator)
    (oracleWork : LpBarrierSecondOrderOracleWork)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ)
    (hassembly :
      LpBarrierSecondOrderOracleDenseAssemblyBound oracle oracleWork
        g1Work g2Work h11Work h12Work h22Work)
    (hblocks :
      HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
        g1Work g2Work h11Work h12Work h22Work) :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracle oracleWork := by
  rcases hassembly with ⟨horacle, hassembly⟩
  rcases hblocks with ⟨C_eval, hC_eval⟩
  refine ⟨horacle, (5 * C_eval + 5 : ℝ), by positivity, ?_⟩
  intro m n hm hn problem decision
  rcases hC_eval m n hm hn with ⟨hg1, hg2, hh11, hh12, hh22⟩
  have hwork := hassembly problem decision
  have hdense := barrierSecondOrderOracleDenseArithmeticWorkBound_le_real
    hm hn hg1 hg2 hh11 hh12 hh22
  calc
    (oracleWork problem decision : ℝ)
      ≤ barrierSecondOrderOracleDenseArithmeticWorkBound m n
          g1Work g2Work h11Work h12Work h22Work := by
            exact_mod_cast hwork
    _ ≤ (5 * C_eval + 5 : ℝ) * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := hdense

/-- The arithmetic work model attached to the concrete dense second-order oracle for
`problem.barrierModelBarrier` satisfies the corresponding dense assembly bound. -/
theorem barrierSecondOrderOracleDenseAssemblyBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) :
    LpBarrierSecondOrderOracleDenseAssemblyBound
      (fun {_} {_} problem decision ↦ problem.barrierSecondOrderOracle decision)
      (fun {n} {m} _ _ ↦
        barrierSecondOrderOracleDenseArithmeticWorkBound m n
          g1Work g2Work h11Work h12Work h22Work)
      g1Work g2Work h11Work h12Work h22Work := by
  refine ⟨?_, ?_⟩
  · intro n m problem decision
    rfl
  · intro _ _ problem decision
    rfl

/-- Theorem 5.4.9.2: in the dense model, if each per-index evaluation of the source-facing block
owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` has uniformly bounded arithmetic cost, then the
actual second-order oracle for `problem.barrierModelBarrier` has arithmetic complexity `O(m n^2)`
for every evaluator/work model whose outputs agree with `problem.barrierSecondOrderOracle` and
whose arithmetic work is bounded by the dense assembly template. -/
theorem barrierSecondOrderOracleDenseArithmeticComplexity_bound
    (oracle : LpBarrierSecondOrderOracleEvaluator)
    (oracleWork : LpBarrierSecondOrderOracleWork)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ)
    (hassembly :
      LpBarrierSecondOrderOracleDenseAssemblyBound oracle oracleWork
        g1Work g2Work h11Work h12Work h22Work)
    (hblocks :
      HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
        g1Work g2Work h11Work h12Work h22Work) :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound
      oracle oracleWork :=
  hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound
    oracle oracleWork
    g1Work g2Work h11Work h12Work h22Work
    hassembly
    hblocks

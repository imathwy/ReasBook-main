import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_9_6
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_4_9_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators RealInnerProductSpace LpBarrierNewtonSystem

variable {n m : ℕ}

open LpApproximationBoxProblem
open LpApproximationEpigraphPoint

/- Theorem 5.4.9.3 lies in the Chapter 5 explicit-structure `ℓ_p`-barrier Newton-system /
short-step complexity domain.

Sampled owner-style declarations:
* `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemKappa`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda0`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda1`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda2`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD`, and
  `LpApproximationBoxProblem.newtonSystemConstraintMatrix` in `Definition_5_4_9_9`, the chapter
  owners for the source-derived Newton blocks coming from `separableLogBarrierF4 problem.p`;
* `problem.StrictBarrierModelPoint` in `Definition_5_4_9_5`, the strict-domain owner already
  established for the logarithmic barrier and its interior points;
* `LpApproximationEpigraphPoint.point`, `objectiveSlack`, and `residualSlack` in
  `Theorem_5_4_8_9`, the chapter owner for the lifted increment variables `(Δx, Δξ, Δτ)`;
* `Matrix.mulVec`, the canonical owner for the vector form of the Newton equations;
* `HasLpBarrierShortStepIterationBound` in `Definition_5_4_9_6`, the chapter's source-facing
  owner for the short-step iteration count bound on the primitive function `N_it`.

Best owner abstraction:
* source-facing: the current `ℓ_p` approximation problem, the current strict barrier-model point,
  the displayed Newton system for the scalar barrier `separableLogBarrierF4 problem.p`, and the
  primitive per-step and total arithmetic-work functions;
* core/canonical: the derived Newton shorthand blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`, `A` from
  `Definition_5_4_9_9`, together with `Matrix.mulVec` and the nearby short-step iteration owner
  `HasLpBarrierShortStepIterationBound`;
* bridge/view: the coordinatewise expansion theorem
  `isLpBarrierNewtonSystemSolution_iff` and the asymptotic bridge from per-step work to total
  short-step work.

Primitive data:
* `problem : LpApproximationBoxProblem n m`;
* `decision : problem.StrictBarrierModelPoint`;
* the right-hand sides `gradX`, `gradTau`, `gradXi`, and `t`;
* the primitive uniform Newton solver family
  `solver : ∀ {n m}, LpApproximationBoxProblem n m → ... → LpApproximationEpigraphPoint n m`;
* the primitive arithmetic-work family
  `arithmeticWork : ∀ {n m}, LpApproximationBoxProblem n m → ... → ℕ`;
* the primitive short-step iteration-count model `iterationCount : ℕ → ℕ → ℕ`.

Derived API:
* the Newton-system solution predicate at a strict barrier-model point, with the lifted increment
  `(Δx, Δξ, Δτ)` still carried by `LpApproximationEpigraphPoint n m`;
* the coordinatewise expansion theorem;
* the derived step-bound owner `LpBarrierNewtonStepBound`;
* the source-facing per-step owner `HasLpBarrierNewtonSystemArithmeticComplexityBound`;
* the explicit per-step arithmetic-budget witness attached to a constant `C_step`;
* the canonical total-work model induced from the iteration-count family and that uniform
  per-step budget, indexed only by `(m, n)`;
* the source-facing total-cost owner
  `HasLpBarrierShortStepTotalArithmeticComplexityBound`;
* the bridge theorem combining the per-step Newton cost with the chapter owner
  `HasLpBarrierShortStepIterationBound`.

This refinement keeps the Newton-system statement on the existing chapter owners, but anchors its
barrier Hessian data at the strict-domain owner `problem.StrictBarrierModelPoint` from
`Definition_5_4_9_5`. The lifted increment still uses the chapter's existing carrier
`LpApproximationEpigraphPoint n m`, and the complexity layer remains as predicates on primitive
solver/work or total-work data rather than on a bespoke wrapper structure. The per-step arithmetic
owner is factored into an explicit witness layer `HasLpBarrierNewtonSystemArithmeticBudget`, and
the short-step bridge now uses the canonical total-work model induced by `iterationCount` and
that uniform per-step budget instead of an unconstrained existential total-work family. -/

/-- The displayed Newton system for the explicit-structure `ℓ_p` approximation barrier, written
using the Chapter 5 source-derived blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`, and `A` attached to the
current `problem` and strict barrier-model point `decision`. The first line is expressed in the
dimensionally consistent form `Λ₀ Δx + A (Λ₁ (Aᵀ Δx) + Λ₂ Δτ) = ∇ₓF`, which is equivalent to
`(Λ₀ + A Λ₁ Aᵀ) Δx + A Λ₂ Δτ = ∇ₓF`. The step variable lives in the canonical lifted carrier
`LpApproximationEpigraphPoint n m`, with `step.point = Δx`, `step.objectiveSlack = Δξ`, and
`step.residualSlack = Δτ`. -/
def IsLpBarrierNewtonSystemSolution
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : EuclideanSpace ℝ (Fin m))
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) : Prop :=
  let κ := κ[decision]
  let Λ₀ := Λ₀[decision]
  let Λ₁ := Λ₁[decision]
  let Λ₂ := Λ₂[decision]
  let D := D[decision]
  let A := A[problem]
  let adjointX := Aᵀ.mulVec step.point
  Matrix.mulVec Λ₀ step.point +
      Matrix.mulVec A (Matrix.mulVec Λ₁ adjointX + Matrix.mulVec Λ₂ step.residualSlack) =
    gradX ∧
    Matrix.mulVec Λ₂ adjointX +
        Matrix.mulVec (D + κ • (1 : Matrix (Fin m) (Fin m) ℝ)) step.residualSlack +
        (κ * step.objectiveSlack) • (1 : Fin m → ℝ) =
      gradTau ∧
    κ * (∑ i : Fin m, step.residualSlack i) + κ * step.objectiveSlack = gradXi + t

-- Proof sketch: unfold `IsLpBarrierNewtonSystemSolution`; the definition is exactly the three
-- displayed equations of the Newton system, written coordinatewise in the `x`- and `τ`-blocks and
-- with the scalar coupling equation in the last line.
/-- Expanding `IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step`
recovers the three equations of the explicit-structure Newton system. -/
theorem isLpBarrierNewtonSystemSolution_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : EuclideanSpace ℝ (Fin m))
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) :
    IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step ↔
      let κ := κ[decision]
      let Λ₀ := Λ₀[decision]
      let Λ₁ := Λ₁[decision]
      let Λ₂ := Λ₂[decision]
      let D := D[decision]
      let A := A[problem]
      let adjointX := Aᵀ.mulVec step.point
      (∀ i : Fin n,
        (Matrix.mulVec Λ₀ step.point) i +
            (Matrix.mulVec A
              (Matrix.mulVec Λ₁ adjointX + Matrix.mulVec Λ₂ step.residualSlack)) i =
          gradX i) ∧
        (∀ i : Fin m,
          (Matrix.mulVec Λ₂ adjointX) i +
              (Matrix.mulVec (D + κ • (1 : Matrix (Fin m) (Fin m) ℝ))
                step.residualSlack) i +
              κ * step.objectiveSlack =
            gradTau i) ∧
        κ * (∑ i : Fin m, step.residualSlack i) + κ * step.objectiveSlack = gradXi + t := by
  dsimp [IsLpBarrierNewtonSystemSolution]
  constructor
  · rintro ⟨hx, hTau, hXi⟩
    refine ⟨?_, ?_, hXi⟩
    · intro i
      simpa using congrFun hx i
    · intro i
      simpa using congrFun hTau i
  · rintro ⟨hx, hTau, hXi⟩
    refine ⟨?_, ?_, hXi⟩
    · simpa using funext hx
    · ext i
      simpa using hTau i

section NewtonSystemArithmeticComplexity

variable
  (solver :
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (_ : problem.StrictBarrierModelPoint)
      (_ : EuclideanSpace ℝ (Fin n))
      (_ : EuclideanSpace ℝ (Fin m))
      (_ _ : ℝ),
      LpApproximationEpigraphPoint n m)
  (arithmeticWork :
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (_ : problem.StrictBarrierModelPoint)
      (_ : EuclideanSpace ℝ (Fin n))
      (_ : EuclideanSpace ℝ (Fin m))
      (_ _ : ℝ),
      ℕ)

/-- The arithmetic-work estimate for one execution of a primitive `ℓ_p`-barrier Newton solver. -/
def LpBarrierNewtonStepBound
    (C : ℝ)
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : EuclideanSpace ℝ (Fin m))
    (gradXi t : ℝ) : Prop :=
  let step := solver problem decision gradX gradTau gradXi t
  IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step ∧
    (arithmeticWork problem decision gradX gradTau gradXi t : ℝ) ≤
      C * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)

/-- A positive constant `C_step` is a valid uniform arithmetic budget for the primitive
`ℓ_p`-barrier Newton solver/work data when every Newton solve lies in
`O(n^3 + m n^2)` with that same constant and returns a genuine solution of the displayed Newton
system. The positivity restriction avoids forcing a spurious zero-cost statement in the
degenerate display case `n = 0`. -/
def HasLpBarrierNewtonSystemArithmeticBudget
    (C_step : ℝ) : Prop :=
  0 < C_step ∧
    ∀ m n : ℕ, 0 < n →
      ∀ (problem : LpApproximationBoxProblem n m)
        (decision : problem.StrictBarrierModelPoint)
        (gradX : EuclideanSpace ℝ (Fin n))
        (gradTau : EuclideanSpace ℝ (Fin m))
        (gradXi t : ℝ),
        LpBarrierNewtonStepBound
          solver arithmeticWork C_step problem decision gradX gradTau gradXi t

/-- Theorem 5.4.9.3's per-step arithmetic-complexity owner for the explicit `ℓ_p`-barrier
Newton system. It records the existence of a positive uniform arithmetic budget
`HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step`. -/
def HasLpBarrierNewtonSystemArithmeticComplexityBound : Prop :=
  ∃ C_step : ℝ, HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step

-- Proof sketch: unfold `HasLpBarrierNewtonSystemArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the per-step arithmetic estimate `O(n^3 + m n^2)` on
-- primitive solver/work data.
/-- Unfolding `HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork` recovers
the explicit constant-factor form of the bound `O(n^3 + m n^2)` on primitive Newton solver/work
data. -/
theorem hasLpBarrierNewtonSystemArithmeticComplexityBound_iff
    : HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork ↔
      ∃ C_step : ℝ,
        HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step := by
  rfl

end NewtonSystemArithmeticComplexity

section ShortStepTotalArithmeticComplexity

variable (ε : ℝ)
  (iterationCount : ℕ → ℕ → ℕ)
  (totalArithmeticWork : ℕ → ℕ → ℕ)

/-- The canonical total arithmetic-work model induced by a short-step iteration-count family and
the uniform per-step arithmetic budget `C_step`. -/
def lpBarrierShortStepTotalArithmeticWork
    (C_step : ℝ) : ℕ → ℕ → ℕ :=
  fun m n ↦
    iterationCount m n *
      Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2))

/-- Expanding `lpBarrierShortStepTotalArithmeticWork iterationCount C_step` recovers the product
of the iteration count and the uniform step budget `⌈C_step (n^3 + m n^2)⌉`. -/
theorem lpBarrierShortStepTotalArithmeticWork_apply
    (C_step : ℝ) (m n : ℕ) :
    lpBarrierShortStepTotalArithmeticWork iterationCount C_step m n =
      iterationCount m n *
        Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) :=
  rfl

/-- Theorem 5.4.9.3's total arithmetic-complexity owner for the short-step `ℓ_p`-barrier method.
It records the source-facing `O(n^2 (m + n)^(3 / 2) log ((m + n) / ε))` bound on primitive total
arithmetic-work data for the full short-step algorithm at a fixed small accuracy `ε ∈ (0, 1)`. A
canonical such family is provided by `lpBarrierShortStepTotalArithmeticWork iterationCount C_step`
once a uniform per-step budget `C_step` is available. -/
def HasLpBarrierShortStepTotalArithmeticComplexityBound
    : Prop :=
  ε ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ C_total : ℝ,
      0 < C_total ∧
        ∀ m n : ℕ, 0 < n →
          (totalArithmeticWork m n : ℝ) ≤
            C_total * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) *
              Real.log (((m + n : ℕ) : ℝ) / ε)

-- Proof sketch: unfold `HasLpBarrierShortStepTotalArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the total short-step arithmetic estimate on primitive total
-- arithmetic-work data.
/-- Unfolding
`HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork` recovers the explicit
constant-factor total arithmetic bound on primitive total arithmetic-work data, together with the
fixed small-accuracy hypothesis `ε ∈ (0, 1)`. -/
theorem hasLpBarrierShortStepTotalArithmeticComplexityBound_iff
    : HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork ↔
      ε ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ C_total : ℝ,
          0 < C_total ∧
            ∀ m n : ℕ, 0 < n →
              (totalArithmeticWork m n : ℝ) ≤
                C_total * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) *
                  Real.log (((m + n : ℕ) : ℝ) / ε) := by
  rfl

end ShortStepTotalArithmeticComplexity

-- Proof sketch: eliminate `Δτ` and then `Δξ`, form the Schur complement in the `x`-variables,
-- and use the diagonal structure of `Λ₀`, `Λ₁`, `Λ₂`, and `D`. Forming the weighted matrices
-- costs `O(m n²)`, while the dense `n × n` factorization and solve cost `O(n³)`.
/-- The explicit `ℓ_p`-barrier Newton system can be solved with arithmetic work
`O(n^3 + m n^2)`. The main public conclusion is the source-facing owner
`HasLpBarrierNewtonSystemArithmeticComplexityBound`; the positive budget constant remains internal
to that owner. -/
theorem lpBarrierNewtonSystemArithmeticComplexity_bound :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : EuclideanSpace ℝ (Fin n))
          (_ : EuclideanSpace ℝ (Fin m))
          (_ _ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : EuclideanSpace ℝ (Fin n))
            (_ : EuclideanSpace ℝ (Fin m))
            (_ _ : ℝ),
            ℕ,
        HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork := sorry

-- Proof sketch: combine the explicit per-step budget witness
-- `HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step` with the short-step
-- iteration-count owner `HasLpBarrierShortStepIterationBound ε iterationCount`, and multiply the
-- iteration count by the induced uniform step budget.
/-- Combining the per-step Newton-system arithmetic bound with the Chapter 5 short-step
iteration-count owner yields the canonical total arithmetic-work model induced by the iteration
count and the same per-step budget witness. That induced total-work family satisfies the
corresponding source-facing total arithmetic-complexity bound. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound_of_budget
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (solver :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : EuclideanSpace ℝ (Fin n))
        (_ : EuclideanSpace ℝ (Fin m))
        (_ _ : ℝ),
        LpApproximationEpigraphPoint n m)
    (arithmeticWork :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : EuclideanSpace ℝ (Fin n))
        (_ : EuclideanSpace ℝ (Fin m))
        (_ _ : ℝ),
        ℕ)
    (C_step : ℝ)
    (hstep : HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    HasLpBarrierShortStepTotalArithmeticComplexityBound ε
      (lpBarrierShortStepTotalArithmeticWork iterationCount C_step) := sorry

-- Proof sketch: unpack the per-step owner to recover a budget witness `C_step`, then apply
-- `lpBarrierShortStepTotalArithmeticComplexity_bound_of_budget` to the induced total-work model.
/-- Combining the per-step arithmetic-complexity owner with the Chapter 5 short-step iteration
owner yields a source-facing total arithmetic-work owner. The induced family
`lpBarrierShortStepTotalArithmeticWork iterationCount C_step` is retained only as bridge data,
through an accompanying budget witness `C_step`. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound_of_bounds
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (solver :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : EuclideanSpace ℝ (Fin n))
        (_ : EuclideanSpace ℝ (Fin m))
        (_ _ : ℝ),
        LpApproximationEpigraphPoint n m)
    (arithmeticWork :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : EuclideanSpace ℝ (Fin n))
        (_ : EuclideanSpace ℝ (Fin m))
        (_ _ : ℝ),
        ℕ)
    (hstep : HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    ∃ totalArithmeticWork : ℕ → ℕ → ℕ,
      HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork ∧
        ∃ C_step : ℝ,
          HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step ∧
            totalArithmeticWork =
              lpBarrierShortStepTotalArithmeticWork iterationCount C_step := sorry

-- Proof sketch: combine `lpBarrierNewtonSystemArithmeticComplexity_bound` with
-- `lpBarrierShortStepTotalArithmeticComplexity_bound_of_bounds`.
/-- Theorem 5.4.9.3: if the short-step `ℓ_p`-barrier method has iteration count controlled by the
chapter owner `HasLpBarrierShortStepIterationBound ε iterationCount`, then there exist primitive
Newton solver/work data satisfying the source-facing per-step owner
`HasLpBarrierNewtonSystemArithmeticComplexityBound`. There also exists source-facing total
arithmetic-work data satisfying `HasLpBarrierShortStepTotalArithmeticComplexityBound ε`; the
canonical induced family `lpBarrierShortStepTotalArithmeticWork iterationCount C_step` is kept
only as bridge data via an accompanying budget witness `C_step`. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : EuclideanSpace ℝ (Fin n))
          (_ : EuclideanSpace ℝ (Fin m))
          (_ _ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : EuclideanSpace ℝ (Fin n))
            (_ : EuclideanSpace ℝ (Fin m))
            (_ _ : ℝ),
            ℕ,
        HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork ∧
          ∃ totalArithmeticWork : ℕ → ℕ → ℕ,
            HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork ∧
              ∃ C_step : ℝ,
                HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step ∧
                  totalArithmeticWork =
                    lpBarrierShortStepTotalArithmeticWork iterationCount C_step :=
  sorry

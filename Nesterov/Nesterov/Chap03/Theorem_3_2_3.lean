import Nesterov.Chap03.Algorithm_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

/- Theorem 3.2.3 lies in the chapter's whole-space multi-constraint first-order method domain.

Sampled owner declarations:
* `MultipleConstraintFirstOrderProblem` in `Algorithm_3_4`, the chapter owner for a convex
  objective, a finite constraint family, and chosen first-order oracles;
* `FirstOrderOracle.correctionStepsize` in `Definition_3_40`, the canonical owner-derived scalar
  `f_j(x) / ‖g_j(x)‖²` for a violated-constraint correction;
* `MultipleConstraintFirstOrderProblem.iterates` in `Algorithm_3_4`, the canonical owner-level
  recursion for the whole-space method `(3.2.24)`;
* `FunctionalConstraintSubgradientMethod.iterates` in `Algorithm_3_3` and
  `ProjectedMultipleConstraintFirstOrderProblem.switchingIterates` in `Algorithm_3_4`, the nearby
  chapter pattern that keeps the recursive iterate family public instead of packaging it behind a
  second owner;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the Chapter 1
  owner for intrinsic minimum values over a sampled feasible set.

Best owner abstraction:
* source-facing: the recursive iterate family
  `problem.iterates ε x₀ selectedConstraintAt : ℕ → E` for method `(3.2.24)`;
* core/canonical: `MultipleConstraintFirstOrderProblem`,
  `FirstOrderOracle.correctionStepsize`, `NormedSpace.normalize`, and
  `SetConstrainedMinimizationProblem.optimalValue`;
* bridge/view: the branch-validity predicate for the chosen indices, the admissible index family
  `𝒜(N)`, the sampled iterate set `𝓕_A(N)`, and the sampled optimal value.

Primitive data:
* the multi-constraint first-order owner `problem`;
* the initial point `x₀`;
* the tolerance `ε`;
* the stepwise branch choices `selectedConstraintAt : ℕ → Option (Fin m)`.

Derived API:
* the recursive iterate family `x₀, x₁, ...`;
* the admissibility predicate `∀ j, f_j(x) ≤ ε`;
* the validity condition saying `none` occurs exactly on admissible iterates and `some j`
  records a violated constraint;
* the textbook admissible family `𝒜(N)`, sampled iterate set `𝓕_A(N)`, and sampled minimum.

This refinement removes the public packaged-method owner entirely. The owner-derived whole-space
step and iterate recursion now live in `Algorithm_3_4`, and the theorem surface here works
directly with that canonical run data to derive the branch equations, `𝒜(N)`, `𝓕_A(N)`, and the
sampled minimum. -/

namespace MultipleConstraintFirstOrderProblem

/-- The admissibility predicate at a point: all constraint inequalities satisfy `f_j(x) ≤ ε`. -/
def IsAdmissible
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x : E) : Prop :=
  ∀ j : Fin m, problem.constraints j x ≤ ε

/-- The chosen branch sequence is valid for method `(3.2.24)` exactly when `none` occurs on
admissible iterates and `some j` records a violated constraint. -/
def IsValidSelection
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) : Prop :=
  ∀ k,
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k)

section Iterates

variable {problem : MultipleConstraintFirstOrderProblem E m}
variable {ε : ℝ} {x0 : E} {selectedConstraintAt : ℕ → Option (Fin m)}

/-- The chosen branch sequence is valid along the recursively generated run. -/
theorem selectedConstraintAt_spec
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    match selectedConstraintAt k with
    | none => problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)
    | some j => ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) :=
  hvalid k

/-- The branch choice is `none` exactly on admissible iterates. -/
theorem selectedConstraintAt_eq_none_iff
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (k : ℕ) :
    selectedConstraintAt k = none ↔
      problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k) := by
  constructor
  · intro hk
    simpa [hk] using problem.selectedConstraintAt_spec hvalid k
  · intro hk
    cases hsel : selectedConstraintAt k with
    | none =>
        rfl
    | some j =>
        have hviol : ε < problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) := by
          simpa [hsel] using problem.selectedConstraintAt_spec hvalid k
        exact (not_lt_of_ge (hk j) hviol).elim

/-- The zeroth iterate is the prescribed initial point `x₀`. -/
@[simp] theorem iterates_zero :
    problem.iterates ε x0 selectedConstraintAt 0 = x0 := by
  rfl

/-- Each successor iterate is obtained from the previous one by the branch rule of
method `(3.2.24)`. -/
@[simp] theorem iterates_succ (k : ℕ) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.step ε (problem.iterates ε x0 selectedConstraintAt k)
        (selectedConstraintAt k) := by
  rfl

/-- At admissible iterates, the successor iterate is the objective step. -/
theorem iterates_succ_eq_objective
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) {k : ℕ}
    (hk : problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.objectiveStep ε (problem.iterates ε x0 selectedConstraintAt k) := by
  have hsel : selectedConstraintAt k = none :=
    (problem.selectedConstraintAt_eq_none_iff hvalid k).2 hk
  rw [iterates_succ, hsel]
  rfl

/-- If the run selects the violated constraint `j` at time `k`, the successor iterate is the
corresponding correction step. -/
theorem iterates_succ_eq_constraint
    {k : ℕ} {j : Fin m} (hsel : selectedConstraintAt k = some j) :
    problem.iterates ε x0 selectedConstraintAt (k + 1) =
      problem.constraintStep j (problem.iterates ε x0 selectedConstraintAt k) := by
  rw [iterates_succ, hsel]
  rfl

/-- The textbook index set `𝒜(N)` of admissible iterates among `x₀, ..., x_N`. -/
def admissibleIndices
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Finset (Fin (N + 1)) :=
  Finset.univ.filter fun k ↦
    problem.IsAdmissible ε (problem.iterates ε x0 selectedConstraintAt k)

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝒜[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIndices problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

open scoped MultipleConstraintFirstOrderProblemNotation

/-- Membership in `𝒜(N)` is equivalent to satisfying all constraint inequalities
`f_j(x_k) ≤ ε`. -/
@[simp] theorem mem_admissibleIndices_iff
    (N : ℕ) {k : Fin (N + 1)} :
    k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ↔
      ∀ j, problem.constraints j (problem.iterates ε x0 selectedConstraintAt k) ≤ ε := by
  simp [admissibleIndices, IsAdmissible]

/-- The textbook set `𝓕_A(N)` of iterates whose indices belong to `𝒜(N)`. -/
def admissibleIterateSet
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) :
    Set E :=
  Set.range fun k : {i : Fin (N + 1) // i ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N)} ↦
    problem.iterates ε x0 selectedConstraintAt k.1

namespace MultipleConstraintFirstOrderProblemNotation

scoped notation:max "𝓕_A[" problem:arg ", " ε:arg ", " x0:arg ", " selected:arg "](" N:arg ")" =>
  admissibleIterateSet problem ε x0 selected N

end MultipleConstraintFirstOrderProblemNotation

/-- The sampled minimum on `𝓕_A(N)`, expressed through the Chapter 1 constrained optimal-value
owner. -/
def sampledOptimalValue
    (problem : MultipleConstraintFirstOrderProblem E m) (ε : ℝ) (x0 : E)
    (selectedConstraintAt : ℕ → Option (Fin m)) (N : ℕ) : EReal :=
  (SetConstrainedMinimizationProblem.mk
      (𝓕_A[problem, ε, x0, selectedConstraintAt](N))
      problem.objective).optimalValue

/-- Membership in `𝓕_A(N)` means that the point is one of the iterates `x_k` with
`k ∈ 𝒜(N)`. -/
theorem mem_admissibleIterateSet_iff
    (N : ℕ) {x : E} :
    x ∈ 𝓕_A[problem, ε, x0, selectedConstraintAt](N) ↔
      ∃ k : Fin (N + 1),
        k ∈ 𝒜[problem, ε, x0, selectedConstraintAt](N) ∧
          problem.iterates ε x0 selectedConstraintAt k = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- The admissible iterate set is nonempty exactly when the admissible index family `𝒜(N)` is
nonempty. -/
theorem admissibleIterateSet_nonempty_iff
    (N : ℕ) :
    𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ↔
      (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty := by
  constructor
  · intro hSet
    rcases Set.range_nonempty_iff_nonempty.mp
        (Set.nonempty_iff_ne_empty.mpr hSet) with ⟨k⟩
    exact ⟨k.1, k.2⟩
  · rintro ⟨k, hk⟩ hEmpty
    have hx : problem.iterates ε x0 selectedConstraintAt k ∈
        𝓕_A[problem, ε, x0, selectedConstraintAt](N) := by
      exact Set.mem_range.mpr ⟨⟨k, hk⟩, rfl⟩
    rw [hEmpty] at hx
    exact hx

-- Proof sketch: argue by contradiction. If every iterate up to time `N` either violates a
-- constraint by more than `ε` or has objective gap larger than `ε`, then each step of method
-- `(3.2.24)` decreases `‖x_k - x*‖²` by at least `ε² / M²`. Summing the drop over
-- `k = 0, ..., N` contradicts the bound `N ≥ (M² / ε²) ‖x₀ - x*‖²`, so some admissible iterate
-- must satisfy the desired objective estimate, which then bounds the sampled minimum.
/-- Theorem 3.2.3: let `x_k = problem.iterates ε x₀ selectedConstraintAt k` be the recursively
generated run of method `(3.2.24)`. If the branch choices are valid, if the objective `f` and
the constraint functions `f_j`, `j = 1, ..., m`, are `M`-Lipschitz on the ball
`B₂(x*, ‖x₀ - x*‖)`, if `x*` is optimal for the constrained feasible set
`{x | ∀ j, f_j(x) ≤ 0}`, and if the number of steps satisfies
`N ≥ (M² / ε²) ‖x₀ - x*‖²`, then the admissible index family `𝒜(N)` is nonempty, hence
`𝓕_A(N)` is nonempty, and the sampled minimum on `𝓕_A(N)` satisfies
`f_N^* ≤ f(x*) + ε`. -/
theorem admissibleIterateSet_nonempty_and_sampledMinimum_le_optimal_add_eps
    (hvalid : problem.IsValidSelection ε x0 selectedConstraintAt) (xStar : E) (M : NNReal)
    (hε : 0 < ε)
    (hf_lipschitz :
      LipschitzOnWith M problem.objective
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hconstraints_lipschitz :
      ∀ j, LipschitzOnWith M (problem.constraints j)
        (Metric.closedBall xStar ‖x0 - xStar‖))
    (hxStar_optimal :
      IsMinOn problem.objective {x | ∀ j, problem.constraints j x ≤ 0} xStar)
    (N : ℕ)
    (hN :
      (((M : ℝ) ^ (2 : ℕ)) / (ε ^ (2 : ℕ))) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
        (N : ℝ)) :
    (𝒜[problem, ε, x0, selectedConstraintAt](N)).Nonempty ∧
      𝓕_A[problem, ε, x0, selectedConstraintAt](N) ≠ ∅ ∧
        problem.sampledOptimalValue ε x0 selectedConstraintAt N ≤
          problem.objective xStar + ε := sorry

end Iterates

end MultipleConstraintFirstOrderProblem

end

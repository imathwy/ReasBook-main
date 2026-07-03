import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_1_6 (from Chap01) -/
open scoped BigOperators

universe u

variable {m : ℕ} {X : Type u}
local notation "R" => EuclideanSpace ℝ (Fin m)

/- Example 1.1.6 lies in the constrained-optimization / least-squares reformulation domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` and
  `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem` in
  `Chap01/Definition_1_3_3`, the Chapter 1 owner for an unconstrained objective on the feasible
  subtype `Q` and its zero-constraint bridge;
* `vectorMap` in `Chap03/Lemma_3_1_16`, the project owner for a finite scalar family packaged as
  an `ℝ^m`-valued residual map;
* `euclideanNormSq_isMeritFunction` in `Chap04/Definition_4_4_1`, the merit-function theorem for
  the canonical squared Euclidean residual scalarization.

Best owner abstraction:
* `SetConstrainedMinimizationProblem Q` for the least-squares reformulation on the structural set
  `Q`;
* `vectorMap` and ordinary composition for packaging the scalar equation family into the
  canonical residual map and merit scalarization.

Primitive data:
* the structural set `Q`;
* the scalar equation family `f_j(x) = a_j`.

Derived API:
* `equationSystemResidual`, the residual vector of the original equality system;
* `equationSystemOptimizationProblem`, the unconstrained squared-residual minimization problem on
  the subtype `Q`;
* the companion sum-of-squares and zero-set lemmas for that owner object.

Source/core/bridge triage:
* source-facing: the least-squares reformulation of `f_j(x) = a_j` on `Q`;
* core/canonical: `SetConstrainedMinimizationProblem Q`;
* bridge/view: `equationSystemResidual`, the specialization of `vectorMap` to the
  coordinates `f_j(x) - a_j`.

The source states `Q ⊆ ℝⁿ`, but this example's reformulation uses no linear, topological, or
metric structure on the ambient space. The faithful primitive data are only the structural set
`Q` and the equation family on its subtype, so the public API is refined to an arbitrary ambient
type `X`.
-/

/-- The residual map of the system `f_j(x) = a_j` on the structural set `Q`. -/
noncomputable abbrev equationSystemResidual
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ) :
    Q → R :=
  vectorMap (fun j x ↦ f j x - a j)

@[simp] theorem equationSystemResidual_apply
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q)
    (j : Fin m) :
    equationSystemResidual f a x j = f j x - a j := by
  simp [equationSystemResidual]

/-- Example 1.1.6: A system of equations `f_j(x) = a_j` on a set `Q ⊆ ℝⁿ` can be converted into
the minimization of the canonical squared residual norm on `Q`; for the coordinate residual map
attached to `f_j(x) = a_j`, this is exactly the textbook sum of squared residuals. The set `Q`
may encode any additional constraints imposed on `x`. -/
noncomputable def equationSystemOptimizationProblem
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ) : SetConstrainedMinimizationProblem Q where
  feasibleSet := Set.univ
  objective := (fun u : R ↦ ‖u‖ ^ (2 : ℕ)) ∘ equationSystemResidual f a

/-- For the coordinate residual map `x ↦ (f_j(x) - a_j)_j`, the squared residual norm is the
textbook sum of squared residuals. -/
theorem equationSystemOptimizationProblem_objective_eq_sum_sq
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemOptimizationProblem f a x =
      ∑ j : Fin m, (f j x - a j) ^ 2 := by
  simpa [equationSystemOptimizationProblem, equationSystemResidual, Function.comp_apply] using
    EuclideanSpace.real_norm_sq_eq (equationSystemResidual f a x)

/-- The coordinate residual map vanishes exactly at solutions of the original system. -/
theorem equationSystemResidual_eq_zero_iff
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemResidual f a x = 0 ↔ ∀ j : Fin m, f j x = a j := by
  constructor
  · intro h j
    exact sub_eq_zero.mp <| by
      simpa using congrArg (fun r : R ↦ r j) h
  · intro hx
    ext j
    rw [equationSystemResidual_apply]
    exact sub_eq_zero.mpr (hx j)

/-- The residual objective for the system `f_j(x) = a_j` vanishes exactly at solutions on `Q`. -/
theorem equationSystemOptimizationProblem_objective_eq_zero_iff
    {Q : Set X}
    (f : Fin m → Q → ℝ)
    (a : Fin m → ℝ)
    (x : Q) :
    equationSystemOptimizationProblem f a x = 0 ↔
      ∀ j : Fin m, f j x = a j := by
  have hφ : IsMeritFunction (fun u : R ↦ ‖u‖ ^ (2 : ℕ)) :=
    euclideanNormSq_isMeritFunction m
  simpa [equationSystemOptimizationProblem, equationSystemResidual, Function.comp_apply] using
    ((hφ.eq_zero_iff (equationSystemResidual f a x)).trans
      (equationSystemResidual_eq_zero_iff f a x))

/-
Example 1.1.6 is formalized by `equationSystemOptimizationProblem` together with
`equationSystemOptimizationProblem_objective_eq_zero_iff`.
-/

/-! ### Example_1_1_7 (from Chap01) -/
variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Primary domain: constrained optimization with a transcendental equality encoding of integrality.

Source/core/bridge triage for Example 1.1.7:
* source-facing: the bounded characteristic problem together with the adjoined equalities
  `sin (π x_i) = 0`
* core/canonical: `GeneralMinimizationProblem` and its owner predicate
  `problem.IsFeasible`
* bridge/view: `boundedCharacteristicProblem` and
  `boundedCharacteristicProblem_isFeasible_iff`, which package the lower/upper characteristic
  bounds into the chapter's owner object and unpack feasibility back to the coordinate conditions

Relevant declarations sampled before refining:
* the owner feasible predicate `problem.IsFeasible` in `Chap01/Definition_1_1_3.lean`
* `boundedCharacteristicProblem` in `Chap01/Example_1_1_5.lean`
* `boundedCharacteristicProblem_isFeasible_iff` in `Chap01/Example_1_1_5.lean`
* `Real.sin_eq_zero_iff` in mathlib, the ambient zero-set description behind the integrality
  encoding

Best owner abstraction:
* `GeneralMinimizationProblem n (m + m + n)`, built by adjoining the new equality constraints to
  the existing source-facing bounded problem from Example 1.1.5

Primitive data:
* the structural set `Q`, objective, characteristic family, and lower/upper bounds
* the coordinate equalities `sin (π x_i) = 0`

Derived API:
* `transcendentalIntegerOptimizationProblem`, the resulting owner object
* `isFeasible_transcendentalIntegerOptimizationProblem_iff`, the source-facing feasibility view
  obtained by combining the owner-level decomposition with the upstream bounded-characteristic
  bridge and the canonical mathlib theorem `Real.sin_eq_zero_iff` -/

/-- Example 1.1.7: Integer constraints can be encoded by adjoining the transcendental equalities
`sin (π x_i) = 0` to the bounded optimization problem on `Q`. -/
noncomputable def transcendentalIntegerOptimizationProblem
    (Q : Set E)
    (objective : Q → ℝ)
    (characteristics : Fin m → Q → ℝ)
    (lowerBounds upperBounds : Fin m → ℝ) :
    GeneralMinimizationProblem n (m + m + n) :=
  let boundedProblem :=
    boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  { boundedProblem with
    constraints :=
      Fin.append boundedProblem.constraints (fun i x ↦ Real.sin (Real.pi * (x.1 i)))
    senses := Fin.append boundedProblem.senses (fun _ ↦ .eq) }

/-- Feasibility for the transcendental integer optimization problem is exactly the conjunction of
the original lower and upper bounds with coordinatewise integrality of the decision variables. -/
theorem isFeasible_transcendentalIntegerOptimizationProblem_iff
    {Q : Set E}
    {objective : Q → ℝ}
    {characteristics : Fin m → Q → ℝ}
    {lowerBounds upperBounds : Fin m → ℝ}
    {x : Q} :
    (transcendentalIntegerOptimizationProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      (∀ j : Fin m, lowerBounds j ≤ characteristics j x ∧ characteristics j x ≤ upperBounds j) ∧
        ∀ i : Fin n, ∃ z : ℤ, x.1 i = z := by
  let boundedProblem :=
    boundedCharacteristicProblem Q objective characteristics lowerBounds upperBounds
  have hproblem :
    (transcendentalIntegerOptimizationProblem Q objective characteristics lowerBounds
      upperBounds).IsFeasible x ↔
      boundedProblem.IsFeasible x ∧
        ∀ i : Fin n, Real.sin (Real.pi * (x.1 i)) = 0 := by
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro j
        simpa [transcendentalIntegerOptimizationProblem, boundedProblem, Fin.append_left] using
          hx (j.castAdd n)
      · intro i
        simpa [ConstraintSense.Holds, transcendentalIntegerOptimizationProblem, boundedProblem,
          Fin.append_right] using hx (i.natAdd (m + m))
    · rintro ⟨hbounded, hsin⟩ i
      cases i using Fin.addCases with
      | left j =>
          simpa [transcendentalIntegerOptimizationProblem, boundedProblem, Fin.append_left] using
            hbounded j
      | right j =>
          simpa [ConstraintSense.Holds, transcendentalIntegerOptimizationProblem, boundedProblem,
            Fin.append_right] using hsin j
  constructor
  · intro hx
    rcases hproblem.mp hx with ⟨hbounded, hsin⟩
    refine ⟨?_, ?_⟩
    · exact (boundedCharacteristicProblem_isFeasible_iff.mp hbounded)
    · intro i
      rcases Real.sin_eq_zero_iff.mp (hsin i) with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hz' : x.1 i * Real.pi = (z : ℝ) * Real.pi := by
        simpa [mul_comm] using hz.symm
      exact (mul_left_inj' Real.pi_ne_zero).mp hz'
  · rintro ⟨hbounded, hinteger⟩
    refine hproblem.mpr ⟨boundedCharacteristicProblem_isFeasible_iff.mpr hbounded, ?_⟩
    intro i
    rcases hinteger i with ⟨z, hz⟩
    rw [hz]
    exact Real.sin_eq_zero_iff.mpr ⟨z, by simp [mul_comm]⟩

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDualMap)
open Matrix
open WithLp (ofLp toLp)

section

variable {m n p : ℕ}

local notation "PerturbationSpace" =>
  EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin p)

/- Theorem 3.24 is `source-facing` in the affine-constrained perturbation/duality API. Its
`core/canonical` owners are already the earlier chapter declarations `effective_domain`,
`IsProperExtendedRealFunction`, `is_convex_function`, the continuous-dual bridge
`strongDualSubdifferential`, and the perturbation owner `value_function` from `Lemma_3_4`. This
file therefore keeps only the source-facing affine primal/dual objects and rewrites the theorem
statements directly in terms of those owners instead of maintaining parallel local copies. -/
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall strongDualSubdifferential
recall value_function_feasible_set
recall value_function

/-- The feasible set of the primal problem consists of the points of `X` satisfying the
coordinatewise inequality constraints `g x ≤ 0` and the affine equality constraint `A x + b = 0`.
-/
def primalFeasibleSet
    (X : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    Set (Fin n → ℝ) :=
  {x | x ∈ X ∧ (∀ i : Fin m, g x i ≤ 0) ∧ A *ᵥ x + b = 0}

/-- Membership in the primal feasible set is exactly the textbook conjunction of set membership,
coordinatewise inequality feasibility, and affine equality feasibility. -/
@[simp] theorem mem_primalFeasibleSet
    (X : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (x : Fin n → ℝ) :
    x ∈ primalFeasibleSet X g A b ↔
      x ∈ X ∧ (∀ i : Fin m, g x i ≤ 0) ∧ A *ᵥ x + b = 0 :=
  Iff.rfl

/-- The source-facing primal feasible set is the zero-perturbation slice of the owner feasible-set
construction after transporting the primal variables into Euclidean space. -/
@[simp] theorem toLp_mem_value_function_feasible_set_zero_iff
    (X : Set (Fin n → ℝ))
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (x : Fin n → ℝ) :
    toLp 2 x ∈
        value_function_feasible_set
          (toLp 2 '' X)
          (fun i x ↦ (g (ofLp x) i : EReal))
          A.toEuclideanLin
          (toLp 2 b)
          0
          0 ↔
      x ∈ primalFeasibleSet X g A b := by
  constructor
  · intro hx
    have hx' : x ∈ X ∧ (∀ i : Fin m, g x i ≤ 0) ∧ toLp 2 (A *ᵥ x) + toLp 2 b = 0 := by
      simpa [Matrix.toLpLin_toLp] using hx
    rcases hx' with ⟨hxX, hxg, hEq⟩
    have : toLp 2 (A *ᵥ x + b) = 0 := by
      simpa using hEq
    exact (mem_primalFeasibleSet X g A b x).2
      ⟨hxX, hxg, by simpa using congrArg ofLp this⟩
  · intro hx
    rcases (mem_primalFeasibleSet X g A b x).1 hx with ⟨hxX, hxg, hEq⟩
    have hEq' : toLp 2 (A *ᵥ x + b) = 0 := by
      simpa using congrArg (toLp 2) hEq
    have hx' : x ∈ X ∧ (∀ i : Fin m, g x i ≤ 0) ∧ toLp 2 (A *ᵥ x) + toLp 2 b = 0 := by
      exact ⟨hxX, hxg, by simpa using hEq'⟩
    simpa [Matrix.toLpLin_toLp] using hx'

/-- The Lagrangian dual objective is the infimum over `X` of the Lagrangian with inequality
multiplier `y` and equality multiplier `z`. -/
def lagrangianDualObjective
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (y : Fin m → ℝ) (z : Fin p → ℝ) : EReal :=
  sInf ((fun x : Fin n → ℝ ↦
    ((f x + dotProduct y (g x) + dotProduct z (A *ᵥ x + b) : ℝ) : EReal)) '' X)

/-- The dual objective values attained by nonnegative inequality multipliers. -/
def dualObjectiveValues
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    Set EReal :=
  {q | ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ,
      (∀ i : Fin m, 0 ≤ y i) ∧ lagrangianDualObjective X f g A b y z = q}

/-- A real number is the primal optimal value when it is the greatest lower bound of the feasible
objective values. -/
def IsPrimalOptimalValue
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (fOpt : ℝ) : Prop :=
  IsGLB (((fun x : Fin n → ℝ ↦ ((f x : ℝ) : EReal)) '' primalFeasibleSet X g A b)) (fOpt : EReal)

/-- A pair `(y, z)` is a dual optimal solution with optimal value `qOpt` when `y` is
coordinatewise nonnegative, the dual objective at `(y, z)` equals `qOpt`, and `qOpt` is the least
upper bound of all attained dual objective values. -/
def IsDualOptimalSolution
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (qOpt : ℝ) (y : Fin m → ℝ) (z : Fin p → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ y i) ∧
    lagrangianDualObjective X f g A b y z = (qOpt : EReal) ∧
    IsLUB (dualObjectiveValues X f g A b) (qOpt : EReal)

/-- The perturbation value function for the affine-constrained problem. This is the
`bridge/view` layer: it keeps the source-facing data `X`, `f`, `g`, `A`, and `b`, while the owner
object is the chapter declaration `value_function` on the Euclidean perturbation space
`ℝ^m × ℝ^p`. -/
def valueFunction
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    PerturbationSpace → EReal :=
  value_function
    (toLp 2 '' X)
    (fun x : EuclideanSpace ℝ (Fin n) ↦ (f (ofLp x) : EReal))
    (fun i x ↦ (g (ofLp x) i : EReal))
    A.toEuclideanLin
    (toLp 2 b)

-- Proof sketch: dual attainment at the primal optimal value gives a multiplier pair whose affine
-- lower bound shows that the owner perturbation value function never takes the value `⊥`, while
-- the finite primal optimal value gives a finite value at `(0,0)`, hence a nonempty effective
-- domain.
/-- Theorem 3.24 (1): if the finite primal optimal value is also attained by a dual optimal
solution, then the perturbation value function is proper. -/
theorem valueFunction_isProper_of_primalOptimalValue_and_dualOptimalSolution_exists
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (fOpt : ℝ)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt)
    (hDualExists :
      ∃ y : Fin m → ℝ, ∃ z : Fin p → ℝ, IsDualOptimalSolution X f g A b fOpt y z) :
    IsProperExtendedRealFunction (valueFunction X f g A b) := sorry

-- Proof sketch: convexity follows directly from the owner theorem `value_function_is_convex`
-- applied to the Euclidean bridge of the primal data. This clause of Theorem 3.24 depends only on
-- convexity of the primal data; the strong-duality hypotheses used in the properness and
-- subdifferential clauses are not needed here.
/-- Theorem 3.24 (2): if the primal data are convex, then the perturbation value function is
convex. -/
theorem valueFunction_is_convex_of_convex_primal_problem
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (hX : Convex ℝ X)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ i : Fin m, ConvexOn ℝ Set.univ (fun x ↦ g x i)) :
    is_convex_function (valueFunction X f g A b) := sorry

-- Proof sketch: if `(y,z)` is dual optimal, the defining lower bound for the dual objective gives
-- the global affine support inequality for the owner perturbation value function at `(0,0)` with
-- supporting functional represented by `-(y,z)`. Conversely, a continuous-dual subgradient
-- inequality at `(0,0)` forces `y ≥ 0` by testing the standard basis perturbations and identifies
-- the dual objective value with the primal optimal value `fOpt`, so the subgradient condition
-- itself yields dual optimality without a separate strong-duality binder.
/-- Theorem 3.24 (3): a multiplier pair `(y,z)` is a dual optimal solution exactly when the
negated pair represents a subgradient of the value function at the origin. -/
theorem isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero
    (X : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ)
    (g : (Fin n → ℝ) → Fin m → ℝ)
    (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ)
    (fOpt : ℝ)
    (y : Fin m → ℝ) (z : Fin p → ℝ)
    (hPrimal : IsPrimalOptimalValue X f g A b fOpt) :
    IsDualOptimalSolution X f g A b fOpt y z ↔
      ContinuousLinearMap.coprod
          (toDualMap ℝ (EuclideanSpace ℝ (Fin m)) (toLp 2 (-y)))
          (toDualMap ℝ (EuclideanSpace ℝ (Fin p)) (toLp 2 (-z))) ∈
        strongDualSubdifferential (valueFunction X f g A b)
          (0 : PerturbationSpace) := sorry

end

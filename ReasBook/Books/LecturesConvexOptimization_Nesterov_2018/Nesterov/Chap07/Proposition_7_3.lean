import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.LinearEqualityFeasibleSet
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators SupportFunction

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ₋₁" => EuclideanSpace ℝ (Fin (n - 1))

/- Proposition 7.3 lies in the chapter's homogeneous linear-programming / support-envelope
duality domain.

Sampled owner-style declarations:
* `supportFunction` and `supportFunction_apply` in `Chap03/Definition_3_9`, the chapter owner for
  suprema of linear functionals over sets;
* `linearEqualityFeasibleSet` and `mem_linearEqualityFeasibleSet_iff` in
  `Chap03/LinearEqualityFeasibleSet`, the chapter owner for feasible regions cut out by
  `u ∈ Q` and a linear equality `A u = b`;
* `zeroOneBox` in `Chap01/Definition_1_3_1`, the project's explicit-dimension box-owner pattern;
* `linearOptimizationProblemWithNonnegativityConstraints` in `Chap05/Definition_5_4_3_1`, a
  nearby project file that specializes equality-feasible-set owners to linear programs.

Best owner abstraction:
* source-facing: the Chapter 7 homogeneous linear-programming value `f*` and dual profile `φ₁`;
* core/canonical: the Chapter 3 support-function owner applied to `coordinatewiseUnitBox m`,
  together with the Chapter 3 equality-feasible-set owner
  `linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0`;
* bridge/view: the coordinatewise box-membership lemma and the explicit sum-of-absolute-values
  formula for `φ₁`.

Primitive data:
* the source-facing box `coordinatewiseUnitBox m`;
* the matrix `hatA` and vector `c`.

Derived API:
* the feasible set and optimal value of the homogeneous linear program;
* the support-function/supremum expansion of `φ₁`;
* the explicit `∑ |(hatA.mulVec y)ᵢ + cᵢ|` formula and the least-value theorem.

This refinement keeps the Chapter 7 source-facing owners, but gives the box its explicit dimension
parameter and presents the feasible region as a thin specialization of the canonical
`linearEqualityFeasibleSet` owner instead of rebuilding the conjunction by hand.
-/

/-- The coordinatewise box `[-1, 1]^m` in `ℝ^m`. -/
abbrev coordinatewiseUnitBox (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {u | ∀ i, |u i| ≤ 1}

/-- Membership in `coordinatewiseUnitBox` means satisfying `|uᵢ| ≤ 1` in every coordinate. -/
@[simp]
theorem mem_coordinatewiseUnitBox_iff {u : Eₘ} :
    u ∈ coordinatewiseUnitBox m ↔ ∀ i, |u i| ≤ 1 :=
  Iff.rfl

/-- The function `φ₁(y)` is the Chapter 3 support function of the coordinatewise box `[-1, 1]^m`,
evaluated at the affine coefficient vector `\hat A y + c`. -/
def homogeneousLinearProgrammingPhi1
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : Eₙ₋₁ → ℝ :=
  fun y ↦ (ξ[coordinatewiseUnitBox m] (hatA.toEuclideanLin y + c)).toReal

/-- Evaluating `homogeneousLinearProgrammingPhi1 hatA c` at `y` recovers its defining supremum
of the linear functional `u ↦ ⟪\hat A y + c, u⟫` over `coordinatewiseUnitBox`. -/
-- Proof sketch: expand the Chapter 3 support-function owner by `supportFunction_apply`.
theorem homogeneousLinearProgrammingPhi1_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      sSup
        ((fun u : Eₘ ↦ inner ℝ (hatA.toEuclideanLin y + c) u) '' coordinatewiseUnitBox m) := sorry

/-- The box-constrained feasible set of the dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
abbrev homogeneousLinearProgrammingFeasibleSet
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) : Set Eₘ :=
  linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin 0

/-- Membership in `homogeneousLinearProgrammingFeasibleSet hatA` means satisfying the linear
constraint `\hat Aᵀ u = 0` together with the coordinatewise bounds `|uᵢ| ≤ 1`. -/
@[simp]
theorem mem_homogeneousLinearProgrammingFeasibleSet_iff
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (u : Eₘ) :
    u ∈ homogeneousLinearProgrammingFeasibleSet hatA ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m := by
  change
    u ∈ linearEqualityFeasibleSet (coordinatewiseUnitBox m) hatA.transpose.toEuclideanLin
      (0 : Eₙ₋₁) ↔
      hatA.transpose.mulVec u = 0 ∧ u ∈ coordinatewiseUnitBox m
  rw [mem_linearEqualityFeasibleSet_iff]
  constructor
  · rintro ⟨hu, hA⟩
    refine ⟨?_, hu⟩
    ext i
    have hi : (hatA.transpose.toEuclideanLin u) i = 0 := by
      simpa using congrArg (fun v : Eₙ₋₁ ↦ v i) hA
    simpa using hi
  · rintro ⟨hA, hu⟩
    refine ⟨hu, ?_⟩
    ext i
    have hi : (hatA.transpose.mulVec u) i = 0 := by
      simpa using congrArg (fun v ↦ v i) hA
    simpa using hi

/-- The optimal value `f*` of the box-constrained dual linear program
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. -/
def homogeneousLinearProgrammingOptimalValue
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) : ℝ :=
  sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA)

/-- Expanding `homogeneousLinearProgrammingOptimalValue hatA c` gives the defining supremum of
the linear functional `u ↦ ⟪c, u⟫` over the feasible set. -/
-- Proof sketch: unfold `homogeneousLinearProgrammingOptimalValue`.
theorem homogeneousLinearProgrammingOptimalValue_eq_sSup
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    homogeneousLinearProgrammingOptimalValue hatA c =
      sSup ((fun u : Eₘ ↦ inner ℝ c u) '' homogeneousLinearProgrammingFeasibleSet hatA) := sorry

/-- The auxiliary function `φ₁` is the sum of the coordinatewise absolute values
`|(\hat A y + c)ᵢ|`. -/
-- Proof sketch: expand the support-function form of `φ₁`, observe that the maximization over
-- `coordinatewiseUnitBox m` decouples by coordinates, and maximize each scalar term
-- `(\hat A y + c)ᵢ uᵢ` over `|uᵢ| ≤ 1`.
theorem homogeneousLinearProgrammingPhi1_eq_sum_abs
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) (y : Eₙ₋₁) :
    homogeneousLinearProgrammingPhi1 hatA c y =
      ∑ i : Fin m, |(hatA.toEuclideanLin y + c) i| := sorry

/-- Proposition 7.3: the box-constrained dual optimal value
`max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}` is the minimum value attained by the function
`y ↦ homogeneousLinearProgrammingPhi1 hatA c y`. -/
-- Proof sketch: use linear-programming duality for the primal problem
-- `max {⟪c, u⟫ : \hat Aᵀ u = 0, |uᵢ| ≤ 1}`. The Lagrangian introduces a free multiplier `y` for
-- `\hat Aᵀ u = 0` and nonnegative multipliers for the box constraints, and eliminating the latter
-- yields the dual objective `homogeneousLinearProgrammingPhi1 hatA c y`. Strong duality then
-- identifies the primal optimal value with the least element of the value set of `φ₁`.
theorem homogeneousLinearProgrammingOptimalValue_isLeast_phi1_values
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ) :
    IsLeast (Set.range (homogeneousLinearProgrammingPhi1 hatA c))
      (homogeneousLinearProgrammingOptimalValue hatA c) := sorry

end

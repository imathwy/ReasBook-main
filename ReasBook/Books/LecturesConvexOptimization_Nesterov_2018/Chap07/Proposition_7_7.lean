import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_3_7
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_1_4_1
import LecturesConvexOptimization_Nesterov_2018.Chap03.Definition_3_4
import LecturesConvexOptimization_Nesterov_2018.Chap07.Proposition_7_9
import LecturesConvexOptimization_Nesterov_2018.Chap07.Proposition_7_12

open scoped BigOperators Matrix
open scoped WeightedGramMatrix

noncomputable section

variable {ι : Type} [Fintype ι]

section PsiStar

/-- The feasible strict-simplex weights for `ψ*` are exactly those whose weighted Gram matrix is
invertible, so the inverse-defined objective is evaluated only on its intended domain. -/
def psiStarFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (StdSimplex.Strict ℝ ι) :=
  {t | IsUnit (B[a](t.1.weights))}

/-- The source-facing objective `⟪B(t)⁻¹ f, f⟫` for `ψ*`, viewed as a function on the feasible
strict-simplex subtype. -/
def psiStarObjective {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    psiStarFeasibleSet a → ℝ :=
  fun ⟨t, _⟩ ↦ dotProduct ((B[a](t.1.weights))⁻¹ *ᵥ f) f

/-- The constrained minimization problem defining `ψ*` on the strict simplex of weights. -/
def psiStarProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (StdSimplex.Strict ℝ ι) where
  feasibleSet := psiStarFeasibleSet a
  objective :=
    let _ : DecidablePred (· ∈ psiStarFeasibleSet a) := Classical.decPred (· ∈ psiStarFeasibleSet a)
    fun t ↦ if ht : t ∈ psiStarFeasibleSet a then psiStarObjective a f ⟨t, ht⟩ else 0

/-- On a feasible strict-simplex point, the constrained-problem objective recovers the source-facing
`ψ*` objective. -/
@[simp] theorem psiStarProblem_apply_of_mem_feasibleSet {n : ℕ}
    (a : ι → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n))
    (t : StdSimplex.Strict ℝ ι) (ht : t ∈ psiStarFeasibleSet a) :
    psiStarProblem a f t = psiStarObjective a f ⟨t, ht⟩ := by
  classical
  simp [psiStarProblem, ht]

/-- The value `ψ*`, recorded as the canonical constrained optimal value on strict simplex
combinations. Using `EReal` keeps the infimum faithful even when the displayed real minimum is not
attained. -/
def psiStar {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  (psiStarProblem a f).optimalValue

end PsiStar

section MaxAbsoluteInner

variable [Nonempty ι]

/-- The unconstrained minimization problem whose negated optimal value is the quadratic max
formulation `maxₓ [2⟪f, x⟫ - maxᵢ ⟪aᵢ, x⟫²]`. -/
def maxQuadraticProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := Set.univ
  objective := fun x ↦
    -(2 * dotProduct f x -
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The quadratic max value, defined through the constrained-optimization owner so that
unbounded-above cases are represented faithfully in `EReal`. -/
def maxQuadraticValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxQuadraticProblem a f).optimalValue

/-- The feasible set for the ratio formulation consists of points where the denominator
`maxᵢ ⟪aᵢ, x⟫²` is strictly positive. -/
def maxRatioFeasibleSet {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 < (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2}

/-- The constrained minimization problem whose negated optimal value is the ratio max formulation.
The feasible set explicitly excludes the non-mathematical totalization of division by zero. -/
def maxRatioProblem {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) :
    SetConstrainedMinimizationProblem (EuclideanSpace ℝ (Fin n)) where
  feasibleSet := maxRatioFeasibleSet a
  objective := fun x ↦
    -((dotProduct f x) ^ 2 /
      (maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) ^ 2)

/-- The ratio max value, defined on the faithful feasible set `0 < maxᵢ ⟪aᵢ, x⟫²`. -/
def maxRatioValue {n : ℕ} (a : ι → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n)) : EReal :=
  -(maxRatioProblem a f).optimalValue

section SupportAbsMin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constrained minimization problem defining
`f* = min {maxᵢ |⟪aᵢ, x⟫| | ⟪f, x⟫ = 1}` on a real inner-product space. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` presentation. -/
def supportAbsMinProblem (a : ι → E) (f : E) :
    SetConstrainedMinimizationProblem E where
  feasibleSet := hyperplane f 1
  objective := maxTypeObjective (fun i x ↦ |inner ℝ (a i) x|)

/-- The constrained support minimum `f*`, recorded as the canonical optimal value of the affine
slice problem. Using `EReal` keeps empty or non-attained cases faithful. -/
def supportAbsMin (a : ι → E) (f : E) : EReal :=
  (supportAbsMinProblem a f).optimalValue

/-- The objective of the constrained support-minimum problem is the finite max
`x ↦ maxᵢ |⟪aᵢ, x⟫|`. -/
@[simp] theorem supportAbsMinProblem_apply (a : ι → E) (f x : E) :
    supportAbsMinProblem a f x =
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  rfl

/-- The feasible set of the constrained support-minimum problem is the affine hyperplane
`hyperplane f 1`. -/
@[simp] theorem supportAbsMinProblem_feasibleSet (a : ι → E) (f : E) :
    (supportAbsMinProblem a f).feasibleSet = hyperplane f 1 :=
  rfl

/-- Membership in the feasible set of the constrained support-minimum problem is exactly the
normalization constraint `⟪f, x⟫ = 1`. -/
@[simp] theorem mem_supportAbsMinProblem_feasibleSet_iff (a : ι → E) {f x : E} :
    x ∈ (supportAbsMinProblem a f).feasibleSet ↔ inner ℝ f x = 1 := by
  rfl

end SupportAbsMin

end MaxAbsoluteInner

section PsiStarTheorems

variable [Nonempty ι]

-- Proof sketch: for each interior simplex point `t`, identify `⟪B(t)⁻¹ f, f⟫` with the
-- optimum of the quadratic form `2⟪f, x⟫ - ⟪B(t)x, x⟫`, compare `⟪B(t)x, x⟫` with
-- `maxᵢ ⟪aᵢ, x⟫²`, and then optimize over `t` and `x`; the ratio identity follows by rescaling
-- along each nonzero ray.
/-- Proposition 7.7: if every interior simplex combination `B(t)` is invertible, then `ψ*`
coincides with both the quadratic max formulation and the ratio max formulation, provided the
index family is nonempty and the ambient space has positive dimension. -/
theorem psiStar_eq_max_formulations
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = maxQuadraticValue a f ∧ maxQuadraticValue a f = maxRatioValue a f :=
  sorry

-- Proof sketch: normalize vectors by the constraint `⟪f, x⟫ = 1` and rewrite the ratio
-- formulation in terms of the minimum of `maxᵢ |⟪aᵢ, x⟫|`.
/-- Under the same nondegeneracy hypotheses as Proposition 7.7, the constrained support minimum
`f*` satisfies the identity `ψ* = (f*)⁻²`. -/
theorem psiStar_eq_supportAbsMin_inv_sq
    (n : ℕ) (hn : 0 < n) (a : ι → EuclideanSpace ℝ (Fin (2 * n)))
    (f : EuclideanSpace ℝ (Fin (2 * n)))
    (hinv : ∀ t : StdSimplex.Strict ℝ ι, IsUnit (B[a](t.1.weights))) :
    psiStar a f = (supportAbsMin a f)⁻¹ ^ 2 :=
  sorry

end PsiStarTheorems

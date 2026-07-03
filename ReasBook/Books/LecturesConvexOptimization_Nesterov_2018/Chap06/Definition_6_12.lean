import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_11
import LecturesConvexOptimization_Nesterov_2018.Chap06.Definition_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped StandardSimplex

variable {n m : ℕ+}

/-- Definition 6.12: [Simplex saddle-point problem and primal--dual nonsmooth forms] a simplex
saddle-point problem is determined by a matrix `A : ℝⁿ → ℝᵐ` and linear terms `c ∈ ℝⁿ` and
`b ∈ ℝᵐ`; the feasible sets are the standard simplices `Δ_n` and `Δ_m`, and the associated
saddle, primal nonsmooth, and dual nonsmooth objectives are the canonical derived declarations
defined below. -/
structure SimplexSaddlePointProblem (n m : ℕ+) where
  /-- The matrix `A : ℝⁿ → ℝᵐ` defining the bilinear coupling term. -/
  matrix : Matrix (Fin (m : ℕ)) (Fin (n : ℕ)) ℝ
  /-- The primal linear term `c ∈ ℝⁿ`. -/
  primalLinearTerm : EuclideanSpace ℝ (Fin (n : ℕ))
  /-- The dual linear term `b ∈ ℝᵐ`. -/
  dualLinearTerm : EuclideanSpace ℝ (Fin (m : ℕ))

namespace SimplexSaddlePointProblem

local notation "Eₙ" => EuclideanSpace ℝ (Fin (n : ℕ))
local notation "Eₘ" => EuclideanSpace ℝ (Fin (m : ℕ))

/-- The canonical Euclidean linear map induced by the matrix `A`. -/
abbrev linearMap (problem : SimplexSaddlePointProblem n m) : Eₙ →ₗ[ℝ] Eₘ :=
  problem.matrix.toEuclideanLin

/-- The simplex saddle-point problem as a Chapter 6 structured objective model. -/
def toStructuredObjectiveModel (problem : SimplexSaddlePointProblem n m) :
    StructuredObjectiveModel Eₙ Eₘ where
  primalSet := (EuclideanSpace.equiv (Fin (n : ℕ)) ℝ) ⁻¹' Δ[n]
  primalSet_bounded := by
    sorry
  primalSet_closed := by
    sorry
  primalSet_convex := by
    sorry
  dualSet := (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ) ⁻¹' Δ[m]
  dualSet_bounded := by
    sorry
  dualSet_closed := by
    sorry
  dualSet_convex := by
    sorry
  smoothPart := InnerProductSpace.toDual ℝ Eₙ problem.primalLinearTerm
  dualPenalty := -InnerProductSpace.toDual ℝ Eₘ problem.dualLinearTerm
  linearMap :=
    (InnerProductSpace.toDual ℝ Eₘ).toContinuousLinearMap.comp
      problem.linearMap.toContinuousLinearMap
  smoothPart_continuous := by
    sorry
  smoothPart_convex := by
    sorry
  dualPenalty_continuous := by
    sorry
  dualPenalty_convex := by
    sorry

/-- The simplex saddle-function
`(x, u) ↦ ⟪A x, u⟫ + ⟪c, x⟫ + ⟪b, u⟫` on `Δ_n × Δ_m`. -/
def saddleFunction (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → Δ[m] → ℝ :=
  fun x u ↦
    dotProduct (problem.matrix.mulVec x.1) u.1 +
      dotProduct problem.primalLinearTerm x.1 +
      dotProduct problem.dualLinearTerm u.1

/-- A simplex saddle-point problem can be evaluated as its canonical saddle function on
`Δ_n × Δ_m`. -/
instance : CoeFun (SimplexSaddlePointProblem n m) (fun _ ↦
    Δ[n] → Δ[m] → ℝ) where
  coe problem := problem.saddleFunction

/-- The primal nonsmooth objective
`x ↦ ⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}` on `Δ_n`. -/
def primalObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[n] → ℝ :=
  fun x ↦
    dotProduct problem.primalLinearTerm x.1 +
      Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m : ℕ) ↦ dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j)

/-- The dual nonsmooth objective
`u ↦ ⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}` on `Δ_m`. -/
def dualObjective (problem : SimplexSaddlePointProblem n m) :
    Δ[m] → ℝ :=
  fun u ↦
    dotProduct problem.dualLinearTerm u.1 +
      Finset.univ.inf' Finset.univ_nonempty
        (fun i : Fin (n : ℕ) ↦
          dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i)

/-- Evaluating the simplex saddle function gives the bilinear term `⟪A x, u⟫` together with the
linear contributions `⟪c, x⟫` and `⟪b, u⟫`. -/
theorem saddleFunction_apply (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) (u : Δ[m]) :
    problem.saddleFunction x u =
      dotProduct (problem.matrix.mulVec x.1) u.1 +
        dotProduct problem.primalLinearTerm x.1 +
        dotProduct problem.dualLinearTerm u.1 :=
  rfl

/-- The primal nonsmooth objective equals the row-wise maximum
`⟪c, x⟫ + max_j {⟪a_j, x⟫ + b^(j)}`, where `a_j` is the `j`-th row of `A`. -/
theorem primalObjective_eq_max_rows (problem : SimplexSaddlePointProblem n m)
    (x : Δ[n]) :
    problem.primalObjective x =
      dotProduct problem.primalLinearTerm x.1 +
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m : ℕ) ↦
            dotProduct (problem.matrix j) x.1 + problem.dualLinearTerm j) :=
  rfl

/-- The dual nonsmooth objective equals the column-wise minimum
`⟪b, u⟫ + min_i {⟪\hat a_i, u⟫ + c^(i)}`, where `\hat a_i` is the `i`-th column of `A`. -/
theorem dualObjective_eq_min_columns (problem : SimplexSaddlePointProblem n m)
    (u : Δ[m]) :
    problem.dualObjective u =
      dotProduct problem.dualLinearTerm u.1 +
        Finset.univ.inf' Finset.univ_nonempty
          (fun i : Fin (n : ℕ) ↦
            dotProduct (problem.matrix.transpose i) u.1 + problem.primalLinearTerm i) :=
  rfl

end SimplexSaddlePointProblem

end

import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Definition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open Seminorm
open scoped BigOperators

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 7.12 lies in the chapter's dual-norm / pullback-seminorm domain.

Sampled owner-style declarations:
- project `Seminorm.dualNorm`
- project `Seminorm.dualNorm_apply`
- mathlib `Seminorm.comp`
- mathlib `normSeminorm`

Best owner abstraction:
- source-facing: `matrixInducedEuclideanSeminorm A`
- core/canonical: `Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin`
- bridge/view: `matrixInducedEuclideanSeminorm_apply`,
  `matrixInducedEuclideanSeminorm_isNorm`

Primitive data:
- a matrix `A : Matrix (Fin m) (Fin n) ℝ`

Derived API:
- pointwise evaluation as `x ↦ ‖A x‖`
- the `Seminorm.IsNorm` instance under injectivity of `A.toEuclideanLin`
- the dual norm formula under an explicit full-column-rank hypothesis, through the chapter owner
  `Seminorm.dualNorm`

Source/core/bridge triage:
- source-facing: the seminorm induced on `ℝⁿ` by the Euclidean norm on `ℝᵐ`
- core/canonical: pullback of `normSeminorm` along `A.toEuclideanLin`
- bridge/view: Gram-form and row-pairing formulas, plus the dual-norm formula

This refinement removes the duplicate local `vectorDualNorm` owner and exposes the matrix-induced
object at the canonical seminorm layer. The textbook function `x ↦ ‖A x‖` is now the evaluation
surface of that owner, while duality uses the existing project owner `Seminorm.dualNorm`.
-/

/-- Definition 7.12: the Euclidean seminorm on `ℝⁿ` induced by a matrix `A ∈ ℝ^(m × n)`, namely
the pullback of the Euclidean norm on `ℝᵐ` along `A.toEuclideanLin`. When `A` has full column
rank, the derived theorem `matrixInducedEuclideanSeminorm_isNorm` upgrades this seminorm to the
textbook norm `x ↦ ‖A x‖`. -/
def matrixInducedEuclideanSeminorm (A : Matrix (Fin m) (Fin n) ℝ) : Seminorm ℝ Eₙ :=
  Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin

/-- Evaluating the induced seminorm recovers the textbook formula `x ↦ ‖A x‖`. -/
theorem matrixInducedEuclideanSeminorm_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x = ‖A.toEuclideanLin x‖ :=
  rfl

/-- If `A` has full column rank, the induced Euclidean seminorm is a genuine norm. -/
theorem matrixInducedEuclideanSeminorm_isNorm
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) := by
  refine ⟨?_⟩
  intro x hx
  apply hA
  simpa using norm_eq_zero.mp (by
    simpa [matrixInducedEuclideanSeminorm_apply] using hx)

/-- If `A` has full column rank, then the induced Euclidean seminorm vanishes only at the
origin. -/
theorem matrixInducedEuclideanSeminorm_eq_zero_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) {x : Eₙ} :
    matrixInducedEuclideanSeminorm A x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact (matrixInducedEuclideanSeminorm_isNorm A hA).eq_zero_of_map_eq_zero hx
  · rintro rfl
    simp [matrixInducedEuclideanSeminorm_apply]

-- Proof sketch: unfold `matrixInducedEuclideanSeminorm`, rewrite `‖A x‖^2` as
-- `⟪A x, A x⟫`, and identify this with the Gram quadratic form for `Aᵀ A`.
/-- The induced Euclidean seminorm is the square root of the quadratic form associated to the
Gram matrix `G = Aᵀ A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_gram
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (inner ℝ ((A.transpose * A).toEuclideanLin x) x) := sorry

-- Proof sketch: expand the Euclidean norm of `A x` as the sum of the squares of its coordinates;
-- these coordinates are the pairings with the rows of `A`, equivalently the columns of `Aᵀ`.
/-- The induced Euclidean seminorm is the square root of the sum of the squared pairings with the
columns of `Aᵀ`, i.e. the rows of `A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_sum_row_pairings
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (∑ i : Fin m, (A i ⬝ᵥ x.ofLp) ^ (2 : ℕ)) := sorry

/-- If `A` has full column rank, then the dual norm of the induced Euclidean seminorm is
`g ↦ √⟪g, (Aᵀ A)⁻¹ g⟫`. -/
theorem dualNorm_matrixInducedEuclideanSeminorm_eq_sqrt_inverse_gram
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) (g : Eₙ) :
    by
      let _ : Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) :=
        matrixInducedEuclideanSeminorm_isNorm A hA
      exact (matrixInducedEuclideanSeminorm A).dualNorm g =
        Real.sqrt (inner ℝ g (((A.transpose * A)⁻¹).toEuclideanLin g)) := by
  sorry

end

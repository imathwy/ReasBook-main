import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.23 lies in the positive-definite matrix / induced-norm domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`
- `Matrix.toEuclideanLin` in mathlib
- `Matrix.toBilin'` in mathlib, for the coordinate-space matrix bilinear-form owner
- `Matrix.PosDef.toQuadraticForm'` in mathlib

Best owner abstraction:
- source-facing: the norm induced on `ℝⁿ` by a positive-definite matrix `G`
- core/canonical: the Chapter 4 bilinear-form owner
  `LinearMap.BilinForm.primalSeminorm B`
- bridge/view: the canonical Euclidean-space bilinear form induced by `Matrix.toEuclideanLin G`

Primitive data:
- a matrix `G : Matrix (Fin n) (Fin n) ℝ`
- its positive-definiteness proof `hG : G.PosDef`

Derived API:
- the source-facing seminorm owner `positiveDefMatrixNorm G hG`
- the source-facing notation `‖x‖[⟨G, hG⟩]`
- the canonical dual notation `‖s‖[⟨G, hG⟩,*]`
- the inverse-matrix formula `√⟪s, G⁻¹ s⟫`

Source/core/bridge triage:
- source-facing: Definition 7.23's matrix-induced norm
- core/canonical: `LinearMap.BilinForm.primalSeminorm` and `Seminorm.dualNorm`
- bridge/view: the bilinear form attached to `Matrix.toEuclideanLin`

This refinement removes the duplicate public matrix-to-bilinear-form owner and the notation-only
wrapper abbrevs. The source-facing matrix object remains a `Seminorm`, defined directly from the
canonical Euclidean linear operator attached to the matrix, and the dual norm is reused from the
Chapter 2 owner
`Seminorm.dualNorm`.
-/

private def matrixBilin (G : Matrix (Fin n) (Fin n) ℝ) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (Matrix.toEuclideanLin G).toContinuousLinearMap).toBilinForm

private theorem matrixToBilinForm_isSymm_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).IsSymm := by
  sorry

private theorem matrixToBilinForm_posDef_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).toQuadraticMap.PosDef := by
  sorry

/-- Definition 7.23 in owner form: a positive-definite matrix `G` induces the canonical seminorm
`x ↦ √⟪Gx, x⟫` on `ℝⁿ`. -/
def positiveDefMatrixNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    Seminorm ℝ E :=
  LinearMap.BilinForm.primalSeminorm
    (matrixBilin G)
    (matrixToBilinForm_posDef_of_posDef G hG)

instance positiveDefMatrixNorm_isNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (positiveDefMatrixNorm G hG).IsNorm :=
  by
    simpa [positiveDefMatrixNorm] using
      (LinearMap.BilinForm.primalSeminorm_isNorm
        (matrixBilin G)
        (matrixToBilinForm_posDef_of_posDef G hG))

namespace PositiveDefMatrixNorm

/- Lean notation for the primal norm induced by a positive-definite matrix. -/
scoped notation:max "‖" x "‖[" G "]" =>
  positiveDefMatrixNorm (Subtype.val G) (Subtype.property G) x

/- Lean notation for the dual norm induced by a positive-definite matrix. -/
scoped notation:max "‖" s "‖[" G ",*]" =>
  Seminorm.dualNorm (positiveDefMatrixNorm (Subtype.val G) (Subtype.property G)) s

end PositiveDefMatrixNorm

open scoped PositiveDefMatrixNorm

-- Proof sketch: `positiveDefMatrixNorm G hG` is the Chapter 4 bilinear-form-induced seminorm for
-- the Euclidean bilinear form associated with `Matrix.toEuclideanLin G`, whose pointwise formula
-- is exactly `√⟪Gx, x⟫`.
/-- Evaluating `positiveDefMatrixNorm G hG` recovers the textbook formula `√⟪Gx, x⟫`. -/
theorem positiveDefMatrixNorm_def
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x : E) :
    ‖x‖[G] =
      Real.sqrt (inner ℝ ((Matrix.toEuclideanLin G.1) x) x) := by
  sorry

-- Proof sketch: the dual norm is the chapter owner `Seminorm.dualNorm`, so its defining
-- support-function formula is the canonical theorem `Seminorm.dualNorm_apply`.
/-- The dual norm of `positiveDefMatrixNorm G hG` is the support function of the `G`-unit ball. -/
theorem positiveDefMatrixNorm_dualNorm_apply
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      sSup ((fun x : E ↦ inner ℝ s x) '' {x | ‖x‖[G] ≤ 1}) := by
  sorry

-- Proof sketch: compare the Chapter 2 support-function definition of
-- `(positiveDefMatrixNorm G hG).dualNorm` with the Chapter 4 strong-dual owner for the bilinear
-- form induced by `Matrix.toEuclideanLin G`, then evaluate that owner by the inverse-matrix
-- formula.
/-- The dual norm of `positiveDefMatrixNorm G hG` is `√⟪s, G⁻¹ s⟫`. -/
theorem positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      Real.sqrt (inner ℝ s ((Matrix.toEuclideanLin G.1⁻¹) s)) := by
  sorry

end

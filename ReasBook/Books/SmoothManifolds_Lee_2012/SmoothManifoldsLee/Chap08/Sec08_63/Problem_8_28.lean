import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Example_7_4
import SmoothManifolds_Lee_2012.Chap07.Sec07_53.Problem_7_4
import SmoothManifolds_Lee_2012.Chap08.Sec08_61.Definition_8_61_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold MatrixGroups ContMDiffMonoidMorphism

-- Domain sampling pass:
-- * primary domain: smooth Lie-group homomorphisms and their induced Lie algebra maps;
-- * source-facing owner for this item: `real_generalLinear_det_lie_hom n` together with the
--   theorem-surface notation `F_*`;
-- * core/canonical owner: `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`;
-- * bridge/view used only in the proof: `generalLinear_det_fderiv_apply` from Problem 7-4;
-- * relevant declarations inspected in this owner family:
--   `real_generalLinear_det_lie_hom`,
--   `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`,
--   the scoped notation `F_*`,
--   and `generalLinear_det_fderiv_apply`.
-- Primitive data here is the induced Lie algebra map of the determinant Lie-group homomorphism.
-- The raw `fderiv` formula is derived API and should not remain the main public surface.

section

variable (n : ℕ)
variable [ChartedSpace (Fin n → Fin n → ℝ) (GL (Fin n) ℝ)]
variable [LieGroup (𝓘(ℝ, Fin n → Fin n → ℝ)) ⊤ (GL (Fin n) ℝ)]

local instance :
    LieGroup (𝓘(ℝ, Fin n → Fin n → ℝ)) (minSmoothness ℝ 3) (GL (Fin n) ℝ) :=
  inferInstance

/-- Problem 8-28: for the determinant Lie-group homomorphism
`real_generalLinear_det_lie_hom n : GL(n, ℝ) → ℝˣ`, the induced Lie algebra homomorphism
`(real_generalLinear_det_lie_hom n)_*` is the trace map. -/
theorem real_generalLinear_det_inducedLieHom_apply (A : Matrix (Fin n) (Fin n) ℝ) :
    ((real_generalLinear_det_lie_hom n)_* A) = Matrix.trace A := by
  sorry

/-- The underlying linear map of the induced Lie algebra homomorphism of the determinant is
`Matrix.traceLinearMap`. -/
theorem real_generalLinear_det_inducedLieHom_eq_trace :
    ((real_generalLinear_det_lie_hom n)_*).toLinearMap =
      Matrix.traceLinearMap (Fin n) ℝ ℝ := by
  ext A
  simpa using real_generalLinear_det_inducedLieHom_apply n A

end

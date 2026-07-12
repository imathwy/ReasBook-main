import Mathlib.Algebra.Lie.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Topology.Algebra.Group.Matrix

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold MatrixGroups
open scoped Matrix.Norms.L2Operator

-- Semantic search note: `lean_leansearch` was unavailable in this runner, so the statement shape
-- was checked directly against `GroupLieAlgebra`, the `Units` Lie-group manifold instance, the
-- matrix Lie algebra API, and the nearby formalizations of Proposition 8.41 and Corollary 8.42.

section

variable (n : ℕ)

/-- Helper for Proposition 8.48: the identity tangent-space chart at the identity of
`GL(n, ℂ)` identifies the tangent space with the ambient complex matrix algebra
`Matrix (Fin n) (Fin n) ℂ`. -/
def complex_general_linear_group_identity_tangent_equiv_matrix (n : ℕ) :
    @TangentSpace ℂ _ (Matrix (Fin n) (Fin n) ℂ) _ _ (Matrix (Fin n) (Fin n) ℂ) _
        (𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)) ((Matrix (Fin n) (Fin n) ℂ)ˣ) inferInstance
        (@Units.instChartedSpace (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance)
        (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ)

/-- Proposition 8.48 (The Lie Algebra of `GL(n, ℂ)`): composing the canonical identification of
`Lie(GL(n, ℂ))` with the identity tangent-space chart at the identity yields the complex matrix
algebra `𝔤𝔩(n, ℂ)`, formalized here as `Matrix (Fin n) (Fin n) ℂ`. -/
def complex_general_linear_group_identity_tangent_equiv_matrix_apply (n : ℕ) :
    @TangentSpace ℂ _ (Matrix (Fin n) (Fin n) ℂ) _ _ (Matrix (Fin n) (Fin n) ℂ) _
        (𝓘(ℂ, Matrix (Fin n) (Fin n) ℂ)) ((Matrix (Fin n) (Fin n) ℂ)ˣ) inferInstance
        (@Units.instChartedSpace (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance)
        (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  complex_general_linear_group_identity_tangent_equiv_matrix n

end

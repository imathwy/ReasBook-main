import Mathlib
import SmoothManifolds_Lee_2012.Chap07.Sec07_51.Exercise_7_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup

noncomputable section

section EuclideanGroup

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ

private def orthogonal_euclidean_toLinearEquiv :
    O(n) →* E ≃ₗ[ℝ] E :=
  (generalLinearEquiv ℝ E).toMonoidHom.comp <|
    (congrLinearEquiv ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv).symm).toMonoidHom.comp
      embeddingGL

private theorem orthogonal_euclidean_toLinearEquiv_toLinearMap
    (A : O(n)) :
    (orthogonal_euclidean_toLinearEquiv n A : E →ₗ[ℝ] E) =
      Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) := by
  ext x i
  rfl

private theorem orthogonal_euclidean_toEuclideanLin_adjoint_comp_self
    (A : O(n)) :
    (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap.adjoint ∘L
        (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap = 1 := by
  have h_mem : ((A : Matrix (Fin n) (Fin n) ℝ) ∈ O(n)) := A.2
  have hA : ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * (A : Matrix (Fin n) (Fin n) ℝ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ :
      (A : Matrix (Fin n) (Fin n) ℝ) ∈ O(n) ↔
        (A : Matrix (Fin n) (Fin n) ℝ)ᵀ * (A : Matrix (Fin n) (Fin n) ℝ) = 1).1 h_mem
  ext x i
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  rw [show LinearMap.adjoint (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)) =
      Matrix.toEuclideanLin ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ) by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (A : Matrix (Fin n) (Fin n) ℝ)).symm]
  simp [hA]

private theorem orthogonal_euclidean_toEuclideanLin_norm_map
    (A : O(n)) (x : E) :
    ‖Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) x‖ = ‖x‖ := by
  let u : E →L[ℝ] E := (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap
  exact ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self u).2
    (orthogonal_euclidean_toEuclideanLin_adjoint_comp_self n A)) x

/-- Example 7.32 (1): the natural action of `O(n)` on `ℝ^n` by linear isometries. -/
def orthogonal_euclidean_linear_equiv :
    O(n) →* E ≃ₗᵢ[ℝ] E where
  toFun A :=
    { toLinearEquiv := orthogonal_euclidean_toLinearEquiv n A
      norm_map' := by
        intro x
        change ‖Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) x‖ = ‖x‖
        exact orthogonal_euclidean_toEuclideanLin_norm_map n A x }
  map_one' := by
    apply LinearIsometryEquiv.toLinearEquiv_injective
    exact (orthogonal_euclidean_toLinearEquiv n).map_one
  map_mul' := by
    intro A B
    apply LinearIsometryEquiv.toLinearEquiv_injective
    exact (orthogonal_euclidean_toLinearEquiv n).map_mul A B

private def orthogonal_euclidean_add_aut :
    O(n) →* AddAut E where
  toFun A := (orthogonal_euclidean_linear_equiv n A).toLinearEquiv.toAddEquiv
  map_one' := by
    ext x
    simpa using congrFun (orthogonal_euclidean_linear_equiv n).map_one x
  map_mul' := by
    intro A B
    ext x
    simpa using congrFun ((orthogonal_euclidean_linear_equiv n).map_mul A B) x

private abbrev euclidean_orthogonal_mul_action :
    O(n) →* MulAut (Multiplicative E) :=
  (MulAutMultiplicative E).symm.toMonoidHom.comp (orthogonal_euclidean_add_aut n)

/-- The semidirect-product bridge sends `x` to the usual linear image `Ax`. -/
@[simp] private theorem euclidean_orthogonal_mul_action_ofAdd
    (A : O(n)) (x : E) :
    euclidean_orthogonal_mul_action n A (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (orthogonal_euclidean_linear_equiv n A x) :=
  by
    simp [euclidean_orthogonal_mul_action, orthogonal_euclidean_add_aut]

/-- Example 7.32 (2): the Euclidean group, realized on the pair type `ℝ^n × O(n)` with the
semidirect-product group law induced by the natural orthogonal action. -/
abbrev euclidean_group :=
  E × O(n)

private abbrev euclidean_group_multiplicative_equiv :
    euclidean_group n ≃ Multiplicative E × O(n) :=
  Multiplicative.ofAdd.prodCongr (Equiv.refl _)

instance : Group (euclidean_group n) := by
  let _ : Group (Multiplicative E × O(n)) :=
    semidirectProductGroup (euclidean_orthogonal_mul_action n)
  exact (euclidean_group_multiplicative_equiv n).group

/-- Example 7.32 (3): multiplication in the Euclidean group is
`(b, A) (b', A') = (b + A b', A A')`. -/
theorem euclidean_group_mul_formula
    (b b' : E) (A A' : O(n)) :
    ((b, A) : euclidean_group n) * (b', A') =
      (b + orthogonal_euclidean_linear_equiv n A b', A * A') := sorry

private def linear_isometry_equiv_to_affine_isometry_equiv :
    (E ≃ₗᵢ[ℝ] E) →* E ≃ᵃⁱ[ℝ] E where
  toFun := LinearIsometryEquiv.toAffineIsometryEquiv
  map_one' := rfl
  map_mul' := by
    intro f g
    sorry

/-- Example 7.32 (4): the Euclidean group acts on `ℝ^n` by affine isometries. -/
def euclidean_group_affine_equiv : euclidean_group n →* E ≃ᵃⁱ[ℝ] E :=
  { toFun := fun g ↦
      AffineIsometryEquiv.constVAdd ℝ E g.1 *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n g.2)
    map_one' := by
      sorry
    map_mul' := by
      intro g h
      sorry }

/-- The Euclidean-group affine action is `(b, A) • x = b + Ax`. -/
theorem euclidean_group_apply_mk
    (b x : E) (A : O(n)) :
    euclidean_group_affine_equiv n (b, A) x =
      b + orthogonal_euclidean_linear_equiv n A x := sorry

end EuclideanGroup

import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff MatrixGroups
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup

-- Semantic recall via `lean_leansearch` confirmed the canonical skew-symmetric owner
-- `LieAlgebra.Orthogonal.so`; local inspection then aligned the subgroup-side surface with the
-- existing `GroupLieAlgebra`-based `SO(n)` analogue in Chapter 8 together with the Chapter 7
-- orthogonal-group files.

local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "M(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "I(" n ")" => 𝓘(ℝ, M(n))

/-- The operator-normed ring structure on real `n × n` matrices used by the ambient `GL(n, ℝ)`
model. -/
local instance real_matrix_normedRing (n : ℕ) : NormedRing (M(n)) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
local instance real_matrix_normedAlgebra (n : ℕ) : NormedAlgebra ℝ (M(n)) :=
  Matrix.linftyOpNormedAlgebra

local instance real_matrix_completeSpace (n : ℕ) : CompleteSpace (M(n)) := by
  infer_instance

/-- Membership in the skew-symmetric matrix Lie algebra `𝔬(n)` is exactly the equation
`A.transpose + A = 0`. -/
theorem mem_orthogonal_lie_subalgebra_iff_transpose_add_eq_zero (n : ℕ)
    (A : M(n)) :
    A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ ↔ A.transpose + A = 0 := sorry

section OrthogonalLieSubgroup

/-- The canonical copy of `O(n)` inside `GL(n, ℝ)`. -/
abbrev orthogonalSubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) :=
  (⊤ : Subgroup (O(n))).map
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℝ ≃*
        LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)).symm.toMonoidHom.comp
      (Matrix.UnitaryGroup.embeddingGL :
        O(n) →* LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)))

/-- The standard charted-space structure on `GL(n, ℝ)` is the one induced from its inclusion into
the operator-normed matrix algebra `M(n)`. -/
noncomputable local instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (M(n)) (GL (Fin n) ℝ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

local notation "LieSubgroupGL(" n ")" =>
  @LieSubgroup ℝ inferInstance (M(n)) inferInstance inferInstance (M(n)) inferInstance
    (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n) (I(n))

/-- The derivative at the identity of the inclusion of a Lie subgroup of `GL(n, ℝ)`. -/
private abbrev orthogonal_group_inclusion_mfderiv {n : ℕ} (S : LieSubgroupGL(n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier →L[ℝ]
      M(n) :=
  @mfderiv ℝ inferInstance S.ModelSpace inferInstance inferInstance S.ModelSpace inferInstance
    (modelWithCornersSelf ℝ S.ModelSpace) S.carrier inferInstance inferInstance M(n)
    inferInstance inferInstance M(n) inferInstance (I(n)) (GL (Fin n) ℝ) inferInstance
    (realGeneralLinearGroupChartedSpace n) (Subtype.val : S.carrier → GL (Fin n) ℝ) (1 : S.carrier)

/-- The Lie subalgebra of `𝔤𝔩(n, ℝ)` singled out by the derivative of the subgroup inclusion at
the identity. This is the `GL(n, ℝ)` specialization of the Theorem 8.46 owner used in Example
8.47. -/
def orthogonal_group_groupLieSubalgebra (n : ℕ) (S : LieSubgroupGL(n))
    [CompleteSpace S.ModelSpace] :
    LieSubalgebra ℝ (M(n)) where
  carrier := Set.range (orthogonal_group_inclusion_mfderiv S)
  zero_mem' := by
    exact ⟨0, by simp [orthogonal_group_inclusion_mfderiv]⟩
  add_mem' := by
    rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', by simp [orthogonal_group_inclusion_mfderiv]⟩
  smul_mem' := by
    intro c x hx
    change c • x ∈ (orthogonal_group_inclusion_mfderiv S).toLinearMap.range
    simpa using
      (Submodule.smul_mem
        ((orthogonal_group_inclusion_mfderiv S).toLinearMap.range) c hx)
  lie_mem' := by
    sorry

/-- Example 8.47: if `S` is the Lie subgroup of `GL(n, ℝ)` whose underlying subgroup is the
canonical copy of `O(n)` and whose chosen Lie-subgroup structure is smoothly identified with the
intrinsic Lie-group structure on `O(n)`, then under the canonical identification from Theorem
8.46 its Lie subalgebra is the skew-symmetric matrix Lie algebra `𝔬(n)`. -/
theorem orthogonal_group_lie_isomorphic_to_so (n : ℕ) (S : LieSubgroupGL(n))
    [CompleteSpace S.ModelSpace]
    {Eₒ : Type*} [NormedAddCommGroup Eₒ] [NormedSpace ℝ Eₒ]
    {Iₒ : ModelWithCorners ℝ Eₒ (O(n))}
    [ChartedSpace Eₒ (O(n))]
    [LieGroup Iₒ (⊤ : WithTop ℕ∞) (O(n))]
    (e : S.carrier ≃* O(n))
    (he : ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) Iₒ (⊤ : WithTop ℕ∞) e)
    (he_symm : ContMDiff Iₒ (modelWithCornersSelf ℝ S.ModelSpace) (⊤ : WithTop ℕ∞) e.symm)
    (hS : S.carrier = orthogonalSubgroupInGeneralLinearGroup n)
    (hcoe : ∀ x : S.carrier, ((e x : O(n)) : M(n)) = ((x : GL (Fin n) ℝ) : M(n))) :
    orthogonal_group_groupLieSubalgebra n S = LieAlgebra.Orthogonal.so (Fin n) ℝ := sorry

end OrthogonalLieSubgroup

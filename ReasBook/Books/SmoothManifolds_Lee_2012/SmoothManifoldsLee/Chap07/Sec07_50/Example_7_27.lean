import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Data.Matrix.Bilinear
import Mathlib.LinearAlgebra.UnitaryGroup

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this environment; the canonical owners were verified
-- directly against mathlib/project source:
-- `Matrix.orthogonalGroup` and `Matrix.mem_orthogonalGroup_iff'`.

open scoped Matrix.Norms.Elementwise MatrixGroups RightActions

-- Domain sampling pass:
-- * primary domain: the real orthogonal group as a matrix Lie subgroup and the embedded
--   submanifold inclusion API;
-- * sampled owner declarations: `Matrix.orthogonalGroup` and
--   `Matrix.mem_orthogonalGroup_iff'`;
-- * owner abstraction used here: the core/canonical owner is `Matrix.orthogonalGroup`, while
--   `orthogonalLevelMap` is the source-facing level-set presentation from the textbook;
-- * source/core/bridge triage: `orthogonalLevelMap` is source-facing, the orthogonal-group owner
--   is core/canonical, and the membership and immersion statements below are bridge/view items;
-- * primitive data: an `n × n` real matrix and the ambient embedded-submanifold structure on
--   `O(n)`;
-- * derived API: level-set membership, equivariance, differential formulas, compactness, and the
--   boundedness estimate used for compactness.

local notation "M(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ

/-- The level-set map `A ↦ A.transpose * A` used to define the orthogonal group. -/
def orthogonalLevelMap (n : ℕ) : M(n) → M(n) :=
  fun A ↦ A.transpose * A

/-- Example 7.27 (1): `O(n)` is the level set of the map `A ↦ A.transpose * A` over the identity
matrix. -/
theorem mem_orthogonalGroup_iff_orthogonalLevelMap_eq_one (n : ℕ)
    (A : M(n)) :
    A ∈ O(n) ↔ orthogonalLevelMap n A = 1 := by
  simpa [orthogonalLevelMap] using
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ (A := A))

/-- Example 7.27 (2): the level-set map is equivariant for right multiplication on `GL(n, ℝ)` and
the congruence action `X ↦ B.transpose * X * B` on matrices. -/
theorem orthogonalLevelMap_mul_generalLinear (n : ℕ)
    (A B : GL (Fin n) ℝ) :
    orthogonalLevelMap n
        (((A * B : GL (Fin n) ℝ) : M(n))) =
      (B : M(n)).transpose * orthogonalLevelMap n (A : M(n)) * (B : M(n)) := by
  -- Unfold the level-set map and reassociate the matrix product.
  simp [orthogonalLevelMap, Matrix.transpose_mul, mul_assoc]

/-- Helper for Example 7.27: transpose on `M(n)` has operator norm at most `1`. -/
lemma transposeContinuousLinearMap_bound (n : ℕ) (A : M(n)) :
    ‖A.transpose‖ ≤ 1 * ‖A‖ := by
  have hNorm : ‖A.transpose‖ ≤ ‖A‖ := le_of_eq A.norm_transpose
  rw [one_mul]
  exact hNorm

/-- Helper for Example 7.27: matrix transpose as a continuous linear map on `M(n)`. -/
def transposeContinuousLinearMap (n : ℕ) : M(n) →L[ℝ] M(n) :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toLinearMap.mkContinuous 1
    (transposeContinuousLinearMap_bound n)

/-- Helper for Example 7.27: `transposeContinuousLinearMap n` acts by matrix transpose. -/
lemma transposeContinuousLinearMap_apply (n : ℕ) (A : M(n)) :
    transposeContinuousLinearMap n A = A.transpose :=
  rfl

/-- Helper for Example 7.27: matrix multiplication is bounded for the elementwise matrix norm. -/
lemma matrixMulContinuousLinearMap_bound (n : ℕ) (A C : M(n)) :
    ‖A * C‖ ≤ (n : ℝ) * ‖A‖ * ‖C‖ := by
  rw [Matrix.norm_le_iff]
  · intro i j
    calc
      ‖(A * C) i j‖ = ‖∑ k : Fin n, A i k * C k j‖ := by simp [Matrix.mul_apply]
      _ ≤ ∑ k : Fin n, ‖A i k * C k j‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, ‖A‖ * ‖C‖ := by
            gcongr
            exact (norm_mul_le _ _).trans <|
              mul_le_mul
                (Matrix.norm_entry_le_entrywise_sup_norm A)
                (Matrix.norm_entry_le_entrywise_sup_norm C)
                (norm_nonneg _)
                (norm_nonneg _)
      _ = (n : ℝ) * ‖A‖ * ‖C‖ := by simp [mul_assoc]
  · positivity

/-- Helper for Example 7.27: matrix multiplication as a continuous bilinear map on `M(n)`. -/
noncomputable def matrixMulContinuousLinearMap (n : ℕ) : M(n) →L[ℝ] M(n) →L[ℝ] M(n) :=
  (mulLinearMap (l := Fin n) (m := Fin n) (n := Fin n) (R := ℝ) :
      M(n) →ₗ[ℝ] M(n) →ₗ[ℝ] M(n)).mkContinuous₂ (n : ℝ)
    (matrixMulContinuousLinearMap_bound n)

/-- Helper for Example 7.27: `matrixMulContinuousLinearMap n` acts by matrix multiplication. -/
lemma matrixMulContinuousLinearMap_apply (n : ℕ) (A C : M(n)) :
    matrixMulContinuousLinearMap n A C = A * C := by
  exact
    LinearMap.mkContinuous₂_apply
      (f := (mulLinearMap (l := Fin n) (m := Fin n) (n := Fin n) (R := ℝ) :
        M(n) →ₗ[ℝ] M(n) →ₗ[ℝ] M(n)))
      (hC := matrixMulContinuousLinearMap_bound n) A C

/-- Helper for Example 7.27: the candidate derivative of `orthogonalLevelMap n` at the identity. -/
noncomputable def orthogonalLevelMapOneDeriv (n : ℕ) : M(n) →L[ℝ] M(n) :=
  ContinuousLinearMap.precompR (M(n)) (matrixMulContinuousLinearMap n) (1 : M(n))
      (ContinuousLinearMap.id ℝ (M(n))) +
    ContinuousLinearMap.precompL (M(n)) (matrixMulContinuousLinearMap n)
      (transposeContinuousLinearMap n) (1 : M(n))

/-- Helper for Example 7.27: applying `orthogonalLevelMapOneDeriv n` gives `B.transpose + B`. -/
lemma orthogonalLevelMapOneDeriv_apply (n : ℕ) (B : M(n)) :
    orthogonalLevelMapOneDeriv n B = B.transpose + B := by
  change
    matrixMulContinuousLinearMap n (1 : M(n)) ((ContinuousLinearMap.id ℝ (M(n))) B) +
        matrixMulContinuousLinearMap n (transposeContinuousLinearMap n B) (1 : M(n)) =
      B.transpose + B
  rw [matrixMulContinuousLinearMap_apply, matrixMulContinuousLinearMap_apply,
    transposeContinuousLinearMap_apply, ContinuousLinearMap.id_apply]
  simp [add_comm]

/-- Helper for Example 7.27: the derivative of `A ↦ A.transpose * A` at the identity is given by
left multiplication by `1` plus right multiplication by `1` after transpose. -/
lemma hasFDerivAt_orthogonalLevelMap_one (n : ℕ) :
    HasFDerivAt (orthogonalLevelMap n)
      (orthogonalLevelMapOneDeriv n)
      (1 : M(n)) := by
  -- Combine the derivatives of transpose and the identity with the product rule.
  have hTranspose :
      HasFDerivAt (fun A : M(n) ↦ A.transpose) (transposeContinuousLinearMap n) (1 : M(n)) := by
    simpa [transposeContinuousLinearMap] using
      (transposeContinuousLinearMap n).hasFDerivAt (x := (1 : M(n)))
  have hId :
      HasFDerivAt (fun A : M(n) ↦ A) (ContinuousLinearMap.id ℝ (M(n))) (1 : M(n)) := by
    simpa using (ContinuousLinearMap.id ℝ (M(n))).hasFDerivAt (x := (1 : M(n)))
  simpa [orthogonalLevelMapOneDeriv, orthogonalLevelMap, matrixMulContinuousLinearMap_apply] using
    (matrixMulContinuousLinearMap n).hasFDerivAt_of_bilinear hTranspose hId

/-- Example 7.27 (3): the differential of `A ↦ A.transpose * A` at the identity sends `B` to
`B.transpose + B`. -/
theorem fderiv_orthogonalLevelMap_one_apply (n : ℕ)
    (B : M(n)) :
    fderiv ℝ (orthogonalLevelMap n) (1 : M(n)) B =
      B.transpose + B := by
  have hApply :=
    congrArg (fun L : M(n) →L[ℝ] M(n) ↦ L B) <|
      (hasFDerivAt_orthogonalLevelMap_one n).fderiv
  simpa [orthogonalLevelMapOneDeriv_apply] using hApply

/-- Helper for Example 7.27: a real square matrix is symmetric exactly when it can be written as
`B.transpose + B`. -/
lemma existsTransposeAdd_eq_iff_isSymm (n : ℕ)
    (S : M(n)) :
    (∃ B : M(n), B.transpose + B = S) ↔ S.IsSymm := by
  constructor
  · rintro ⟨B, rfl⟩
    -- A matrix of the form `Bᵀ + B` is symmetric by a standard transpose computation.
    simpa using Matrix.isSymm_transpose_add_self B
  · intro hS
    -- For a symmetric matrix, the witness `(1 / 2) • S` recovers `S`.
    refine ⟨(1 / 2 : ℝ) • S, ?_⟩
    calc
      (((1 / 2 : ℝ) • S).transpose + (1 / 2 : ℝ) • S)
          = (1 / 2 : ℝ) • S.transpose + (1 / 2 : ℝ) • S := by
              simp
      _ = (1 / 2 : ℝ) • S + (1 / 2 : ℝ) • S := by rw [hS.eq]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • S := by rw [add_smul]
      _ = (1 : ℝ) • S := by norm_num
      _ = S := by simp

/-- Example 7.27 (4): the image of the differential of `A ↦ A.transpose * A` at the identity is
exactly the subspace of symmetric matrices. -/
theorem exists_fderiv_orthogonalLevelMap_one_eq_iff_isSymm (n : ℕ)
    (S : M(n)) :
    (∃ B : M(n),
      fderiv ℝ (orthogonalLevelMap n) (1 : M(n)) B = S) ↔
        S.IsSymm := by
  -- Rewrite the differential image using the explicit derivative formula at the identity.
  rw [← existsTransposeAdd_eq_iff_isSymm]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, by simpa [fderiv_orthogonalLevelMap_one_apply] using hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, by simpa [fderiv_orthogonalLevelMap_one_apply] using hB⟩

/-- Helper for Example 7.27: the orthogonal-group carrier in matrix space is the level set
`{A | orthogonalLevelMap n A = 1}`. -/
lemma orthogonalGroup_eq_levelSet (n : ℕ) :
    ((O(n) : Set (M(n))) = {A : M(n) | orthogonalLevelMap n A = 1}) := by
  -- Translate subgroup membership into the level-set equation entrywise.
  ext A
  change A ∈ O(n) ↔ orthogonalLevelMap n A = 1
  exact mem_orthogonalGroup_iff_orthogonalLevelMap_eq_one n A

/-- Helper for Example 7.27: every entry of an orthogonal matrix has norm at most `1`. -/
lemma orthogonalGroup_entry_norm_le_one (n : ℕ)
    (A : O(n)) (i j : Fin n) :
    ‖(A : M(n)) i j‖ ≤ 1 := by
  -- Read the diagonal of `Aᵀ * A = 1` as a sum of squares of one column.
  have hOrth :
      ((A : M(n)).transpose * (A : M(n))) = 1 := by
    simpa [orthogonalLevelMap] using
      (mem_orthogonalGroup_iff_orthogonalLevelMap_eq_one n (A : M(n))).mp A.property
  have hDiag : ∑ k : Fin n, (A : M(n)) k j * (A : M(n)) k j = 1 := by
    have hEntry := congrArg (fun X : M(n) ↦ X j j) hOrth
    simpa [Matrix.mul_apply] using hEntry
  have hTerm :
      (A : M(n)) i j * (A : M(n)) i j ≤
        ∑ k : Fin n, (A : M(n)) k j * (A : M(n)) k j := by
    simpa using
      (Finset.single_le_sum
        (f := fun k : Fin n ↦ (A : M(n)) k j * (A : M(n)) k j)
        (fun k _hk ↦ by simpa [pow_two] using sq_nonneg ((A : M(n)) k j))
        (by simp : i ∈ (Finset.univ : Finset (Fin n))))
  have hSq : ((A : M(n)) i j) ^ 2 ≤ 1 := by
    nlinarith [hTerm, hDiag]
  have hAbs : |(A : M(n)) i j| ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one ((A : M(n)) i j)).mp hSq
  simpa [Real.norm_eq_abs] using hAbs

/-- Helper for Example 7.27: the orthogonal-group carrier is bounded in ambient matrix space. -/
lemma orthogonalGroup_isBoundedInMatrixSpace (n : ℕ) :
    Bornology.IsBounded ((O(n) : Set (M(n)))) := by
  -- A uniform entrywise bound yields a uniform bound in the ambient matrix norm.
  refine isBounded_iff_forall_norm_le.2 ⟨1, ?_⟩
  intro A hA
  rw [Matrix.norm_le_iff zero_le_one]
  intro i j
  exact orthogonalGroup_entry_norm_le_one n ⟨A, hA⟩ i j

/-- Example 7.27 (5): the real orthogonal group `O(n)` is compact. -/
theorem isCompact_orthogonalGroup (n : ℕ) :
    IsCompact (Set.univ : Set (O(n))) := by
  -- Transfer compactness of the subtype to compactness of its image in matrix space.
  rw [Subtype.isCompact_iff]
  have hClosed : IsClosed ((O(n) : Set (M(n)))) := by
    -- The orthogonal group is a closed level set of the continuous map `A ↦ Aᵀ * A`.
    rw [orthogonalGroup_eq_levelSet]
    have hCont : Continuous (orthogonalLevelMap n) := by
      simpa [orthogonalLevelMap] using (show Continuous fun A : M(n) ↦ A.transpose * A by fun_prop)
    exact isClosed_eq hCont continuous_const
  -- Closed and bounded subsets of finite-dimensional matrix space are compact.
  simpa [Set.image_univ, Subtype.range_coe] using
    Metric.isCompact_of_isClosed_isBounded hClosed (orthogonalGroup_isBoundedInMatrixSpace n)

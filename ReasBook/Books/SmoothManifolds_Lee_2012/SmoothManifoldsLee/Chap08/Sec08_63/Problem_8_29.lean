import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContDiff Manifold Matrix MatrixGroups
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup
open Matrix.SpecialLinearGroup

local notation "Mℝ(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "Mℂ(" n ")" => Matrix (Fin n) (Fin n) ℂ
local notation "Iℝ(" n ")" => 𝓘(ℝ, Mℝ(n))
local notation "Iℂ(" n ")" => 𝓘(ℂ, Mℂ(n))
local notation "Iℝℂ(" n ")" => 𝓘(ℝ, Mℂ(n))
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "SO(" n ")" => Matrix.specialOrthogonalGroup (Fin n) ℝ
local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ
local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ

/-- The operator-normed ring structure on real `n × n` matrices used by the real matrix models. -/
local instance real_matrix_normedRing (n : ℕ) : NormedRing (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
local instance real_matrix_normedAlgebra (n : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedAlgebra

local instance real_matrix_completeSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := by
  infer_instance

/-- The operator-normed ring structure on complex `n × n` matrices used by the complex matrix
models. -/
local instance complex_matrix_normedRing (n : ℕ) : NormedRing (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed complex-algebra structure on complex `n × n` matrices. -/
local instance complex_matrix_normedAlgebra (n : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.linftyOpNormedAlgebra

local instance complex_matrix_completeSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := by
  infer_instance

/-- The standard charted-space structure on `GL(n, ℝ)` comes from the open embedding into the
ambient real matrix algebra. -/
noncomputable local instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℝ(n)) (GL (Fin n) ℝ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

/-- The standard charted-space structure on `GL(n, ℂ)` comes from the open embedding into the
ambient complex matrix algebra. -/
noncomputable local instance complexGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℂ(n)) (GL (Fin n) ℂ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

local notation "RealLieSubgroupGL(" n ")" =>
  @LieSubgroup ℝ inferInstance (Mℝ(n)) inferInstance inferInstance (Mℝ(n)) inferInstance
    (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n) (Iℝ(n))

local notation "ComplexLieSubgroupGL(" n ")" =>
  @LieSubgroup ℂ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n) (Iℂ(n))

local notation "RealLieSubgroupGLComplex(" n ")" =>
  @LieSubgroup ℝ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n)
      (Iℝℂ(n))

local notation "RealGLIsManifold(" n ")" =>
  @IsManifold ℝ inferInstance (Mℝ(n)) inferInstance inferInstance (Mℝ(n)) inferInstance
    (Iℝ(n)) ω (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)

local notation "ComplexGLIsManifold(" n ")" =>
  @IsManifold ℂ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (Iℂ(n)) ω (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealComplexGLIsManifold(" n ")" =>
  @IsManifold ℝ inferInstance (Mℂ(n)) inferInstance inferInstance (Mℂ(n)) inferInstance
    (Iℝℂ(n)) ω (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealGLLieGroup(" n ")" =>
  @LieGroup ℝ inferInstance (Mℝ(n)) inferInstance (Mℝ(n)) inferInstance inferInstance
    (Iℝ(n)) ∞ (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n)

local notation "ComplexGLLieGroup(" n ")" =>
  @LieGroup ℂ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℂ(n)) ∞ (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n)

local notation "RealComplexGLLieGroup(" n ")" =>
  @LieGroup ℝ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℝℂ(n)) ∞ (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n)

local notation "RealGLLieGroupMinSmoothness(" n ")" =>
  @LieGroup ℝ inferInstance (Mℝ(n)) inferInstance (Mℝ(n)) inferInstance inferInstance
    (Iℝ(n)) (minSmoothness ℝ 3) (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupChartedSpace n)

local notation "ComplexGLLieGroupMinSmoothness(" n ")" =>
  @LieGroup ℂ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℂ(n)) (minSmoothness ℂ 3) (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n)

local notation "RealComplexGLLieGroupMinSmoothness(" n ")" =>
  @LieGroup ℝ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℝℂ(n)) (minSmoothness ℝ 3) (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupChartedSpace n)

local notation "RealGLGroupLieAlgebra(" n ")" =>
  @GroupLieAlgebra ℝ inferInstance (Mℝ(n)) inferInstance (Mℝ(n)) inferInstance inferInstance
    (Iℝ(n)) (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) inferInstance

local notation "ComplexGLGroupLieAlgebra(" n ")" =>
  @GroupLieAlgebra ℂ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℂ(n)) (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n) inferInstance

local notation "RealComplexGLGroupLieAlgebra(" n ")" =>
  @GroupLieAlgebra ℝ inferInstance (Mℂ(n)) inferInstance (Mℂ(n)) inferInstance inferInstance
    (Iℝℂ(n)) (GL (Fin n) ℂ) inferInstance (complexGeneralLinearGroupChartedSpace n) inferInstance

/-- The derivative at the identity of the inclusion of a Lie subgroup of `GL(n, ℝ)`. -/
private abbrev real_problem_8_29_inclusion_mfderiv {n : ℕ} (S : RealLieSubgroupGL(n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier →L[ℝ] Mℝ(n) :=
  @mfderiv ℝ inferInstance S.ModelSpace inferInstance inferInstance S.ModelSpace inferInstance
    (modelWithCornersSelf ℝ S.ModelSpace) S.carrier inferInstance inferInstance Mℝ(n)
    inferInstance inferInstance Mℝ(n) inferInstance (Iℝ(n)) (GL (Fin n) ℝ) inferInstance
    (realGeneralLinearGroupChartedSpace n) (Subtype.val : S.carrier → GL (Fin n) ℝ) (1 : S.carrier)

/-- The derivative at the identity of the inclusion of a Lie subgroup of `GL(n, ℂ)`. -/
private abbrev complex_problem_8_29_inclusion_mfderiv {n : ℕ} (S : ComplexLieSubgroupGL(n)) :
    GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier →L[ℂ] Mℂ(n) :=
  @mfderiv ℂ inferInstance S.ModelSpace inferInstance inferInstance S.ModelSpace inferInstance
    (modelWithCornersSelf ℂ S.ModelSpace) S.carrier inferInstance inferInstance Mℂ(n)
    inferInstance inferInstance Mℂ(n) inferInstance (Iℂ(n)) (GL (Fin n) ℂ) inferInstance
    (complexGeneralLinearGroupChartedSpace n) (Subtype.val : S.carrier → GL (Fin n) ℂ)
    (1 : S.carrier)

/-- The derivative at the identity of the inclusion of a real Lie subgroup of `GL(n, ℂ)`. -/
private abbrev real_complex_problem_8_29_inclusion_mfderiv {n : ℕ} (S : RealLieSubgroupGLComplex(n)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier →L[ℝ] Mℂ(n) :=
  @mfderiv ℝ inferInstance S.ModelSpace inferInstance inferInstance S.ModelSpace inferInstance
    (modelWithCornersSelf ℝ S.ModelSpace) S.carrier inferInstance inferInstance Mℂ(n)
    inferInstance inferInstance Mℂ(n) inferInstance (Iℝℂ(n)) (GL (Fin n) ℂ) inferInstance
    (complexGeneralLinearGroupChartedSpace n) (Subtype.val : S.carrier → GL (Fin n) ℂ)
    (1 : S.carrier)

/-- The Lie subalgebra of `𝔤𝔩(n, ℝ)` obtained from a Lie subgroup of `GL(n, ℝ)` via the canonical
identification from Theorem 8.46. -/
def real_problem_8_29_groupLieSubalgebra (n : ℕ) (S : RealLieSubgroupGL(n))
    [CompleteSpace S.ModelSpace] :
    LieSubalgebra ℝ (Mℝ(n)) := by
  letI : LieGroup (modelWithCornersSelf ℝ S.ModelSpace) (minSmoothness ℝ 3) S.carrier :=
    inferInstance
  refine
    { carrier := Set.range (real_problem_8_29_inclusion_mfderiv S)
      zero_mem' := ?_
      add_mem' := ?_
      smul_mem' := ?_
      lie_mem' := ?_ }
  · exact ⟨0, map_zero (real_problem_8_29_inclusion_mfderiv S)⟩
  · rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add (real_problem_8_29_inclusion_mfderiv S) x' y'⟩
  · rintro c x ⟨x', rfl⟩
    exact
      ⟨(c • x' : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier), by
        simpa using map_smul (real_problem_8_29_inclusion_mfderiv S) c x'⟩
  · sorry

/-- The Lie subalgebra of `𝔤𝔩(n, ℂ)` obtained from a Lie subgroup of `GL(n, ℂ)` via the canonical
identification from Theorem 8.46. -/
def complex_problem_8_29_groupLieSubalgebra (n : ℕ) (S : ComplexLieSubgroupGL(n))
    [CompleteSpace S.ModelSpace] :
    LieSubalgebra ℂ (Mℂ(n)) := by
  letI : LieGroup (modelWithCornersSelf ℂ S.ModelSpace) (minSmoothness ℂ 3) S.carrier :=
    inferInstance
  refine
    { carrier := Set.range (complex_problem_8_29_inclusion_mfderiv S)
      zero_mem' := ?_
      add_mem' := ?_
      smul_mem' := ?_
      lie_mem' := ?_ }
  · exact ⟨0, map_zero (complex_problem_8_29_inclusion_mfderiv S)⟩
  · rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add (complex_problem_8_29_inclusion_mfderiv S) x' y'⟩
  · rintro c x ⟨x', rfl⟩
    exact
      ⟨(c • x' : GroupLieAlgebra (modelWithCornersSelf ℂ S.ModelSpace) S.carrier), by
        simpa using map_smul (complex_problem_8_29_inclusion_mfderiv S) c x'⟩
  · sorry

/-- The Lie subalgebra of `𝔤𝔩(n, ℂ)` obtained from a real Lie subgroup of `GL(n, ℂ)` via the
canonical identification from Theorem 8.46. -/
def real_complex_problem_8_29_groupLieSubalgebra (n : ℕ) (S : RealLieSubgroupGLComplex(n))
    [CompleteSpace S.ModelSpace] :
    LieSubalgebra ℝ (Mℂ(n)) := by
  letI : LieGroup (modelWithCornersSelf ℝ S.ModelSpace) (minSmoothness ℝ 3) S.carrier :=
    inferInstance
  refine
    { carrier := Set.range (real_complex_problem_8_29_inclusion_mfderiv S)
      zero_mem' := ?_
      add_mem' := ?_
      smul_mem' := ?_
      lie_mem' := ?_ }
  · exact ⟨0, map_zero (real_complex_problem_8_29_inclusion_mfderiv S)⟩
  · rintro x y ⟨x', rfl⟩ ⟨y', rfl⟩
    exact ⟨x' + y', map_add (real_complex_problem_8_29_inclusion_mfderiv S) x' y'⟩
  · rintro c x ⟨x', rfl⟩
    exact
      ⟨(c • x' : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier), by
        simpa using map_smul (real_complex_problem_8_29_inclusion_mfderiv S) c x'⟩
  · sorry

/-- The canonical inclusion `SO(n) → O(n)`. -/
private def specialOrthogonalToOrthogonal (n : ℕ) : SO(n) →* O(n) where
  toFun A := ⟨A.1, A.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical inclusion `SO(n) → GL(n, ℝ)`. -/
private def specialOrthogonalToGeneralLinearGroup (n : ℕ) : SO(n) →* GL (Fin n) ℝ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℝ ≃*
      LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      O(n) →* LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ))).comp
    (specialOrthogonalToOrthogonal n)

/-- The canonical copy of `SO(n)` inside `GL(n, ℝ)`. -/
def specialOrthogonalSubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) :=
  (⊤ : Subgroup (SO(n))).map (specialOrthogonalToGeneralLinearGroup n)

/-- The canonical copy of `SL(n, ℝ)` inside `GL(n, ℝ)`. -/
abbrev specialLinearRealSubgroupInGeneralLinearGroup (n : ℕ) :
    Subgroup (GL (Fin n) ℝ) :=
  toGL.range

/-- The canonical inclusion `U(n) → GL(n, ℂ)`. -/
abbrev unitarySubgroupToGeneralLinearGroup (n : ℕ) : U(n) →* GL (Fin n) ℂ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℂ ≃*
      LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      U(n) →* LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)))

/-- The canonical copy of `U(n)` inside `GL(n, ℂ)`. -/
def unitarySubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℂ) :=
  (⊤ : Subgroup (U(n))).map (unitarySubgroupToGeneralLinearGroup n)

/-- The canonical inclusion `SU(n) → U(n)`. -/
def specialUnitaryToUnitary (n : ℕ) : SU(n) →* U(n) where
  toFun A := ⟨A.1, Matrix.specialUnitaryGroup_le_unitaryGroup A.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The canonical inclusion `SU(n) → GL(n, ℂ)`. -/
private def specialUnitaryToGeneralLinearGroup (n : ℕ) : SU(n) →* GL (Fin n) ℂ :=
  (unitarySubgroupToGeneralLinearGroup n).comp (specialUnitaryToUnitary n)

/-- The canonical copy of `SU(n)` inside `GL(n, ℂ)`. -/
def specialUnitarySubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℂ) :=
  (⊤ : Subgroup (SU(n))).map (specialUnitaryToGeneralLinearGroup n)

/-- The canonical copy of `SL(n, ℂ)` inside `GL(n, ℂ)`. -/
abbrev specialLinearComplexSubgroupInGeneralLinearGroup (n : ℕ) :
    Subgroup (GL (Fin n) ℂ) :=
  toGL.range

-- Semantic search note: `lean_leansearch` was used to confirm the `GroupLieAlgebra`/Lie-subalgebra
-- surface, and the relevant owners were then checked directly against
-- `LieAlgebra.SpecialLinear.sl`, `LieAlgebra.Orthogonal.so`, and the local matrix-group files.

/-- A smooth real Lie-group structure on a group charted by real matrices supplies the `C^3`
instance used by `GroupLieAlgebra`. -/
local instance real_matrix_real_lieGroup_minSmoothness
    {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)}
    [ChartedSpace (Matrix (Fin n) (Fin n) ℝ) G] [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G :=
  ((minSmoothness_of_isRCLikeNormedField : minSmoothness ℝ (3 : ℕ∞ω) = (3 : ℕ∞ω))).symm ▸
    (inferInstance : LieGroup I (3 : ℕ∞ω) G)

/-- A smooth real Lie-group structure on a group charted by complex matrices, viewed as a real
manifold, supplies the `C^3` instance used by `GroupLieAlgebra`. -/
local instance real_matrix_complex_lieGroup_minSmoothness
    {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)}
    [ChartedSpace (Matrix (Fin n) (Fin n) ℂ) G] [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G :=
  ((minSmoothness_of_isRCLikeNormedField : minSmoothness ℝ (3 : ℕ∞ω) = (3 : ℕ∞ω))).symm ▸
    (inferInstance : LieGroup I (3 : ℕ∞ω) G)

/-- A smooth complex Lie-group structure on a group charted by complex matrices supplies the `C^3`
instance used by `GroupLieAlgebra`. -/
local instance complex_matrix_complex_lieGroup_minSmoothness
    {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℂ (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ)}
    [ChartedSpace (Matrix (Fin n) (Fin n) ℂ) G] [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℂ 3) G :=
  ((minSmoothness_of_isRCLikeNormedField : minSmoothness ℂ (3 : ℕ∞ω) = (3 : ℕ∞ω))).symm ▸
    (inferInstance : LieGroup I (3 : ℕ∞ω) G)

/-- The skew-Hermitian predicate cutting out the real matrix Lie algebra `𝔲(n)`. -/
private def is_unitary_matrix_lie (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = -A

/-- Zero is skew-Hermitian. -/
private theorem is_unitary_matrix_lie_zero (n : ℕ) :
    is_unitary_matrix_lie n (0 : Matrix (Fin n) (Fin n) ℂ) := by
  -- The zero matrix satisfies the defining skew-Hermitian equation by direct simplification.
  simp [is_unitary_matrix_lie]

/-- The skew-Hermitian matrices are closed under addition. -/
private theorem is_unitary_matrix_lie_add (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_unitary_matrix_lie n A) (hB : is_unitary_matrix_lie n B) :
    is_unitary_matrix_lie n (A + B) := by
  -- Conjugate transpose is additive, so the defining equation rewrites termwise.
  rw [is_unitary_matrix_lie] at hA hB ⊢
  rw [Matrix.conjTranspose_add, hA, hB]
  abel

/-- The skew-Hermitian matrices are closed under real scalar multiplication. -/
private theorem is_unitary_matrix_lie_real_smul (n : ℕ) (r : ℝ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : is_unitary_matrix_lie n A) :
    is_unitary_matrix_lie n (r • A) := by
  -- Real scalars are fixed by conjugation, so skew-Hermitianity is preserved under `ℝ`-scaling.
  rw [is_unitary_matrix_lie] at hA ⊢
  simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ ↦ r • M) hA

/-- The skew-Hermitian matrices are closed under the commutator bracket. -/
private theorem is_unitary_matrix_lie_lie (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_unitary_matrix_lie n A) (hB : is_unitary_matrix_lie n B) :
    is_unitary_matrix_lie n ⁅A, B⁆ := by
  -- The adjoint reverses products, so the commutator picks up a minus sign.
  rw [is_unitary_matrix_lie] at hA hB ⊢
  calc
    (⁅A, B⁆ : Matrix (Fin n) (Fin n) ℂ)ᴴ = Bᴴ * Aᴴ - Aᴴ * Bᴴ := by
      simp [Ring.lie_def]
    _ = B * A - A * B := by rw [hA, hB]; simp
    _ = -(A * B - B * A) := by
      abel
    _ = -(⁅A, B⁆ : Matrix (Fin n) (Fin n) ℂ) := by rw [Ring.lie_def]

/-- The real matrix Lie algebra `𝔲(n)`, realized as the skew-Hermitian `n x n` complex matrices.
-/
def unitary_matrix_lie_subalgebra (n : ℕ) : LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | is_unitary_matrix_lie n A}
  zero_mem' := is_unitary_matrix_lie_zero n
  add_mem' := fun hA hB ↦ is_unitary_matrix_lie_add n hA hB
  smul_mem' := fun r _ hA ↦ is_unitary_matrix_lie_real_smul n r hA
  lie_mem' := fun hA hB ↦ is_unitary_matrix_lie_lie n hA hB

/-- Membership in `unitary_matrix_lie_subalgebra n` is the skew-Hermitian condition `Aᴴ = -A`. -/
theorem unitary_matrix_lie_subalgebra_mem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ unitary_matrix_lie_subalgebra n ↔ Aᴴ = -A := by
  -- This is exactly the carrier predicate used in the definition.
  rfl

/-- The skew-Hermitian trace-zero predicate cutting out the real matrix Lie algebra `𝔰𝔲(n)`. -/
private def is_special_unitary_matrix_lie (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Aᴴ = -A ∧ Matrix.trace A = 0

/-- Zero is skew-Hermitian and trace zero. -/
private theorem is_special_unitary_matrix_lie_zero (n : ℕ) :
    is_special_unitary_matrix_lie n (0 : Matrix (Fin n) (Fin n) ℂ) := by
  -- Both defining conditions are immediate for the zero matrix.
  simp [is_special_unitary_matrix_lie]

/-- The skew-Hermitian trace-zero matrices are closed under addition. -/
private theorem is_special_unitary_matrix_lie_add (n : ℕ)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_special_unitary_matrix_lie n A) (hB : is_special_unitary_matrix_lie n B) :
    is_special_unitary_matrix_lie n (A + B) := by
  rcases hA with ⟨hA_skew, hA_trace⟩
  rcases hB with ⟨hB_skew, hB_trace⟩
  -- Both the skew-Hermitian and trace-zero conditions are additive.
  constructor
  · exact is_unitary_matrix_lie_add n hA_skew hB_skew
  · simp [Matrix.trace_add, hA_trace, hB_trace]

/-- The skew-Hermitian trace-zero matrices are closed under real scalar multiplication. -/
private theorem is_special_unitary_matrix_lie_real_smul (n : ℕ) (r : ℝ)
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : is_special_unitary_matrix_lie n A) :
    is_special_unitary_matrix_lie n (r • A) := by
  rcases hA with ⟨hA_skew, hA_trace⟩
  -- Real scalar multiplication preserves both defining conditions.
  constructor
  · exact is_unitary_matrix_lie_real_smul n r hA_skew
  · simp [Matrix.trace_smul, hA_trace]

/-- The skew-Hermitian trace-zero matrices are closed under the commutator bracket. -/
private theorem is_special_unitary_matrix_lie_lie (n : ℕ) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : is_special_unitary_matrix_lie n A) (hB : is_special_unitary_matrix_lie n B) :
    is_special_unitary_matrix_lie n ⁅A, B⁆ := by
  rcases hA with ⟨hA_skew, _hA_trace⟩
  rcases hB with ⟨hB_skew, _hB_trace⟩
  -- The commutator stays skew-Hermitian, and its trace vanishes by the standard trace identity.
  constructor
  · exact is_unitary_matrix_lie_lie n hA_skew hB_skew
  · exact
      (LieAlgebra.matrix_trace_commutator_zero (Fin n) ℂ A B)

/-- The real matrix Lie algebra `𝔰𝔲(n)`, realized as the trace-zero skew-Hermitian `n x n`
complex matrices. -/
def special_unitary_matrix_lie_subalgebra (n : ℕ) :
    LieSubalgebra ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {A | is_special_unitary_matrix_lie n A}
  zero_mem' := is_special_unitary_matrix_lie_zero n
  add_mem' := fun hA hB ↦ is_special_unitary_matrix_lie_add n hA hB
  smul_mem' := fun r _ hA ↦ is_special_unitary_matrix_lie_real_smul n r hA
  lie_mem' := fun hA hB ↦ is_special_unitary_matrix_lie_lie n hA hB

/-- Membership in `special_unitary_matrix_lie_subalgebra n` is the condition
`Aᴴ = -A ∧ Matrix.trace A = 0`. -/
theorem special_unitary_matrix_lie_subalgebra_mem
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔ Aᴴ = -A ∧ Matrix.trace A = 0 := by
  -- This is exactly the carrier predicate used in the definition.
  rfl

/-- Helper for Problem 8-29: membership in `LieAlgebra.SpecialLinear.sl (Fin n) 𝕜` is exactly the
trace-zero condition. -/
private theorem mem_specialLinear_iff_traceZero {𝕜 : Type*} [CommRing 𝕜] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    A ∈ LieAlgebra.SpecialLinear.sl (Fin n) 𝕜 ↔ Matrix.trace A = 0 := by
  -- `𝔰𝔩(n, 𝕜)` is defined as the kernel of the trace map.
  change A ∈ LinearMap.ker (Matrix.traceLinearMap (Fin n) 𝕜 𝕜) ↔ Matrix.trace A = 0
  simp [LinearMap.mem_ker]

/-- Helper for Problem 8-29: skew-symmetric real matrices have trace zero. -/
private theorem orthogonalMatricesTraceZero (n : ℕ)
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ) :
    Matrix.trace A = 0 := by
  -- Rewrite membership as `Aᵀ = -A` and take traces of both sides.
  rw [LieAlgebra.Orthogonal.mem_so] at hA
  have hTrace := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose, Matrix.trace_neg] at hTrace
  linarith

/-- Helper for Problem 8-29: the local `𝔰𝔲(n)` model is exactly the skew-Hermitian trace-zero
part of the local `𝔲(n)` model. -/
private theorem mem_specialUnitary_iff_mem_unitary_and_traceZero
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ special_unitary_matrix_lie_subalgebra n ↔
      A ∈ unitary_matrix_lie_subalgebra n ∧ Matrix.trace A = 0 := by
  -- Expand both carrier predicates and regroup the conjunctions.
  rw [special_unitary_matrix_lie_subalgebra_mem, unitary_matrix_lie_subalgebra_mem]

/-- Problem 8-29 (1): if `S` is the Lie subgroup of `GL(n, ℝ)` whose underlying subgroup is the
canonical copy of `SL(n, ℝ)`, then under the canonical identification from Theorem 8.46 its Lie
algebra is the trace-zero matrix Lie algebra `𝔰𝔩(n, ℝ)`. -/
theorem special_linear_real_lie_equiv_sl (n : ℕ)
    (S : RealLieSubgroupGL(n))
    [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearRealSubgroupInGeneralLinearGroup n) :
    real_problem_8_29_groupLieSubalgebra n S = LieAlgebra.SpecialLinear.sl (Fin n) ℝ := sorry

/-- Problem 8-29 (2): if `S` is the Lie subgroup of `GL(n, ℝ)` whose underlying subgroup is the
canonical copy of `SO(n)`, then under the canonical identification from Theorem 8.46 its Lie
algebra is the skew-symmetric matrix Lie algebra `𝔬(n)`. -/
theorem special_orthogonal_lie_equiv_so (n : ℕ)
    (S : RealLieSubgroupGL(n))
    [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialOrthogonalSubgroupInGeneralLinearGroup n) :
    real_problem_8_29_groupLieSubalgebra n S = LieAlgebra.Orthogonal.so (Fin n) ℝ := sorry

/-- Problem 8-29 (3): if `S` is the Lie subgroup of `GL(n, ℂ)` whose underlying subgroup is the
canonical copy of `SL(n, ℂ)`, then under the canonical identification from Theorem 8.46 its Lie
algebra is the trace-zero complex matrix Lie algebra `𝔰𝔩(n, ℂ)`. -/
theorem special_linear_complex_lie_equiv_sl (n : ℕ)
    (S : ComplexLieSubgroupGL(n))
    [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialLinearComplexSubgroupInGeneralLinearGroup n) :
    complex_problem_8_29_groupLieSubalgebra n S = LieAlgebra.SpecialLinear.sl (Fin n) ℂ := sorry

/-- Problem 8-29 (4): if `S` is the real Lie subgroup of `GL(n, ℂ)` whose underlying subgroup is
the canonical copy of `U(n)`, then under the canonical identification from Theorem 8.46 its Lie
algebra is the real Lie algebra `𝔲(n)` of skew-Hermitian complex matrices. -/
theorem unitary_lie_equiv_u (n : ℕ)
    (S : RealLieSubgroupGLComplex(n))
    [CompleteSpace S.ModelSpace]
    (hS : S.carrier = unitarySubgroupInGeneralLinearGroup n) :
    real_complex_problem_8_29_groupLieSubalgebra n S = unitary_matrix_lie_subalgebra n := sorry

/-- Problem 8-29 (5): if `S` is the real Lie subgroup of `GL(n, ℂ)` whose underlying subgroup is
the canonical copy of `SU(n)`, then under the canonical identification from Theorem 8.46 its Lie
algebra is the real Lie algebra `𝔰𝔲(n)` of trace-zero skew-Hermitian complex matrices. -/
theorem special_unitary_lie_equiv_su (n : ℕ)
    (S : RealLieSubgroupGLComplex(n))
    [CompleteSpace S.ModelSpace]
    (hS : S.carrier = specialUnitarySubgroupInGeneralLinearGroup n) :
    real_complex_problem_8_29_groupLieSubalgebra n S = special_unitary_matrix_lie_subalgebra n := sorry

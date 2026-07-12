import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Matrix
import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Definition_5_30_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Corollary_5_14
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Theorem_5_53
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix.Norms.Operator Manifold ContDiff MatrixGroups
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup

-- Semantic recall via `lean_leansearch` confirmed the canonical matrix-group owner
-- `Matrix.unitaryGroup`; local inspection fixed the ambient `GL(n, ℂ)` carrier as the image of
-- `Matrix.UnitaryGroup.embeddingGL`, with Chapter 5/7 owners `Set.IsProperlyEmbedded` and
-- `LieSubgroup` for the source-facing statements below.

local notation "U(" n ")" => Matrix.unitaryGroup (Fin n) ℂ

/-- The canonical copy of `U(n)` inside `GL(n, ℂ)`. -/
abbrev unitarySubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℂ) :=
  (⊤ : Subgroup (U(n))).map
    ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℂ ≃*
        LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)).symm.toMonoidHom.comp
      (Matrix.UnitaryGroup.embeddingGL :
        U(n) →* LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)))

section ComplexUnitaryLieSubgroup

variable {n : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "M(" n ")" => Matrix (Fin n) (Fin n) ℂ
local notation "I(" n ")" => 𝓘(ℝ, M(n))
local notation "SA(" n ")" => selfAdjoint (M(n))

/-- Helper for Problem 7-13: the operator-normed ring structure on complex `n × n` matrices. -/
local instance complexMatrixNormedRing (n : ℕ) : NormedRing (M(n)) :=
  Matrix.linftyOpNormedRing

/-- Helper for Problem 7-13: the corresponding normed real-algebra structure on complex
`n × n` matrices. -/
local instance complexMatrixNormedAlgebra (n : ℕ) : NormedAlgebra ℝ (M(n)) :=
  Matrix.linftyOpNormedAlgebra

/-- Helper for Problem 7-13: the ambient complex matrix space is complete for the operator norm. -/
local instance complexMatrixCompleteSpace (n : ℕ) : CompleteSpace (M(n)) := by
  infer_instance

/-- The standard charted-space structure on `GL(n, ℂ)` is the one induced from its inclusion into
the operator-normed matrix algebra `M(n)`. -/
noncomputable instance complexGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (M(n)) (GL (Fin n) ℂ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

local notation "LieSubgroupGL(" n ")" =>
  @LieSubgroup ℝ inferInstance (M(n)) inferInstance inferInstance (M(n)) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance (complexGeneralLinearGroupChartedSpace n) (I(n))

/-- Helper for Problem 7-13: the subtype inclusion of an embedded subgroup of `GL(n, ℂ)` is
smooth in the induced manifold structure. -/
lemma embeddedSubgroupSubtypeVal_contMDiff
    (S : Subgroup (GL (Fin n) ℂ)) [ChartedSpace F S]
    [IsManifold (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I(n) (modelWithCornersSelf ℝ F) (S : Set (GL (Fin n) ℂ))) :
    ContMDiff (modelWithCornersSelf ℝ F) (I(n)) (⊤ : WithTop ℕ∞) (Subtype.val : S → GL (Fin n) ℂ) := by
  -- The Chapter 5 embedded-submanifold bridge makes the subtype inclusion smooth.
  simpa using
    subtype_val_contMDiff_of_isSmoothEmbedding
      (I := I(n)) (J := modelWithCornersSelf ℝ F) (S := (S : Set (GL (Fin n) ℂ)))
      hS.isSmoothEmbedding_subtype_val

/-- Helper for Problem 7-13: the ambient multiplication on an embedded subgroup of `GL(n, ℂ)`
restricts to the intrinsic subgroup multiplication. -/
lemma embeddedSubgroupMul_codRestrict_eq
    (S : Subgroup (GL (Fin n) ℂ)) :
    Set.codRestrict
      (fun p : S × S ↦ (p.1 : GL (Fin n) ℂ) * (p.2 : GL (Fin n) ℂ))
      (S : Set (GL (Fin n) ℂ))
      (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)
      =
      (fun p : S × S ↦ p.1 * p.2) := rfl

/-- Helper for Problem 7-13: multiplication is smooth on an embedded subgroup of `GL(n, ℂ)` with
its induced manifold structure. -/
lemma embeddedSubgroupMul_contMDiff
    (S : Subgroup (GL (Fin n) ℂ)) [ChartedSpace F S]
    [IsManifold (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I(n) (modelWithCornersSelf ℝ F) (S : Set (GL (Fin n) ℂ))) :
    ContMDiff
      ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞)
      (fun p : S × S ↦ p.1 * p.2) := by
  have hfst : ContMDiff
      ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      (I(n)) (⊤ : WithTop ℕ∞) fun p : S × S ↦ (p.1 : GL (Fin n) ℂ) := by
    -- Each projection becomes an ambient smooth map after composing with the subtype inclusion.
    simpa using
      (embeddedSubgroupSubtypeVal_contMDiff (n := n) (F := F) S hS).comp
        (contMDiff_fst :
          ContMDiff
            ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
            (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) fun p : S × S ↦ p.1)
  have hsnd : ContMDiff
      ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      (I(n)) (⊤ : WithTop ℕ∞) fun p : S × S ↦ (p.2 : GL (Fin n) ℂ) := by
    -- The same restriction argument applies to the second projection.
    simpa using
      (embeddedSubgroupSubtypeVal_contMDiff (n := n) (F := F) S hS).comp
        (contMDiff_snd :
          ContMDiff
            ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
            (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) fun p : S × S ↦ p.2)
  have hmulAmbient : ContMDiff
      ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      (I(n)) (⊤ : WithTop ℕ∞) fun p : S × S ↦
        (p.1 : GL (Fin n) ℂ) * (p.2 : GL (Fin n) ℂ) := by
    -- Ambient multiplication is smooth, so the restricted ambient product is smooth as well.
    simpa using hfst.mul hsnd
  have hmulSubtype : ContMDiff
      ((modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞)
      (Set.codRestrict
        (fun p : S × S ↦ (p.1 : GL (Fin n) ℂ) * (p.2 : GL (Fin n) ℂ))
        (S : Set (GL (Fin n) ℂ))
        (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)) :=
    contMDiff_toSubtype_of_isEmbeddedSubmanifold
      (I := I(n))
      (J := modelWithCornersSelf ℝ F)
      (K := (modelWithCornersSelf ℝ F).prod (modelWithCornersSelf ℝ F))
      hmulAmbient
      (fun p : S × S ↦ S.mul_mem p.1.property p.2.property)
  -- Rewrite the codomain-restricted ambient product into the subgroup multiplication.
  rw [embeddedSubgroupMul_codRestrict_eq (n := n) (S := S)] at hmulSubtype
  exact hmulSubtype

/-- Helper for Problem 7-13: the ambient inversion on an embedded subgroup of `GL(n, ℂ)`
restricts to the intrinsic subgroup inverse. -/
lemma embeddedSubgroupInv_codRestrict_eq
    (S : Subgroup (GL (Fin n) ℂ)) :
    Set.codRestrict
      (fun x : S ↦ ((x : GL (Fin n) ℂ)⁻¹))
      (S : Set (GL (Fin n) ℂ))
      (fun x : S ↦ S.inv_mem x.property)
      =
      (fun x : S ↦ x⁻¹) := rfl

/-- Helper for Problem 7-13: inversion is smooth on an embedded subgroup of `GL(n, ℂ)` with its
induced manifold structure. -/
lemma embeddedSubgroupInv_contMDiff
    (S : Subgroup (GL (Fin n) ℂ)) [ChartedSpace F S]
    [IsManifold (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I(n) (modelWithCornersSelf ℝ F) (S : Set (GL (Fin n) ℂ))) :
    ContMDiff (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ F)
      (⊤ : WithTop ℕ∞) (fun x : S ↦ x⁻¹) := by
  have hinvAmbient : ContMDiff (modelWithCornersSelf ℝ F) (I(n))
      (⊤ : WithTop ℕ∞) fun x : S ↦ ((x : GL (Fin n) ℂ)⁻¹) := by
    -- Ambient inversion is smooth after precomposing with the smooth subtype inclusion.
    simpa using
      (embeddedSubgroupSubtypeVal_contMDiff (n := n) (F := F) S hS).inv
  have hinvSubtype : ContMDiff
      (modelWithCornersSelf ℝ F) (modelWithCornersSelf ℝ F)
      (⊤ : WithTop ℕ∞)
      (Set.codRestrict
        (fun x : S ↦ ((x : GL (Fin n) ℂ)⁻¹))
        (S : Set (GL (Fin n) ℂ))
        (fun x : S ↦ S.inv_mem x.property)) :=
    contMDiff_toSubtype_of_isEmbeddedSubmanifold
      (I := I(n))
      (J := modelWithCornersSelf ℝ F)
      (K := modelWithCornersSelf ℝ F)
      hinvAmbient
      (fun x : S ↦ S.inv_mem x.property)
  -- Rewrite the codomain-restricted ambient inverse into the subgroup inverse.
  rw [embeddedSubgroupInv_codRestrict_eq (n := n) (S := S)] at hinvSubtype
  exact hinvSubtype

/-- Helper for Problem 7-13: an embedded subgroup of `GL(n, ℂ)` inherits a Lie-group structure
from the ambient Lie group. -/
lemma embeddedSubgroupLieGroup
    (S : Subgroup (GL (Fin n) ℂ)) [ChartedSpace F S]
    [IsManifold (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold I(n) (modelWithCornersSelf ℝ F) (S : Set (GL (Fin n) ℂ))) :
    LieGroup (modelWithCornersSelf ℝ F) (⊤ : WithTop ℕ∞) S := by
  -- The Lie-group axioms reduce exactly to smoothness of multiplication and inversion.
  refine
    { contMDiff_mul := embeddedSubgroupMul_contMDiff (n := n) (F := F) S hS
      contMDiff_inv := embeddedSubgroupInv_contMDiff (n := n) (F := F) S hS }

/-- Helper for Problem 7-13: the canonical monoid homomorphism from `U(n)` into `GL(n, ℂ)` used
to define the ambient subgroup. -/
abbrev unitarySubgroupToGeneralLinearGroup (n : ℕ) : U(n) →* GL (Fin n) ℂ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℂ ≃*
      LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      U(n) →* LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ)))

/-- Helper for Problem 7-13: the chosen embedding of `U(n)` into `GL(n, ℂ)` keeps the underlying
matrix unchanged. -/
lemma unitarySubgroupToGeneralLinearGroup_coe (A : U(n)) :
    ↑(unitarySubgroupToGeneralLinearGroup n A) = (A : M(n)) := by
  -- Compare the two `GL` elements entrywise after expanding the defining matrix/linear maps.
  ext i j
  simp [unitarySubgroupToGeneralLinearGroup, Matrix.UnitaryGroup.embeddingGL,
    Matrix.UnitaryGroup.toGL]

/-- Helper for Problem 7-13: membership in the subgroup image is equivalent to the usual unitary
matrix equation `Aᴴ * A = 1`. -/
lemma mem_unitarySubgroupInGeneralLinearGroup_iff (A : GL (Fin n) ℂ) :
    A ∈ unitarySubgroupInGeneralLinearGroup n ↔ ((↑A : M(n))ᴴ * ↑A = 1) := by
  constructor
  · intro hA
    rcases Subgroup.mem_map.mp hA with ⟨U, -, hU⟩
    -- Transport the unitary equation from the source matrix `U` to the ambient `GL` matrix `A`.
    have hMatrix : (↑A : M(n)) = (U : M(n)) := by
      rw [← hU, unitarySubgroupToGeneralLinearGroup_coe]
    simpa [hMatrix, star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  · intro hA
    -- Package the ambient matrix `A` itself as a unitary matrix and map it into the subgroup.
    let U : U(n) := ⟨(A : M(n)), (Matrix.mem_unitaryGroup_iff').2 hA⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨U, by simp, ?_⟩
    -- The image element has the same underlying matrix as `A`, so the `GL` elements are equal.
    ext i j
    simp [U, unitarySubgroupToGeneralLinearGroup_coe]

/-- Helper for Problem 7-13: the matrix `Aᴴ * A` is self-adjoint for every `A ∈ GL(n, ℂ)`. -/
lemma unitaryGramMatrix_isSelfAdjoint (A : GL (Fin n) ℂ) :
    IsSelfAdjoint (((↑A : M(n))ᴴ) * ↑A) := by
  -- The Gram matrix is fixed by conjugate transpose because `(Bᴴ * B)ᴴ = Bᴴ * B`.
  change ((((↑A : M(n))ᴴ * ↑A)ᴴ) = ((↑A : M(n))ᴴ * ↑A))
  simpa using Matrix.conjTranspose_mul ((↑A : M(n))ᴴ) (↑A : M(n))

/-- Helper for Problem 7-13: the carrier of `U(n)` is closed in the ambient matrix space. -/
lemma isClosed_unitaryGroupCarrier (n : ℕ) :
    IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (M(n))) := by
  let f : M(n) → M(n) := fun A ↦ star A * A
  have hf : Continuous f := by
    -- The Gram map is continuous because conjugate transpose and matrix multiplication are.
    simpa [f] using continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  -- A matrix is unitary exactly when it maps to `1` under the Gram map.
  rw [show (Matrix.unitaryGroup (Fin n) ℂ : Set (M(n))) = f ⁻¹' ({1} : Set (M(n))) by
        ext A
        simp [f, Matrix.mem_unitaryGroup_iff']]
  exact IsClosed.preimage hf isClosed_singleton

/-- Helper for Problem 7-13: the subgroup carrier inside `GL(n, ℂ)` is closed. -/
lemma isClosed_unitarySubgroupInGeneralLinearGroupCarrier (n : ℕ) :
    IsClosed (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := by
  let f : GL (Fin n) ℂ → M(n) := fun A ↦ (A : M(n))
  have hf : Continuous f := Units.continuous_val
  -- Rewrite the subgroup carrier as the preimage of the closed unitary locus in matrix space.
  rw [show (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) =
      f ⁻¹' (Matrix.unitaryGroup (Fin n) ℂ : Set (M(n))) by
        ext A
        simp [f, mem_unitarySubgroupInGeneralLinearGroup_iff, Matrix.mem_unitaryGroup_iff']]
  exact IsClosed.preimage hf (isClosed_unitaryGroupCarrier n)

/-- Helper for Problem 7-13: the ambient Gram map is the self-adjoint part of `Aᴴ * A`. -/
noncomputable def ambientUnitaryGramMap (n : ℕ) : M(n) → SA(n) :=
  fun A : M(n) ↦ selfAdjointPartL ℝ (Aᴴ * A)

/-- Helper for Problem 7-13: the Gram map on `GL(n, ℂ)` is the ambient Gram map restricted along
the matrix inclusion. -/
noncomputable def unitaryGramMap (n : ℕ) : GL (Fin n) ℂ → SA(n) :=
  fun A : GL (Fin n) ℂ ↦ ambientUnitaryGramMap n (A : M(n))

/-- Helper for Problem 7-13: coercing the ambient Gram map back to matrices recovers `Aᴴ * A`. -/
lemma ambientUnitaryGramMap_coe (A : M(n)) :
    ((ambientUnitaryGramMap n A : SA(n)) : M(n)) = Aᴴ * A := by
  -- The Gram matrix is already self-adjoint, so the self-adjoint projection is the identity.
  simp [ambientUnitaryGramMap, IsSelfAdjoint.coe_selfAdjointPart_apply,
    IsSelfAdjoint.star_mul_self]

/-- Helper for Problem 7-13: coercing the `GL` Gram map back to matrices gives the usual Gram
matrix formula. -/
lemma unitaryGramMap_coe (A : GL (Fin n) ℂ) :
    ((unitaryGramMap n A : SA(n)) : M(n)) = ((↑A : M(n))ᴴ) * ↑A := by
  -- The `GL` Gram map is just the ambient one evaluated on the underlying matrix.
  simpa [unitaryGramMap] using ambientUnitaryGramMap_coe (n := n) (A := (A : M(n)))

/-- Helper for Problem 7-13: the fiber of `unitaryGramMap` over `1` is the canonical subgroup
copy of `U(n)` inside `GL(n, ℂ)`. -/
lemma unitarySubgroupInGeneralLinearGroup_eq_gramFiber (n : ℕ) :
    (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) =
      unitaryGramMap n ⁻¹' ({1} : Set (SA(n))) := by
  -- Compare membership after forgetting the self-adjoint structure on the codomain.
  ext A
  simp [mem_unitarySubgroupInGeneralLinearGroup_iff, unitaryGramMap_coe]

/-- Helper for Problem 7-13: the linearized ambient Gram map before projecting to the
self-adjoint part. -/
noncomputable def ambientUnitaryGramRawDeriv (A : M(n)) : M(n) →L[ℝ] M(n) :=
  ((↑A : M(n))ᴴ) • ContinuousLinearMap.id ℝ (M(n)) +
    (starL' ℝ : M(n) →L[ℝ] M(n)) <• (A : M(n))

/-- Helper for Problem 7-13: the Fréchet derivative of the ambient Gram map. -/
noncomputable def ambientUnitaryGramDeriv (A : M(n)) : M(n) →L[ℝ] SA(n) :=
  (selfAdjointPartL ℝ : M(n) →L[ℝ] SA(n)).comp (ambientUnitaryGramRawDeriv (n := n) A)

/-- Helper for Problem 7-13: the ambient Gram map is smooth. -/
lemma ambientUnitaryGramMap_contMDiff :
    ContMDiff (I(n)) (modelWithCornersSelf ℝ (SA(n))) ∞ (ambientUnitaryGramMap n) := by
  -- The map is the composition of a polynomial matrix map with the continuous linear
  -- self-adjoint projection.
  simpa [ambientUnitaryGramMap] using
    (selfAdjointPartL ℝ : M(n) →L[ℝ] SA(n)).contMDiff.comp
      (((starL' ℝ : M(n) →L[ℝ] M(n)).contMDiff).mul contMDiff_id)

/-- Helper for Problem 7-13: the ambient Gram derivative is obtained by differentiating `Aᴴ * A`
in matrix space and then projecting to the self-adjoint part. -/
lemma ambientUnitaryGramMap_hasFDerivAt (A : M(n)) :
    HasFDerivAt (ambientUnitaryGramMap n) (ambientUnitaryGramDeriv (n := n) A) A := by
  -- Route correction: compute the derivative in ambient matrix space first and only then apply
  -- the continuous linear self-adjoint projection.
  have hraw :
      HasFDerivAt (fun B : M(n) ↦ Bᴴ * B) (ambientUnitaryGramRawDeriv (n := n) A) A := by
    simpa [ambientUnitaryGramRawDeriv] using
      ((starL' ℝ : M(n) →L[ℝ] M(n)).hasFDerivAt.mul'
        (ContinuousLinearMap.id ℝ (M(n))).hasFDerivAt :
        HasFDerivAt (fun B : M(n) ↦ Bᴴ * B)
          (((↑A : M(n))ᴴ) • ContinuousLinearMap.id ℝ (M(n)) +
            (starL' ℝ : M(n) →L[ℝ] M(n)) <• (A : M(n))) A)
  simpa [ambientUnitaryGramMap, ambientUnitaryGramDeriv] using
    ((selfAdjointPartL ℝ : M(n) →L[ℝ] SA(n)).hasFDerivAt.comp A hraw)

/-- Helper for Problem 7-13: applying the raw ambient Gram derivative has the expected matrix
formula `Aᴴ * X + Xᴴ * A`. -/
lemma ambientUnitaryGramRawDeriv_apply (A X : M(n)) :
    ambientUnitaryGramRawDeriv (n := n) A X = Aᴴ * X + Xᴴ * A := by
  -- Expand the bundled continuous linear map on a tangent vector.
  simp [ambientUnitaryGramRawDeriv, ContinuousLinearMap.add_apply]

/-- Helper for Problem 7-13: the raw ambient Gram derivative always lands in the self-adjoint
matrices. -/
lemma ambientUnitaryGramRawDeriv_isSelfAdjoint (A X : M(n)) :
    IsSelfAdjoint (ambientUnitaryGramRawDeriv (n := n) A X) := by
  -- The derivative is fixed by conjugate transpose because its two summands swap places.
  rw [ambientUnitaryGramRawDeriv_apply]
  change ((Aᴴ * X + Xᴴ * A)ᴴ) = Aᴴ * X + Xᴴ * A
  simp [Matrix.conjTranspose_mul, add_comm]

/-- Helper for Problem 7-13: on the unitary fiber, the ambient Gram derivative has the explicit
preimage `(1 / 2 : ℝ) • (A * H)` for each self-adjoint target `H`. -/
lemma ambientUnitaryGramDeriv_apply_witness {A : M(n)} (hA : Aᴴ * A = 1) (H : SA(n)) :
    ambientUnitaryGramDeriv (n := n) A ((1 / 2 : ℝ) • (A * (H : M(n)))) = H := by
  -- First rewrite the projected derivative back to the raw self-adjoint matrix identity.
  apply Subtype.ext
  have hself :
      IsSelfAdjoint
        (ambientUnitaryGramRawDeriv (n := n) A ((1 / 2 : ℝ) • (A * (H : M(n))))) :=
    ambientUnitaryGramRawDeriv_isSelfAdjoint (n := n) A ((1 / 2 : ℝ) • (A * (H : M(n))))
  rw [show ((ambientUnitaryGramDeriv (n := n) A ((1 / 2 : ℝ) • (A * (H : M(n))))) : M(n)) =
      ambientUnitaryGramRawDeriv (n := n) A ((1 / 2 : ℝ) • (A * (H : M(n)))) by
        simpa [ambientUnitaryGramDeriv] using hself.coe_selfAdjointPart_apply ℝ]
  rw [ambientUnitaryGramRawDeriv_apply]
  have hH : ((H : M(n))ᴴ) = (H : M(n)) := H.2.star_eq
  calc
    Aᴴ * ((1 / 2 : ℝ) • (A * (H : M(n)))) +
        (((1 / 2 : ℝ) • (A * (H : M(n))))ᴴ) * A
        = (1 / 2 : ℝ) • ((Aᴴ * A) * (H : M(n))) +
            (1 / 2 : ℝ) • (((H : M(n))ᴴ * Aᴴ) * A) := by
              simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, mul_assoc, hH]
    _ = (1 / 2 : ℝ) • (H : M(n)) + (1 / 2 : ℝ) • ((H : M(n))ᴴ) := by
      simp [hA, mul_assoc]
    _ = (H : M(n)) := by
      rw [hH]
      simpa [two_smul] using invOf_two_smul_add_invOf_two_smul ℝ (H : M(n))

/-- Helper for Problem 7-13: at a unitary point, the ambient Gram derivative is surjective. -/
lemma ambientUnitaryGramDeriv_surjective {A : M(n)} (hA : Aᴴ * A = 1) :
    Function.Surjective (ambientUnitaryGramDeriv (n := n) A) := by
  -- The explicit witness from the source proof solves the linear equation.
  intro H
  exact ⟨(1 / 2 : ℝ) • (A * (H : M(n))), ambientUnitaryGramDeriv_apply_witness (n := n) hA H⟩

/-- Helper for Problem 7-13: the Gram map on `GL(n, ℂ)` is smooth. -/
lemma unitaryGramMap_contMDiff :
    ContMDiff (I(n)) (modelWithCornersSelf ℝ (SA(n))) ∞ (unitaryGramMap n) := by
  -- Smoothness is inherited from the ambient Gram map and the smooth units inclusion.
  simpa [unitaryGramMap] using
    (ambientUnitaryGramMap_contMDiff (n := n)).comp
      (Units.contMDiff_val :
        ContMDiff (I(n)) (I(n)) ∞ (fun A : GL (Fin n) ℂ ↦ (A : M(n))))

/-- Helper for Problem 7-13: the manifold derivative of the `GL` Gram map is the ambient Gram
derivative composed with the derivative of the matrix inclusion. -/
lemma unitaryGramMap_mfderiv_eq_ambient_comp_val (A : GL (Fin n) ℂ) :
    mfderiv (I(n)) (modelWithCornersSelf ℝ (SA(n))) (unitaryGramMap n) A =
      (ambientUnitaryGramDeriv (n := n) (A : M(n))).comp
        (mfderiv (I(n)) (I(n)) (fun B : GL (Fin n) ℂ ↦ (B : M(n))) A) := by
  -- Apply the manifold chain rule to the literal composition through the units inclusion.
  have hAmbient :
      MDifferentiableAt (I(n)) (modelWithCornersSelf ℝ (SA(n))) (ambientUnitaryGramMap n)
        (A : M(n)) :=
    (ambientUnitaryGramMap_hasFDerivAt (n := n) (A := (A : M(n)))).hasMFDerivAt.mdifferentiableAt
  have hVal :
      MDifferentiableAt (I(n)) (I(n)) (fun B : GL (Fin n) ℂ ↦ (B : M(n))) A := by
    exact (Units.contMDiff_val :
      ContMDiff (I(n)) (I(n)) ∞ (fun B : GL (Fin n) ℂ ↦ (B : M(n)))).contMDiffAt.mdifferentiableAt
        (by simp)
  have hcomp := mfderiv_comp (x := A) hAmbient hVal
  rw [show mfderiv (I(n)) (modelWithCornersSelf ℝ (SA(n))) (ambientUnitaryGramMap n) (A : M(n)) =
      ambientUnitaryGramDeriv (n := n) (A : M(n)) by
        rw [mfderiv_eq_fderiv]
        exact (ambientUnitaryGramMap_hasFDerivAt (n := n) (A := (A : M(n)))).fderiv] at hcomp
  simpa [unitaryGramMap] using hcomp

/-- Helper for Problem 7-13: the derivative of the units inclusion is surjective because the
singleton chart on `GL(n, ℂ)` is the inclusion map itself. -/
lemma generalLinearGroup_val_mfderiv_surjective (A : GL (Fin n) ℂ) :
    Function.Surjective (mfderiv (I(n)) (I(n)) (fun B : GL (Fin n) ℂ ↦ (B : M(n))) A) := by
  -- In the units chart, the inclusion is literally `chartAt`, whose manifold derivative is
  -- surjective on its source.
  simpa using (chartAt (M(n)) A).mfderiv_surjective (by simp)

/-- Helper for Problem 7-13: the self-adjoint matrices in `M(n)` have real dimension `n^2`. -/
lemma selfAdjointMatrix_finrank_real (n : ℕ) :
    Module.finrank ℝ (SA(n)) = n ^ 2 := by
  -- Route correction: use the abstract decomposition into self- and skew-adjoint parts instead of
  -- an entrywise coordinate count.
  let eSkew : skewAdjoint (M(n)) ≃ₗ[ℝ] SA(n) :=
    LinearEquiv.ofBijective skewAdjoint.negISMul <| by
      constructor
      · intro X Y hXY
        apply Subtype.ext
        have hMul := congrArg (fun Z : SA(n) => (Complex.I : ℂ) • (Z : M(n))) hXY
        simpa using hMul
      · intro H
        refine ⟨⟨Complex.I • (H : M(n)), ?_⟩, ?_⟩
        · change ((Complex.I : ℂ) • (H : M(n)))ᴴ = -((Complex.I : ℂ) • (H : M(n)))
          simp [H.2.star_eq]
        · apply Subtype.ext
          simp
  let e :
      M(n) ≃ₗ[ℝ] SA(n) × SA(n) :=
    (StarModule.decomposeProdAdjoint ℝ (M(n))).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (SA(n))) eSkew)
  have hdim :
      Module.finrank ℝ (M(n)) = Module.finrank ℝ (SA(n) × SA(n)) := LinearEquiv.finrank_eq e
  have hMatrix : Module.finrank ℝ (M(n)) = 2 * n ^ 2 := by
    simp [M, Module.finrank_matrix, Complex.finrank_real_complex, pow_two, mul_assoc, mul_comm]
  rw [Module.finrank_prod] at hdim
  rw [hMatrix] at hdim
  omega

/-- Helper for Problem 7-13: `1` is a regular value of the `GL` Gram map. -/
lemma unitaryGramMap_isRegularValue_one :
    Manifold.IsRegularValue (I(n)) (modelWithCornersSelf ℝ (SA(n))) (unitaryGramMap n) 1 := by
  -- Check regularity pointwise on the fiber, then combine ambient surjectivity with the
  -- surjectivity of the units-chart derivative.
  rw [Manifold.isRegularValue_iff_forall_isRegularPoint]
  intro A hA
  rw [Manifold.isRegularPoint_iff_surjective_mfderiv]
  have hFiber : ((↑A : M(n))ᴴ) * ↑A = 1 := by
    exact congrArg (fun H : SA(n) => (H : M(n))) hA
  rw [unitaryGramMap_mfderiv_eq_ambient_comp_val (n := n) A]
  exact (ambientUnitaryGramDeriv_surjective (n := n) hFiber).comp
    (generalLinearGroup_val_mfderiv_surjective (n := n) A)

/-- Helper for Problem 7-13: the ambient matrix space has real dimension `2 * n^2`. -/
lemma complexMatrix_finrank_real (n : ℕ) :
    Module.finrank ℝ (M(n)) = 2 * n ^ 2 := by
  -- Rewrite the matrix space dimension as the product of the complex and matrix finranks.
  simp [M, Module.finrank_matrix, Complex.finrank_real_complex, pow_two, mul_assoc, mul_left_comm,
    mul_comm]

/-- Problem 7-13 (1): for each `n ≥ 1`, the canonical copy of `U(n)` in `GL(n, ℂ)` admits a Lie
subgroup structure whose model space has real dimension `n^2`. -/
theorem unitarySubgroupInGeneralLinearGroup_has_lieSubgroup_structure
    (hn : 0 < n) :
    ∃ (S : LieSubgroupGL(n)) (h_finiteDimensional : FiniteDimensional ℝ S.ModelSpace),
      S.carrier = unitarySubgroupInGeneralLinearGroup n ∧
      Module.finrank ℝ S.ModelSpace = n ^ 2 := by
  -- Route correction: build the Lie subgroup structure from the regular level set of the Gram map
  -- on `GL(n, ℂ)`, but do all linear-algebra calculations in ambient matrix space.
  let _ := hn
  let k : ℕ := Module.finrank ℝ (M(n)) - Module.finrank ℝ (SA(n))
  let K := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
  have hLevelSet :=
    regular_level_set_has_embedded_submanifold_structure
      (I := I(n)) (J := modelWithCornersSelf ℝ (SA(n)))
      (Φ := unitaryGramMap n) (c := (1 : SA(n)))
      (unitaryGramMap_contMDiff (n := n)) (unitaryGramMap_isRegularValue_one (n := n))
  dsimp [k, K] at hLevelSet
  rcases hLevelSet with ⟨cs, hs, hEmbedded, _⟩
  have cs' : ChartedSpace (EuclideanSpace ℝ (Fin k))
      (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := by
    simpa [unitarySubgroupInGeneralLinearGroup_eq_gramFiber (n := n)] using cs
  have hs' : IsManifold K ∞ (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := by
    simpa [unitarySubgroupInGeneralLinearGroup_eq_gramFiber (n := n)] using hs
  have hEmbedded' :
      IsEmbeddedSubmanifold I(n) K (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := by
    simpa [unitarySubgroupInGeneralLinearGroup_eq_gramFiber (n := n)] using hEmbedded
  let S : LieSubgroupGL(n) := by
    classical
    refine
      { carrier := unitarySubgroupInGeneralLinearGroup n
        ModelSpace := EuclideanSpace ℝ (Fin k)
        instNormedAddCommGroupModelSpace := inferInstance
        instNormedSpaceModelSpace := inferInstance
        instTopologicalSpaceCarrier := inferInstance
        instChartedSpaceCarrier := cs'
        instLieGroupCarrier := ?_
        subtype_val_isImmersion := ?_ }
    · let _ : ChartedSpace (EuclideanSpace ℝ (Fin k))
          (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := cs'
      let _ : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))) ∞
          (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) := hs'
      exact embeddedSubgroupLieGroup
        (n := n) (F := EuclideanSpace ℝ (Fin k))
        (S := unitarySubgroupInGeneralLinearGroup n) hEmbedded'
    · exact hEmbedded'.isSmoothEmbedding_subtype_val.isImmersion
  refine ⟨S, inferInstance, rfl, ?_⟩
  -- The regular-level-set model space has dimension `ambient - codomain = n^2`.
  dsimp [S, k]
  simp [complexMatrix_finrank_real, selfAdjointMatrix_finrank_real]
  omega

/-- Problem 7-13 (2): the canonical copy of `U(n)` in `GL(n, ℂ)` is properly embedded in the
ambient general linear group. -/
theorem unitarySubgroupInGeneralLinearGroup_isProperlyEmbedded
    (hn : 0 < n) :
    (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)).IsProperlyEmbedded := by
  -- The positivity hypothesis is part of the source statement, but closedness does not use it.
  let _ := hn
  have hClosed : IsClosed (unitarySubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℂ)) :=
    isClosed_unitarySubgroupInGeneralLinearGroupCarrier n
  -- Closed subsets are properly embedded in the Chapter 5 sense.
  exact hClosed.isProperlyEmbedded

end ComplexUnitaryLieSubgroup

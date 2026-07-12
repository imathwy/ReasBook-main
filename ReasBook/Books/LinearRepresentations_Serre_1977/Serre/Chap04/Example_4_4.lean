import Mathlib.Tactic.Recall
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

-- Semantic recall verified during statement shaping:
-- `ClosedSubgroup.instCompactSpaceSubtypeMem`,
-- `Matrix.of_mem_specialOrthogonalGroup_fin_two_iff`, and the relevant
-- standard group/topology APIs are already available.

universe u

/-- Helper for Example 4-4: every entry of a real special-orthogonal matrix lies in `[-1, 1]`. -/
private theorem specialOrthogonalGroupEntry_mem_Icc {n : ℕ}
    (A : Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ) (i j : Fin (n + 2)) :
    ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) i j) ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases Matrix.mem_specialOrthogonalGroup_iff.mp A.2 with ⟨h_orthogonal, _h_det⟩
  -- Orthogonality identifies the squared column norm with the corresponding diagonal entry of `1`.
  have hmul :
      ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)).transpose *
        (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin (n + 2)) (R := ℝ)).1 h_orthogonal
  have hcolumn :
      ∑ k : Fin (n + 2), ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) k j) ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
      congrFun (congrFun hmul j) j
  -- A single nonnegative summand is bounded by the whole column norm.
  have hentry_sq :
      ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) i j) ^ 2 ≤ 1 := by
    calc
      ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) i j) ^ 2 ≤
          ∑ k : Fin (n + 2), ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) k j) ^ 2 := by
        exact Finset.single_le_sum
          (fun k _hk ↦ sq_nonneg ((A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) k j))
          (Finset.mem_univ i)
      _ = 1 := hcolumn
  constructor
  · nlinarith [hentry_sq]
  · nlinarith [hentry_sq]

/-- Helper for Example 4-4: the real special-orthogonal carrier is a closed subset of the ambient
matrix space. -/
private theorem isClosed_specialOrthogonalGroupSet (n : ℕ) :
    IsClosed {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ |
      A ∈ Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ} := by
  have horthogonalClosed :
      IsClosed {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ | A.transpose * A = 1} := by
    -- Orthogonality is the zero set of the continuous map `A ↦ Aᵀ * A - 1`.
    exact isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const
  have hdeterminantClosed :
      IsClosed {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ | A.det = (1 : ℝ)} := by
    -- The determinant is continuous on finite-dimensional matrix spaces.
    exact isClosed_eq continuous_id.matrix_det continuous_const
  have hdescription :
      {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ |
        A ∈ Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ} =
        {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ | A.transpose * A = 1} ∩
          {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ | A.det = (1 : ℝ)} := by
    ext A
    simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff']
  rw [hdescription]
  exact horthogonalClosed.inter hdeterminantClosed

/-- Example 4-4 (1): for every Euclidean dimension `n + 2`, the rotation group about a fixed point,
formalized as `Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ`, is compact. -/
instance compactSpaceRotationGroupEuclidean (n : ℕ) :
    CompactSpace (Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ) := by
  -- View `SO(n + 2)` as a closed subset of the compact box of matrices with entries in `[-1, 1]`.
  have hbox :
      IsCompact ((Set.Icc (-1 : ℝ) 1).matrix :
        Set (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)) :=
    IsCompact.matrix isCompact_Icc
  have hsubset :
      {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ |
        A ∈ Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ} ⊆
        ((Set.Icc (-1 : ℝ) 1).matrix :
          Set (Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)) := by
    intro A hA
    simpa [Set.mem_matrix] using
      fun i j ↦ specialOrthogonalGroupEntry_mem_Icc ⟨A, hA⟩ i j
  have hcompactSet :
      IsCompact {A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ |
        A ∈ Matrix.specialOrthogonalGroup (Fin (n + 2)) ℝ} :=
    IsCompact.of_isClosed_subset hbox (isClosed_specialOrthogonalGroupSet n) hsubset
  simpa using (isCompact_iff_compactSpace.mp hcompactSet)

private def planeRotationGroupToCircle (A : Matrix.specialOrthogonalGroup (Fin 2) ℝ) : Circle :=
  ⟨Complex.mk (A.1 0 0) (A.1 1 0), by
    rcases Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp A.2 with
      ⟨h_diag, h_skew, h_norm⟩
    · have h_column : A.1 0 0 ^ 2 + A.1 1 0 ^ 2 = 1 := by
        simpa [h_skew, pow_two] using h_norm
      have h_column' : A.1 0 0 * A.1 0 0 + A.1 1 0 * A.1 1 0 = 1 := by
        simpa [pow_two] using h_column
      exact mem_sphere_zero_iff_norm.2 <| by
        simpa [Complex.norm_def, Complex.normSq_apply, Real.sqrt_one] using h_column'⟩

private def circleToPlaneRotationGroup :
    Circle →* Matrix.specialOrthogonalGroup (Fin 2) ℝ where
  toFun z := ⟨!![(z : ℂ).re, -((z : ℂ).im); (z : ℂ).im, (z : ℂ).re], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    constructor
    · rfl
    constructor
    · simp
    · simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' z w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Complex.mul_re, Complex.mul_im]
    all_goals ring_nf

private theorem planeRotationGroupToCircle_leftInverse :
    Function.LeftInverse planeRotationGroupToCircle circleToPlaneRotationGroup := by
  intro z
  apply Circle.ext
  rfl

private theorem planeRotationGroupToCircle_rightInverse :
    Function.RightInverse planeRotationGroupToCircle circleToPlaneRotationGroup := by
  intro A
  apply Subtype.ext
  ext i j
  rcases Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp A.2 with
    ⟨h_diag, h_skew, h_norm⟩
  fin_cases i <;> fin_cases j
  · rfl
  · simpa [planeRotationGroupToCircle, circleToPlaneRotationGroup] using h_skew.symm
  · rfl
  · simpa [planeRotationGroupToCircle, circleToPlaneRotationGroup] using h_diag

private theorem circleToPlaneRotationGroup_injective :
    Function.Injective circleToPlaneRotationGroup :=
  planeRotationGroupToCircle_leftInverse.injective

private theorem planeRotationGroupToCircle_map_mul
    (A B : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    planeRotationGroupToCircle (A * B) =
      planeRotationGroupToCircle A * planeRotationGroupToCircle B := by
  apply circleToPlaneRotationGroup_injective
  rw [planeRotationGroupToCircle_rightInverse (A * B), map_mul,
    planeRotationGroupToCircle_rightInverse A, planeRotationGroupToCircle_rightInverse B]

/-- Example 4-4 (2): the plane-rotation group `Matrix.specialOrthogonalGroup (Fin 2) ℝ`
is canonically equivalent to `Circle ≃ S¹`. -/
def planeRotationGroupEquivCircle :
    Matrix.specialOrthogonalGroup (Fin 2) ℝ ≃* Circle where
  toFun := planeRotationGroupToCircle
  invFun := circleToPlaneRotationGroup
  left_inv := planeRotationGroupToCircle_rightInverse
  right_inv := planeRotationGroupToCircle_leftInverse
  map_mul' := planeRotationGroupToCircle_map_mul

/-- The equivalence `planeRotationGroupEquivCircle` sends a plane rotation matrix to the point of
`Circle` whose real part is the first entry of the first column. -/
@[simp] theorem planeRotationGroupEquivCircle_re
    (A : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    Complex.re (planeRotationGroupEquivCircle A) =
      (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := rfl

/-- The equivalence `planeRotationGroupEquivCircle` sends a plane rotation matrix to the point of
`Circle` whose imaginary part is the second entry of the first column. -/
@[simp] theorem planeRotationGroupEquivCircle_im
    (A : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
    Complex.im (planeRotationGroupEquivCircle A) =
      (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := rfl

/-- The inverse of `planeRotationGroupEquivCircle` sends `z : Circle` to the standard rotation
matrix with entries `re z` and `im z`. -/
@[simp] theorem planeRotationGroupEquivCircle_symm_toMatrix (z : Circle) :
    ((planeRotationGroupEquivCircle.symm z : Matrix.specialOrthogonalGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![Complex.re z, -Complex.im z; Complex.im z, Complex.re z] :=
  rfl

/- Example 4-4 (3): every closed subgroup of a compact topological group is compact.
This is the canonical instance `ClosedSubgroup.instCompactSpaceSubtypeMem`, already recalled in
`Serre/Chap04/Proposition_4_3.lean`. -/
recall ClosedSubgroup.instCompactSpaceSubtypeMem

/- Example 4-4 (4): the translation group of `EuclideanSpace ℝ (Fin (n + 1))`, identified with
the additive group of translation vectors `a` in `x ↦ x + a`, is not compact.
This is an immediate specialization of the canonical instance
`RealNormedSpace.noncompactSpace`. -/
recall RealNormedSpace.noncompactSpace

/-- The quadratic form `x^2 + y^2 + z^2 - t^2` on `ℝ^4`. -/
noncomputable def lorentzQuadraticForm : QuadraticForm ℝ (Fin 4 → ℝ) :=
  QuadraticMap.weightedSumSquares ℝ fun i ↦ if i = 3 then (-1 : ℝ) else 1

/-- The Lorentz quadratic form is `x^2 + y^2 + z^2 - t^2` in coordinates. -/
theorem lorentzQuadraticForm_apply (v : Fin 4 → ℝ) :
    lorentzQuadraticForm v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 - v 3 ^ 2 := by
  simp [lorentzQuadraticForm, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four,
    pow_two, sub_eq_add_neg, add_assoc]

/-- Helper for Example 4-4: the linear action attached to `A * B` is the composition of the
actions of `B` and `A`. -/
private theorem lorentzAction_mul_apply (A B : GL (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    (Matrix.GeneralLinearGroup.toLin (A * B)).toLinearEquiv v =
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv
        ((Matrix.GeneralLinearGroup.toLin B).toLinearEquiv v) := by
  -- The matrix `toLin` map and `toLinearEquiv` both respect multiplication.
  simp

/-- Helper for Example 4-4: the linear action of `A` cancels the action of `A⁻¹`. -/
private theorem lorentzAction_inv_apply_apply (A : GL (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv
      ((Matrix.GeneralLinearGroup.toLin A⁻¹).toLinearEquiv v) = v := by
  -- In the general linear group, the induced linear equivalence of the inverse is the inverse
  -- equivalence.
  simpa [LinearMap.GeneralLinearGroup.toLinearEquiv_inv] using
    LinearEquiv.apply_symm_apply (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v

/-- Helper for Example 4-4: the identity matrix preserves `lorentzQuadraticForm`. -/
private theorem lorentzGroup_one_mem :
    (1 : GL (Fin 4) ℝ) ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v} := by
  -- The identity action fixes every vector.
  intro v
  simp

/-- Helper for Example 4-4: the Lorentz-preserving condition is stable under multiplication. -/
private theorem lorentzGroup_mul_mem {A B : GL (Fin 4) ℝ}
    (hA : A ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v})
    (hB : B ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v}) :
    A * B ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v} := by
  intro v
  -- Rewrite the product action as a composition and apply the two preservation hypotheses.
  rw [lorentzAction_mul_apply]
  rw [hA]
  exact hB v

/-- Helper for Example 4-4: the Lorentz-preserving condition is stable under inversion. -/
private theorem lorentzGroup_inv_mem {A : GL (Fin 4) ℝ}
    (hA : A ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v}) :
    A⁻¹ ∈ {A | ∀ v,
      lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
        lorentzQuadraticForm v} := by
  intro v
  -- Apply the preservation law to `A⁻¹ • v` and then cancel `A` against `A⁻¹`.
  have hA' := hA ((Matrix.GeneralLinearGroup.toLin A⁻¹).toLinearEquiv v)
  rw [lorentzAction_inv_apply_apply] at hA'
  exact hA'.symm

/-- The subgroup of `GL (Fin 4) ℝ` preserving `x^2 + y^2 + z^2 - t^2`. -/
def lorentzGroup : Subgroup (GL (Fin 4) ℝ) where
  carrier := {A | ∀ v,
    lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
      lorentzQuadraticForm v}
  one_mem' := lorentzGroup_one_mem
  mul_mem' := fun hA hB ↦ lorentzGroup_mul_mem hA hB
  inv_mem' := fun hA ↦ lorentzGroup_inv_mem hA

@[simp] theorem mem_lorentzGroup_iff (A : GL (Fin 4) ℝ) :
    A ∈ lorentzGroup ↔
      ∀ v,
        lorentzQuadraticForm ((Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v) =
          lorentzQuadraticForm v :=
  Iff.rfl

namespace lorentzGroup

/-- An element of `lorentzGroup` acts by an isometric automorphism of `lorentzQuadraticForm`. -/
noncomputable def toIsometryEquiv (A : lorentzGroup) :
    lorentzQuadraticForm.IsometryEquiv lorentzQuadraticForm where
  __ := (Matrix.GeneralLinearGroup.toLin (A : GL (Fin 4) ℝ)).toLinearEquiv
  map_app' := A.2

@[simp] theorem toIsometryEquiv_toLinearEquiv (A : lorentzGroup) :
    (lorentzGroup.toIsometryEquiv A).toLinearEquiv =
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv :=
  rfl

@[simp] theorem toIsometryEquiv_apply (A : lorentzGroup) (v : Fin 4 → ℝ) :
    lorentzGroup.toIsometryEquiv A v =
      (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v :=
  rfl

@[simp] theorem map_lorentzQuadraticForm (A : lorentzGroup) (v : Fin 4 → ℝ) :
    lorentzQuadraticForm (lorentzGroup.toIsometryEquiv A v) = lorentzQuadraticForm v :=
  (lorentzGroup.toIsometryEquiv A).map_app v

end lorentzGroup

private noncomputable def lorentzBoostMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
    0, 1, 0, 0;
    0, 0, Real.cosh t, Real.sinh t;
    0, 0, Real.sinh t, Real.cosh t]

private noncomputable def lorentzBoostGL (t : ℝ) : GL (Fin 4) ℝ :=
  ⟨lorentzBoostMatrix t, lorentzBoostMatrix (-t), by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzBoostMatrix, Matrix.mul_apply, Fin.sum_univ_four, Real.cosh_neg,
        Real.sinh_neg]
    all_goals try ring_nf
    all_goals simpa [sub_eq_add_neg, add_comm] using Real.cosh_sq_sub_sinh_sq t
  , by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lorentzBoostMatrix, Matrix.mul_apply, Fin.sum_univ_four, Real.cosh_neg,
        Real.sinh_neg]
    all_goals try ring_nf
    all_goals simpa [sub_eq_add_neg, add_comm] using Real.cosh_sq_sub_sinh_sq t⟩

private theorem lorentzBoost_mem (t : ℝ) : lorentzBoostGL t ∈ lorentzGroup := by
  intro v
  have hboost :
      (Matrix.GeneralLinearGroup.toLin (lorentzBoostGL t)).toLinearEquiv v =
        ![v 0, v 1, Real.cosh t * v 2 + Real.sinh t * v 3,
          Real.sinh t * v 2 + Real.cosh t * v 3] := by
    ext i
    fin_cases i <;>
      simp [lorentzBoostGL, lorentzBoostMatrix, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
  rw [hboost, lorentzQuadraticForm_apply, lorentzQuadraticForm_apply]
  simp [pow_two, sub_eq_add_neg, mul_add, add_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

private noncomputable def lorentzBoost (t : ℝ) : lorentzGroup :=
  ⟨lorentzBoostGL t, lorentzBoost_mem t⟩

private theorem lorentzBoost_coord (t : ℝ) :
    (lorentzBoost t).1 2 3 = Real.sinh t := by
  simp [lorentzBoost, lorentzBoostGL, lorentzBoostMatrix]

/-- Example 4-4 (5): the Lorentz group preserving `x^2 + y^2 + z^2 - t^2` is not compact. -/
instance noncompactSpaceLorentzGroup : NoncompactSpace lorentzGroup := by
  refine ⟨?_⟩
  intro h_compact
  letI : CompactSpace lorentzGroup := ⟨h_compact⟩
  let coord : lorentzGroup → ℝ := fun A ↦ ((A : GL (Fin 4) ℝ) 2) 3
  have hcoord : Continuous coord := by
    let row : lorentzGroup → Fin 4 → ℝ := fun A ↦ ((A : GL (Fin 4) ℝ) 2)
    have hrow : Continuous row :=
      Matrix.GeneralLinearGroup.continuous_apply
        (fun A : lorentzGroup ↦ (A : GL (Fin 4) ℝ)) continuous_subtype_val 2
    simpa [coord, row] using (continuous_apply 3).comp hrow
  have hsurj : Set.range coord = Set.univ := by
    ext r
    constructor
    · intro hr
      simp
    · intro _
      rcases Real.sinh_surjective r with ⟨t, rfl⟩
      exact ⟨lorentzBoost t, lorentzBoost_coord t⟩
  have hcompactRange : IsCompact (Set.range coord) := isCompact_range hcoord
  rw [hsurj] at hcompactRange
  exact noncompact_univ ℝ hcompactRange

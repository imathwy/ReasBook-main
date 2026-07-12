import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Domain sampling: the primary domain is the quaternion unit sphere and its standard matrix model.
-- The owner declarations inspected before refinement were `unitSphereToUnits`,
-- `Matrix.specialUnitaryGroup`, `Matrix.mem_specialUnitaryGroup_iff`, and `ContinuousMulEquiv`.
-- Source-facing primitive data are points of `sphere (0 : ℍ) 1`; the `SU(2)` realization is a
-- bridge/view of that owner, so the public API below stays rooted in the sphere rather than a
-- duplicate subgroup wrapper or an ad hoc `SU2` alias.

open scoped Quaternion
open scoped MatrixGroups
open Metric (sphere)

local notation "SU(" n ")" => Matrix.specialUnitaryGroup (Fin n) ℂ
local notation "QuaternionSphere" => sphere (0 : ℍ) 1

/-- Helper for Problem 7-23: `unitSphereToUnits ℍ` is continuous on the quaternion unit sphere. -/
lemma continuous_unitSphereToUnitsQuaternion :
    Continuous (unitSphereToUnits ℍ : QuaternionSphere → ℍˣ) := by
  -- `Units.continuous_iff` reduces continuity into the units group to the value and inverse-value
  -- coordinates, both of which come from the ambient quaternion topology.
  rw [Units.continuous_iff]
  constructor
  · simpa using continuous_subtype_val
  · simpa using (continuous_subtype_val.inv₀ ne_zero_of_mem_unit_sphere)

/-- Problem 7-23 (1): the unit quaternions, canonically realized as `sphere (0 : ℍ) 1`, embed
as a closed subgroup of the Lie group `ℍˣ` through `unitSphereToUnits ℍ`. -/
theorem quaternionSphere_isClosedEmbedding_unitSphereToUnits :
    Topology.IsClosedEmbedding (unitSphereToUnits ℍ : QuaternionSphere → ℍˣ) := by
  letI : CompactSpace QuaternionSphere := Metric.sphere.compactSpace (0 : ℍ) 1
  -- A continuous injective map from a compact space into a Hausdorff space is a closed embedding.
  exact Continuous.isClosedEmbedding
    continuous_unitSphereToUnitsQuaternion
    unitSphereToUnits_injective

/-- Helper for Problem 7-23: the standard `2 × 2` complex matrix attached to a quaternion. -/
def quaternionToSpecialUnitaryMatrix (q : ℍ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((q.re : ℂ) + (q.imI : ℂ) * Complex.I), ((q.imJ : ℂ) + (q.imK : ℂ) * Complex.I);
    (-(q.imJ : ℂ) + (q.imK : ℂ) * Complex.I), ((q.re : ℂ) - (q.imI : ℂ) * Complex.I)]

/-- Helper for Problem 7-23: the `(0,0)` entry of the quaternion matrix model is multiplicative. -/
lemma quaternionToSpecialUnitaryMatrix_mul_apply_zero_zero (p q : ℍ) :
    quaternionToSpecialUnitaryMatrix (p * q) 0 0 =
      (quaternionToSpecialUnitaryMatrix p * quaternionToSpecialUnitaryMatrix q) 0 0 := by
  -- The top-left entry is the complex form of the scalar and `i`-component multiplication laws.
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

/-- Helper for Problem 7-23: the `(0,1)` entry of the quaternion matrix model is multiplicative. -/
lemma quaternionToSpecialUnitaryMatrix_mul_apply_zero_one (p q : ℍ) :
    quaternionToSpecialUnitaryMatrix (p * q) 0 1 =
      (quaternionToSpecialUnitaryMatrix p * quaternionToSpecialUnitaryMatrix q) 0 1 := by
  -- The top-right entry packages the `j`- and `k`-component multiplication formulas.
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

/-- Helper for Problem 7-23: the `(1,0)` entry of the quaternion matrix model is multiplicative. -/
lemma quaternionToSpecialUnitaryMatrix_mul_apply_one_zero (p q : ℍ) :
    quaternionToSpecialUnitaryMatrix (p * q) 1 0 =
      (quaternionToSpecialUnitaryMatrix p * quaternionToSpecialUnitaryMatrix q) 1 0 := by
  -- The bottom-left entry is the conjugate companion of the top-right entry.
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

/-- Helper for Problem 7-23: the `(1,1)` entry of the quaternion matrix model is multiplicative. -/
lemma quaternionToSpecialUnitaryMatrix_mul_apply_one_one (p q : ℍ) :
    quaternionToSpecialUnitaryMatrix (p * q) 1 1 =
      (quaternionToSpecialUnitaryMatrix p * quaternionToSpecialUnitaryMatrix q) 1 1 := by
  -- The bottom-right entry is the conjugate companion of the top-left entry.
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring

/-- Helper for Problem 7-23: the quaternion matrix model is multiplicative. -/
lemma quaternionToSpecialUnitaryMatrix_mul (p q : ℍ) :
    quaternionToSpecialUnitaryMatrix (p * q) =
      quaternionToSpecialUnitaryMatrix p * quaternionToSpecialUnitaryMatrix q := by
  -- The global matrix identity is assembled from the four entrywise computations above.
  ext i j
  fin_cases i
  · fin_cases j
    · exact quaternionToSpecialUnitaryMatrix_mul_apply_zero_zero p q
    · exact quaternionToSpecialUnitaryMatrix_mul_apply_zero_one p q
  · fin_cases j
    · exact quaternionToSpecialUnitaryMatrix_mul_apply_one_zero p q
    · exact quaternionToSpecialUnitaryMatrix_mul_apply_one_one p q

/-- Helper for Problem 7-23: the quaternion matrix model has determinant `Quaternion.normSq q`. -/
lemma quaternionToSpecialUnitaryMatrix_det (q : ℍ) :
    Matrix.det (quaternionToSpecialUnitaryMatrix q) = (((Quaternion.normSq q : ℝ) : ℂ)) := by
  -- Expanding the `2 × 2` determinant recovers the quaternion norm-square formula.
  have hnorm :
      (((Quaternion.normSq q : ℝ) : ℂ)) =
        ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 : ℝ) : ℂ) := by
    exact congrArg (fun x : ℝ ↦ (x : ℂ)) (Quaternion.normSq_def' q)
  rw [hnorm]
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.det_fin_two_of, pow_two] <;>
    ring

/-- Helper for Problem 7-23: the `(0,0)` entry of `M(q) * star (M(q))` is `Quaternion.normSq q`. -/
lemma quaternionToSpecialUnitaryMatrix_mul_star_apply_zero_zero (q : ℍ) :
    (quaternionToSpecialUnitaryMatrix q * star (quaternionToSpecialUnitaryMatrix q)) 0 0 =
      (((((Quaternion.normSq q : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0) := by
  -- The diagonal entry collapses to the sum of the four squared coordinates.
  have hnorm :
      (((Quaternion.normSq q : ℝ) : ℂ)) =
        ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 : ℝ) : ℂ) := by
    exact congrArg (fun x : ℝ ↦ (x : ℂ)) (Quaternion.normSq_def' q)
  rw [hnorm]
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;>
    ring

/-- Helper for Problem 7-23: the `(0,1)` entry of `M(q) * star (M(q))` vanishes. -/
lemma quaternionToSpecialUnitaryMatrix_mul_star_apply_zero_one (q : ℍ) :
    (quaternionToSpecialUnitaryMatrix q * star (quaternionToSpecialUnitaryMatrix q)) 0 1 =
      (((((Quaternion.normSq q : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 1) := by
  -- The off-diagonal terms cancel pairwise.
  simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-- Helper for Problem 7-23: the `(1,0)` entry of `M(q) * star (M(q))` vanishes. -/
lemma quaternionToSpecialUnitaryMatrix_mul_star_apply_one_zero (q : ℍ) :
    (quaternionToSpecialUnitaryMatrix q * star (quaternionToSpecialUnitaryMatrix q)) 1 0 =
      (((((Quaternion.normSq q : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 0) := by
  -- The other off-diagonal entry cancels by the same symmetry.
  simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-- Helper for Problem 7-23: the `(1,1)` entry of `M(q) * star (M(q))` is `Quaternion.normSq q`. -/
lemma quaternionToSpecialUnitaryMatrix_mul_star_apply_one_one (q : ℍ) :
    (quaternionToSpecialUnitaryMatrix q * star (quaternionToSpecialUnitaryMatrix q)) 1 1 =
      (((((Quaternion.normSq q : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 1 1) := by
  -- The second diagonal entry matches the same scalar norm-square.
  have hnorm :
      (((Quaternion.normSq q : ℝ) : ℂ)) =
        ((q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2 : ℝ) : ℂ) := by
    exact congrArg (fun x : ℝ ↦ (x : ℂ)) (Quaternion.normSq_def' q)
  rw [hnorm]
  apply Complex.ext <;>
    simp [quaternionToSpecialUnitaryMatrix, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;>
    ring

/-- Helper for Problem 7-23: the quaternion matrix model is unitary up to the scalar
`Quaternion.normSq q`. -/
lemma quaternionToSpecialUnitaryMatrix_mul_star (q : ℍ) :
    quaternionToSpecialUnitaryMatrix q * star (quaternionToSpecialUnitaryMatrix q) =
      ((((Quaternion.normSq q : ℝ) : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  -- The matrix identity is assembled from the four entrywise computations above.
  ext i j
  fin_cases i
  · fin_cases j
    · exact quaternionToSpecialUnitaryMatrix_mul_star_apply_zero_zero q
    · exact quaternionToSpecialUnitaryMatrix_mul_star_apply_zero_one q
  · fin_cases j
    · exact quaternionToSpecialUnitaryMatrix_mul_star_apply_one_zero q
    · exact quaternionToSpecialUnitaryMatrix_mul_star_apply_one_one q

/-- Helper for Problem 7-23: the matrix attached to a unit quaternion lies in `SU(2)`. -/
lemma quaternionToSpecialUnitaryMatrix_mem (q : QuaternionSphere) :
    quaternionToSpecialUnitaryMatrix (q : ℍ) ∈ SU(2) := by
  have hnorm : ‖(q : ℍ)‖ = 1 := by
    -- Membership in the sphere is exactly the unit-norm condition.
    simpa [Metric.mem_sphere, dist_eq_norm] using q.property
  have hnormSq : Quaternion.normSq (q : ℍ) = 1 := by
    simpa [Quaternion.normSq_eq_norm_mul_self, hnorm] using congrArg (fun r : ℝ ↦ r * r) hnorm
  refine (Matrix.mem_specialUnitaryGroup_iff).2 ?_
  constructor
  · -- The unitary condition is the normalized `M * star M = 1` identity.
    rw [Matrix.mem_unitaryGroup_iff]
    simpa [hnormSq] using quaternionToSpecialUnitaryMatrix_mul_star (q : ℍ)
  · -- The determinant is the same norm-square, hence also `1`.
    simpa [hnormSq] using quaternionToSpecialUnitaryMatrix_det (q : ℍ)

/-- Helper for Problem 7-23: the quaternion encoded by the first row of a special unitary matrix. -/
def specialUnitaryFirstRowQuaternion (A : SU(2)) : ℍ :=
  ⟨((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re,
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im,
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re,
    ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im⟩

/-- Helper for Problem 7-23: forget an `SU(2)` matrix to the corresponding element of `SL(2, ℂ)`. -/
def specialUnitaryToSpecialLinear (A : SU(2)) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨(A : Matrix (Fin 2) (Fin 2) ℂ), A.2.2⟩

/-- Helper for Problem 7-23: forgetting `star A` from `SU(2)` to `SL(2, ℂ)` agrees with
inversion. -/
lemma specialUnitaryToSpecialLinear_star_eq_inv (A : SU(2)) :
    specialUnitaryToSpecialLinear (star A) = (specialUnitaryToSpecialLinear A)⁻¹ := by
  -- Route correction: keep the inverse comparison inside `SL(2, ℂ)` so the proof only uses the
  -- subgroup identity `star A = A⁻¹`.
  apply eq_inv_iff_mul_eq_one.mpr
  ext i j
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M i j) A.2.1.1

/-- Helper for Problem 7-23: the conjugate transpose of an `SU(2)` matrix is the explicit
`SL₂` inverse matrix. -/
lemma specialUnitaryStar_eq_explicit (A : SU(2)) :
    star (A : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((A : Matrix (Fin 2) (Fin 2) ℂ) 1 1), -((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1);
        -((A : Matrix (Fin 2) (Fin 2) ℂ) 1 0), ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
  -- First forget the subgroup equality, then read the `SL₂` inverse formula entrywise.
  simpa [specialUnitaryToSpecialLinear] using
    congrArg Subtype.val ((specialUnitaryToSpecialLinear_star_eq_inv A).trans
      (Matrix.SpecialLinearGroup.SL2_inv_expl (specialUnitaryToSpecialLinear A)))

/-- Helper for Problem 7-23: the star of a complex number is `re - im * I`. -/
lemma complexStar_eq_re_sub_im_mul_I (z : ℂ) :
    star z = (z.re : ℂ) - z.im * Complex.I := by
  calc
    star z = ((star z).re : ℂ) + (star z).im * Complex.I := by
      symm
      exact Complex.re_add_im (star z)
    _ = (z.re : ℂ) - z.im * Complex.I := by
      simp [Complex.star_def, sub_eq_add_neg]

/-- Helper for Problem 7-23: the bottom-right entry of an `SU(2)` matrix is the conjugate of the
top-left entry. -/
lemma specialUnitaryMatrix_apply_one_one (A : SU(2)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 1 =
      star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
  -- Compare the `(0,0)` entry of the explicit `star` formula with the conjugate transpose.
  have hcompare :
      star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) =
        ((A : Matrix (Fin 2) (Fin 2) ℂ) 1 1) := by
    simpa [Matrix.star_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0)
        (specialUnitaryStar_eq_explicit A)
  simpa using hcompare.symm

/-- Helper for Problem 7-23: the bottom-left entry of an `SU(2)` matrix is minus the conjugate of
the top-right entry. -/
lemma specialUnitaryMatrix_apply_one_zero (A : SU(2)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) 1 0 =
      -star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) := by
  -- Compare the `(1,0)` entry of the explicit `star` formula with the conjugate transpose.
  have hcompare :
      star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) =
        -((A : Matrix (Fin 2) (Fin 2) ℂ) 1 0) := by
    simpa [Matrix.star_apply] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 1 0)
        (specialUnitaryStar_eq_explicit A)
  have := congrArg Neg.neg hcompare
  simpa using this.symm

/-- Helper for Problem 7-23: an `SU(2)` matrix is determined by its first row. -/
lemma specialUnitaryMatrix_eq_fromFirstRow (A : SU(2)) :
    (A : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0), ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1);
        (-star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1)),
        star ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
  -- Route correction: consume the already-isolated entry lemmas instead of replaying the inverse
  -- comparison inside the final extensionality proof.
  ext i j
  fin_cases i
  · fin_cases j
    · rfl
    · rfl
  · fin_cases j
    · simp [specialUnitaryMatrix_apply_one_zero A]
    · simpa using specialUnitaryMatrix_apply_one_one A

/-- Helper for Problem 7-23: the first-row quaternion reconstructed from `A : SU(2)` has
norm-square `1`. -/
lemma specialUnitaryFirstRowQuaternion_normSq (A : SU(2)) :
    Quaternion.normSq (specialUnitaryFirstRowQuaternion A) = 1 := by
  have hfirstRow :
      Complex.normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) +
        Complex.normSq ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) = 1 := by
    have hentry :
        ((A : Matrix (Fin 2) (Fin 2) ℂ) * star (A : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 =
          (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 := by
      exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 0) A.2.1.2
    -- The `(0,0)` entry of `A * star A = 1` is exactly the sum of the squared norms of the
    -- first-row entries.
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Complex.normSq_apply] using
      congrArg Complex.re hentry
  -- The reconstructed quaternion records those four real coordinates, so it has the same
  -- norm-square as the first row of `A`.
  simpa [specialUnitaryFirstRowQuaternion, Quaternion.normSq_def', Complex.normSq_apply,
    pow_two, add_assoc, add_left_comm, add_comm] using hfirstRow

/-- Helper for Problem 7-23: the first-row quaternion of an `SU(2)` matrix has unit norm. -/
lemma specialUnitaryFirstRow_memQuaternionSphere (A : SU(2)) :
    specialUnitaryFirstRowQuaternion A ∈ QuaternionSphere := by
  have hnormSq : Quaternion.normSq (specialUnitaryFirstRowQuaternion A) = 1 :=
    specialUnitaryFirstRowQuaternion_normSq A
  have hnormMul :
      ‖specialUnitaryFirstRowQuaternion A‖ * ‖specialUnitaryFirstRowQuaternion A‖ = 1 := by
    simpa [Quaternion.normSq_eq_norm_mul_self] using hnormSq
  have hnorm : ‖specialUnitaryFirstRowQuaternion A‖ = 1 := by
    -- A nonnegative real number with square `1` must itself be `1`.
    nlinarith [norm_nonneg (specialUnitaryFirstRowQuaternion A), hnormMul]
  -- Membership in the unit sphere is the unit-norm condition.
  rw [Metric.mem_sphere, dist_eq_norm]
  simpa using hnorm

/-- The standard matrix model of a unit quaternion `a + bi + cj + dk` as an element of `SU(2)`. -/
def quaternionSphereToSpecialUnitary (q : QuaternionSphere) : SU(2) :=
  ⟨quaternionToSpecialUnitaryMatrix (q : ℍ), quaternionToSpecialUnitaryMatrix_mem q⟩

/-- Recover the unit quaternion represented by a special unitary matrix via the first row of the
standard quaternion matrix model. -/
def specialUnitaryToQuaternionSphere (A : SU(2)) : QuaternionSphere :=
  ⟨specialUnitaryFirstRowQuaternion A, specialUnitaryFirstRow_memQuaternionSphere A⟩

/-- Helper for Problem 7-23: the first-row reconstruction is a left inverse to the quaternion
matrix model. -/
lemma quaternionSphereToSpecialUnitary_left_inv (q : QuaternionSphere) :
    specialUnitaryToQuaternionSphere (quaternionSphereToSpecialUnitary q) = q := by
  -- Unfolding the first row of the explicit quaternion matrix recovers the original coordinates.
  apply Subtype.ext
  ext <;> simp [specialUnitaryToQuaternionSphere, specialUnitaryFirstRowQuaternion,
    quaternionSphereToSpecialUnitary, quaternionToSpecialUnitaryMatrix]

/-- Helper for Problem 7-23: the quaternion matrix model is surjective with inverse given by the
first row. -/
lemma quaternionSphereToSpecialUnitary_right_inv (A : SU(2)) :
    quaternionSphereToSpecialUnitary (specialUnitaryToQuaternionSphere A) = A := by
  -- The shape lemma identifies the second row in terms of the first row.
  apply Subtype.ext
  simpa [quaternionSphereToSpecialUnitary, specialUnitaryToQuaternionSphere,
    specialUnitaryFirstRowQuaternion, quaternionToSpecialUnitaryMatrix,
    complexStar_eq_re_sub_im_mul_I, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (specialUnitaryMatrix_eq_fromFirstRow A).symm

/-- Helper for Problem 7-23: the quaternion matrix model is a homomorphism. -/
lemma quaternionSphereToSpecialUnitary_map_mul (x y : QuaternionSphere) :
    quaternionSphereToSpecialUnitary (x * y) =
      quaternionSphereToSpecialUnitary x * quaternionSphereToSpecialUnitary y := by
  -- The ambient matrix model is multiplicative, and the sphere multiplication is inherited from
  -- quaternion multiplication.
  apply Subtype.ext
  simpa [quaternionSphereToSpecialUnitary, Metric.unitSphere.coe_mul] using
    quaternionToSpecialUnitaryMatrix_mul (x : ℍ) (y : ℍ)

/-- Helper for Problem 7-23: the quaternion matrix model is continuous. -/
lemma quaternionSphereToSpecialUnitary_continuous :
    Continuous quaternionSphereToSpecialUnitary := by
  -- Continuity is checked on the ambient matrix coordinates before re-entering the subtype.
  have hRe : Continuous fun q : QuaternionSphere ↦ (((q : ℍ).re : ℂ)) :=
    (continuous_ofReal).comp (Quaternion.continuous_re.comp continuous_subtype_val)
  have hImI : Continuous fun q : QuaternionSphere ↦ (((q : ℍ).imI : ℂ)) :=
    (continuous_ofReal).comp (Quaternion.continuous_imI.comp continuous_subtype_val)
  have hImJ : Continuous fun q : QuaternionSphere ↦ (((q : ℍ).imJ : ℂ)) :=
    (continuous_ofReal).comp (Quaternion.continuous_imJ.comp continuous_subtype_val)
  have hImK : Continuous fun q : QuaternionSphere ↦ (((q : ℍ).imK : ℂ)) :=
    (continuous_ofReal).comp (Quaternion.continuous_imK.comp continuous_subtype_val)
  exact
    (show Continuous (fun q : QuaternionSphere ↦ quaternionToSpecialUnitaryMatrix (q : ℍ)) by
      refine continuous_matrix ?_
      intro i j
      fin_cases i
      · fin_cases j
        · simpa [quaternionToSpecialUnitaryMatrix] using hRe.add (hImI.mul continuous_const)
        · simpa [quaternionToSpecialUnitaryMatrix] using hImJ.add (hImK.mul continuous_const)
      · fin_cases j
        · simpa [quaternionToSpecialUnitaryMatrix] using hImJ.neg.add (hImK.mul continuous_const)
        · simpa [quaternionToSpecialUnitaryMatrix, sub_eq_add_neg] using
            hRe.sub (hImI.mul continuous_const)).subtype_mk _

/-- Helper for Problem 7-23: the first-row reconstruction from `SU(2)` is continuous. -/
lemma specialUnitaryToQuaternionSphere_continuous :
    Continuous specialUnitaryToQuaternionSphere := by
  -- Each quaternion coordinate is a continuous matrix-entry real or imaginary part.
  have h00 : Continuous fun A : SU(2) ↦ ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0) :=
    (continuous_apply_apply 0 0).comp continuous_subtype_val
  have h01 : Continuous fun A : SU(2) ↦ ((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1) :=
    (continuous_apply_apply 0 1).comp continuous_subtype_val
  have hTuple :
      Continuous fun A : SU(2) ↦
        (![(((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re),
          (((A : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im),
          (((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).re),
          (((A : Matrix (Fin 2) (Fin 2) ℂ) 0 1).im)] : EuclideanSpace ℝ (Fin 4)) := by
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa using Complex.continuous_re.comp h00
    · simpa using Complex.continuous_im.comp h00
    · simpa using Complex.continuous_re.comp h01
    · simpa using Complex.continuous_im.comp h01
  exact
    (show Continuous fun A : SU(2) ↦ specialUnitaryFirstRowQuaternion A by
      simpa [specialUnitaryFirstRowQuaternion] using
        (Quaternion.linearIsometryEquivTuple.symm.continuous.comp hTuple)).subtype_mk _

/-- Problem 7-23 (2): the unit quaternions are continuously group-isomorphic to `SU(2)`. -/
def quaternionSphereContinuousMulEquivSpecialUnitary : QuaternionSphere ≃ₜ* SU(2) where
  toFun := quaternionSphereToSpecialUnitary
  invFun := specialUnitaryToQuaternionSphere
  left_inv := quaternionSphereToSpecialUnitary_left_inv
  right_inv := quaternionSphereToSpecialUnitary_right_inv
  map_mul' := quaternionSphereToSpecialUnitary_map_mul
  continuous_toFun := quaternionSphereToSpecialUnitary_continuous
  continuous_invFun := specialUnitaryToQuaternionSphere_continuous

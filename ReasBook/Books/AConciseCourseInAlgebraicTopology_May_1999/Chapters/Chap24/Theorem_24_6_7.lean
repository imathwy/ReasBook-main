import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Theorem_24_6_6

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical mathlib owner surfaced for the source-side
-- algebraic datum on `EuclideanSpace ℝ (Fin n)`. This file therefore keeps the Euclidean
-- multiplication datum explicit and records only the concrete sphere-valued constructions that are
-- directly induced by it.

/-- A multiplication on `EuclideanSpace ℝ (Fin n)` with a unit and no zero divisors. -/
structure RealDivisionLikeMultiplication (n : ℕ) where
  /-- The bilinear multiplication map on `EuclideanSpace ℝ (Fin n)`. -/
  mul :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
  /-- The distinguished multiplicative unit. -/
  one : EuclideanSpace ℝ (Fin n)
  /-- Left multiplication by the distinguished unit is the identity. -/
  one_mul : ∀ x : EuclideanSpace ℝ (Fin n), mul one x = x
  /-- Right multiplication by the distinguished unit is the identity. -/
  mul_one : ∀ x : EuclideanSpace ℝ (Fin n), mul x one = x
  /-- The distinguished multiplicative unit is nonzero. -/
  one_ne_zero : one ≠ 0
  /-- The multiplication has no zero divisors. -/
  eq_zero_or_eq_zero_of_mul_eq_zero :
    ∀ {x y : EuclideanSpace ℝ (Fin n)}, mul x y = 0 → x = 0 ∨ y = 0

namespace RealDivisionLikeMultiplication

/-- The defining properties of a division-like multiplication on `EuclideanSpace ℝ (Fin n)`. -/
theorem spec {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    (∀ x : EuclideanSpace ℝ (Fin n), μ.mul μ.one x = x) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), μ.mul x μ.one = x) ∧
      μ.one ≠ 0 ∧
      ∀ ⦃x y : EuclideanSpace ℝ (Fin n)⦄, μ.mul x y = 0 → x = 0 ∨ y = 0 :=
  ⟨μ.one_mul, μ.mul_one, μ.one_ne_zero,
    fun {_ _} h ↦ μ.eq_zero_or_eq_zero_of_mul_eq_zero h⟩

/-- If both inputs are nonzero, then their product under a division-like multiplication is
nonzero. -/
theorem mul_ne_zero {n : ℕ} (μ : RealDivisionLikeMultiplication n)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (hy : y ≠ 0) :
    μ.mul x y ≠ 0 := by
  intro hxy
  rcases μ.eq_zero_or_eq_zero_of_mul_eq_zero hxy with hzero | hzero
  · exact hx hzero
  · exact hy hzero

/-- A division-like multiplication can exist only in positive dimension. -/
theorem pos {n : ℕ} (μ : RealDivisionLikeMultiplication n) : 0 < n := by
  by_contra hn
  have h0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst h0
  exact μ.one_ne_zero (Subsingleton.elim _ _)

/-- The ambient dimension, viewed as a positive natural number. -/
def toPNat {n : ℕ} (μ : RealDivisionLikeMultiplication n) : ℕ+ :=
  ⟨n, μ.pos⟩

@[simp] theorem coe_toPNat {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    (μ.toPNat : ℕ) = n := rfl

private theorem normalize_mem_metricSphere {m : ℕ}
    {v : EuclideanSpace ℝ (Fin m)} (hv : v ≠ 0) :
    NormedSpace.normalize v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  simpa [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv

private def spherePointTypeEq (n : ℕ) (hn : 0 < n) :
    ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = TopCat.sphere (n - 1) :=
  let hSphere : (n - 1) + 1 = n := Nat.succ_pred_eq_of_pos hn
  Eq.trans
    (congrArg (fun k ↦ ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1)) hSphere.symm)
    rfl

private def spherePointOfNonzeroVector (n : ℕ) (hn : 0 < n)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    TopCat.sphere (n - 1) :=
  let normalized : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    ⟨NormedSpace.normalize v, normalize_mem_metricSphere hv⟩
  cast (spherePointTypeEq n hn) (ULift.up normalized)

/-- The distinguished unit of a division-like multiplication determines a point of `S^(n - 1)`. -/
def unitSpherePoint {n : ℕ} (μ : RealDivisionLikeMultiplication n) : TopCat.sphere (n - 1) :=
  spherePointOfNonzeroVector n μ.pos μ.one μ.one_ne_zero

private def spherePointOfVector {n : ℕ} (μ : RealDivisionLikeMultiplication n)
    (v : EuclideanSpace ℝ (Fin n)) : TopCat.sphere (n - 1) :=
  if hv : v = 0 then
    μ.unitSpherePoint
  else
    spherePointOfNonzeroVector n μ.pos v hv

private def vectorOfSpherePoint (n : ℕ) (hn : 0 < n) (x : TopCat.sphere (n - 1)) :
    EuclideanSpace ℝ (Fin n) :=
  ((cast (spherePointTypeEq n hn).symm x).down : EuclideanSpace ℝ (Fin n))

private theorem vectorOfSpherePoint_ne_zero (n : ℕ) (hn : 0 < n)
    (x : TopCat.sphere (n - 1)) :
    vectorOfSpherePoint n hn x ≠ 0 := by
  have hnorm : ‖vectorOfSpherePoint n hn x‖ = 1 := by
    have hmem :
        (((cast (spherePointTypeEq n hn).symm x).down : Metric.sphere
          (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      (cast (spherePointTypeEq n hn).symm x).down.2
    rw [vectorOfSpherePoint]
    rwa [mem_sphere_zero_iff_norm] at hmem
  intro hx
  have : ‖vectorOfSpherePoint n hn x‖ = 0 := by simp [hx]
  linarith

private theorem spherePointOfNonzeroVector_smul_pos {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    spherePointOfNonzeroVector n hn (r • v) (smul_ne_zero hr.ne' hv) =
      spherePointOfNonzeroVector n hn v hv := by
  unfold spherePointOfNonzeroVector
  simp [NormedSpace.normalize_smul_of_pos hr]

private theorem spherePointOfVector_smul_pos {n : ℕ} (μ : RealDivisionLikeMultiplication n)
    {v : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    μ.spherePointOfVector (r • v) = μ.spherePointOfVector v := by
  by_cases hv : v = 0
  · subst hv
    simp [spherePointOfVector]
  · have hr0 : r ≠ 0 := hr.ne'
    simp [spherePointOfVector, hv, hr0, spherePointOfNonzeroVector_smul_pos μ.pos hv hr]

private theorem spherePointOfNonzeroVector_vectorOfSpherePoint (n : ℕ) (hn : 0 < n)
    (x : TopCat.sphere (n - 1)) :
    spherePointOfNonzeroVector n hn (vectorOfSpherePoint n hn x)
      (vectorOfSpherePoint_ne_zero n hn x) = x := by
  let y : ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    cast (spherePointTypeEq n hn).symm x
  have hnorm : ‖(y.down : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hmem :
        ((y.down : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
          EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      y.down.2
    rwa [mem_sphere_zero_iff_norm] at hmem
  have hy0 : (y.down : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
    intro hy0
    have : ‖(y.down : EuclideanSpace ℝ (Fin n))‖ = 0 := by simp [hy0]
    linarith
  unfold spherePointOfNonzeroVector vectorOfSpherePoint
  change
    cast (spherePointTypeEq n hn)
        (ULift.up
          (⟨NormedSpace.normalize (y.down : EuclideanSpace ℝ (Fin n)),
            normalize_mem_metricSphere hy0⟩ :
              Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) =
      x
  have hy_eq :
      (⟨NormedSpace.normalize (y.down : EuclideanSpace ℝ (Fin n)), normalize_mem_metricSphere hy0⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) = y.down := by
    apply Subtype.ext
    simp [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm]
  have hy_up :
      ULift.up
          ((⟨NormedSpace.normalize (y.down : EuclideanSpace ℝ (Fin n)),
              normalize_mem_metricSphere hy0⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) =
        y := by
    apply ULift.ext
    simpa using hy_eq
  rw [hy_up]
  simp [y]

private theorem spherePointOfVector_vectorOfSpherePoint {n : ℕ}
    (μ : RealDivisionLikeMultiplication n) (x : TopCat.sphere (n - 1)) :
    μ.spherePointOfVector (vectorOfSpherePoint n μ.pos x) = x := by
  simp [spherePointOfVector, vectorOfSpherePoint_ne_zero,
    spherePointOfNonzeroVector_vectorOfSpherePoint]

private theorem vectorOfSpherePoint_unitSpherePoint
    {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    vectorOfSpherePoint n μ.pos μ.unitSpherePoint = NormedSpace.normalize μ.one := by
  unfold RealDivisionLikeMultiplication.unitSpherePoint
    spherePointOfNonzeroVector vectorOfSpherePoint
  simp

/-- The normalized multiplication induced on `S^(n - 1)` by a division-like multiplication on
`EuclideanSpace ℝ (Fin n)`. -/
def sphereMultiplicationMap {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    C(TopCat.sphere (n - 1) × TopCat.sphere (n - 1), TopCat.sphere (n - 1)) where
  toFun := fun xy ↦
    μ.spherePointOfVector
      (μ.mul
        (vectorOfSpherePoint n μ.pos xy.1)
        (vectorOfSpherePoint n μ.pos xy.2))
  continuous_toFun := by
    sorry

/-- Left multiplication by the distinguished sphere point acts as the identity on the normalized
sphere multiplication induced by `μ`. -/
theorem sphereMultiplicationMap_left_unit {n : ℕ}
    (μ : RealDivisionLikeMultiplication n) :
    μ.sphereMultiplicationMap.comp
        ((ContinuousMap.const _ μ.unitSpherePoint).prodMk (ContinuousMap.id _)) =
      ContinuousMap.id _ := by
  ext x
  have hone : 0 < ‖μ.one‖ := norm_pos_iff.mpr μ.one_ne_zero
  have hmul :
      μ.mul (vectorOfSpherePoint n μ.pos μ.unitSpherePoint) (vectorOfSpherePoint n μ.pos x) =
        ‖μ.one‖⁻¹ • vectorOfSpherePoint n μ.pos x := by
    rw [vectorOfSpherePoint_unitSpherePoint]
    simp [NormedSpace.normalize, μ.one_mul]
  calc
    μ.sphereMultiplicationMap (μ.unitSpherePoint, x)
        = μ.spherePointOfVector
            (μ.mul (vectorOfSpherePoint n μ.pos μ.unitSpherePoint)
              (vectorOfSpherePoint n μ.pos x)) :=
      rfl
    _ = μ.spherePointOfVector (‖μ.one‖⁻¹ • vectorOfSpherePoint n μ.pos x) := by rw [hmul]
    _ = μ.spherePointOfVector (vectorOfSpherePoint n μ.pos x) := by
      exact spherePointOfVector_smul_pos μ (inv_pos.mpr hone)
    _ = x := spherePointOfVector_vectorOfSpherePoint μ x

/-- Right multiplication by the distinguished sphere point acts as the identity on the normalized
sphere multiplication induced by `μ`. -/
theorem sphereMultiplicationMap_right_unit {n : ℕ}
    (μ : RealDivisionLikeMultiplication n) :
    μ.sphereMultiplicationMap.comp
        ((ContinuousMap.id _).prodMk (ContinuousMap.const _ μ.unitSpherePoint)) =
      ContinuousMap.id _ := by
  ext x
  have hone : 0 < ‖μ.one‖ := norm_pos_iff.mpr μ.one_ne_zero
  have hmul :
      μ.mul (vectorOfSpherePoint n μ.pos x) (vectorOfSpherePoint n μ.pos μ.unitSpherePoint) =
        ‖μ.one‖⁻¹ • vectorOfSpherePoint n μ.pos x := by
    rw [vectorOfSpherePoint_unitSpherePoint]
    simp [NormedSpace.normalize, μ.mul_one]
  calc
    μ.sphereMultiplicationMap (x, μ.unitSpherePoint)
        = μ.spherePointOfVector
            (μ.mul (vectorOfSpherePoint n μ.pos x)
              (vectorOfSpherePoint n μ.pos μ.unitSpherePoint)) :=
      rfl
    _ = μ.spherePointOfVector (‖μ.one‖⁻¹ • vectorOfSpherePoint n μ.pos x) := by rw [hmul]
    _ = μ.spherePointOfVector (vectorOfSpherePoint n μ.pos x) := by
      exact spherePointOfVector_smul_pos μ (inv_pos.mpr hone)
    _ = x := spherePointOfVector_vectorOfSpherePoint μ x

/-- The canonical Chapter 24 multiplication-like datum on `S^(n - 1)` induced by a
division-like multiplication on `EuclideanSpace ℝ (Fin n)`. -/
def toSphereMultiplicationLike {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    SphereMultiplicationLike μ.toPNat where
  map := μ.sphereMultiplicationMap
  unit := μ.unitSpherePoint
  unit_mul_homotopy := by
    exact (ContinuousMap.HomotopyRel.refl (ContinuousMap.id _) {μ.unitSpherePoint}).cast
      (sphereMultiplicationMap_left_unit μ).symm rfl
  mul_unit_homotopy := by
    exact (ContinuousMap.HomotopyRel.refl (ContinuousMap.id _) {μ.unitSpherePoint}).cast
      (sphereMultiplicationMap_right_unit μ).symm rfl

@[simp] theorem toSphereMultiplicationLike_map {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    μ.toSphereMultiplicationLike.map = μ.sphereMultiplicationMap := rfl

@[simp] theorem toSphereMultiplicationLike_unit {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    μ.toSphereMultiplicationLike.unit = μ.unitSpherePoint := rfl

/-- Any explicit division-like multiplication on `EuclideanSpace ℝ (Fin n)` forces
`n = 1`, `n = 2`, `n = 4`, or `n = 8`. -/
theorem possibleDimensions {n : ℕ} (μ : RealDivisionLikeMultiplication n) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  letI : HSpace (TopCat.sphere ((μ.toPNat : ℕ) - 1)) :=
    instHSpaceSphereMultiplicationLike μ.toSphereMultiplicationLike
  simpa [μ.coe_toPNat] using hSpaceSphere_possibleDimensions μ.toPNat

end RealDivisionLikeMultiplication

/-- Theorem 24.6.7. If `EuclideanSpace ℝ (Fin n)` admits a bilinear multiplication with
identity and no zero divisors, then `n = 1`, `n = 2`, `n = 4`, or `n = 8`. -/
theorem realDivisionLikeMultiplication_possibleDimensions {n : ℕ}
    (hμ : Nonempty (RealDivisionLikeMultiplication n)) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  rcases hμ with ⟨μ⟩
  exact μ.possibleDimensions

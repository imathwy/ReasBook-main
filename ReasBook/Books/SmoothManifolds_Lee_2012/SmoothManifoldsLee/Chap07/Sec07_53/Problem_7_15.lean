import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.UnitaryGroup
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Definition_7_47_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Domain sampling: the source-facing comparison is between the standard matrix Lie groups
-- `Matrix.specialOrthogonalGroup (Fin 2) ℝ`, `Matrix.unitaryGroup (Fin 1) ℂ`, and the circle
-- group `Circle`. The theorem-level owner is `LieGroupIsomorphism`; the primitive comparison data
-- are the explicit multiplicative equivalences below, while smoothness is derived theorem data on
-- the standard matrix-space manifold models.

open scoped Matrix.Norms.Operator ContDiff Manifold MatrixGroups

local notation "SO(2)" => Matrix.specialOrthogonalGroup (Fin 2) ℝ
local notation "U(1)" => Matrix.unitaryGroup (Fin 1) ℂ

/-- The standard algebraic comparison `SO(2) → S¹`, sending a rotation matrix
`[[a, -b], [b, a]]` to `a + bi`. -/
def so2ToCircle (A : SO(2)) : Circle :=
  ⟨(((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I), by
    have hA :
        (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∧
          (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ∧
          (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 = 1 :=
      Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp A.property
    have hsq :
        ‖(((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
            (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I)‖ ^ 2 = 1 := by
      calc
        ‖(((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
            (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I)‖ ^ 2
            = Complex.normSq
                (((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
                  (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I) := by
                simpa using
                  Complex.sq_norm
                    (((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
                      (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I)
        _ = (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 := by
              simp [Complex.normSq_apply, pow_two]
        _ = (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ^ 2 := by
              rw [hA.2.1, neg_sq]
        _ = 1 := hA.2.2
    have hnorm :
        ‖(((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
            (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I)‖ = 1 := by
      have hnonneg :
          0 ≤ ‖(((A : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) +
              (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * Complex.I)‖ :=
        norm_nonneg _
      nlinarith [hsq]
    exact mem_sphere_zero_iff_norm.mpr hnorm⟩

/-- The inverse algebraic comparison `S¹ → SO(2)`, sending `a + bi` to the rotation matrix
`[[a, -b], [b, a]]`. -/
def circleToSO2 (z : Circle) : SO(2) :=
  ⟨!![(z : ℂ).re, -(z : ℂ).im; (z : ℂ).im, (z : ℂ).re], by
    rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    constructor
    · rfl
    constructor
    · rfl
    have hz : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      calc
        (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = Complex.normSq (z : ℂ) := by
          simp [Complex.normSq_apply, pow_two]
        _ = 1 := Circle.normSq_coe z
    simpa [neg_sq] using hz⟩

/-- Multiplicativity of the standard map `SO(2) → S¹`. -/
theorem so2ToCircle_map_mul (A B : SO(2)) :
    so2ToCircle (A * B) = so2ToCircle A * so2ToCircle B := by
  sorry

/-- `circleToSO2` and `so2ToCircle` are inverse on `SO(2)`. -/
theorem circleToSO2_left_inv (A : SO(2)) :
    circleToSO2 (so2ToCircle A) = A := by
  sorry

/-- `so2ToCircle` and `circleToSO2` are inverse on `S¹`. -/
theorem so2ToCircle_right_inv (z : Circle) :
    so2ToCircle (circleToSO2 z) = z := by
  sorry

/-- The canonical algebraic identification `SO(2) ≃* S¹`. -/
def so2MulEquivCircle : SO(2) ≃* Circle where
  toFun := so2ToCircle
  invFun := circleToSO2
  left_inv := circleToSO2_left_inv
  right_inv := so2ToCircle_right_inv
  map_mul' := so2ToCircle_map_mul

/-- The standard algebraic comparison `U(1) → S¹`, taking a `1 × 1` unitary matrix to its unique
entry. -/
def u1ToCircle (A : U(1)) : Circle :=
  ⟨(A : Matrix (Fin 1) (Fin 1) ℂ) 0 0, by
    have hA :
        (A : Matrix (Fin 1) (Fin 1) ℂ) * star (A : Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp A.property
    have hnormSq : Complex.normSq ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0) = 1 := by
      have hentry := congrArg Complex.re (congr_fun (congr_fun hA 0) 0)
      simpa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply, Matrix.one_apply,
        Complex.normSq_apply, Complex.mul_re, pow_two] using hentry
    have hsq : ‖(A : Matrix (Fin 1) (Fin 1) ℂ) 0 0‖ ^ 2 = 1 := by
      calc
        ‖(A : Matrix (Fin 1) (Fin 1) ℂ) 0 0‖ ^ 2
            = Complex.normSq ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0) := by
                simpa using Complex.sq_norm ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
        _ = 1 := hnormSq
    have hnorm : ‖(A : Matrix (Fin 1) (Fin 1) ℂ) 0 0‖ = 1 := by
      have hnonneg : 0 ≤ ‖(A : Matrix (Fin 1) (Fin 1) ℂ) 0 0‖ := norm_nonneg _
      nlinarith [hsq]
    exact mem_sphere_zero_iff_norm.mpr hnorm⟩

/-- The inverse algebraic comparison `S¹ → U(1)`, viewing a circle element as a `1 × 1` unitary
matrix. -/
def circleToU1 (z : Circle) : U(1) :=
  ⟨!![((z : ℂ))], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i
    fin_cases j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp [Complex.mul_conj', Circle.norm_coe z]⟩

/-- Multiplicativity of the standard map `U(1) → S¹`. -/
theorem u1ToCircle_map_mul (A B : U(1)) :
    u1ToCircle (A * B) = u1ToCircle A * u1ToCircle B := by
  sorry

/-- `circleToU1` and `u1ToCircle` are inverse on `U(1)`. -/
theorem circleToU1_left_inv (A : U(1)) :
    circleToU1 (u1ToCircle A) = A := by
  sorry

/-- `u1ToCircle` and `circleToU1` are inverse on `S¹`. -/
theorem u1ToCircle_right_inv (z : Circle) :
    u1ToCircle (circleToU1 z) = z := by
  sorry

/-- The canonical algebraic identification `U(1) ≃* S¹`. -/
def u1MulEquivCircle : U(1) ≃* Circle where
  toFun := u1ToCircle
  invFun := circleToU1
  left_inv := circleToU1_left_inv
  right_inv := u1ToCircle_right_inv
  map_mul' := u1ToCircle_map_mul

/-- The resulting algebraic bridge `SO(2) ≃* U(1)`. -/
def so2MulEquivU1 : SO(2) ≃* U(1) :=
  so2MulEquivCircle.trans u1MulEquivCircle.symm

section StandardLieGroupStatements

local notation "M₂ℝ" => Matrix (Fin 2) (Fin 2) ℝ
local notation "M₁ℂ" => Matrix (Fin 1) (Fin 1) ℂ
local notation "I₂ℝ" => 𝓘(ℝ, M₂ℝ)
local notation "I₁ℂ" => 𝓘(ℝ, M₁ℂ)

-- Semantic recall: `Problem_7_20` uses explicit matrix-model `[ChartedSpace]` / `[LieGroup]`
-- assumptions for matrix groups, while `lean_leansearch` only surfaced the canonical `Circle`
-- Lie-group instance. The source-facing statements below therefore stay on the standard matrix
-- models through explicit assumptions rather than transported private instances.

/-- Problem 7-15 (1): `SO(2)` is Lie-group-isomorphic to `S¹` for the standard matrix Lie-group
structure on `SO(2)`. -/
def so2LieGroupIsomorphismCircle
    [instChartedSO2 : ChartedSpace M₂ℝ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ)]
    [instLieGroupSO2 : @LieGroup ℝ inferInstance M₂ℝ inferInstance M₂ℝ inferInstance
      inferInstance I₂ℝ ∞ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ) inferInstance
      inferInstance instChartedSO2]
    : @LieGroupIsomorphism ℝ inferInstance M₂ℝ inferInstance inferInstance M₂ℝ inferInstance
        (EuclideanSpace ℝ (Fin 1)) inferInstance inferInstance (EuclideanSpace ℝ (Fin 1))
        inferInstance (𝓘(ℝ, M₂ℝ)) (𝓡 1) ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ)
        inferInstance inferInstance instChartedSO2 Circle inferInstance inferInstance
        inferInstance where
  toDiffeomorph :=
    { toEquiv := so2MulEquivCircle.toEquiv
      contMDiff_toFun := sorry
      contMDiff_invFun := sorry }
  map_mul' := so2MulEquivCircle.map_mul

/-- The underlying multiplicative equivalence of `so2LieGroupIsomorphismCircle` is
`so2MulEquivCircle`. -/
theorem so2LieGroupIsomorphismCircle_toMulEquiv
    [instChartedSO2 : ChartedSpace M₂ℝ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ)]
    [instLieGroupSO2 : @LieGroup ℝ inferInstance M₂ℝ inferInstance M₂ℝ inferInstance
      inferInstance I₂ℝ ∞ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ) inferInstance
      inferInstance instChartedSO2]
    : so2LieGroupIsomorphismCircle.toMulEquiv = so2MulEquivCircle := sorry

/-- The standard Lie-group isomorphism `U(1) ≃ S¹` for the matrix Lie-group structure on
`U(1)`. -/
def u1LieGroupIsomorphismCircle
    [instChartedU1 : ChartedSpace M₁ℂ ↥(Matrix.unitaryGroup (Fin 1) ℂ)]
    [instLieGroupU1 : @LieGroup ℝ inferInstance M₁ℂ inferInstance M₁ℂ inferInstance
      inferInstance I₁ℂ ∞ ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance inferInstance
      instChartedU1]
    : @LieGroupIsomorphism ℝ inferInstance M₁ℂ inferInstance inferInstance M₁ℂ inferInstance
        (EuclideanSpace ℝ (Fin 1)) inferInstance inferInstance (EuclideanSpace ℝ (Fin 1))
        inferInstance (𝓘(ℝ, M₁ℂ)) (𝓡 1) ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance
        inferInstance instChartedU1 Circle inferInstance inferInstance inferInstance where
  toDiffeomorph :=
    { toEquiv := u1MulEquivCircle.toEquiv
      contMDiff_toFun := sorry
      contMDiff_invFun := sorry }
  map_mul' := u1MulEquivCircle.map_mul

/-- The underlying multiplicative equivalence of `u1LieGroupIsomorphismCircle` is
`u1MulEquivCircle`. -/
theorem u1LieGroupIsomorphismCircle_toMulEquiv
    [instChartedU1 : ChartedSpace M₁ℂ ↥(Matrix.unitaryGroup (Fin 1) ℂ)]
    [instLieGroupU1 : @LieGroup ℝ inferInstance M₁ℂ inferInstance M₁ℂ inferInstance
      inferInstance I₁ℂ ∞ ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance inferInstance
      instChartedU1]
    : u1LieGroupIsomorphismCircle.toMulEquiv = u1MulEquivCircle := sorry

/-- The induced standard Lie-group isomorphism `SO(2) ≃ U(1)`. Its algebraic bridge is
`so2MulEquivU1`. -/
def so2LieGroupIsomorphismU1
    [instChartedSO2 : ChartedSpace M₂ℝ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ)]
    [instChartedU1 : ChartedSpace M₁ℂ ↥(Matrix.unitaryGroup (Fin 1) ℂ)]
    [instLieGroupSO2 : @LieGroup ℝ inferInstance M₂ℝ inferInstance M₂ℝ inferInstance
      inferInstance I₂ℝ ∞ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ) inferInstance
      inferInstance instChartedSO2]
    [instLieGroupU1 : @LieGroup ℝ inferInstance M₁ℂ inferInstance M₁ℂ inferInstance
      inferInstance I₁ℂ ∞ ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance inferInstance
      instChartedU1]
    : @LieGroupIsomorphism ℝ inferInstance M₂ℝ inferInstance inferInstance M₂ℝ inferInstance
        M₁ℂ inferInstance inferInstance M₁ℂ inferInstance (𝓘(ℝ, M₂ℝ)) (𝓘(ℝ, M₁ℂ))
        ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ) inferInstance inferInstance instChartedSO2
        ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance inferInstance instChartedU1 where
  toDiffeomorph :=
    { toEquiv := so2MulEquivU1.toEquiv
      contMDiff_toFun := sorry
      contMDiff_invFun := sorry }
  map_mul' := so2MulEquivU1.map_mul

/-- The underlying multiplicative equivalence of `so2LieGroupIsomorphismU1` is
`so2MulEquivU1`. -/
theorem so2LieGroupIsomorphismU1_toMulEquiv
    [instChartedSO2 : ChartedSpace M₂ℝ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ)]
    [instChartedU1 : ChartedSpace M₁ℂ ↥(Matrix.unitaryGroup (Fin 1) ℂ)]
    [instLieGroupSO2 : @LieGroup ℝ inferInstance M₂ℝ inferInstance M₂ℝ inferInstance
      inferInstance I₂ℝ ∞ ↥(Matrix.specialOrthogonalGroup (Fin 2) ℝ) inferInstance
      inferInstance instChartedSO2]
    [instLieGroupU1 : @LieGroup ℝ inferInstance M₁ℂ inferInstance M₁ℂ inferInstance
      inferInstance I₁ℂ ∞ ↥(Matrix.unitaryGroup (Fin 1) ℂ) inferInstance inferInstance
      instChartedU1]
    : so2LieGroupIsomorphismU1.toMulEquiv = so2MulEquivU1 := sorry

end StandardLieGroupStatements

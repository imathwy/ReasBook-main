import BauschkeLean.Chap13.Text_13_18_1
import BauschkeLean.Chap20.Fact_20_18
import BauschkeLean.Chap23.Proposition_23_34
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Real.Spectrum

open scoped InnerProductSpace

universe u

namespace ERealFunction

open ContinuousLinearMap

noncomputable section

section MetricInverseSquareRoot

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 24.24: strong monotonicity upgrades the self-adjoint metric operator
to a positive operator. -/
private theorem metricOperator_isPositive
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    U.IsPositive := by
  -- Combine self-adjointness with the quadratic-form lower bound from strong monotonicity.
  refine (ContinuousLinearMap.isPositive_iff' U).2 ?_
  refine ⟨hU_self, ?_⟩
  intro x
  exact le_trans
    (mul_nonneg (le_of_lt hU_strong.pos) (sq_nonneg ‖x‖))
    (hU_strong.ineq x)

/-- Helper for Proposition 24.24: the inverse metric operator is still a positive operator. -/
private theorem inverseMetric_isPositive
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    U.inverse.IsPositive := by
  have hU_inv :
      U.IsInvertible :=
    ContinuousLinearMap.isInvertible_of_isSelfAdjoint_of_isStronglyMonotone
      U hU_self hU_strong
  have hU_unit : IsUnit U := by
    -- Package the inverse from strong monotonicity as a unit in the endomorphism ring.
    refine ⟨⟨U, U.inverse, ?_, ?_⟩, rfl⟩
    · ext x
      exact hU_inv.self_apply_inverse x
    · ext x
      exact hU_inv.inverse_apply_self x
  have hUinv_self : IsSelfAdjoint U.inverse :=
    inverse_isSelfAdjoint_of_isSelfAdjoint_of_isUnit hU_self hU_unit
  refine (ContinuousLinearMap.isPositive_iff' U.inverse).2 ?_
  refine ⟨hUinv_self, ?_⟩
  intro x
  let y : H := U.inverse x
  have hy_nonneg :
      0 ≤ α * ‖y‖ ^ 2 := by
    -- The strong-monotonicity coefficient is positive, so the lower energy term is nonnegative.
    exact mul_nonneg (le_of_lt hU_strong.pos) (sq_nonneg ‖y‖)
  have hy_bound :
      α * ‖y‖ ^ 2 ≤ ⟪U.inverse x, x⟫_ℝ := by
    -- Rewrite the strong-monotonicity inequality at `y = U⁻¹ x` in inverse-metric coordinates.
    simpa [y, hU_inv.self_apply_inverse x, real_inner_comm] using hU_strong.ineq y
  exact le_trans hy_nonneg hy_bound

/-- Helper for Proposition 24.24: the inverse metric operator is nonnegative in the operator
order. -/
private theorem inverseMetric_nonneg
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    0 ≤ U.inverse := by
  -- Convert the already established positivity predicate to the ambient operator order.
  exact (ContinuousLinearMap.nonneg_iff_isPositive U.inverse).2
    (inverseMetric_isPositive U hU_self hU_strong)

/-- Helper for Proposition 24.24: the inverse metric operator is a unit, so any square-root
candidate would automatically package to a continuous linear equivalence. -/
private theorem inverseMetric_isUnit
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    IsUnit U.inverse := by
  have hU_inv :
      U.IsInvertible :=
    ContinuousLinearMap.isInvertible_of_isSelfAdjoint_of_isStronglyMonotone
      U hU_self hU_strong
  -- Use `U` itself as the inverse witness for `U.inverse`.
  refine ⟨⟨U.inverse, U, ?_, ?_⟩, rfl⟩
  · ext x
    exact hU_inv.inverse_apply_self x
  · ext x
    exact hU_inv.self_apply_inverse x

/-- Helper for Proposition 24.24: the inverse metric operator is strictly positive in the
algebraic sense needed by the CFC square-root theorems. -/
private theorem inverseMetric_isStrictlyPositive
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    IsStrictlyPositive U.inverse := by
  -- Combine the order-theoretic nonnegativity with the unit witness from strong monotonicity.
  exact (inverseMetric_isUnit U hU_self hU_strong).isStrictlyPositive
    (inverseMetric_nonneg U hU_self hU_strong)

/-- Helper for Proposition 24.24: a positive real Hilbert-space operator has nonnegative
quasispectrum. -/
private theorem quasispectrumRestricts_of_isPositive
    (T : H →L[ℝ] H) (hT : T.IsPositive) :
    QuasispectrumRestricts T ContinuousMap.realToNNReal := by
  rw [QuasispectrumRestricts.nnreal_iff]
  intro x hx
  by_contra hx_nonneg
  have hx_lt : x < 0 := lt_of_not_ge hx_nonneg
  have hshift_self : IsSelfAdjoint (T - x • (1 : H →L[ℝ] H)) := by
    -- Subtracting a real scalar multiple of the identity preserves self-adjointness.
    have hscalar_self : IsSelfAdjoint (x • (1 : H →L[ℝ] H)) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
      intro y z
      calc
        ⟪(x • (1 : H →L[ℝ] H)) y, z⟫_ℝ = x * ⟪y, z⟫_ℝ := by simp [real_inner_smul_left]
        _ = ⟪y, (x • (1 : H →L[ℝ] H)) z⟫_ℝ := by
              simpa using (inner_smul_right y z x).symm
    exact hT.isSelfAdjoint.sub hscalar_self
  have hshift_strong :
      (T - x • (1 : H →L[ℝ] H)).toLinearMap.IsStronglyMonotone (-x) := by
    -- The negative scalar shift contributes the coercive lower bound `(-x) ‖y‖²`.
    refine ⟨by simpa using neg_pos.mpr hx_lt, ?_⟩
    intro y
    have hy_nonneg : 0 ≤ ⟪T y, y⟫_ℝ :=
      hT.inner_nonneg_left y
    calc
      (-x) * ‖y‖ ^ 2 ≤ ⟪T y, y⟫_ℝ + (-x) * ‖y‖ ^ 2 := by
        nlinarith
      _ = ⟪(T - x • (1 : H →L[ℝ] H)) y, y⟫_ℝ := by
        calc
          ⟪T y, y⟫_ℝ + (-x) * ‖y‖ ^ 2
              = ⟪T y, y⟫_ℝ + ⟪(-x • y), y⟫_ℝ := by
                  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
          _ = ⟪T y + (-x • y), y⟫_ℝ := by rw [inner_add_left]
          _ = ⟪(T - x • (1 : H →L[ℝ] H)) y, y⟫_ℝ := by
                simp [sub_eq_add_neg, add_comm]
  have hshift_inv :
      (T - x • (1 : H →L[ℝ] H)).IsInvertible :=
    ContinuousLinearMap.isInvertible_of_isSelfAdjoint_of_isStronglyMonotone
      (T - x • (1 : H →L[ℝ] H)) hshift_self hshift_strong
  have hshift_unit : IsUnit (T - x • (1 : H →L[ℝ] H)) := by
    -- Package the inverse coming from strong monotonicity as a unit.
    refine ⟨⟨T - x • (1 : H →L[ℝ] H), (T - x • (1 : H →L[ℝ] H)).inverse, ?_, ?_⟩, rfl⟩
    · ext y
      exact hshift_inv.self_apply_inverse y
    · ext y
      exact hshift_inv.inverse_apply_self y
  have hx_not_spectrum : x ∉ spectrum ℝ T := by
    -- A negative spectral value would contradict invertibility of the shifted operator.
    rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one]
    exact (IsUnit.sub_iff).2 hshift_unit
  have hx_unit : IsUnit x :=
    isUnit_iff_ne_zero.mpr hx_lt.ne
  have hx_not_quasispectrum : x ∉ quasispectrum ℝ T := by
    -- Over a field, negative scalars are units, so the quasispectrum collapses to the spectrum.
    rw [quasispectrum_eq_spectrum_union ℝ T]
    simp [hx_not_spectrum, hx_lt.ne]
  exact hx_not_quasispectrum hx

/-- Helper for Proposition 24.24: the theorem-local complex scalar action on `PairComplex`
extends the existing real scalar action. -/
private instance pairComplexIsScalarTower :
    IsScalarTower ℝ ℂ (ContinuousLinearMap.PairComplex (H := H)) where
  smul_assoc r c z := by
    apply WithLp.ofLp_injective
    simp [ContinuousLinearMap.pairComplex_smul_apply, sub_eq_add_neg]
    constructor <;> simp [smul_smul]

/-- Helper for Proposition 24.24: complexifying a unit endomorphism preserves invertibility on
the PairComplex model. -/
private theorem pairLiftComplex_isUnit_of_isUnit
    (T : H →L[ℝ] H) (hT : IsUnit T) :
    IsUnit (ContinuousLinearMap.pairLiftComplex (H := H) T) := by
  -- Transport the unit witness through the multiplicative `pairLiftComplex` functor.
  rcases hT with ⟨u, rfl⟩
  refine ⟨⟨ContinuousLinearMap.pairLiftComplex (H := H) (↑u : H →L[ℝ] H),
      ContinuousLinearMap.pairLiftComplex (H := H) (↑u⁻¹ : H →L[ℝ] H), ?_, ?_⟩, rfl⟩
  · -- Push the left-inverse identity through `pairLiftComplex` at the map level.
    calc
      ContinuousLinearMap.pairLiftComplex (H := H) (↑u : H →L[ℝ] H) *
          ContinuousLinearMap.pairLiftComplex (H := H) (↑u⁻¹ : H →L[ℝ] H)
          = ContinuousLinearMap.pairLiftComplex (H := H) (↑u * ↑u⁻¹) := by
              rw [← ContinuousLinearMap.pairLiftComplex_mul]
      _ = ContinuousLinearMap.pairLiftComplex (H := H) (1 : H →L[ℝ] H) := by
            simpa using congrArg (ContinuousLinearMap.pairLiftComplex (H := H)) u.val_inv
      _ = 1 := by
            ext z
            rfl
  · -- Push the right-inverse identity through `pairLiftComplex` at the map level.
    calc
      ContinuousLinearMap.pairLiftComplex (H := H) (↑u⁻¹ : H →L[ℝ] H) *
          ContinuousLinearMap.pairLiftComplex (H := H) (↑u : H →L[ℝ] H)
          = ContinuousLinearMap.pairLiftComplex (H := H) (↑u⁻¹ * ↑u) := by
              rw [← ContinuousLinearMap.pairLiftComplex_mul]
      _ = ContinuousLinearMap.pairLiftComplex (H := H) (1 : H →L[ℝ] H) := by
            simpa using congrArg (ContinuousLinearMap.pairLiftComplex (H := H)) u.inv_val
      _ = 1 := by
            ext z
            rfl

/-- Helper for Proposition 24.24: the PairComplex lift intertwines adjoints with the ambient
star structure. -/
private theorem pairLiftComplex_adjoint
    (T : H →L[ℝ] H) :
    (ContinuousLinearMap.pairLiftComplex (H := H) T).adjoint =
      ContinuousLinearMap.pairLiftComplex (H := H) T.adjoint := by
  -- Characterize the adjoint by the complex inner product on the PairComplex model.
  rw [eq_comm]
  apply (ContinuousLinearMap.eq_adjoint_iff
    (ContinuousLinearMap.pairLiftComplex (H := H) T.adjoint)
    (ContinuousLinearMap.pairLiftComplex (H := H) T)).2
  intro z w
  simp [ContinuousLinearMap.pairLiftComplex_apply, ContinuousLinearMap.pairComplexInner,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 24.24: the embedded real copy has the same norm in the PairComplex
model. -/
private theorem norm_ofRealVec
    (x : H) :
    ‖ContinuousLinearMap.ofRealVec (H := H) x‖ = ‖x‖ := by
  -- The diagonal embedding is the standard `(x, 0)` inclusion in the `L²` pair norm.
  rw [ContinuousLinearMap.ofRealVec_apply]
  simpa using (WithLp.norm_toLp_fst (p := 2) (α := H) (β := H) x)

/-- Helper for Proposition 24.24: projecting the embedded real copy recovers the original
vector. -/
private theorem fstL_ofRealVec
    (x : H) :
    (WithLp.fstL (p := 2) ℝ H H) (ContinuousLinearMap.ofRealVec (H := H) x) = x := by
  -- The first-coordinate projection undoes the diagonal embedding on `(x, 0)`.
  rw [ContinuousLinearMap.ofRealVec_apply]
  simp

/-- Helper for Proposition 24.24: `pairLiftComplex` is a bounded real-linear map on the operator
space. -/
private noncomputable def pairLiftComplexOperatorMap :
    (H →L[ℝ] H) →L[ℝ]
      (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
        ContinuousLinearMap.PairComplex (H := H)) :=
  -- Package the theorem-local complex lift as a continuous map between operator spaces.
  (LinearMap.mkContinuous
    { toFun := fun T => ContinuousLinearMap.pairLiftComplex (H := H) T
      map_add' := by
        intro S T
        ext z
        apply WithLp.ofLp_injective
        ext <;> simp [ContinuousLinearMap.pairLiftComplex_apply, map_add]
      map_smul' := by
        intro r T
        ext z
        apply WithLp.ofLp_injective
        ext <;> simp [ContinuousLinearMap.pairLiftComplex_apply,
          ContinuousLinearMap.pairComplex_smul_apply, map_smul] }
    2
    (by
      intro T
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro z
      calc
        ‖ContinuousLinearMap.pairLiftComplex (H := H) T z‖
            = ‖WithLp.toLp 2 (T z.fst, T z.snd)‖ := by
                rw [ContinuousLinearMap.pairLiftComplex_apply]
        _ ≤ ‖WithLp.toLp 2 (T z.fst, (0 : H))‖ + ‖WithLp.toLp 2 ((0 : H), T z.snd)‖ := by
              rw [show WithLp.toLp 2 (T z.fst, T z.snd) =
                  WithLp.toLp 2 (T z.fst, (0 : H)) + WithLp.toLp 2 ((0 : H), T z.snd) by
                    apply WithLp.ofLp_injective
                    ext <;> simp]
              exact norm_add_le _ _
        _ = ‖T z.fst‖ + ‖T z.snd‖ := by
              simp [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd]
        _ ≤ ‖T‖ * ‖z.fst‖ + ‖T‖ * ‖z.snd‖ := by
              gcongr <;> exact T.le_opNorm _
        _ = ‖T‖ * (‖z.fst‖ + ‖z.snd‖) := by ring
        _ ≤ ‖T‖ * (2 * ‖z‖) := by
              gcongr
              nlinarith [WithLp.norm_fst_le (p := (2 : ENNReal)) (α := H) (β := H) z,
                WithLp.norm_snd_le (p := (2 : ENNReal)) (α := H) (β := H) z]
        _ = (2 * ‖T‖) * ‖z‖ := by ring))

/-- Helper for Proposition 24.24: restricting a complex PairComplex endomorphism to the embedded
real copy recovers a real operator. -/
private noncomputable def pairLiftComplexRetract :
    (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
        ContinuousLinearMap.PairComplex (H := H)) →L[ℝ] (H →L[ℝ] H) :=
  -- Compose with the diagonal embedding and first-coordinate projection to return to `H`.
  (LinearMap.mkContinuous
    { toFun := fun Y =>
        (WithLp.fstL (p := 2) ℝ H H) ∘L (Y.restrictScalars ℝ) ∘L
          ContinuousLinearMap.ofRealVec (H := H)
      map_add' := by
        intro Y Z
        ext x
        simp
      map_smul' := by
        intro r Y
        ext x
        simp [ContinuousLinearMap.pairComplex_smul_apply] }
    1
    (by
      intro Y
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
      intro x
      calc
        ‖((WithLp.fstL (p := 2) ℝ H H) ∘L (Y.restrictScalars ℝ) ∘L
            ContinuousLinearMap.ofRealVec (H := H)) x‖
            ≤ ‖(Y.restrictScalars ℝ) (ContinuousLinearMap.ofRealVec (H := H) x)‖ := by
                simpa using
                  (WithLp.norm_fst_le (p := (2 : ENNReal)) (α := H) (β := H)
                    ((Y.restrictScalars ℝ) (ContinuousLinearMap.ofRealVec (H := H) x)))
        _ ≤ ‖Y.restrictScalars ℝ‖ * ‖ContinuousLinearMap.ofRealVec (H := H) x‖ := by
              exact (Y.restrictScalars ℝ).le_opNorm _
        _ = ‖Y‖ * ‖x‖ := by
              rw [ContinuousLinearMap.norm_restrictScalars, norm_ofRealVec (H := H)]
        _ = (1 : ℝ) * ‖Y‖ * ‖x‖ := by ring))

/-- Helper for Proposition 24.24: the PairComplex lift has a continuous left inverse on the
operator space. -/
private theorem pairLiftComplexRetract_pairLiftComplex
    (T : H →L[ℝ] H) :
    pairLiftComplexRetract (H := H)
        (ContinuousLinearMap.pairLiftComplex (H := H) T) = T := by
  -- Restrict the lifted operator to the embedded real copy and project back to `H`.
  ext x
  rw [pairLiftComplexRetract, LinearMap.mkContinuous_apply]
  change
    (WithLp.fstL (p := 2) ℝ H H)
        (ContinuousLinearMap.pairLiftComplex (H := H) T
          (ContinuousLinearMap.ofRealVec (H := H) x)) = T x
  rw [ContinuousLinearMap.pairLiftComplex_ofRealVec]
  exact fstL_ofRealVec (H := H) (T x)

/-- Helper for Proposition 24.24: the PairComplex lift is injective because its continuous
retraction recovers the original operator. -/
private theorem pairLiftComplex_injective
    {S T : H →L[ℝ] H}
    (h : ContinuousLinearMap.pairLiftComplex (H := H) S =
      ContinuousLinearMap.pairLiftComplex (H := H) T) :
    S = T := by
  -- Apply the retraction to turn equality of lifts back into equality on `H`.
  simpa [pairLiftComplexRetract_pairLiftComplex (H := H)]
    using congrArg (pairLiftComplexRetract (H := H)) h

/-- Helper for Proposition 24.24: `pairLiftComplex` is a real non-unital star-algebra
homomorphism. -/
private noncomputable def pairLiftComplexStarHom :
    (H →L[ℝ] H) →⋆ₙₐ[ℝ]
      (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
        ContinuousLinearMap.PairComplex (H := H)) where
  toFun := ContinuousLinearMap.pairLiftComplex (H := H)
  map_zero' := by
    ext z
    simp [ContinuousLinearMap.pairLiftComplex_apply]
  map_add' := by
    intro S T
    ext z
    apply WithLp.ofLp_injective
    ext <;> simp [ContinuousLinearMap.pairLiftComplex_apply]
  map_mul' := ContinuousLinearMap.pairLiftComplex_mul (H := H)
  map_smul' := by
    intro r T
    ext z
    apply WithLp.ofLp_injective
    ext <;> simp [ContinuousLinearMap.pairLiftComplex_apply]
  map_star' := by
    intro T
    simpa using (pairLiftComplex_adjoint (H := H) T).symm

/-- Helper for Proposition 24.24: the PairComplex lift range is closed because the theorem-local
retraction is a continuous left inverse. -/
private theorem pairLiftComplexStarHom_isClosedRange :
    IsClosed
      ((NonUnitalStarAlgHom.range (pairLiftComplexStarHom (H := H) :
        (H →L[ℝ] H) →⋆ₙₐ[ℝ]
          (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
            ContinuousLinearMap.PairComplex (H := H))) :
        NonUnitalStarSubalgebra ℝ
          (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
            ContinuousLinearMap.PairComplex (H := H))) : Set
          (ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
            ContinuousLinearMap.PairComplex (H := H))) := by
  -- The continuous retraction shows the lift is a closed embedding on its image.
  have hleft :
      (pairLiftComplexOperatorMap (H := H)).HasLeftInverse := by
    refine ⟨pairLiftComplexRetract (H := H), ?_⟩
    intro T
    exact pairLiftComplexRetract_pairLiftComplex (H := H) T
  simpa [pairLiftComplexOperatorMap, pairLiftComplexStarHom, NonUnitalStarAlgHom.coe_range]
    using hleft.isClosed_range

/-- Helper for Proposition 24.24: the PairComplex endomorphism algebra is the ambient complex
operator algebra used to construct and descend the inverse square root. -/
private abbrev pairComplexOperator :=
  ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
    ContinuousLinearMap.PairComplex (H := H)

/-- Helper for Proposition 24.24: complex scalars can be pushed across one factor of operator
multiplication on the PairComplex endomorphism algebra. -/
private theorem pairComplexOperator_complex_smul_mul
    (c : ℂ) (S T : pairComplexOperator (H := H)) :
    (c • S) * T = S * (c • T) := by
  -- Evaluate both sides on a vector and use complex linearity of `S`.
  ext z
  change c • S (T z) = S (c • T z)
  rw [map_smul]

/-- Helper for Proposition 24.24: real scalars can be pushed across one factor of operator
multiplication on the PairComplex endomorphism algebra. -/
private theorem pairComplexOperator_real_smul_mul
    (r : ℝ) (S T : pairComplexOperator (H := H)) :
    (r • S) * T = S * (r • T) := by
  -- The restricted real action agrees definitionally with the complex action by `(r : ℂ)`.
  simpa using pairComplexOperator_complex_smul_mul (H := H) (c := (r : ℂ)) S T

/-- Helper for Proposition 24.24: the complexified inverse metric operator admits a positive
invertible CFC square root. -/
private theorem pairComplexCfcSqrtData
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    ∃ Y : ContinuousLinearMap.PairComplex (H := H) →L[ℂ]
        ContinuousLinearMap.PairComplex (H := H),
      Y.IsPositive ∧
      Y * Y = ContinuousLinearMap.pairLiftComplex (H := H) U.inverse ∧
      IsUnit Y :=
  -- TODO: construct `Y := CFC.sqrt (pairLiftComplex U.inverse)` once the theorem-local
  -- PairComplex real-CFC bridge and closed-range descent are packaged without instance-search
  -- timeouts; `pairComplexOperator_complex_smul_mul` and `pairComplexOperator_real_smul_mul`
  -- record the scalar/ multiplication compatibilities needed for that bridge.
  sorry

/-- Helper for Proposition 24.24: positivity of the complex diagonal lift reflects back to the
original real operator on `H`. -/
private theorem isPositive_of_pairLiftComplex_isPositive
    {T : H →L[ℝ] H}
    (hT_pair : (ContinuousLinearMap.pairLiftComplex (H := H) T).IsPositive) :
    T.IsPositive := by
  refine (ContinuousLinearMap.isPositive_iff' T).2 ?_
  constructor
  · -- Test symmetry of the complex lift on embedded real vectors and project back to `H`.
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    have hsymm :=
      hT_pair.isSymmetric
        (ContinuousLinearMap.ofRealVec (H := H) x)
        (ContinuousLinearMap.ofRealVec (H := H) y)
    exact Complex.ofReal_injective <| by
      simpa [ContinuousLinearMap.pairLiftComplex_apply, ContinuousLinearMap.ofRealVec_apply,
        ContinuousLinearMap.pairComplexInner] using hsymm
  · -- The quadratic form on embedded real vectors is the original real quadratic form.
    intro x
    have hinner :=
      hT_pair.inner_nonneg_left (ContinuousLinearMap.ofRealVec (H := H) x)
    rw [ContinuousLinearMap.pairLiftComplexInner_ofRealVec] at hinner
    exact_mod_cast hinner

/-- Helper for Proposition 24.24: under the textbook hypotheses on `U`, the inverse metric
operator has a positive square root that is already a unit. -/
private theorem existsPositiveUnitSquareRootOfInverseMetric
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    ∃ u : (H →L[ℝ] H)ˣ,
      (↑u : H →L[ℝ] H).IsPositive ∧
      (↑u : H →L[ℝ] H) * ↑u = U.inverse :=
    by
  -- TODO: descend the PairComplex CFC square root to a real operator after packaging the
  -- closed-range membership step that is still blocked by the same PairComplex real-CFC
  -- instance frontier recorded in `pairComplexCfcSqrtData`.
  sorry

/-- Helper for Proposition 24.24: the unit-based continuous linear equivalence uses the same
square as the underlying endomorphism ring product. -/
private theorem ofUnit_toContinuousLinearMap_sq
    (u : (H →L[ℝ] H)ˣ) :
    (ContinuousLinearEquiv.ofUnit u).toContinuousLinearMap.comp
        (ContinuousLinearEquiv.ofUnit u).toContinuousLinearMap =
      (↑u : H →L[ℝ] H) * ↑u := by
  rfl

/-- Helper for Proposition 24.24: under the textbook hypotheses on `U`, there exists a positive
square-root equivalence witness for `U.inverse`. -/
theorem exists_metricInverseSquareRootEquiv
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    ∃ L : H ≃L[ℝ] H,
      L.toContinuousLinearMap.IsPositive ∧
      L.toContinuousLinearMap.comp L.toContinuousLinearMap = U.inverse := by
  -- Route correction: avoid the stalled `pairLiftComplex` transport and build the square root
  -- directly in the real operator algebra.
  obtain ⟨u, hu_pos, hu_sq⟩ :=
    existsPositiveUnitSquareRootOfInverseMetric U hU_self hU_strong
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_, ?_⟩
  · -- The packaged equivalence inherits positivity from the unit-valued square root.
    simpa using hu_pos
  · -- The square identity is the same computation before and after `ContinuousLinearEquiv.ofUnit`.
    calc
      (ContinuousLinearEquiv.ofUnit u).toContinuousLinearMap.comp
          (ContinuousLinearEquiv.ofUnit u).toContinuousLinearMap
          = (↑u : H →L[ℝ] H) * ↑u :=
            ofUnit_toContinuousLinearMap_sq u
      _ = U.inverse := hu_sq

end MetricInverseSquareRoot

end

end ERealFunction

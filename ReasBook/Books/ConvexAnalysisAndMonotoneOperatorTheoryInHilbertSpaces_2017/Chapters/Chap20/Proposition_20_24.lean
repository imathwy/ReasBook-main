import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap02.Definition_2_23
import BauschkeLean.Chap20.Definition_20_1
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.24 is the renorming statement for maximally monotone operators
  under a self-adjoint strongly monotone linear operator.
- `core/canonical`: the owner abstractions are the renormed Hilbert space built from
  `InnerProductSpace.Core`, maximal monotonicity as `Maximal IsMonotone`, and the Chapter 1
  set-valued-operator transport owners `comp` and `toSetValuedOperator`.
- `bridge/view`: `ContinuousLinearMap.Renormed.continuousLinearEquiv` is the canonical
  identification between the renormed space and the original Hilbert space; the theorem
  `isMaximallyMonotone_renormed_iff` rewrites the canonical maximality statement back to the
  textbook pairing formula. -/
-- Semantic recall: `lean_leansearch` did not surface a more specific transport owner here, so the
-- verified local API remains `Maximal IsMonotone`, `comp`, and `toSetValuedOperator`.

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strong monotonicity of a self-adjoint bounded linear operator gives coercivity of the
associated sesquilinear form. -/
theorem toSesqForm_isCoercive_of_isStronglyMonotone
    (U : H →L[ℝ] H) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    IsCoercive U.toSesqForm := by
  -- Use the strong-monotonicity constant itself as the coercivity witness.
  refine ⟨α, hU_strong.pos, ?_⟩
  intro x
  simpa [pow_two, mul_assoc, ContinuousLinearMap.toSesqForm_apply_coe, real_inner_comm] using
    hU_strong.ineq x

variable [CompleteSpace H]

/-- The coercive equivalence attached to `U.toSesqForm` recovers `U` when `U` is self-adjoint and
strongly monotone. -/
private theorem coerciveEquivOfToSesqForm_eq_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    (((toSesqForm_isCoercive_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin :
        H ≃L[ℝ] H) : H →L[ℝ] H) = U := by
  -- The Lax-Milgram vector representing `x` is characterized by the same pairing as `U x`.
  ext x
  exact
    ((toSesqForm_isCoercive_of_isStronglyMonotone U hU_strong).unique_continuousLinearEquivOfBilin
      (v := x) (f := U x) fun y => by
        simpa [ContinuousLinearMap.toSesqForm_apply_coe] using hU_self.isSymmetric x y).symm

/-- A self-adjoint strongly monotone bounded linear operator is invertible. -/
theorem isInvertible_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    U.IsInvertible := by
  -- Transport the inverse from the coercive Lax-Milgram equivalence back to `U`.
  let e : H ≃L[ℝ] H :=
    (toSesqForm_isCoercive_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin
  have hEq : ((e : H ≃L[ℝ] H) : H →L[ℝ] H) = U :=
    coerciveEquivOfToSesqForm_eq_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := (e.symm : H →L[ℝ] H)) ?_ ?_
  · rw [← hEq]
    ext x
    simp [e]
  · rw [← hEq]
    ext x
    simp [e]

/-- The `U`-twisted pairing reduces to the original inner product after applying `U⁻¹` on the
first coordinate. -/
theorem inner_inverse_map_eq_inner
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y : H) :
    ⟪U.inverse x, U y⟫_ℝ = ⟪x, y⟫_ℝ := by
  -- Move `U` from the second slot to the first by self-adjointness, then cancel `U⁻¹`.
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  calc
    ⟪U.inverse x, U y⟫_ℝ = ⟪U (U.inverse x), y⟫_ℝ := by
      simpa using (hU_self.isSymmetric (U.inverse x) y).symm
    _ = ⟪x, y⟫_ℝ := by
      rw [hInv.self_apply_inverse]

/-- The `U`-twisted pairing of differences agrees with the original inner product of the
corresponding inverse-transformed differences. -/
theorem inner_inverse_sub_map_sub_eq_inner_sub
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y u v : H) :
    ⟪U.inverse (x - y), U u - U v⟫_ℝ = ⟪x - y, u - v⟫_ℝ := by
  -- Normalize the second slot to a single `U`-image and reuse the basic inverse identity.
  rw [map_sub]
  simpa using inner_inverse_map_eq_inner U hU_self hU_strong (x - y) (u - v)

/-- The renormed Hilbert space `K` from Proposition 20.24, defined on the same vectors as `H`
with inner product `(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. -/
structure Renormed (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) where
  /-- The identity-on-vectors map from `H` to the renormed Hilbert space `K`. -/
  up (U hU_self hU_strong) ::
  /-- The underlying vector in the original Hilbert space `H`. -/
  down : H

namespace Renormed

variable (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)

/-- Coercion from the renormed Hilbert space back to the original ambient space. -/
instance instCoeOut : CoeOut (Renormed U hU_self hU_strong) H where
  coe := Renormed.down

/-- Converting an original-space vector into the renormed space and back does nothing. -/
@[simp] theorem down_up (x : H) :
    ((Renormed.up U hU_self hU_strong x : Renormed U hU_self hU_strong) : H) = x := by
  -- The wrapper stores the original vector unchanged.
  rfl

/-- Converting a renormed-space vector back to `H` and rewrapping it is the identity. -/
@[simp] theorem up_down (x : Renormed U hU_self hU_strong) :
    Renormed.up U hU_self hU_strong (x : H) = x := by
  -- `Renormed.up` is the inverse of the coercion back to `H`.
  cases x
  rfl

@[ext] theorem ext {x y : Renormed U hU_self hU_strong} (hxy : (x : H) = (y : H)) : x = y := by
  -- The wrapper has no extra data beyond the underlying vector.
  cases x
  cases y
  cases hxy
  rfl

/-- The renormed space is canonically equivalent to the original vector space. -/
private def equiv : Renormed U hU_self hU_strong ≃ H where
  toFun x := x
  invFun := Renormed.up U hU_self hU_strong
  left_inv := up_down U hU_self hU_strong
  right_inv := down_up U hU_self hU_strong

/-- Additive structure on the renormed space transported from `H`. -/
instance instAddCommGroup : AddCommGroup (Renormed U hU_self hU_strong) :=
  (equiv U hU_self hU_strong).addCommGroup

/-- Scalar multiplication on the renormed space transported from `H`. -/
instance instModule : Module ℝ (Renormed U hU_self hU_strong) :=
  (equiv U hU_self hU_strong).module ℝ

/-- The renormed space is linearly equivalent to the original ambient space. -/
private def linearEquiv : Renormed U hU_self hU_strong ≃ₗ[ℝ] H where
  toFun x := x
  invFun := Renormed.up U hU_self hU_strong
  left_inv := up_down U hU_self hU_strong
  right_inv := down_up U hU_self hU_strong
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Coercion from the renormed space preserves addition. -/
@[simp] theorem coe_add (x y : Renormed U hU_self hU_strong) :
    ((x + y : Renormed U hU_self hU_strong) : H) = (x : H) + (y : H) := by
  -- The transported additive structure is defined pointwise on the underlying vectors.
  cases x
  cases y
  rfl

/-- Coercion from the renormed space preserves subtraction. -/
@[simp] theorem coe_sub (x y : Renormed U hU_self hU_strong) :
    ((x - y : Renormed U hU_self hU_strong) : H) = (x : H) - (y : H) := by
  -- Subtraction is inherited from the ambient additive group structure.
  cases x
  cases y
  rfl

/-- Coercion from the renormed space preserves real scalar multiplication. -/
@[simp] theorem coe_smul (r : ℝ) (x : Renormed U hU_self hU_strong) :
    (((r • x : Renormed U hU_self hU_strong)) : H) = r • (x : H) := by
  -- The transported module structure is also pointwise on the underlying vectors.
  cases x
  rfl

/-- Helper for Proposition 20.24: the `U⁻¹`-twisted pairing can move the inverse from the left
slot to the right slot. -/
private theorem inner_inverse_eq_inner_inverse_right
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y : H) :
    ⟪U.inverse x, y⟫_ℝ = ⟪x, U.inverse y⟫_ℝ := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Insert `U (U⁻¹ y)` and move `U` across the inner product by self-adjointness.
  calc
    ⟪U.inverse x, y⟫_ℝ = ⟪U.inverse x, U (U.inverse y)⟫_ℝ := by
      rw [hInv.self_apply_inverse]
    _ = ⟪U (U.inverse x), U.inverse y⟫_ℝ := by
      simpa using (hU_self.isSymmetric (U.inverse x) (U.inverse y)).symm
    _ = ⟪x, U.inverse y⟫_ℝ := by
      rw [hInv.self_apply_inverse]

-- Route correction: instead of filling `innerProductSpaceCore` inline, record the stable pairing
-- and coercion rewrites as named lemmas and reuse them in the core fields.
/-- Helper for Proposition 20.24: the renormed pairing is symmetric up to conjugation. -/
private theorem twistedInner_conj_symm (x y : Renormed U hU_self hU_strong) :
    ⟪U.inverse (y : H), (x : H)⟫_ℝ = ⟪U.inverse (x : H), (y : H)⟫_ℝ := by
  -- Over `ℝ`, Hermitian symmetry is ordinary symmetry.
  simpa [real_inner_comm] using
    inner_inverse_eq_inner_inverse_right U hU_self hU_strong (y : H) (x : H)

/-- Helper for Proposition 20.24: the renormed pairing is nonnegative on the diagonal. -/
private theorem twistedInner_re_nonneg (x : Renormed U hU_self hU_strong) :
    0 ≤ ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Strong monotonicity of `U` applied to `U⁻¹ x` gives the required lower bound.
  have hbound :
      α * ‖U.inverse (x : H)‖ ^ 2 ≤ ⟪(x : H), U.inverse (x : H)⟫_ℝ := by
    simpa [hInv.self_apply_inverse (x : H)] using hU_strong.ineq (U.inverse (x : H))
  have hbound' :
      α * ‖U.inverse (x : H)‖ ^ 2 ≤ ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
    simpa [real_inner_comm] using hbound
  exact le_trans (mul_nonneg (le_of_lt hU_strong.pos) (sq_nonneg ‖U.inverse (x : H)‖)) hbound'

/-- Helper for Proposition 20.24: the renormed pairing is additive in the first slot. -/
private theorem twistedInner_add_left
    (x y z : Renormed U hU_self hU_strong) :
    ⟪U.inverse (((x + y : Renormed U hU_self hU_strong) : H)), (z : H)⟫_ℝ =
      ⟪U.inverse (x : H), (z : H)⟫_ℝ + ⟪U.inverse (y : H), (z : H)⟫_ℝ := by
  -- The additive structure is transported from `H`, so the ambient additivity lemma applies.
  simp [coe_add, map_add, inner_add_left]

/-- Helper for Proposition 20.24: the renormed pairing is linear in the first slot over `ℝ`. -/
private theorem twistedInner_smul_left
    (x y : Renormed U hU_self hU_strong) (r : ℝ) :
    ⟪U.inverse ((((r • x : Renormed U hU_self hU_strong)) : H)), (y : H)⟫_ℝ =
      r * ⟪U.inverse (x : H), (y : H)⟫_ℝ := by
  -- Over `ℝ`, conjugation is trivial and scalar multiplication commutes with `U⁻¹`.
  simpa [coe_smul, map_smul] using real_inner_smul_left (U.inverse (x : H)) (y : H) r

/-- Helper for Proposition 20.24: the renormed pairing is definite. -/
private theorem twistedInner_definite (x : Renormed U hU_self hU_strong)
    (hx : ⟪U.inverse (x : H), (x : H)⟫_ℝ = 0) :
    x = 0 := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Strong monotonicity forces `U⁻¹ x = 0`, hence also `x = 0`.
  have hineq :
      α * ‖U.inverse (x : H)‖ ^ 2 ≤ ⟪(x : H), U.inverse (x : H)⟫_ℝ := by
    simpa [hInv.self_apply_inverse (x : H)] using hU_strong.ineq (U.inverse (x : H))
  have hx' : ⟪(x : H), U.inverse (x : H)⟫_ℝ = 0 := by
    simpa [real_inner_comm] using hx
  have hbound : α * ‖U.inverse (x : H)‖ ^ 2 ≤ 0 := by
    simpa [hx'] using hineq
  have hnorm_zero : ‖U.inverse (x : H)‖ = 0 := by
    have hsq_zero : ‖U.inverse (x : H)‖ ^ 2 = 0 := by
      nlinarith [hbound, hU_strong.pos, sq_nonneg ‖U.inverse (x : H)‖]
    exact eq_zero_of_pow_eq_zero hsq_zero
  have hinv_zero : U.inverse (x : H) = 0 := norm_eq_zero.mp hnorm_zero
  apply ext U hU_self hU_strong
  simpa [hinv_zero] using (hInv.self_apply_inverse (x : H)).symm

/-- The inner-product core on the renormed space with pairing `(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. -/
@[reducible] private def innerProductSpaceCore
    : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) where
  inner x y := ⟪U.inverse (x : H), (y : H)⟫_ℝ
  conj_inner_symm := twistedInner_conj_symm U hU_self hU_strong
  re_inner_nonneg := twistedInner_re_nonneg U hU_self hU_strong
  add_left := twistedInner_add_left U hU_self hU_strong
  smul_left := twistedInner_smul_left U hU_self hU_strong
  definite := twistedInner_definite U hU_self hU_strong

/-- The inner-product core on the renormed space. -/
instance instInnerProductSpaceCore : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) :=
  innerProductSpaceCore U hU_self hU_strong

/-- The renormed inner-product-space structure on `H` with pairing
`(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. -/
instance instNormedAddCommGroup : NormedAddCommGroup (Renormed U hU_self hU_strong) :=
  letI : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) :=
    innerProductSpaceCore U hU_self hU_strong
  this.toNormedAddCommGroup

/-- The renormed inner-product-space structure on `H` with pairing
`(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. -/
instance instInnerProductSpace : InnerProductSpace ℝ (Renormed U hU_self hU_strong) := .ofCore _

/-- The renormed norm square is computed by the `U⁻¹`-twisted inner product. -/
private theorem norm_sq_eq_inner_inverse
    (x : Renormed U hU_self hU_strong) :
    ‖x‖ ^ 2 = ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
  -- In a real inner-product space, the norm square is the real part of `⟪x, x⟫`.
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ) x]
  rfl

/-- Helper for Proposition 20.24: strong monotonicity gives a lower bound on the renormed norm
in terms of the ambient norm of `U⁻¹ x`. -/
private theorem renormedNormSq_ge_inverseNormSq
    (x : Renormed U hU_self hU_strong) :
    α * ‖U.inverse (x : H)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Rewrite the strong-monotonicity estimate into the renormed norm square.
  calc
    α * ‖U.inverse (x : H)‖ ^ 2 ≤ ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
      simpa [real_inner_comm, hInv.self_apply_inverse (x : H)] using
        hU_strong.ineq (U.inverse (x : H))
    _ = ‖x‖ ^ 2 := by
      rw [← norm_sq_eq_inner_inverse U hU_self hU_strong x]

/-- Helper for Proposition 20.24: the ambient norm of `x` is controlled by `‖U‖` times the
ambient norm of `U⁻¹ x`. -/
private theorem originalNorm_le_opNorm_mul_inverseNorm
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x : H) :
    ‖x‖ ≤ ‖U‖ * ‖U.inverse x‖ := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Rewrite `x` as `U (U⁻¹ x)` and apply the operator norm estimate for `U`.
  calc
    ‖x‖ = ‖U (U.inverse x)‖ := by rw [hInv.self_apply_inverse]
    _ ≤ ‖U‖ * ‖U.inverse x‖ := ContinuousLinearMap.le_opNorm U (U.inverse x)

/-- The renormed norm is bounded above by the original norm times `√‖U⁻¹‖`. -/
private theorem norm_le_sqrt_inverse_norm_mul_original_norm
    (x : Renormed U hU_self hU_strong) :
    ‖x‖ ≤ Real.sqrt ‖U.inverse‖ * ‖(x : H)‖ := by
  -- Compare the renormed norm square with Cauchy-Schwarz and the operator norm of `U⁻¹`.
  have hsq :
      ‖x‖ ^ 2 ≤ (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 := by
    calc
      ‖x‖ ^ 2 = ⟪U.inverse (x : H), (x : H)⟫_ℝ := norm_sq_eq_inner_inverse U hU_self hU_strong x
      _ ≤ ‖U.inverse (x : H)‖ * ‖(x : H)‖ := by
        exact le_trans (le_abs_self _) <|
          by simpa using norm_inner_le_norm (𝕜 := ℝ) (U.inverse (x : H)) (x : H)
      _ ≤ (‖U.inverse‖ * ‖(x : H)‖) * ‖(x : H)‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm U.inverse (x : H)
      _ = (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 := by
        have hsquare :
            (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 =
              ‖U.inverse‖ * (‖(x : H)‖ * ‖(x : H)‖) := by
          calc
            (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 =
                (Real.sqrt ‖U.inverse‖)^2 * ‖(x : H)‖^2 := by
              ring
            _ = ‖U.inverse‖ * ‖(x : H)‖^2 := by
              rw [Real.sq_sqrt (norm_nonneg U.inverse)]
            _ = ‖U.inverse‖ * (‖(x : H)‖ * ‖(x : H)‖) := by
              ring
        simpa [pow_two, mul_assoc] using hsquare.symm
  have hleft_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
  have hright_nonneg : 0 ≤ Real.sqrt ‖U.inverse‖ * ‖(x : H)‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

/-- The original norm is bounded above by the renormed norm times `‖U‖ / √α`. -/
private theorem original_norm_le_opNorm_div_sqrt_mul_norm
    (x : Renormed U hU_self hU_strong) :
    ‖(x : H)‖ ≤ ‖U‖ / Real.sqrt α * ‖x‖ := by
  have hsqrt_pos : 0 < Real.sqrt α := Real.sqrt_pos.mpr hU_strong.pos
  have hinv_scaled :
      Real.sqrt α * ‖U.inverse (x : H)‖ ≤ ‖x‖ := by
    have hsq :
        (Real.sqrt α * ‖U.inverse (x : H)‖) ^ 2 ≤ ‖x‖ ^ 2 := by
      calc
        (Real.sqrt α * ‖U.inverse (x : H)‖) ^ 2 = α * ‖U.inverse (x : H)‖ ^ 2 := by
          calc
            (Real.sqrt α * ‖U.inverse (x : H)‖) ^ 2 =
                (Real.sqrt α)^2 * ‖U.inverse (x : H)‖^2 := by
              ring
            _ = α * ‖U.inverse (x : H)‖^2 := by
              rw [Real.sq_sqrt (le_of_lt hU_strong.pos)]
        _ ≤ ‖x‖ ^ 2 := renormedNormSq_ge_inverseNormSq U hU_self hU_strong x
    have hleft_nonneg : 0 ≤ Real.sqrt α * ‖U.inverse (x : H)‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hright_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith
  have hmain : ‖(x : H)‖ * Real.sqrt α ≤ ‖U‖ * ‖x‖ := by
    -- First bound `‖x‖` by `‖U‖ * ‖U⁻¹ x‖`, then absorb the `√α` factor into the renormed norm.
    calc
      ‖(x : H)‖ * Real.sqrt α = Real.sqrt α * ‖(x : H)‖ := by ring
      _ ≤ Real.sqrt α * (‖U‖ * ‖U.inverse (x : H)‖) := by
        gcongr
        exact originalNorm_le_opNorm_mul_inverseNorm U hU_self hU_strong (x : H)
      _ = ‖U‖ * (Real.sqrt α * ‖U.inverse (x : H)‖) := by ring
      _ ≤ ‖U‖ * ‖x‖ := by
        exact mul_le_mul_of_nonneg_left hinv_scaled (norm_nonneg U)
  -- Divide by the positive factor `√α` to obtain the ambient-to-renormed norm comparison.
  have hdiv : ‖(x : H)‖ ≤ (‖U‖ * ‖x‖) / Real.sqrt α := by
    exact (le_div_iff₀ hsqrt_pos).2 hmain
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

/-- The inverse of the canonical equivalence is bounded by `√‖U⁻¹‖`. -/
private theorem continuousLinearEquiv_symm_bound (x : H) :
    ‖Renormed.up U hU_self hU_strong x‖ ≤ Real.sqrt ‖U.inverse‖ * ‖x‖ := by
  -- The inverse map is just the wrapper `Renormed.up`, so the norm bound is the renormed bound.
  simpa using
    norm_le_sqrt_inverse_norm_mul_original_norm U hU_self hU_strong
      (Renormed.up U hU_self hU_strong x)

/-- The canonical continuous linear equivalence from the renormed Hilbert space back to `H`. -/
def continuousLinearEquiv : Renormed U hU_self hU_strong ≃L[ℝ] H :=
  (linearEquiv U hU_self hU_strong).toContinuousLinearEquivOfBounds
    (‖U‖ / Real.sqrt α) (Real.sqrt ‖U.inverse‖)
    (original_norm_le_opNorm_div_sqrt_mul_norm U hU_self hU_strong)
    (continuousLinearEquiv_symm_bound U hU_self hU_strong)

/-- The forward continuous linear equivalence acts as the identity on vectors. -/
@[simp] theorem continuousLinearEquiv_apply (x : Renormed U hU_self hU_strong) :
    continuousLinearEquiv U hU_self hU_strong x = (x : H) := by
  -- The underlying linear equivalence is the identity on vectors.
  rfl

/-- The inverse continuous linear equivalence also acts as the identity on vectors. -/
@[simp] theorem continuousLinearEquiv_symm_apply (x : H) :
    (continuousLinearEquiv U hU_self hU_strong).symm x =
      Renormed.up U hU_self hU_strong x := by
  -- The inverse equivalence is exactly the wrapper map.
  rfl

/-- Completeness transfers from `H` to the renormed Hilbert space. -/
instance instCompleteSpace
    : CompleteSpace (Renormed U hU_self hU_strong) := by
  -- Transfer completeness across the canonical continuous linear equivalence.
  let e := (continuousLinearEquiv U hU_self hU_strong).symm
  have he : IsUniformEmbedding e.toEquiv := e.isUniformEmbedding
  exact (completeSpace_congr (e := e.toEquiv) he).1 inferInstance

end Renormed

end ContinuousLinearMap

namespace SetValuedOperator

open ContinuousLinearMap
open ContinuousLinearMap.Renormed

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Reinterpret a set-valued operator on `H` as one on the renormed Hilbert space from
Proposition 20.24. This is a pure change of ambient inner product, not a new operator. -/
abbrev renormed (A : SetValuedOperator H H) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U)
    {α : ℝ} (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    SetValuedOperator
      (Renormed U hU_self hU_strong)
      (Renormed U hU_self hU_strong) :=
  let e := continuousLinearEquiv U hU_self hU_strong
  (((e.symm : H → Renormed U hU_self hU_strong).toSetValuedOperator)).comp
    (A.comp ((e : Renormed U hU_self hU_strong → H).toSetValuedOperator))

/-- Membership in `U A` is equivalent to membership in `A` after applying `U⁻¹` to the value. -/
@[simp] private theorem mem_comp_toSetValuedOperator_iff_inverse_mem
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) {α : ℝ}
    (hU_self : IsSelfAdjoint U) (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x u : H) :
    u ∈ ((((U : H → H).toSetValuedOperator).comp A) : SetValuedOperator H H) x ↔
      U.inverse u ∈ A x := by
  -- Unfold composition once; the singleton witness is exactly `U⁻¹ u`.
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  constructor
  · intro hu
    rcases (SetValuedOperator.mem_comp _ _ _ _).1 hu with ⟨v, hvA, hvu⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hvu
    rw [hvu, hInv.inverse_apply_self]
    exact hvA
  · intro hu
    refine (SetValuedOperator.mem_comp _ _ _ _).2 ?_
    refine ⟨U.inverse u, hu, ?_⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    exact (hInv.self_apply_inverse u).symm

/-- The canonical owner `Maximal SetValuedOperator.IsMonotone` on the renormed Hilbert space from
Proposition 20.24 unfolds to the source pairing formula
`⟪U⁻¹ (x - y), u - v⟫_ℝ`. -/
-- Membership in the renormed copy of `A` is just ordinary membership after forgetting the
-- wrapper.
@[simp] private theorem mem_renormed_iff
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)
    (x u : Renormed U hU_self hU_strong) :
    u ∈ A.renormed U hU_self hU_strong x ↔ (u : H) ∈ A (x : H) := by
  -- Unfold the conjugation by the canonical equivalence and collapse the singleton witnesses.
  constructor
  · intro hu
    rcases (SetValuedOperator.mem_comp _ _ _ _).1 hu with ⟨y, hyA, hyu⟩
    rcases (SetValuedOperator.mem_comp _ _ _ _).1 hyA with ⟨z, hz, hyA⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hz hyu
    have hz' : z = (x : H) := by
      simpa using hz
    have hy' : (u : H) = y := by
      simpa [continuousLinearEquiv_symm_apply] using
        congrArg (fun w : Renormed U hU_self hU_strong => (w : H)) hyu
    simpa [hy', hz'] using hyA
  · intro hu
    refine (SetValuedOperator.mem_comp _ _ _ _).2 ?_
    refine ⟨(u : H), ?_, ?_⟩
    · refine (SetValuedOperator.mem_comp _ _ _ _).2 ?_
      refine ⟨(x : H), ?_, hu⟩
      rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
      simp
    · rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
      simp [continuousLinearEquiv_symm_apply]

/-- Helper for Proposition 20.24: the renormed inner product on wrapped differences matches the
ambient `U⁻¹`-twisted pairing after expanding the linear subtraction. -/
@[simp] private theorem inner_up_sub_up_eq_twisted
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y u v : H) :
    ⟪Renormed.up U hU_self hU_strong x - Renormed.up U hU_self hU_strong y,
      Renormed.up U hU_self hU_strong u - Renormed.up U hU_self hU_strong v⟫_ℝ =
        ⟪U.inverse (x - y), u - v⟫_ℝ := by
  rfl

/-- Helper for Proposition 20.24: forgetting the wrapper rewrites the renormed inner product back
to the ambient `U⁻¹`-twisted pairing. -/
@[simp] private theorem inner_renormed_sub_eq_twisted
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)
    (x y u v : Renormed U hU_self hU_strong) :
    ⟪x - y, u - v⟫_ℝ =
      ⟪U.inverse ((x : H) - (y : H)), (u : H) - (v : H)⟫_ℝ := by
  rfl

theorem isMaximallyMonotone_renormed_iff
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    Maximal SetValuedOperator.IsMonotone (A.renormed U hU_self hU_strong) ↔
      ∀ x u : H, u ∈ A x ↔
        ∀ ⦃y v : H⦄, v ∈ A y →
          0 ≤ ⟪U.inverse (x - y), u - v⟫_ℝ := by
  -- Translate the renormed Minty criterion through the identity-on-vectors equivalence.
  rw [SetValuedOperator.maximal_iff_mem_iff]
  constructor
  · intro hRen x u
    have hRenXu := hRen (Renormed.up U hU_self hU_strong x) (Renormed.up U hU_self hU_strong u)
    constructor
    · intro hu y v hv
      have huR :
          Renormed.up U hU_self hU_strong u ∈
            A.renormed U hU_self hU_strong (Renormed.up U hU_self hU_strong x) := by
        simpa using (mem_renormed_iff A U hU_self hU_strong
          (Renormed.up U hU_self hU_strong x) (Renormed.up U hU_self hU_strong u)).2 hu
      have hvR :
          Renormed.up U hU_self hU_strong v ∈
            A.renormed U hU_self hU_strong (Renormed.up U hU_self hU_strong y) := by
        simpa using (mem_renormed_iff A U hU_self hU_strong
          (Renormed.up U hU_self hU_strong y) (Renormed.up U hU_self hU_strong v)).2 hv
      -- Test the renormed Minty relation on the wrapped graph point `(y, v)`.
      simpa using hRenXu.1 huR hvR
    · intro hrel
      have hrelR :
          ∀ ⦃y v : Renormed U hU_self hU_strong⦄,
            v ∈ A.renormed U hU_self hU_strong y →
              0 ≤
                ⟪Renormed.up U hU_self hU_strong x - y,
                  Renormed.up U hU_self hU_strong u - v⟫_ℝ := by
        intro y v hv
        have hvH : (v : H) ∈ A (y : H) := (mem_renormed_iff A U hU_self hU_strong y v).1 hv
        -- Forget the wrapper and apply the source-side criterion to the ambient vectors.
        simpa using hrel (y := (y : H)) (v := (v : H)) hvH
      have huR :
          Renormed.up U hU_self hU_strong u ∈
            A.renormed U hU_self hU_strong (Renormed.up U hU_self hU_strong x) :=
        hRenXu.2 hrelR
      exact (mem_renormed_iff A U hU_self hU_strong
        (Renormed.up U hU_self hU_strong x) (Renormed.up U hU_self hU_strong u)).1 huR
  · intro hSrc x u
    constructor
    · intro hu y v hv
      have huH : (u : H) ∈ A (x : H) := (mem_renormed_iff A U hU_self hU_strong x u).1 hu
      have hvH : (v : H) ∈ A (y : H) := (mem_renormed_iff A U hU_self hU_strong y v).1 hv
      -- Apply the source-side Minty criterion to the ambient vectors `(x, u)` and `(y, v)`.
      simpa using (hSrc (x : H) (u : H)).1 huH hvH
    · intro hrel
      have hrelH :
          ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪U.inverse ((x : H) - y), (u : H) - v⟫_ℝ := by
        intro y v hv
        have hvR :
            Renormed.up U hU_self hU_strong v ∈
              A.renormed U hU_self hU_strong (Renormed.up U hU_self hU_strong y) := by
          simpa using (mem_renormed_iff A U hU_self hU_strong
            (Renormed.up U hU_self hU_strong y) (Renormed.up U hU_self hU_strong v)).2 hv
        -- Rewrap the ambient graph point `(y, v)` and feed it to the renormed Minty relation.
        simpa using
          hrel (y := Renormed.up U hU_self hU_strong y)
            (v := Renormed.up U hU_self hU_strong v) hvR
      exact (mem_renormed_iff A U hU_self hU_strong x u).2 ((hSrc (x : H) (u : H)).2 hrelH)

/-- Proposition 20.24: if `A` is maximally monotone and `U` is self-adjoint and strongly
monotone, then the operator `U A = U.toSetValuedOperator.comp A` is maximally monotone
on the renormed Hilbert space `ContinuousLinearMap.Renormed U hU_self hU_strong` whose inner
product is
`(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. The companion theorem
`isMaximallyMonotone_renormed_iff` rewrites this canonical maximal-monotonicity statement back
into the source pairing formula. -/
theorem comp_isMaximallyMonotone_of_isSelfAdjoint_of_isStronglyMonotone
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) {α : ℝ}
    (hA : Maximal SetValuedOperator.IsMonotone A) (hU_self : IsSelfAdjoint U)
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    Maximal SetValuedOperator.IsMonotone
      ((((U : H → H).toSetValuedOperator).comp A).renormed U hU_self hU_strong) := by
  have hInv : U.IsInvertible :=
    isInvertible_of_isSelfAdjoint_of_isStronglyMonotone U hU_self hU_strong
  -- Reduce maximality of `U A` on the renormed space to the ambient Minty criterion from `A`.
  rw [isMaximallyMonotone_renormed_iff]
  intro x u
  rw [mem_comp_toSetValuedOperator_iff_inverse_mem A U hU_self hU_strong x u]
  constructor
  · intro hu y v hv
    rw [mem_comp_toSetValuedOperator_iff_inverse_mem A U hU_self hU_strong y v] at hv
    have hsource :
        0 ≤ ⟪x - y, U.inverse u - U.inverse v⟫_ℝ :=
      (Maximal.mem_iff hA x (U.inverse u)).1 hu hv
    have htransport :
        ⟪U.inverse x - U.inverse y, u - v⟫_ℝ = ⟪x - y, U.inverse u - U.inverse v⟫_ℝ := by
      -- Rewrite the renormed pairing back to the original-space pairing for `A`.
      simpa [map_sub, hInv.self_apply_inverse u, hInv.self_apply_inverse v] using
        inner_inverse_sub_map_sub_eq_inner_sub U hU_self hU_strong x y
          (U.inverse u) (U.inverse v)
    simpa [htransport] using hsource
  · intro hrel
    refine (Maximal.mem_iff hA x (U.inverse u)).2 ?_
    intro y w hw
    have hUw :
        U w ∈ ((((U : H → H).toSetValuedOperator).comp A) : SetValuedOperator H H) y := by
      rw [mem_comp_toSetValuedOperator_iff_inverse_mem A U hU_self hU_strong y (U w)]
      simpa [hInv.inverse_apply_self] using hw
    have htarget :
        0 ≤ ⟪U.inverse (x - y), u - U w⟫_ℝ :=
      hrel (y := y) (v := U w) hUw
    have htransport :
        ⟪U.inverse x - U.inverse y, u - U w⟫_ℝ = ⟪x - y, U.inverse u - w⟫_ℝ := by
      -- This is the same transport identity, now specialized to the witness `w ∈ A y`.
      simpa [map_sub, hInv.self_apply_inverse u] using
        inner_inverse_sub_map_sub_eq_inner_sub U hU_self hU_strong x y (U.inverse u) w
    simpa [map_sub, htransport] using htarget

end SetValuedOperator

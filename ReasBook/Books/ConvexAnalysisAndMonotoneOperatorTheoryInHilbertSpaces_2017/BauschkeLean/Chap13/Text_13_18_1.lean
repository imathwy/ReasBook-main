import Mathlib
import BauschkeLean.Chap13.Example_13_18
import BauschkeLean.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {α β : Set.Ioi (0 : ℝ)} {A B : S(H)}

/-- Helper for Text 13 18 1: a Loewner lower scalar bound yields the corresponding quadratic-form
lower bound. -/
lemma loewner_scalar_lower_bound_inner_sq {γ : Set.Ioi (0 : ℝ)} {T : S(H)}
    (hγT : (γ : ℝ) • 1 ≤ T) :
    ∀ x : H, (γ : ℝ) * ‖x‖ ^ 2 ≤ ⟪(T : H →L[ℝ] H) x, x⟫_ℝ := by
  -- Evaluate the Loewner inequality on an arbitrary vector.
  intro x
  have hinner := (loewner_le_iff_forall_inner_le ((γ : ℝ) • 1) T).mp hγT x
  simpa [inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm, mul_left_comm, mul_assoc] using
    hinner

/-- Helper for Text 13 18 1: a positive scalar Loewner lower bound forces nonnegativity. -/
lemma loewner_nonneg_of_pos_scalar_lower_bound {γ : Set.Ioi (0 : ℝ)} {T : S(H)}
    (hγT : (γ : ℝ) • 1 ≤ T) :
    0 ≤ T := by
  -- Compare `0` with the positive scalar lower endpoint and then use the assumed sandwich.
  rw [loewner_le_iff_forall_inner_le]
  intro x
  calc
    ⟪(((0 : S(H)) : H →L[ℝ] H) x), x⟫_ℝ = 0 := by simp
    _ ≤ (γ : ℝ) * ‖x‖ ^ 2 := by
      exact mul_nonneg γ.2.le (sq_nonneg ‖x‖)
    _ ≤ ⟪(T : H →L[ℝ] H) x, x⟫_ℝ := loewner_scalar_lower_bound_inner_sq hγT x

/-- Helper for Text 13 18 1: a positive scalar lower bound yields invertibility. -/
lemma isUnit_of_loewner_scalar_lower_bound {γ : Set.Ioi (0 : ℝ)} {T : S(H)}
    (hγT : (γ : ℝ) • 1 ≤ T) :
    IsUnit (T : H →L[ℝ] H) := by
  set c : ℝ := (γ : ℝ)
  have hc : 0 < c := γ.2
  have hbound := loewner_scalar_lower_bound_inner_sq hγT
  -- Feed the quadratic lower bound into the standard invertibility criterion.
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (T : H →L[ℝ] H) (c := ⟨c, hc.le⟩) hc ?_
  intro x
  calc
    ‖x‖ ^ 2 * c = (γ : ℝ) * ‖x‖ ^ 2 := by
      simp [c, mul_comm]
    _ ≤ ⟪(T : H →L[ℝ] H) x, x⟫_ℝ := hbound x
    _ ≤ ‖⟪(T : H →L[ℝ] H) x, x⟫_ℝ‖ := le_abs_self _

/-- Helper for Text 13 18 1: the inverse of an invertible self-adjoint operator is self-adjoint. -/
lemma inverse_isSelfAdjoint_of_isSelfAdjoint_of_isUnit {T : H →L[ℝ] H}
    (hT_self : IsSelfAdjoint T) (hT_unit : IsUnit T) :
    IsSelfAdjoint T.inverse := by
  -- Lift `T` to a unit and use that star commutes with inversion.
  rcases hT_unit with ⟨u, rfl⟩
  have hu_self : star u = u := by
    apply Units.ext
    simpa using hT_self.star_eq
  rw [← ringInverse_eq_inverse, Ring.inverse_unit]
  change star ((↑u⁻¹ : H →L[ℝ] H)) = (↑u⁻¹ : H →L[ℝ] H)
  have hu_inv_self : star u⁻¹ = u⁻¹ := by
    simpa using congrArg Inv.inv hu_self
  simpa using congrArg Units.val hu_inv_self

/-- Helper for Text 13 18 1: inversion reverses the Loewner order on nonnegative invertible
self-adjoint operators. -/
lemma selfAdjoint_inverse_antitone_of_nonneg_of_isUnit {P Q : S(H)}
    (hP_nonneg : 0 ≤ P) (hPQ : P ≤ Q)
    (hP_unit : IsUnit (P : H →L[ℝ] H)) (hQ_unit : IsUnit (Q : H →L[ℝ] H)) :
    (Q : H →L[ℝ] H).inverse ≤ (P : H →L[ℝ] H).inverse := by
  let p : H →L[ℝ] H := (P : H →L[ℝ] H)
  let q : H →L[ℝ] H := (Q : H →L[ℝ] H)
  have hp_self : IsSelfAdjoint p := P.2
  have hq_self : IsSelfAdjoint q := Q.2
  have hpInv_self : IsSelfAdjoint p.inverse :=
    inverse_isSelfAdjoint_of_isSelfAdjoint_of_isUnit hp_self hP_unit
  have hqInv_self : IsSelfAdjoint q.inverse :=
    inverse_isSelfAdjoint_of_isSelfAdjoint_of_isUnit hq_self hQ_unit
  have hp_quad : ∀ y : H, 0 ≤ ⟪p y, y⟫_ℝ := by
    intro y
    simpa [p] using (loewner_le_iff_forall_inner_le (0 : S(H)) P).mp hP_nonneg y
  have hgap_quad : ∀ y : H, 0 ≤ ⟪((Q - P : S(H)) : H →L[ℝ] H) y, y⟫_ℝ := by
    intro y
    have hPQy : ⟪p y, y⟫_ℝ ≤ ⟪q y, y⟫_ℝ :=
      by simpa [p, q] using (loewner_le_iff_forall_inner_le P Q).mp hPQ y
    simpa [p, q, sub_apply, inner_sub_left] using sub_nonneg.mpr hPQy
  -- Route correction: replace the unavailable real-functional-calculus route by the textbook
  -- quadratic-form identity for the inverse gap.
  rw [ContinuousLinearMap.le_def]
  refine (ContinuousLinearMap.isPositive_iff' (p.inverse - q.inverse)).mpr ?_
  refine ⟨?_, ?_⟩
  · -- The inverse gap is self-adjoint because each inverse is self-adjoint.
    change star (p.inverse - q.inverse) = p.inverse - q.inverse
    simp [hpInv_self.star_eq, hqInv_self.star_eq]
  · intro x
    let u : H := q.inverse x
    let d : H := p.inverse x - u
    have hp_cancel : p (p.inverse x) = x := by
      simpa [p, ← ringInverse_eq_inverse] using
        congrArg (fun S : H →L[ℝ] H ↦ S x) (Ring.mul_inverse_cancel p hP_unit)
    have hq_cancel : q u = x := by
      -- Cancel `q` against its inverse on `x`.
      simpa [q, u, ← ringInverse_eq_inverse] using
        congrArg (fun S : H →L[ℝ] H ↦ S x) (Ring.mul_inverse_cancel q hQ_unit)
    have hd_image : p d = (q - p) u := by
      -- The error term `d` records exactly the gap between the two inverse images.
      calc
        p d = p (p.inverse x - u) := by rfl
        _ = p (p.inverse x) - p u := by simp [map_sub]
        _ = x - p u := by rw [hp_cancel]
        _ = q u - p u := by rw [hq_cancel]
        _ = (q - p) u := by simp [sub_apply]
    have hqu_decomp : q u = p d + p u := by
      -- Re-express `q u` using the error identity `p d = (q - p) u`.
      calc
        q u = (q - p) u + p u := by simp [sub_apply]
        _ = p d + p u := by rw [← hd_image]
    have hqu_decomp' : p u + p d = q u := by
      -- This is the same decomposition with the summands reordered.
      rw [hqu_decomp, add_comm]
    have hsum_nonneg : 0 ≤ ⟪(q - p) u, u⟫_ℝ + ⟪p d, d⟫_ℝ := by
      -- Both summands are nonnegative quadratic forms.
      simpa [p, q] using add_nonneg (hgap_quad u) (hp_quad d)
    have hgap_nonneg : 0 ≤ ⟪(p.inverse - q.inverse) x, x⟫_ℝ := by
      -- Expand the inverse gap into the sum of the gap term and the positive `P`-energy of `d`.
      calc
        0 ≤ ⟪(q - p) u, u⟫_ℝ + ⟪p d, d⟫_ℝ := hsum_nonneg
        _ = ⟪(p.inverse - q.inverse) x, x⟫_ℝ := by
          calc
            ⟪(q - p) u, u⟫_ℝ + ⟪p d, d⟫_ℝ
                = ⟪p d, d⟫_ℝ + ⟪p d, u⟫_ℝ := by rw [hd_image, add_comm]
            _ = ⟪d, p d⟫_ℝ + ⟪p d, u⟫_ℝ := by
              simpa using congrArg (fun t : ℝ ↦ t + ⟪p d, u⟫_ℝ) (hp_self.isSymmetric d d)
            _ = ⟪d, p d⟫_ℝ + ⟪d, p u⟫_ℝ := by
              simpa using congrArg (fun t : ℝ ↦ ⟪d, p d⟫_ℝ + t) (hp_self.isSymmetric d u)
            _ = ⟪d, p d + p u⟫_ℝ := by rw [inner_add_right]
            _ = ⟪d, p u + p d⟫_ℝ := by rw [show p d + p u = p u + p d by simp [add_comm]]
            _ = ⟪d, q u⟫_ℝ := by rw [hqu_decomp']
            _ = ⟪(p.inverse - q.inverse) x, x⟫_ℝ := by
              simp [p, q, d, u, hq_cancel, sub_apply]
    simpa using hgap_nonneg

-- Proof sketch: from `β • 1 ≤ B ≤ A` in the self-adjoint Loewner order, both operators are
-- positive and bounded below away from zero, hence invertible. Apply the standard order-reversing
-- property of inversion on positive operators.
/-- Text 13 18 1: clause (i). For self-adjoint operators, if `β • Id ≤ B ≤ A`, then taking
inverses reverses the Loewner order: `A⁻¹ ≤ B⁻¹`. -/
theorem sandwiched_positive_operators_inverse_antitone
    (hBA : B ≤ A)
    (hβB : (β : ℝ) • 1 ≤ B) :
    (A : H →L[ℝ] H).inverse ≤ (B : H →L[ℝ] H).inverse := by
  have hβA : (β : ℝ) • 1 ≤ A := hβB.trans hBA
  have hB_nonneg : 0 ≤ B := loewner_nonneg_of_pos_scalar_lower_bound hβB
  have hA_unit : IsUnit (A : H →L[ℝ] H) := isUnit_of_loewner_scalar_lower_bound hβA
  have hB_unit : IsUnit (B : H →L[ℝ] H) := isUnit_of_loewner_scalar_lower_bound hβB
  -- Apply inverse antitonicity to the positive operators `B ≤ A`.
  exact selfAdjoint_inverse_antitone_of_nonneg_of_isUnit hB_nonneg hBA hB_unit hA_unit

-- Proof sketch: the lower bound `β • 1 ≤ B` in `S(H)` makes `B` positive and bounded below away
-- from zero, hence injective with closed range, so `B` is invertible.
/-- Clause (i): a self-adjoint operator `B` is invertible as soon as `β • Id ≤ B`. -/
theorem sandwiched_positive_operators_right_isUnit
    (hβB : (β : ℝ) • 1 ≤ B) :
    IsUnit (B : H →L[ℝ] H) := by
  -- Reuse the direct lower-bound invertibility criterion established above.
  exact isUnit_of_loewner_scalar_lower_bound hβB

omit [CompleteSpace H] in
/-- Helper for Text 13 18 1: the inverse of a positive scalar multiple of `Id` is the reciprocal
scalar multiple of `Id`. -/
lemma inverse_scalar_smul_one (γ : Set.Ioi (0 : ℝ)) :
    (((γ : ℝ) • (1 : H →L[ℝ] H)).inverse) = ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H) := by
  -- Rewrite the scalar operator through `algebraMap` and compute its ring inverse.
  have hγ_unit : IsUnit (γ : ℝ) := isUnit_iff_ne_zero.mpr (ne_of_gt γ.2)
  let u : (H →L[ℝ] H)ˣ := hγ_unit.unit.map (algebraMap ℝ (H →L[ℝ] H))
  rw [← Algebra.algebraMap_eq_smul_one, ← ringInverse_eq_inverse]
  change Ring.inverse (↑u : H →L[ℝ] H) = ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H)
  rw [Ring.inverse_unit]
  simp [u, Algebra.algebraMap_eq_smul_one]

/-- Helper for Text 13 18 1: a scalar Loewner lower bound yields the operator-norm bound on the
inverse. -/
lemma inverse_norm_bound_of_loewner_lower_bound {γ : Set.Ioi (0 : ℝ)} {T : S(H)}
    (hγT : (γ : ℝ) • 1 ≤ T) :
    ∀ x : H, ‖(T : H →L[ℝ] H).inverse x‖ ≤ (γ : ℝ)⁻¹ * ‖x‖ := by
  -- Apply the lower quadratic bound to `T⁻¹ x` and cancel one factor of its norm.
  let f : H →L[ℝ] H := (T : H →L[ℝ] H)
  have hT_unit : IsUnit f := sandwiched_positive_operators_right_isUnit hγT
  have hbound := loewner_scalar_lower_bound_inner_sq hγT
  intro x
  let y : H := f.inverse x
  have hy_image : f y = x := by
    -- Cancel the inverse on the right.
    simpa [f, y, ← ringInverse_eq_inverse] using
      congrArg (fun S : H →L[ℝ] H ↦ S x) (Ring.mul_inverse_cancel f hT_unit)
  have hy_estimate : (γ : ℝ) * ‖y‖ ^ 2 ≤ ‖x‖ * ‖y‖ := by
    calc
      (γ : ℝ) * ‖y‖ ^ 2 ≤ ⟪f y, y⟫_ℝ := hbound y
      _ = ⟪x, y⟫_ℝ := by rw [hy_image]
      _ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm _ _
  by_cases hy_zero : y = 0
  · -- The zero case is immediate.
    have hy_eval : (T : H →L[ℝ] H).inverse x = 0 := by
      simpa [f, y] using hy_zero
    simpa [hy_eval] using
      (show 0 ≤ (γ : ℝ)⁻¹ * ‖x‖ from mul_nonneg (inv_nonneg.mpr γ.2.le) (norm_nonneg x))
  · -- Otherwise divide the quadratic estimate by `‖y‖`.
    have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy_zero
    have hcancel : (γ : ℝ) * ‖y‖ ≤ ‖x‖ := by
      nlinarith [hy_estimate, γ.2, hy_norm_pos]
    have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
    have hγ_inv_nonneg : 0 ≤ (γ : ℝ)⁻¹ := inv_nonneg.mpr γ.2.le
    calc
      ‖(T : H →L[ℝ] H).inverse x‖ = ‖y‖ := by simp [f, y]
      _ = (γ : ℝ)⁻¹ * ((γ : ℝ) * ‖y‖) := by
        field_simp [hγ_ne]
      _ ≤ (γ : ℝ)⁻¹ * ‖x‖ := by
        gcongr
      _ = (γ : ℝ)⁻¹ * ‖x‖ := rfl

-- Proof sketch: the direct lower bound `β • 1 ≤ A` makes `A` positive and bounded below away
-- from zero, hence invertible. Compare `A` with `α • 1` and reverse the order after inversion.
/-- Clause (i): if the self-adjoint operator `A` satisfies `β • Id ≤ A ≤ α • Id`, then `A⁻¹`
dominates `α⁻¹ • Id`. -/
theorem sandwiched_positive_operators_left_endpoint_le_inverse
    (hA_upper : A ≤ (α : ℝ) • 1)
    (hβA : (β : ℝ) • 1 ≤ A) :
    ((α : ℝ)⁻¹) • (1 : H →L[ℝ] H) ≤ (A : H →L[ℝ] H).inverse := by
  have hA_nonneg : 0 ≤ A := loewner_nonneg_of_pos_scalar_lower_bound hβA
  have hA_unit : IsUnit (A : H →L[ℝ] H) := sandwiched_positive_operators_right_isUnit hβA
  have hα_unit : IsUnit (((α : ℝ) • (1 : S(H)) : S(H)) : H →L[ℝ] H) :=
    isUnit_of_loewner_scalar_lower_bound (T := (α : ℝ) • (1 : S(H))) le_rfl
  -- Compare `A` with the scalar upper endpoint and then simplify the scalar inverse.
  simpa [inverse_scalar_smul_one] using
    selfAdjoint_inverse_antitone_of_nonneg_of_isUnit
      (P := A) (Q := (α : ℝ) • (1 : S(H))) hA_nonneg hA_upper hA_unit hα_unit

-- Proof sketch: first prove that `B` is invertible. Then compare `β • 1` with `B` and reverse
-- the order after taking inverses.
/-- Clause (i): if `B` is self-adjoint and `β • Id ≤ B`, then `B⁻¹` is bounded above by
`β⁻¹ • Id`. -/
theorem sandwiched_positive_operators_inverse_le_right_endpoint
    (hβB : (β : ℝ) • 1 ≤ B) :
    (B : H →L[ℝ] H).inverse ≤ ((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) := by
  let f : H →L[ℝ] H := (B : H →L[ℝ] H)
  have hB_unit : IsUnit f := sandwiched_positive_operators_right_isUnit hβB
  have hInv_self : IsSelfAdjoint f.inverse :=
    inverse_isSelfAdjoint_of_isSelfAdjoint_of_isUnit B.2 hB_unit
  -- Show positivity of the scalar gap by evaluating it on arbitrary vectors.
  rw [ContinuousLinearMap.le_def]
  refine (ContinuousLinearMap.isPositive_iff' (((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) - f.inverse)).mpr ?_
  refine ⟨?_, ?_⟩
  · -- Both summands are self-adjoint, so their difference is self-adjoint.
    change star (((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) - f.inverse) =
        ((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) - f.inverse
    simp [hInv_self.star_eq]
  · intro x
    let y : H := f.inverse x
    have hy_bound := inverse_norm_bound_of_loewner_lower_bound hβB x
    have hinner_upper : ⟪f.inverse x, x⟫_ℝ ≤ (β : ℝ)⁻¹ * ‖x‖ ^ 2 := by
      -- Bound the quadratic form by Cauchy-Schwarz and the pointwise inverse norm estimate.
      calc
        ⟪f.inverse x, x⟫_ℝ = ⟪y, x⟫_ℝ := by rfl
        _ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm _ _
        _ ≤ ((β : ℝ)⁻¹ * ‖x‖) * ‖x‖ := by
          gcongr
        _ = (β : ℝ)⁻¹ * ‖x‖ ^ 2 := by ring
    -- Rewrite the gap as the scalar quadratic form minus the inverse quadratic form.
    calc
      0 ≤ (β : ℝ)⁻¹ * ‖x‖ ^ 2 - ⟪f.inverse x, x⟫_ℝ := sub_nonneg.mpr hinner_upper
      _ = ⟪(((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) x), x⟫_ℝ - ⟪f.inverse x, x⟫_ℝ := by
        simp [real_inner_smul_left, inner_self_eq_norm_sq_to_K, pow_two]
      _ = ⟪((((β : ℝ)⁻¹) • (1 : H →L[ℝ] H) - f.inverse) x), x⟫_ℝ := by
        simp [sub_apply, inner_sub_left]

-- Proof sketch: for a positive self-adjoint operator, positivity gives the order bound
-- `A ≤ ‖A‖ • 1`. Reverse that inequality after inversion and evaluate the resulting operator
-- inequality on `x`.
/-- Clause (ii): for a positive invertible self-adjoint operator, the quadratic form of the
inverse is bounded below by `‖A‖⁻¹ ‖x‖²`. -/
theorem positive_unit_operator_inverse_inner_self_ge_inv_norm
    (A : S(H)) (hA_nonneg : 0 ≤ A)
    (hA_unit : IsUnit (A : H →L[ℝ] H)) (x : H) :
    ((‖(A : H →L[ℝ] H)‖ : ℝ)⁻¹) * ‖x‖ ^ 2 ≤
      ⟪((A : H →L[ℝ] H).inverse) x, x⟫_ℝ := by
  by_cases hH : Subsingleton H
  · -- On a subsingleton space every vector is zero, so both quadratic forms vanish.
    have hx0 : x = 0 := Subsingleton.elim _ _
    subst hx0
    simp
  letI : Nontrivial H := not_subsingleton_iff_nontrivial.mp hH
  have hA_ne_zero : (A : H →L[ℝ] H) ≠ 0 := by
    rcases hA_unit with ⟨u, hu⟩
    simpa [hu] using (u.ne_zero : (↑u : H →L[ℝ] H) ≠ 0)
  have hnorm_pos : 0 < ‖(A : H →L[ℝ] H)‖ := by
    have hnorm_ne : ‖(A : H →L[ℝ] H)‖ ≠ 0 := by
      intro hzero
      exact hA_ne_zero ((ContinuousLinearMap.opNorm_zero_iff (f := (A : H →L[ℝ] H))).mp hzero)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm_ne)
  let γ : Set.Ioi (0 : ℝ) := ⟨‖(A : H →L[ℝ] H)‖, hnorm_pos⟩
  have hA_upper : A ≤ (γ : ℝ) • 1 := by
    -- Bound a positive self-adjoint operator above by its operator norm times the identity.
    rw [loewner_le_iff_forall_inner_le]
    intro y
    have hAy_nonneg : 0 ≤ ⟪(A : H →L[ℝ] H) y, y⟫_ℝ := by
      simpa using (loewner_le_iff_forall_inner_le (0 : S(H)) A).mp hA_nonneg y
    calc
      ⟪(A : H →L[ℝ] H) y, y⟫_ℝ = ‖⟪(A : H →L[ℝ] H) y, y⟫_ℝ‖ := by
        rw [Real.norm_of_nonneg hAy_nonneg]
      _ ≤ ‖(A : H →L[ℝ] H) y‖ * ‖y‖ := by
        simpa [Real.norm_eq_abs] using abs_real_inner_le_norm ((A : H →L[ℝ] H) y) y
      _ ≤ (‖(A : H →L[ℝ] H)‖ * ‖y‖) * ‖y‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm (A : H →L[ℝ] H) y
      _ = (γ : ℝ) * ‖y‖ ^ 2 := by
        simp [γ, pow_two, mul_assoc]
      _ = ⟪(((γ : ℝ) • (1 : H →L[ℝ] H)) y), y⟫_ℝ := by
        simp [real_inner_smul_left, inner_self_eq_norm_sq_to_K, pow_two]
  have hγ_unit : IsUnit (((γ : ℝ) • (1 : S(H)) : S(H)) : H →L[ℝ] H) :=
    isUnit_of_loewner_scalar_lower_bound (T := (γ : ℝ) • (1 : S(H))) le_rfl
  have hscalar_le :
      ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H) ≤ (A : H →L[ℝ] H).inverse := by
    -- Reverse the norm-endpoint inequality through inversion.
    simpa [inverse_scalar_smul_one] using
      selfAdjoint_inverse_antitone_of_nonneg_of_isUnit
        (P := A) (Q := (γ : ℝ) • (1 : S(H))) hA_nonneg hA_upper hA_unit hγ_unit
  have hx_nonneg :
      0 ≤
        ⟪(((A : H →L[ℝ] H).inverse - ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H)) x), x⟫_ℝ := by
    -- Evaluate the positive inverse gap on the vector `x`.
    have hpos :
        (((A : H →L[ℝ] H).inverse - ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H))).IsPositive :=
      (ContinuousLinearMap.le_def (((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H)) ((A : H →L[ℝ] H).inverse)).mp
        hscalar_le
    exact
      ((ContinuousLinearMap.isPositive_iff'
        ((A : H →L[ℝ] H).inverse - ((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H))).mp hpos).2 x
  have hx_le :
      ⟪(((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H) x), x⟫_ℝ ≤
        ⟪((A : H →L[ℝ] H).inverse x), x⟫_ℝ := by
    -- Rewrite the positive gap as the desired quadratic-form comparison.
    simpa [sub_apply, inner_sub_left] using hx_nonneg
  calc
    ((‖(A : H →L[ℝ] H)‖ : ℝ)⁻¹) * ‖x‖ ^ 2 = ((γ : ℝ)⁻¹) * ‖x‖ ^ 2 := by
      simp [γ]
    _ = ⟪(((γ : ℝ)⁻¹) • (1 : H →L[ℝ] H) x), x⟫_ℝ := by
      simp [real_inner_smul_left, inner_self_eq_norm_sq_to_K, pow_two]
    _ ≤ ⟪((A : H →L[ℝ] H).inverse x), x⟫_ℝ := hx_le

-- Proof sketch: the lower bound `β • 1 ≤ A` in the self-adjoint Loewner order becomes
-- `A.inverse ≤ β⁻¹ • 1` after inversion. Taking operator norms then yields the stated estimate.
/-- Clause (iii): if the self-adjoint operator `A` dominates `β • Id` with `β > 0`, then the norm
of its inverse is at most `β⁻¹`. -/
theorem lower_bounded_operator_norm_inverse_le_inv_scalar
    (β : Set.Ioi (0 : ℝ)) (A : S(H))
    (hβA : (β : ℝ) • 1 ≤ A) :
    ‖((A : H →L[ℝ] H).inverse)‖ ≤ (β : ℝ)⁻¹ := by
  let f : H →L[ℝ] H := (A : H →L[ℝ] H)
  -- Bound `A⁻¹` pointwise and pass to the operator norm.
  refine ContinuousLinearMap.opNorm_le_bound f.inverse (inv_nonneg.mpr β.2.le) ?_
  intro x
  simpa [f] using inverse_norm_bound_of_loewner_lower_bound hβA x

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace ContinuousLinearMap

/-- The Gram operator `A†A`, packaged in the self-adjoint Loewner-order owner `S(H)`. -/
noncomputable abbrev gram (A : H →L[ℝ] H) : S(H) :=
  ⟨A.adjoint.comp A, (isPositive_adjoint_comp_self A).isSelfAdjoint⟩

end ContinuousLinearMap

/-- Helper for Text 13 18 1: the Gram quadratic form equals the squared norm of the image. -/
lemma gram_inner_self_eq_norm_sq (A : H →L[ℝ] H) (x : H) :
    ⟪(A.gram : H →L[ℝ] H) x, x⟫_ℝ = ‖A x‖ ^ 2 := by
  -- Rewrite `A.gram` as `A†A` and use the standard adjoint norm identity.
  simpa [ContinuousLinearMap.gram] using (A.apply_norm_sq_eq_inner_adjoint_left x).symm

-- Proof sketch: `LipschitzWith 1 A` is equivalent to `‖A‖ ≤ 1` by the operator-norm/Lipschitz
-- API. For the positive self-adjoint Gram operator `A.gram`, the quadratic-form inequality from
-- Example 13.18 rewrites `A†A ≤ 1` to `‖A x‖² ≤ ‖x‖²`, which is the same
-- contraction bound.
/-- Clause (iv) of Text 13 18 1: a linear operator is nonexpansive exactly when
its Gram operator `A.gram` is bounded above by `Id` in the Loewner order on `S(H)`. -/
theorem nonexpansive_iff_gram_le_one
    (A : H →L[ℝ] H) :
    LipschitzWith 1 A ↔ A.gram ≤ 1 := by
  rw [loewner_le_iff_forall_inner_le]
  constructor
  · intro hA x
    -- Apply nonexpansiveness to the pair `(x, 0)` and square the resulting norm bound.
    have hx : ‖A x‖ ≤ ‖x‖ := by
      simpa [dist_eq_norm] using hA.dist_le_mul x 0
    have hsq : ‖A x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      nlinarith [hx, norm_nonneg (A x), norm_nonneg x]
    calc
      ⟪(A.gram : H →L[ℝ] H) x, x⟫_ℝ = ‖A x‖ ^ 2 := gram_inner_self_eq_norm_sq A x
      _ ≤ ‖x‖ ^ 2 := hsq
      _ = ⟪(1 : H →L[ℝ] H) x, x⟫_ℝ := by
        simp [inner_self_eq_norm_sq_to_K]
  · intro hA
    -- Evaluate the Loewner inequality on `x - y` and recover the distance estimate.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hsq : ‖A (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      calc
        ‖A (x - y)‖ ^ 2 = ⟪(A.gram : H →L[ℝ] H) (x - y), x - y⟫_ℝ := by
          symm
          exact gram_inner_self_eq_norm_sq A (x - y)
        _ ≤ ⟪(1 : H →L[ℝ] H) (x - y), x - y⟫_ℝ := hA (x - y)
        _ = ‖x - y‖ ^ 2 := by
          simp [inner_self_eq_norm_sq_to_K]
    have hnorm : ‖A (x - y)‖ ≤ ‖x - y‖ := by
      nlinarith [hsq, norm_nonneg (A (x - y)), norm_nonneg (x - y)]
    simpa [dist_eq_norm, map_sub] using hnorm

-- Proof sketch: use `strictlyLoewner_iff_forall_inner_lt` from Example 13.18 on `A.gram`, then
-- rewrite `⟪(A†A) x, x⟫ = ‖A x‖²`. The resulting strict quadratic-form inequality is
-- equivalent to strict distance contraction between distinct vectors by applying it to `x - y`.
/-- Companion operator-order reformulation of Text 13.18.1, clause (v): whole-space strict
nonexpansiveness of a linear operator is equivalent to strict Loewner domination `A.gram ≺ Id`. -/
theorem strictly_nonexpansive_iff_gram_strictlyLoewner_one
    (A : H →L[ℝ] H) :
    StrictlyNonexpansiveOn Set.univ A ↔ A.gram ≺ 1 := by
  rw [strictlyNonexpansiveOn_iff, strictlyLoewner_iff_forall_inner_lt]
  constructor
  · intro hA x hx
    -- Specialize strict nonexpansiveness to the pair `(x, 0)` and square the strict norm bound.
    have hxnorm : ‖A x‖ < ‖x‖ := by
      simpa [dist_eq_norm] using hA x (by simp) 0 (by simp) hx
    have hsq : ‖A x‖ ^ 2 < ‖x‖ ^ 2 := by
      nlinarith [hxnorm, norm_nonneg (A x), norm_nonneg x]
    calc
      ⟪(A.gram : H →L[ℝ] H) x, x⟫_ℝ = ‖A x‖ ^ 2 := gram_inner_self_eq_norm_sq A x
      _ < ‖x‖ ^ 2 := hsq
      _ = ⟪(1 : H →L[ℝ] H) x, x⟫_ℝ := by
        simp [inner_self_eq_norm_sq_to_K]
  · intro hA x _ y _ hxy
    -- Apply the strict Loewner bound to `x - y` and convert back to a strict distance bound.
    have hsq : ‖A (x - y)‖ ^ 2 < ‖x - y‖ ^ 2 := by
      calc
        ‖A (x - y)‖ ^ 2 = ⟪(A.gram : H →L[ℝ] H) (x - y), x - y⟫_ℝ := by
          symm
          exact gram_inner_self_eq_norm_sq A (x - y)
        _ < ⟪(1 : H →L[ℝ] H) (x - y), x - y⟫_ℝ := hA (x - y) (sub_ne_zero.mpr hxy)
        _ = ‖x - y‖ ^ 2 := by
          simp [inner_self_eq_norm_sq_to_K]
    have hnorm : ‖A (x - y)‖ < ‖x - y‖ := by
      nlinarith [hsq, norm_nonneg (A (x - y)), norm_nonneg (x - y)]
    simpa [dist_eq_norm, map_sub] using hnorm

end

section

variable {𝕜 : Type*} [NormedField 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Helper for Text 13 18 1: whole-space strict nonexpansiveness of a linear map is equivalent to
strict norm contraction on every nonzero vector. -/
lemma strictly_nonexpansive_on_univ_iff_forall_norm_image_lt
    (A : H →L[𝕜] H) :
    StrictlyNonexpansiveOn Set.univ A ↔
      ∀ x : H, x ≠ 0 → ‖A x‖ < ‖x‖ := by
  rw [strictlyNonexpansiveOn_iff]
  constructor
  · intro hA x hx
    -- Evaluate strict nonexpansiveness at `(x, 0)`.
    simpa [dist_eq_norm] using hA x (by simp) 0 (by simp) hx
  · intro hA x _ y _ hxy
    -- Apply the origin-based estimate to the difference `x - y`.
    simpa [dist_eq_norm, map_sub] using hA (x - y) (sub_ne_zero.mpr hxy)

/-- Helper for Text 13 18 1: under the fixed-point identity `Function.fixedPoints A = {0}`,
strict quasinonexpansiveness is the same as strict norm contraction away from the origin. -/
lemma strictly_quasinonexpansive_with_zero_fixed_points_iff_forall_norm_image_lt
    (A : H →L[𝕜] H) :
    (StrictlyQuasinonexpansiveOn Set.univ A ∧
      Function.fixedPoints A = ({0} : Set H)) ↔
      ∀ x : H, x ≠ 0 → ‖A x‖ < ‖x‖ := by
  rw [strictlyQuasinonexpansiveOn_iff]
  constructor
  · rintro ⟨hA, hfix⟩ x hx
    -- The only fixed point is `0`, so the quasinonexpansive inequality can be tested there.
    have hx_univ : x ∈ Set.univ := by
      simp
    have hxnot : x ∉ fixedPointSetOn Set.univ A := by
      intro hxfix
      have hxmem : x ∈ Function.fixedPoints A := by
        rw [fixedPointSetOn_eq_inter_fixedPoints, Set.mem_inter_iff] at hxfix
        exact hxfix.2
      rw [hfix] at hxmem
      exact hx (by simpa using hxmem)
    have hxdiff : x ∈ Set.univ \ fixedPointSetOn Set.univ A := by
      exact ⟨hx_univ, hxnot⟩
    have hzero : (0 : H) ∈ fixedPointSetOn Set.univ A := by
      rw [fixedPointSetOn_eq_inter_fixedPoints, Set.mem_inter_iff]
      constructor
      · simp
      · rw [Function.mem_fixedPoints_iff]
        simp
    simpa [dist_eq_norm] using hA x hxdiff 0 hzero
  · intro hA
    -- First identify the fixed-point set, then rewrite strict quasinonexpansiveness against `0`.
    have hfix : Function.fixedPoints A = ({0} : Set H) := by
      ext z
      rw [Set.mem_singleton_iff, Function.mem_fixedPoints_iff]
      constructor
      · intro hz
        by_contra hz0
        have hzlt : ‖A z‖ < ‖z‖ := hA z hz0
        simp [hz] at hzlt
      · rintro rfl
        simp
    refine ⟨?_, hfix⟩
    intro x hx y hy
    have hy0 : y = 0 := by
      have hyfix : y ∈ Function.fixedPoints A := by
        rw [fixedPointSetOn_eq_inter_fixedPoints, Set.mem_inter_iff] at hy
        exact hy.2
      rw [hfix] at hyfix
      simpa using hyfix
    have hx0 : x ≠ 0 := by
      intro hxzero
      apply hx.2
      subst hxzero
      rw [fixedPointSetOn_eq_inter_fixedPoints, Set.mem_inter_iff]
      constructor
      · simp
      · rw [Function.mem_fixedPoints_iff]
        simp
    simpa [hy0, dist_eq_norm] using hA x hx0

-- Proof sketch: for a linear map, pairwise nonexpansiveness is equivalent to the one-point
-- estimate `‖A x‖ ≤ ‖x‖` by applying the pairwise bound to `(x, 0)` and using linearity.
/-- Companion norm reformulation of Text 13.18.1, clause (iv): for a linear operator,
nonexpansiveness is equivalent to the pointwise bound `‖A x‖ ≤ ‖x‖` for every vector `x`. -/
theorem nonexpansive_iff_forall_norm_image_le
    (A : H →L[𝕜] H) :
    LipschitzWith 1 A ↔ ∀ x : H, ‖A x‖ ≤ ‖x‖ := by
  constructor
  · intro hA x
    -- Evaluate the Lipschitz bound at `(x, 0)`.
    simpa [dist_eq_norm] using hA.dist_le_mul x 0
  · intro hA
    -- Apply the one-point bound to the difference `x - y`.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [dist_eq_norm, map_sub] using hA (x - y)

-- Proof sketch: if the fixed-point set is `{0}`, then strict quasinonexpansiveness reduces to the
-- strict contraction estimate against the single fixed point `0`; for a linear map, that is
-- exactly the canonical whole-space strict-nonexpansive owner on `Set.univ`.
/-- Companion bridge for Text 13.18.1, clause (v): if `Function.fixedPoints A = {0}`, then strict
quasinonexpansiveness on the whole space is exactly whole-space strict nonexpansiveness. -/
theorem strict_quasinonexpansive_with_zero_fixedPoints_iff_strictly_nonexpansive
    (A : H →L[𝕜] H) :
    (StrictlyQuasinonexpansiveOn Set.univ A ∧
      Function.fixedPoints A = ({0} : Set H)) ↔
      StrictlyNonexpansiveOn Set.univ A := by
  -- Both sides reduce to strict norm contraction on nonzero vectors.
  rw [strictly_quasinonexpansive_with_zero_fixed_points_iff_forall_norm_image_lt,
    strictly_nonexpansive_on_univ_iff_forall_norm_image_lt]

-- Proof sketch: for a linear map, strict nonexpansiveness on all pairs reduces to the origin-based
-- estimate `‖A x‖ < ‖x‖` for `x ≠ 0` by applying the pairwise inequality to `(x, 0)` and using
-- linearity.
/-- Companion norm reformulation of Text 13.18.1, clause (v): whole-space strict nonexpansiveness
of a linear operator is equivalent to strict norm contraction on every nonzero vector. -/
theorem strictly_nonexpansive_iff_forall_norm_image_lt
    (A : H →L[𝕜] H) :
    StrictlyNonexpansiveOn Set.univ A ↔
      ∀ x : H, x ≠ 0 → ‖A x‖ < ‖x‖ := by
  -- This is exactly the helper equivalence specialized to the current map.
  simpa using strictly_nonexpansive_on_univ_iff_forall_norm_image_lt (A := A)

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Clause (v) of Text 13 18 1: a linear operator is strictly quasinonexpansive on the whole space
with fixed-point set `{0}` exactly when its Gram operator is strictly below `Id` in the strict
Loewner order. -/
theorem strict_quasinonexpansive_with_zero_fixedPoints_iff_gram_strictlyLoewner_one
    (A : H →L[ℝ] H) :
    (StrictlyQuasinonexpansiveOn Set.univ A ∧
      Function.fixedPoints A = ({0} : Set H)) ↔ A.gram ≺ 1 := by
  rw [strict_quasinonexpansive_with_zero_fixedPoints_iff_strictly_nonexpansive,
    strictly_nonexpansive_iff_gram_strictlyLoewner_one]

end

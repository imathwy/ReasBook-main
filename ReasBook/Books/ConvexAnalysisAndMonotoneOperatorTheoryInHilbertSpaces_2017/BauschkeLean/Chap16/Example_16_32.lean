import Mathlib
import BauschkeLean.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

noncomputable section

section NormSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Classical decidability of equality on `H`, used to state the piecewise formula for the norm
subdifferential. -/
local instance instDecidableEqNormSubdifferential : DecidableEq H := Classical.decEq H

/-- Helper for Example 16 32: for the norm, subdifferential membership is the real-valued affine
minorant inequality obtained by unpacking the `EReal` owner. -/
private lemma mem_subdifferential_norm_iff (x u : H) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u + ‖x‖ ≤ ‖y‖ := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    -- All terms are finite reals here, so the `EReal` inequality descends to `ℝ`.
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_add] using hu y)
  · intro hu y
    -- Conversely, recast the real inequality back into the `EReal` owner.
    exact (EReal.coe_le_coe_iff).2 (by simpa [EReal.coe_add] using hu y)

/-- Helper for Example 16 32: at the origin, the norm subdifferential is the closed unit ball. -/
private lemma mem_subdifferential_norm_zero_iff (u : H) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) (0 : H) ↔ u ∈ Metric.closedBall (0 : H) 1 := by
  rw [mem_subdifferential_norm_iff]
  constructor
  · intro hu
    -- Testing the affine minorant inequality at `y = u` yields `‖u‖² ≤ ‖u‖`.
    have hsq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
      simpa [sub_zero, real_inner_self_eq_norm_sq] using hu u
    have hu_norm_le : ‖u‖ ≤ 1 := by
      nlinarith [hsq_le, norm_nonneg u]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_norm_le
  · intro hu y
    -- The unit-ball bound and Cauchy--Schwarz give the required affine minorant inequality.
    have hu_norm_le : ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    calc
      inner ℝ (y - (0 : H)) u + ‖(0 : H)‖ ≤ ‖y - (0 : H)‖ * ‖u‖ := by
        simpa using real_inner_le_norm (y - (0 : H)) u
      _ ≤ ‖y - (0 : H)‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hu_norm_le (norm_nonneg (y - (0 : H)))
      _ = ‖y‖ := by simp

/-- Helper for Example 16 32: away from the origin, the norm subdifferential is the singleton
containing the normalized vector. -/
private lemma mem_subdifferential_norm_nonzero_iff_eq_inv_norm_smul {x u : H} (hx : x ≠ 0) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) x ↔ u = ‖x‖⁻¹ • x := by
  rw [mem_subdifferential_norm_iff]
  constructor
  · intro hu
    -- Testing at `y = 0` gives the lower bound `‖x‖ ≤ ⟪x, u⟫`.
    have hu_zero : ‖x‖ ≤ inner ℝ x u := by
      have hzero := hu (0 : H)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
    have hu_norm_ge : 1 ≤ ‖u‖ := by
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hinner_le : inner ℝ x u ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
      have hmul : ‖x‖ ≤ ‖x‖ * ‖u‖ := le_trans hu_zero hinner_le
      by_contra hu_lt
      have hu_lt' : ‖u‖ < 1 := lt_of_not_ge hu_lt
      have hmul_lt : ‖x‖ * ‖u‖ < ‖x‖ := by
        nlinarith
      exact (not_lt_of_ge hmul hmul_lt)
    -- Testing at `y = x + u` and using the triangle inequality gives the reverse bound.
    have hu_eval := hu (x + u)
    have hu_norm_le : ‖u‖ ≤ 1 := by
      have hsq_add : ‖u‖ ^ 2 + ‖x‖ ≤ ‖x + u‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, real_inner_self_eq_norm_sq]
          using hu_eval
      have htri : ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le x u
      have hsq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
        linarith
      nlinarith [hsq_le, norm_nonneg u]
    have hu_norm : ‖u‖ = 1 := by
      linarith
    -- Equality in Cauchy--Schwarz aligns `u` with `x` on the same nonnegative ray.
    have hinner_eq_norm : inner ℝ x u = ‖x‖ := by
      have hinner_le : inner ℝ x u ≤ ‖x‖ := by
        simpa [hu_norm] using (real_inner_le_norm x u)
      linarith
    have hinner_eq : inner ℝ x u = ‖x‖ * ‖u‖ := by
      simpa [hu_norm] using hinner_eq_norm
    have halign : ‖u‖ • x = ‖x‖ • u := (inner_eq_norm_mul_iff_real).1 hinner_eq
    have hxnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    calc
      u = ‖x‖⁻¹ • (‖x‖ • u) := by
        rw [smul_smul, inv_mul_cancel₀ hxnorm_ne, one_smul]
      _ = ‖x‖⁻¹ • (‖u‖ • x) := by rw [halign]
      _ = ‖x‖⁻¹ • x := by rw [hu_norm, one_smul]
  · intro hu y
    -- Substituting the normalized vector reduces the inequality to Cauchy--Schwarz.
    rw [hu]
    calc
      inner ℝ (y - x) (‖x‖⁻¹ • x) + ‖x‖ = inner ℝ y (‖x‖⁻¹ • x) := by
        rw [inner_sub_left, real_inner_smul_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hx]
        ring
      _ ≤ ‖y‖ * ‖‖x‖⁻¹ • x‖ := real_inner_le_norm y (‖x‖⁻¹ • x)
      _ ≤ ‖y‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (by simpa using (norm_smul_inv_norm hx).le) (norm_nonneg y)
      _ = ‖y‖ := by simp

-- Proof sketch: unpack the defining affine-minorant inequality for the norm subdifferential. At
-- `x = 0`, testing at `y = u` shows `‖u‖² ≤ ‖u‖`, hence `‖u‖ ≤ 1`, and the converse is just
-- Cauchy--Schwarz. For `x ≠ 0`, testing at `y = 0` and `y = x + u` gives `‖u‖ = 1`; equality in
-- Cauchy--Schwarz then forces `u` to be the normalized vector `‖x‖⁻¹ • x`.
/-- Example 16 32: the subdifferential of the norm is the singleton containing the normalized
vector away from `0`, and the closed unit ball at `0`. -/
theorem subdifferential_norm_eq_singleton_or_closedBall (x : H) :
    (∂ (fun y : H ↦ ‖y‖).toEReal) x =
      if x = 0 then (Metric.closedBall (0 : H) 1 : Set H) else ({‖x‖⁻¹ • x} : Set H) := by
  by_cases hx : x = 0
  · subst hx
    -- The origin branch is exactly the closed-ball characterization proved above.
    ext u
    rw [mem_subdifferential_norm_zero_iff]
    simp
  · -- Away from `0`, membership is equivalent to equality with the normalized vector.
    ext u
    rw [mem_subdifferential_norm_nonzero_iff_eq_inv_norm_smul (x := x) (u := u) hx]
    simp [hx]

end NormSubdifferential

end

end ERealFunction

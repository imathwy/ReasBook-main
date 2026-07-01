import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Real
open Real.Angle

namespace Complex

/-- `θ` is an argument of `t` when `t` is nonzero and the angle class of `θ` agrees with the
canonical owner `Complex.arg t : Angle`. -/
def IsArgument (t : ℂ) (θ : ℝ) : Prop :=
  t ≠ 0 ∧ (θ : Angle) = arg t

/-- Any argument is necessarily an argument of a nonzero complex number. -/
theorem IsArgument.ne_zero {t : ℂ} {θ : ℝ} (h : IsArgument t θ) : t ≠ 0 :=
  h.1

/-- The source-facing notion of argument is equivalent to the normalized exponential description
on the unit circle. -/
theorem isArgument_iff_exp_eq_div_norm {t : ℂ} {θ : ℝ} :
    IsArgument t θ ↔ exp (θ * I) = t / ‖t‖ := by
  constructor
  · rintro ⟨ht, hθ⟩
    have hnorm : (‖t‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr ht
    have harg : exp (arg t * I) = t / ‖t‖ := by
      apply (eq_div_iff hnorm).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using norm_mul_exp_arg_mul_I t
    obtain ⟨n, hn⟩ := angle_eq_iff_two_pi_dvd_sub.mp hθ
    have hperiod : Circle.exp θ = Circle.exp (arg t) :=
      (Circle.exp_eq_exp).2 ⟨n, by linarith [hn]⟩
    have hperiod' : exp (θ * I) = exp (arg t * I) := by
      simpa [Circle.coe_exp] using congrArg (fun z : Circle ↦ (z : ℂ)) hperiod
    exact hperiod'.trans harg
  · intro hθ
    have ht : t ≠ 0 := by
      intro ht
      simpa [ht, hθ] using exp_ne_zero (θ * I)
    have hnorm : (‖t‖ : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr ht
    have harg : exp (arg t * I) = t / ‖t‖ := by
      apply (eq_div_iff hnorm).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using norm_mul_exp_arg_mul_I t
    have hperiod : Circle.exp θ = Circle.exp (arg t) := by
      rw [Circle.ext_iff, Circle.coe_exp, Circle.coe_exp]
      exact hθ.trans harg.symm
    obtain ⟨n, hn⟩ := (Circle.exp_eq_exp).1 hperiod
    refine ⟨ht, ?_⟩
    rw [angle_eq_iff_two_pi_dvd_sub]
    refine ⟨n, by linarith [hn]⟩

/-- Definition I.3-extra-6: for a nonzero complex number `t`, a real number `θ` is an argument
of `t` exactly when it differs from the principal argument `arg t` by an integral multiple of
`2 * π`. This is the canonical bridge from the source's multivalued notion to mathlib's owner
declaration `Complex.arg`. -/
theorem isArgument_iff {t : ℂ} {θ : ℝ} :
    IsArgument t θ ↔ t ≠ 0 ∧ ∃ n : ℤ, θ = arg t + n * (2 * π) := by
  constructor
  · rintro ⟨ht, hθ⟩
    obtain ⟨n, hn⟩ := angle_eq_iff_two_pi_dvd_sub.mp hθ
    refine ⟨ht, n, ?_⟩
    linarith [hn]
  · rintro ⟨ht, n, rfl⟩
    refine ⟨ht, ?_⟩
    rw [angle_eq_iff_two_pi_dvd_sub]
    refine ⟨n, by ring⟩

/-- Any argument of `t` reconstructs `t` as `|t| * exp (θ * I)`. -/
theorem eq_norm_mul_exp_mul_I_of_isArgument {t : ℂ} {θ : ℝ}
    (h : IsArgument t θ) :
    t = ‖t‖ * exp (θ * I) := by
  have ht := h.ne_zero
  have hθ := isArgument_iff_exp_eq_div_norm.mp h
  have hnorm : (‖t‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr ht
  have hmul : exp (θ * I) * ‖t‖ = t := (eq_div_iff hnorm).1 hθ
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul.symm

/-- Adding an integral multiple of `2 * π` to an argument gives another argument of the same
nonzero complex number. -/
theorem isArgument_add_int_mul_two_pi {t : ℂ} {θ : ℝ}
    (h : IsArgument t θ) (n : ℤ) :
    IsArgument t (θ + n * (2 * π)) := by
  rcases isArgument_iff.mp h with ⟨ht, m, hm⟩
  refine isArgument_iff.mpr ⟨ht, m + n, ?_⟩
  rw [hm]
  rw [Int.cast_add, add_mul]
  ring

end Complex

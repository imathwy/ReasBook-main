import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

/-- Definition I.3-extra-7: `z` is a complex logarithm of `t` when `exp z = t`. This keeps the
source's multivalued notion; mathlib's `Complex.log t = Real.log ‖t‖ + Complex.arg t * I` is a
canonical witness when `t ≠ 0`. -/
def IsLogarithm (t z : ℂ) : Prop :=
  exp z = t

/-- The principal branch `Complex.log` is a logarithm of every nonzero complex number. -/
theorem isLogarithm_log {t : ℂ} (ht : t ≠ 0) : IsLogarithm t (log t) :=
  exp_log ht

/-- Any complex number that admits a logarithm is nonzero. -/
theorem IsLogarithm.ne_zero {t z : ℂ} (h : IsLogarithm t z) : t ≠ 0 := by
  rw [← h]
  exact exp_ne_zero z

-- Proof sketch: if `exp z = t`, then `t ≠ 0` by `Complex.exp_ne_zero`; conversely, for `t ≠ 0`
-- the principal value `Complex.log t` is a logarithm by `Complex.exp_log`.
/-- Complex logarithms exist exactly for nonzero complex numbers. -/
theorem exists_logarithm_iff (t : ℂ) :
    (∃ z : ℂ, IsLogarithm t z) ↔ t ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact hz.ne_zero
  · intro ht
    exact ⟨log t, isLogarithm_log ht⟩

/- `Complex.isLogarithm_log` repackages `Complex.exp_log` as a witness for the source-facing
multivalued notion of logarithm. -/
#check Complex.isLogarithm_log

-- Proof sketch: for `x > 0`, the principal complex logarithm agrees with the real logarithm via
-- `Complex.ofReal_log`, and `Complex.exp_log` then gives the required identity.
/-- For a positive real number, the usual real logarithm is a complex logarithm. -/
theorem realLog_isLogarithm_of_pos {x : ℝ} (hx : 0 < x) :
    IsLogarithm (x : ℂ) (Real.log x) := by
  rw [IsLogarithm, ofReal_log hx.le, exp_log]
  exact_mod_cast hx.ne'

end Complex

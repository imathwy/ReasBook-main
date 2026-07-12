import DifferentialForms_Cartan_1970.I.section03.«frozen_0008_Definition_I_3_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

-- Proof sketch: `Complex.slitPlane` is defined by `0 < t.re ∨ t.im ≠ 0`, so strict positivity of
-- the real part places `t` in the slit plane immediately.
/-- A complex number with positive real part lies in the slit plane. -/
theorem mem_slitPlane_of_re_pos {t : ℂ} (ht : 0 < t.re) :
    t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, ← lt_or_lt_iff_ne]
  exact Or.inl ht

-- Proof sketch: the half-plane `{t | 0 < t.re}` is open and convex, hence connected;
-- `Complex.log` is continuous there because this set lies in `Complex.slitPlane`; and
-- `Complex.exp_log` gives `exp (log t) = t` at every point since `0 < t.re` implies `t ≠ 0`.
/-- Example I.3-extra-9: the principal logarithm `Complex.log t = Real.log ‖t‖ + arg t * I`
is a branch of `log t` on the open half-plane `Re t > 0`. -/
theorem principalLog_isLogBranchOn_rightHalfPlane :
    IsLogBranchOn Complex.log {t : ℂ | 0 < t.re} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using isOpen_lt continuous_zero continuous_re
  · exact (convex_halfSpace_re_gt 0).isConnected ⟨1, by simp⟩
  · simpa using continuousOn_id.clog fun t ht ↦ mem_slitPlane_of_re_pos ht
  · intro t ht
    simpa using Complex.exp_log (Complex.slitPlane_ne_zero (mem_slitPlane_of_re_pos ht))

end Complex

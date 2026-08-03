import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section

variable {H : Type u}
variable {p : ℕ}
variable {g : Fin p → H → ℝ}
variable {xbar : H}
variable {νbar : Fin p → ℝ}

/- Source/core/bridge triage:
- `source-facing`: Remark 19.31 isolates the strictly inactive-constraint consequence of
  complementary slackness for the inequality multipliers `νᵢ`.
- `core/canonical`: the mathematical core is the scalar relation `νᵢ * gᵢ(x̄) = 0` together
  with the sign conditions `0 ≤ νᵢ` and `gᵢ(x̄) < 0`.
- `bridge/view`: no mixed-space packaging is needed here, because the equality block plays no role
  in the remark.
-/

/-- Remark 19.31: any strictly inactive inequality constraint whose multiplier satisfies the
complementary slackness condition has zero multiplier. -/
theorem inequalityMultiplier_eq_zero_of_strictlyInactiveConstraint
    (hcomp : ∀ i : Fin p, 0 ≤ νbar i ∧ νbar i * g i xbar = 0)
    (i : Fin p)
    (hstrict : g i xbar < 0) :
    νbar i = 0 := by
  rcases hcomp i with ⟨hνi, hprod⟩
  by_contra hne
  have hνpos : 0 < νbar i := by
    exact lt_of_le_of_ne hνi (by simpa [eq_comm] using hne)
  have hmulneg : νbar i * g i xbar < 0 :=
    mul_neg_of_pos_of_neg hνpos hstrict
  exact (ne_of_lt hmulneg) hprod

end

end ERealFunction

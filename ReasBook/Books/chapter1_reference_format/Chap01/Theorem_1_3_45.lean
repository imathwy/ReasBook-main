import Mathlib
import chapter1_reference_format.Chap01.Definition_1_3_35

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Polynomial

variable {K : Type u} [CommRing K] [NoZeroDivisors K] [CharZero K]

/-- Theorem 1.3.45: for a polynomial over a characteristic-zero domain, `a` is a root of
multiplicity `r` if and only if all iterated derivatives of orders `< r` vanish at `a`, while the
`r`-th iterated derivative does not vanish at `a`. -/
-- Proof sketch: the zero-polynomial case is impossible because `r : ℕ+`. For `P ≠ 0`, use
-- `lt_rootMultiplicity_iff_isRoot_iterate_derivative hP` to express vanishing of all lower iterated
-- derivatives, and use `eval_iterate_derivative_rootMultiplicity` together with `CharZero K` to show
-- that the iterated derivative of order exactly the multiplicity is nonzero.
theorem rootMultiplicity_eq_iff_eval_iterate_derivative
    (P : K[X]) (a : K) (r : ℕ+) :
    P.rootMultiplicity a = (r : ℕ) ↔
      (∀ i < (r : ℕ), (derivative^[i] P).eval a = 0) ∧
      (derivative^[(r : ℕ)] P).eval a ≠ 0 := by
  by_cases hP : P = 0
  · have hr : (r : ℕ) ≠ 0 := PNat.ne_zero r
    constructor
    · intro h
      have h0 : (0 : ℕ) = (r : ℕ) := by simpa [hP] using h
      exact False.elim <| hr h0.symm
    · rintro ⟨_, hnonzero⟩
      exact False.elim <| hnonzero <| by simp [hP]
  · constructor
    · intro hr
      refine ⟨?_, ?_⟩
      · intro i hi
        have hroot := (lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1 (hr ▸ hi) i le_rfl
        simpa [IsRoot] using hroot
      · rw [← hr, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
        exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
          (eval_divByMonic_pow_rootMultiplicity_ne_zero a hP)
    · rintro ⟨hvanish, hnonzero⟩
      have hlt : (r : ℕ) - 1 < P.rootMultiplicity a := by
        apply lt_rootMultiplicity_of_isRoot_iterate_derivative hP
        intro m hm
        have hm' : m < (r : ℕ) := by
          exact lt_of_le_of_lt hm (Nat.sub_lt (PNat.pos r) Nat.one_pos)
        simpa [IsRoot] using hvanish m hm'
      have hle : (r : ℕ) ≤ P.rootMultiplicity a := by
        have hs : Nat.succ ((r : ℕ) - 1) = (r : ℕ) := by
          simpa [Nat.pred_eq_sub_one] using Nat.succ_pred_eq_of_pos (PNat.pos r)
        exact hs ▸ Nat.succ_le_of_lt hlt
      have hge : P.rootMultiplicity a ≤ (r : ℕ) := by
        refine Nat.le_of_not_gt fun hr' ↦ ?_
        have hroot := (lt_rootMultiplicity_iff_isRoot_iterate_derivative hP).1 hr' (r : ℕ) le_rfl
        exact hnonzero <| by simpa [IsRoot] using hroot
      exact le_antisymm hge hle

end Polynomial

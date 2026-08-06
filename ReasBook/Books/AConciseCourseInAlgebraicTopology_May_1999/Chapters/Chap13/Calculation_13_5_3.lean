import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Calculation_13_5_8

open CategoryTheory.Limits

noncomputable section

/- Calculation 13.5.3 (1): for `RP²` using a two-vertex CW structure, the degree-`0` integral
homology group is infinite cyclic. -/
#check realProjectiveSpace_integralHomology_zero 2

/- Calculation 13.5.3 (2): for `RP²` using a two-vertex CW structure, the degree-`1` integral
homology group is cyclic of order `2`. -/
#check realProjectiveSpace_integralHomology_odd_lt 2 1 (by decide) (by decide) (by decide)

/-- Calculation 13.5.3 (3): for `RP²` using a two-vertex CW structure, every integral homology
group in degree `q ≥ 2` vanishes. -/
theorem realProjectivePlane_integralHomology_isZero (q : ℕ) (hq : 2 ≤ q) :
    IsZero (realProjectiveSpaceIntegralHomology 2 q) := by
  simpa using
    realProjectiveSpace_integralHomology_isZero 2 q
      (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq))
      (Or.inr hq)
      (Or.inl (by decide : ¬ Odd 2))

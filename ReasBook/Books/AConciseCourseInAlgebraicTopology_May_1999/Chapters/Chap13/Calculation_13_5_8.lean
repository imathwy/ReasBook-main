import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- The integral singular homology object `H_q(RP^n; ℤ)`. -/
abbrev realProjectiveSpaceIntegralHomology (n q : ℕ) : ModuleCat ℤ :=
  integralSingularHomology q (TopCat.of (RealProjectiveSpace n))

/-- Unfolding `realProjectiveSpaceIntegralHomology` recovers the chapter-level integral singular
homology owner on `RP^n`. -/
theorem realProjectiveSpaceIntegralHomology_def (n q : ℕ) :
    realProjectiveSpaceIntegralHomology n q =
      integralSingularHomology q (TopCat.of (RealProjectiveSpace n)) :=
  rfl

/-- Calculation 13.5.8 (1): the degree-`0` integral homology of `RP^n` is infinite cyclic. -/
theorem realProjectiveSpace_integralHomology_zero (n : ℕ) :
    Nonempty (realProjectiveSpaceIntegralHomology n 0 ≅ ModuleCat.of ℤ ℤ) := sorry

/-- Calculation 13.5.8 (2): every positive odd integral homology group `H_q(RP^n; ℤ)` with
`q < n` is cyclic of order `2`. -/
theorem realProjectiveSpace_integralHomology_odd_lt
    (n q : ℕ) (hqpos : 0 < q) (hqodd : Odd q) (hqlt : q < n) :
    Nonempty (realProjectiveSpaceIntegralHomology n q ≅ ModuleCat.of ℤ (ZMod 2)) := sorry

/-- Calculation 13.5.8 (3): if `n` is odd, then the top integral homology group
`H_n(RP^n; ℤ)` is infinite cyclic. -/
theorem realProjectiveSpace_integralHomology_top_of_odd
    (n : ℕ) (hnodd : Odd n) :
    Nonempty (realProjectiveSpaceIntegralHomology n n ≅ ModuleCat.of ℤ ℤ) := sorry

/-- Calculation 13.5.8 (4): apart from degree `0`, the odd degrees `q < n`, and the top degree
when `n` is odd, the integral homology of `RP^n` vanishes. -/
theorem realProjectiveSpace_integralHomology_isZero
    (n q : ℕ) (hq0 : q ≠ 0)
    (hqnotOddLt : ¬ Odd q ∨ n ≤ q)
    (hnotTopOdd : ¬ Odd n ∨ q ≠ n) :
    IsZero (realProjectiveSpaceIntegralHomology n q) := sorry

import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Prod
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology

open AlgebraicTopology CategoryTheory Limits

noncomputable section

-- Semantic recall: no canonical Klein-bottle homology computation theorem is available in the
-- current environment, so this file records the source-facing homology owner directly via the
-- chapter-level abbreviation `integralSingularHomology`, together with `≅` and `IsZero`
-- companions.

/-- The integral singular homology object `H_q(K; ℤ)` of the Klein bottle `K`. -/
abbrev kleinBottleIntegralHomology (q : ℕ) : ModuleCat ℤ :=
  integralSingularHomology q (TopCat.of KleinBottleFromSquare)

/-- Unfolding `kleinBottleIntegralHomology` recovers the chapter-level integral singular homology
owner on `KleinBottleFromSquare`. -/
theorem kleinBottleIntegralHomology_def (q : ℕ) :
    kleinBottleIntegralHomology q = integralSingularHomology q (TopCat.of KleinBottleFromSquare) :=
  rfl

/-- Calculation 13.5.4 (1): the degree-`0` integral homology of the Klein bottle `K` is infinite
cyclic. -/
theorem kleinBottle_integralHomology_zero :
    Nonempty (kleinBottleIntegralHomology 0 ≅ ModuleCat.of ℤ ℤ) := sorry

/-- Calculation 13.5.4 (2): the degree-`1` integral homology of the Klein bottle `K` is
`ℤ ⊕ ZMod 2`, formalized as the product module `ℤ × ZMod 2`. -/
theorem kleinBottle_integralHomology_one :
    Nonempty (kleinBottleIntegralHomology 1 ≅ ModuleCat.of ℤ (ℤ × ZMod 2)) := sorry

/-- Calculation 13.5.4 (3): every integral homology group `H_q(K; ℤ)` of the Klein bottle `K`
vanishes for `q ≥ 2`. -/
theorem kleinBottle_integralHomology_isZero_of_two_le
    (q : ℕ) (hq : 2 ≤ q) :
    IsZero (kleinBottleIntegralHomology q) := sorry

import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a canonical `RP^n` mod-`2` homology
-- theorem in the current environment. Local Chapter 13 precedent therefore records the source-
-- facing homology object directly via `singularHomologyFunctor`, together with `≅` and `IsZero`
-- companions.

/-- The `ZMod 2`-valued singular homology object `H_q(RP^n; ZMod 2)`. -/
abbrev realProjectiveSpaceModTwoHomology (n q : ℕ) : ModuleCat (ZMod 2) :=
  ((singularHomologyFunctor (ModuleCat (ZMod 2)) q).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of (RealProjectiveSpace n))

/-- Unfolding `realProjectiveSpaceModTwoHomology` recovers the constant-coefficient singular
homology owner on `RP^n` with coefficients in `ZMod 2`. -/
theorem realProjectiveSpaceModTwoHomology_def (n q : ℕ) :
    realProjectiveSpaceModTwoHomology n q =
      ((singularHomologyFunctor (ModuleCat (ZMod 2)) q).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).obj (TopCat.of (RealProjectiveSpace n)) :=
  rfl

/-- Calculation 13.5.9 (1): the `ZMod 2`-valued homology of `RP^n` is `ZMod 2` in every degree
`q ≤ n`. -/
theorem realProjectiveSpace_modTwoHomology_le
    (n q : ℕ) (hq : q ≤ n) :
    Nonempty (realProjectiveSpaceModTwoHomology n q ≅ ModuleCat.of (ZMod 2) (ZMod 2)) := sorry

/-- Calculation 13.5.9 (2): the `ZMod 2`-valued homology of `RP^n` vanishes in every degree
`q > n`. -/
theorem realProjectiveSpace_modTwoHomology_gt
    (n q : ℕ) (hq : n < q) :
    IsZero (realProjectiveSpaceModTwoHomology n q) := sorry

import Mathlib
import StacksProject_2024.Chap26.Example_26_14_3_Affine_space_with_zero_doubled
import StacksProject_2024.Chap29.Definition_29_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical separated-scheme owner
`Scheme.IsSeparated`; local Chapter 26 precedent supplies the doubled-origin affine line, and
Definition 29.12.1 supplies `AlgebraicGeometry.AmpleFamily`. The Stacks tag evidence agrees on
`0FXT`. -/

/-- Remark 29.12.3: the affine line with zero doubled has an ample family of invertible
modules, witnessed by a family `L_n` indexed by integers and by sections whose nonvanishing
opens are the two affine charts, but the scheme is not separated. -/
@[stacks 0FXT]
theorem exists_ampleFamily_not_isSeparated_affineLineWithZeroDoubled
    (k : Type u) [Field k] :
    ∃ (A : AffineSpaceWithZeroDoubled k 1),
      ∃ (L : ℤ → A.X.Modules),
        ∃ (hL : ∀ n : ℤ, Scheme.Modules.Invertible (L n)),
          ∃ (s : (L (1 : ℤ)).sections),
            ∃ (t : (L (-1 : ℤ)).sections),
              AmpleFamily L ∧
                A.chart 0 = (hL (1 : ℤ)).nonvanishingOpen s ∧
                A.chart 1 = (hL (-1 : ℤ)).nonvanishingOpen t ∧
                ¬ A.X.IsSeparated := sorry

end AlgebraicGeometry

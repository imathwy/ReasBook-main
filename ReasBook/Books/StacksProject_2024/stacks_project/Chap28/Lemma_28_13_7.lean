import Mathlib
import StacksProject_2024.Chap28.Lemma_28_13_8
import StacksProject_2024.Chap28.Remark_28_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced `IsClosedImmersion` as the canonical scheme-side owner for closed
-- subschemes, and local Chapter 31 files quantify over closed immersions `i : Z ⟶ X` rather than
-- introducing a wrapper object. The source statement is therefore best exposed as a Nagata
-- criterion in terms of all integral closed subschemes represented this way.

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- Lemma 28.13.7: a locally Noetherian scheme `X` is Nagata if and only if every integral closed
subscheme of `X`, represented by a closed immersion `i : Z ⟶ X`, is Japanese. -/
@[stacks 033Y]
theorem nagata_iff_forall_integral_closedSubscheme_japanese :
    Nagata X ↔
      ∀ ⦃Z : Scheme.{u}⦄ (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z], Japanese Z := sorry

end AlgebraicGeometry.Scheme

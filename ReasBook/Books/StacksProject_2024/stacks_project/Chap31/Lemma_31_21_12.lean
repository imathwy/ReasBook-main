import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_9_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` only surfaced ambient scheme-stalk regularity infrastructure, while local
-- Chapter 28/31 precedent already fixes the canonical owners `Scheme.Regular` and
-- `IsRegularImmersion`. The source is therefore recorded directly on those owners.

/-- Lemma 31.21.12: let `i : Z ⟶ X` be an immersion. If `Z` and `X` are regular schemes, then `i`
is a regular immersion. -/
@[stacks 0E9J]
theorem isRegularImmersion_of_isImmersion_of_regular
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] [Scheme.Regular Z] [Scheme.Regular X] :
    IsRegularImmersion i := sorry

end AlgebraicGeometry

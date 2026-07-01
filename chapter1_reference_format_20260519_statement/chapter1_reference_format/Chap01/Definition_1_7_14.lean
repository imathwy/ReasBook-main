import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {S : Type u} [PartialOrder S]

/- Definition 1.7.14: for a partial order on `S`, the canonical well-order notion is
`IsWellOrder S (· < ·)`. The source-facing least-element characterization is already recorded by
the earlier chapter theorem `isWellOrder_iff_nonempty_subsets_have_least`. -/
#check IsWellOrder S (· < ·)

#check isWellOrder_iff_nonempty_subsets_have_least

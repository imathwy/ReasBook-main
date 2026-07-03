import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Lemma 12.7.4 is `core/canonical`: the source statement is exactly the owner transfer theorem
`CategoryTheory.abelianOfAdjunction` ([stacks 03A3]). No source-facing data is being defined here,
so the refined file should recall that owner theorem directly rather than introduce a parallel
local wrapper around the adjunction hypotheses. -/
recall abelianOfAdjunction

end CategoryTheory

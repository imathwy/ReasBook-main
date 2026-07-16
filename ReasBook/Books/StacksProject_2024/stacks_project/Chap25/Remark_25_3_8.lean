import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap25.Lemma_25_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

namespace CategoryTheory

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasPullbacks C]

-- The source-facing remark is a pure canonical recall: the preceding lemma already proves the
-- stronger statement that the entire type of hypercoverings of `X` is small.

/- Remark 25.3.8: the previous lemma states the stronger fact that the full type of hypercoverings
of `X` is set-sized, formalized by the canonical theorem `CategoryTheory.small_hypercoverings`,
not merely that there exists a set-sized cofinal system of choices of hypercoverings. -/
recall small_hypercoverings

end CategoryTheory

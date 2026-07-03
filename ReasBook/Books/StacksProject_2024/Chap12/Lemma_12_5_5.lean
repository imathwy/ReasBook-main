import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Lemma 12.5.5: the source sentence "all finite limits and all finite colimits exist" splits
canonically into the owner instances `Abelian.hasFiniteLimits` and
`Abelian.hasFiniteColimits`. -/
recall Abelian.hasFiniteLimits

/- Companion recall for the finite-colimit half of Lemma 12.5.5. -/
recall Abelian.hasFiniteColimits

end CategoryTheory

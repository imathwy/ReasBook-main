import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Lemma 12.7.3: for an exact functor between abelian categories, the canonical exact-functor map
on `Ext¹` sends the extension class of a short exact sequence to the extension class of its image
short exact sequence. This is exactly the owner theorem
`CategoryTheory.Abelian.Ext.mapExactFunctor_extClass`, so the refined file should recall that
canonical result directly rather than keep redundant local exact-to-additive scaffolding. -/
recall Abelian.Ext.mapExactFunctor_extClass

end CategoryTheory

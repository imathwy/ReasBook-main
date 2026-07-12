import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Lemma 12.5.18: for a morphism of snake inputs coming from a commutative diagram with exact
rows in an abelian category, the induced morphisms on kernels, connecting morphisms, and
cokernels assemble into a morphism between the associated six-term snake-lemma diagrams.
Equivalently, the induced kernel-cokernel diagram commutes. -/
recall ShortComplex.SnakeInput.composableArrowsFunctor

/- Companion recall: the central square in the induced diagram commutes, i.e. the connecting
morphisms are natural with respect to morphisms of snake inputs. -/
recall ShortComplex.SnakeInput.naturality_δ

end CategoryTheory

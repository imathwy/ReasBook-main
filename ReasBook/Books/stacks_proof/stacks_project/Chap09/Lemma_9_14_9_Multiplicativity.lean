import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap09.Definition_9_14_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.14.9:
- primary domain: separable and inseparable degrees in towers of field extensions;
- sampled owner declarations:
  `Field.sepDegree`,
  `Field.insepDegree`,
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic`,
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- best owner abstraction: the canonical mathlib tower-law owners
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- primitive data: only a tower `F ⟶ E ⟶ K` and the algebraicity of the middle extension `E / F`;
- derived API: the textbook display order `[K : F]_s = [K : E]_s [E : F]_s` and
  `[K : F]_i = [K : E]_i [E : F]_i`, obtained from the canonical owners by symmetry and
  commutativity of cardinal multiplication.

Source/core/bridge triage:
- `source-facing`: the textbook multiplicativity formulas written in degree notation;
- `core/canonical`: the mathlib tower laws
  `Field.sepDegree_mul_sepDegree_of_isAlgebraic` and
  `Field.insepDegree_mul_insepDegree_of_isAlgebraic`;
- `bridge/view`: only the harmless reordering of factors into the textbook display order.

This file should therefore be pure canonical recall. Keeping local wrapper theorems here would
duplicate the owner declarations without adding new mathematics.
-/

/- Lemma 9.14.9 (Multiplicativity) (1): the canonical owner for separable-degree multiplicativity
in a tower `K / E / F` is `Field.sepDegree_mul_sepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]_s * [K : E]_s = [K : F]_s` is exactly the
textbook formula up to symmetry and commutativity. -/
recall Field.sepDegree_mul_sepDegree_of_isAlgebraic

/- Lemma 9.14.9 (Multiplicativity) (2): the canonical owner for inseparable-degree multiplicativity
in a tower `K / E / F` is `Field.insepDegree_mul_insepDegree_of_isAlgebraic`. Through the notation
from Definition 9.14.7, its statement `[E : F]_i * [K : E]_i = [K : F]_i` is exactly the
textbook formula up to symmetry and commutativity. -/
recall Field.insepDegree_mul_insepDegree_of_isAlgebraic

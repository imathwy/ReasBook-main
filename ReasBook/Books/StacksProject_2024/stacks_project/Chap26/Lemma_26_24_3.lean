import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` returned the exact canonical composition instances
-- `AlgebraicGeometry.IsImmersion.comp`, `AlgebraicGeometry.IsClosedImmersion.comp`, and
-- `AlgebraicGeometry.IsOpenImmersion.comp`. This item is therefore recorded as a pure
-- canonical recall, following nearby Chapter 26 recall-only files.

/- Lemma 26.24.3 (1): a composition of immersions of schemes is an immersion. -/
recall AlgebraicGeometry.IsImmersion.comp

/- Lemma 26.24.3 (2): a composition of closed immersions of schemes is a closed immersion. -/
recall AlgebraicGeometry.IsClosedImmersion.comp

/- Lemma 26.24.3 (3): a composition of open immersions of schemes is an open immersion. -/
recall AlgebraicGeometry.IsOpenImmersion.comp

section

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

variable [IsImmersion f] [IsImmersion g]

#check (inferInstance : IsImmersion (f ≫ g))

variable [IsClosedImmersion f] [IsClosedImmersion g]

#check (inferInstance : IsClosedImmersion (f ≫ g))

variable [IsOpenImmersion f] [IsOpenImmersion g]

#check (inferInstance : IsOpenImmersion (f ≫ g))

end

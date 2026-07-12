import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall / analogue check:
-- `lean_leansearch` recalled the canonical scheme-side owner `AlgebraicGeometry.Etale`;
-- a direct mathlib source check in `Morphisms/Etale` verifies the exact unnamed instance
-- `[IsOpenImmersion f] : Etale f`, so this item is recorded as a pure canonical recall.

/- Lemma 29.36.9: any open immersion is étale. This is a pure canonical recall: mathlib already
provides the instance `[IsOpenImmersion f] : Etale f`. -/
recall AlgebraicGeometry.Etale.instOfIsOpenImmersion

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

#check (inferInstance : Etale f)

end

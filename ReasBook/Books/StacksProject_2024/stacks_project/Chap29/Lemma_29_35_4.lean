import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the scheme-side composition owner
  `AlgebraicGeometry.FormallyUnramified.instIsStableUnderCompositionScheme` together with the
  ring-level composition theorem `Algebra.Unramified.comp`;
- `Lemma_29_14_5.lean` records the generic affine-local composition theorem `locallyOfType_comp`;
- local Section 29.35 precedent fixes the source-facing owners for this item as `Unramified` and
  `GUnramified`.
-/

section

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- Lemma 29.35.4 (1): the composition of two morphisms which are unramified is unramified. -/
@[stacks 02G9]
theorem unramified_comp [Unramified f] [Unramified g] :
    Unramified (f ≫ g) := sorry

/-- Lemma 29.35.4 (2): the composition of two morphisms which are G-unramified is G-unramified. -/
@[stacks 02G9]
theorem gUnramified_comp [GUnramified f] [GUnramified g] :
    GUnramified (f ≫ g) := sorry

end

end AlgebraicGeometry

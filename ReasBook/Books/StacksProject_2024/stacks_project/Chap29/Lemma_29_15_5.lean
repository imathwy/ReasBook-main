import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall / owner check:
-- - `Definition_29_15_1.lean` records the source phrase "of finite type" for scheme morphisms by
--   the chapter owner `Scheme.Hom.FiniteType`;
-- - mathlib already provides the canonical instance route from `IsImmersion f` to
--   `LocallyOfFiniteType f`, so that part of the source is a pure recall;
-- - the closed-immersion finite-type consequence is source-facing at the chapter owner level and
--   should therefore be stated directly on `Scheme.Hom.FiniteType`.

/- Lemma 29.15.5 (2): an immersion is locally of finite type. This is a pure canonical recall of
the existing mathlib instance. -/
recall AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    LocallyOfFiniteType f

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Lemma 29.15.5 (1): a closed immersion is of finite type. -/
@[stacks 01T6]
theorem finiteType_of_isClosedImmersion [IsClosedImmersion f] :
    FiniteType f := by
  exact
    { toQuasiCompact := inferInstance
      toLocallyOfFiniteType := inferInstance }

end AlgebraicGeometry.Scheme.Hom

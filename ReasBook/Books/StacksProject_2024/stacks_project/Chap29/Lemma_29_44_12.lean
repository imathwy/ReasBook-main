import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall / analogue check:
-- `lean_leansearch` surfaced the exact canonical consequences
-- `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion` and
-- `AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion`.
-- Following local Chapter 29 precedent, the source is recorded as source-facing theorem statements
-- from an explicit `IsClosedImmersion f` hypothesis rather than as a recall-only block.

/-- Lemma 29.44.12 (1): a closed immersion is finite. -/
theorem closedImmersion_isFinite
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsClosedImmersion f) :
    IsFinite f := sorry

/-- Lemma 29.44.12 (2): a closed immersion is integral. -/
theorem closedImmersion_isIntegral
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : IsClosedImmersion f) :
    IsIntegralHom f := sorry

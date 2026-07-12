import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall / analogue check:
-- `lean_leansearch` found the canonical scheme-side base-change stability instances
-- `AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme` and
-- `AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme`, so this item is a direct
-- recall of existing mathlib API.

/- Lemma 29.44.6 (1): a base change of a finite morphism is finite. This is exactly the canonical
scheme-side base-change stability instance for `IsFinite`. -/
recall AlgebraicGeometry.IsFinite.instIsStableUnderBaseChangeScheme

/- Lemma 29.44.6 (2): a base change of an integral morphism is integral. This is exactly the
canonical scheme-side base-change stability instance for `IsIntegralHom`. -/
recall AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme

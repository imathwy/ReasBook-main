import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` recalled the canonical scheme-morphism composition instances
-- `AlgebraicGeometry.IsFinite.instCompScheme` and
-- `AlgebraicGeometry.IsIntegralHom.instCompScheme`, so this item is a direct recall of existing
-- mathlib API.

/- Lemma 29.44.5 (1): a composition of finite morphisms is finite. This is exactly the canonical
scheme-side composition instance for `IsFinite`. -/
recall AlgebraicGeometry.IsFinite.instCompScheme

/- Lemma 29.44.5 (2): a composition of integral morphisms is integral. This is exactly the
canonical scheme-side composition instance for `IsIntegralHom`. -/
recall AlgebraicGeometry.IsIntegralHom.instCompScheme

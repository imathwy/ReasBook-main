import Mathlib
import StacksProject_2024.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` found no existing scheme-theoretic-density intersection
-- theorem; local Chapter 29 precedent uses `schemeTheoreticallyDense` on `X.Opens`.
-- The tag evidence is consistent: item tag `01RF` matches the source URL `/tag/01RF`.

variable {X : Scheme.{u}}

/-- Lemma 29.7.6: If `U`, `V` are scheme theoretically dense open subschemes of a scheme `X`,
then their intersection is scheme theoretically dense in `X`. -/
@[stacks 01RF]
theorem schemeTheoreticallyDense_inf {U V : X.Opens}
    (hU : schemeTheoreticallyDense U) (hV : schemeTheoreticallyDense V) :
    schemeTheoreticallyDense (U ⊓ V) := sorry

end AlgebraicGeometry

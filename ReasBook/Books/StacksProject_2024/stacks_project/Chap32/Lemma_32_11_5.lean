import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsClosedImmersion`,
-- `IsHomeomorph`, and `Scheme.IsQuasiAffine`; local Chapter 30 precedent uses the same
-- closed-immersion/homeomorphism setup with extra Noetherian hypotheses.

/-- Lemma 32.11.5: let `i : Z ⟶ X` be a closed immersion of schemes inducing a homeomorphism of
underlying topological spaces. Then `X` is quasi-affine if and only if `Z` is quasi-affine. -/
@[stacks 0B7L]
theorem isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (hi : IsHomeomorph i) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `IsClosedImmersion`,
-- `IsHomeomorph`, and `Scheme.IsQuasiAffine`; local Lemma 30.17.5 precedent uses the same
-- closed-immersion/homeomorphism setup for Noetherian schemes.

/-- Lemma 30.17.6: let `i : Z ⟶ X` be a closed immersion of Noetherian schemes inducing a
homeomorphism of underlying topological spaces. Then `X` is quasi-affine if and only if `Z` is
quasi-affine. -/
@[stacks 0B7K]
theorem isQuasiAffine_iff_of_isClosedImmersion_isHomeomorph
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsNoetherian X] [IsNoetherian Z]
    [IsClosedImmersion i] (hi : IsHomeomorph i) :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine := sorry

end AlgebraicGeometry

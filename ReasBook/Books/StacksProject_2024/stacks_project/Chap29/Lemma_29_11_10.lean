import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 29.11.10: a closed immersion is an affine morphism. This is a pure canonical recall of
the existing affine-morphism instance for closed immersions. -/
@[stacks 01K9]
recall AlgebraicGeometry.IsClosedImmersion.instIsAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsAffineHom f

end AlgebraicGeometry

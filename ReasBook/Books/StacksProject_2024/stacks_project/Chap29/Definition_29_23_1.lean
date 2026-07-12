import Mathlib.Tactic.Recall
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Definition 29.23.1: for a morphism of schemes `f : X ⟶ S`, the textbook condition that `f` is
universally open is the canonical mathlib owner `AlgebraicGeometry.UniversallyOpen f`. -/
recall AlgebraicGeometry.UniversallyOpen

/- Companion recall: the source definition saying that every base change of `f` is open is exactly
the canonical bridge `AlgebraicGeometry.universallyOpen_iff`. -/
recall AlgebraicGeometry.universallyOpen_iff

/- Companion recall: a universally open morphism is open on underlying topological spaces via the
canonical theorem `Scheme.Hom.isOpenMap`. -/
recall Scheme.Hom.isOpenMap

end AlgebraicGeometry

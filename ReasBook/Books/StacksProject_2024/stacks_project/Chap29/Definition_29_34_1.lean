import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Tactic.Recall

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- Chapter 10 and nearby Chapter 29 recall-only files use the canonical `recall` surface rather
  than local aliases or raw `#check` items;
- local verification confirmed that the source definition is already owned by `Smooth`, with the
  affine-neighborhood criterion given by `Smooth.iff_forall_exists_isStandardSmooth` and the
  affine coordinate-ring notion of “standard smooth” given by `RingHom.IsStandardSmooth`.
-/

/- Definition 29.34.1: a morphism of schemes is smooth precisely in the canonical mathlib sense
`Smooth f`, and the affine “standard smooth” clause is owned by `RingHom.IsStandardSmooth`. -/
recall Smooth

/- Companion recall: the source-facing affine-neighborhood criterion for smoothness. -/
recall Smooth.iff_forall_exists_isStandardSmooth

/- Companion recall: the affine-coordinate notion of “standard smooth”. -/
recall RingHom.IsStandardSmooth

end AlgebraicGeometry

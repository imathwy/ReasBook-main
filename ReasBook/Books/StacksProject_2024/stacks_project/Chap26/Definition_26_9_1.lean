import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

-- Semantic recall: mathlib already owns schemes via `AlgebraicGeometry.Scheme`, together with the
-- canonical forgetful map to locally ringed spaces and the induced morphism bridge
-- `Scheme.Hom.toLRSHom`. For this numbered definition, Chapter 26 precedent keeps the source item
-- as a pure canonical recall rather than introducing a local alias for `Sch`.
/- Source/core/bridge triage:
- `source-facing`: schemes and their morphisms, as in the source category `Sch`.
- `core/canonical`: `AlgebraicGeometry.Scheme`.
- `bridge/view`: `Scheme.forgetToLocallyRingedSpace` and `Scheme.Hom.toLRSHom`. -/

/- Definition 26.9.1: a scheme is the canonical mathlib owner `AlgebraicGeometry.Scheme`, namely a
locally ringed space with affine open neighbourhoods around every point. The category `Sch` of the
source is therefore the canonical category whose objects are schemes and whose morphisms are the
ambient morphisms `X ⟶ Y`. -/
recall AlgebraicGeometry.Scheme
recall AlgebraicGeometry.Scheme.local_affine
recall AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace
recall Scheme.Hom.toLRSHom

end AlgebraicGeometry

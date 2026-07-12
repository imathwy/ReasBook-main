import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical scheme-morphism owner
  `AlgebraicGeometry.IsSmoothOfRelativeDimension`;
- `lake lean` on this file confirmed that the current nondeprecated public surface is
  `SmoothOfRelativeDimension`, with the legacy `IsSmoothOfRelativeDimension` name retained only as
  a deprecated alias;
- this numbered item is therefore recall-only: the source definition is recorded directly on the
  canonical owner rather than through a parallel wrapper.
-/

/- Definition 29.34.13: a morphism of schemes `f : X ⟶ S` is smooth of relative dimension `d` if
it is smooth and `\Omega_{X/S}` is finite locally free of constant rank `d`. In mathlib this
source-facing notion is the canonical owner `SmoothOfRelativeDimension d f`. -/
recall SmoothOfRelativeDimension

/- Companion recall: the canonical relative-dimension owner carries the underlying smoothness of
`f` through the standard theorem below. -/
recall SmoothOfRelativeDimension.smooth

end AlgebraicGeometry

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical affineness owner
-- `IsAffine`, the affine-scheme category `AffineScheme`, the canonical spectrum comparison
-- `Scheme.isoSpec`, and the forgetful path
-- `AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace`.

/- Definition 26.5.5: an affine scheme is represented in mathlib either as a scheme `X` equipped
with `AlgebraicGeometry.IsAffine X`, or as an object of the canonical category
`AlgebraicGeometry.AffineScheme`; morphisms of affine schemes are the ambient morphisms of locally
ringed spaces obtained by forgetting along `AffineScheme.forgetToScheme` and
`Scheme.forgetToLocallyRingedSpace`. -/
recall IsAffine
recall AffineScheme

/- Companion recall: the canonical functor from affine schemes to schemes. -/
recall AffineScheme.forgetToScheme

/- Companion recall: an affine scheme `X` is canonically isomorphic to the spectrum of its global
sections by `Scheme.isoSpec`. -/
recall Scheme.isoSpec

/- Companion recall: an affine scheme viewed through the scheme owner can be packaged into the
canonical affine-scheme category by `AffineScheme.of`. -/
recall AffineScheme.of

/- Companion recall: the underlying locally ringed-space morphism of an affine-scheme morphism is
obtained by forgetting first to schemes and then to locally ringed spaces. -/
recall Scheme.forgetToLocallyRingedSpace

end AlgebraicGeometry

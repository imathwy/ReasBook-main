import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced
-- `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`,
-- `AlgebraicGeometry.Scheme.GlueData`, and `AlgebraicGeometry.Scheme.GlueData.glued` as the
-- canonical gluing owners. The source-faithful surface here is the scheme gluing datum itself,
-- not an existential wrapper asserting that the glued locally ringed space merely admits some
-- scheme structure.

/- Lemma 26.14.2: if the gluing datum of Lemma 26.14.1 is formed from schemes, then the resulting
locally ringed space is already packaged by the canonical scheme gluing owner
`Scheme.GlueData.toLocallyRingedSpaceGlueData`, and the glued object is the scheme
`Scheme.GlueData.glued`. -/
#check Scheme.GlueData.glued
#check Scheme.GlueData.toLocallyRingedSpaceGlueData

/- Lemma 26.14.2: the locally ringed space underlying the glued scheme is canonically the glued
locally ringed space of the forgotten gluing datum. In mathlib this is exactly
`Scheme.GlueData.isoLocallyRingedSpace`. -/
recall Scheme.GlueData.isoLocallyRingedSpace

#check Scheme.GlueData.isoLocallyRingedSpace

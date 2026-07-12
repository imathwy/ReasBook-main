import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `AlgebraicGeometry.IsLocallyNoetherian` and `AlgebraicGeometry.IsNoetherian`, together with the
-- affine specialization `AlgebraicGeometry.isLocallyNoetherian_Spec` and the scheme-level
-- characterization `AlgebraicGeometry.isNoetherian_iff`. This item is therefore a direct recall of
-- existing mathlib scheme predicates rather than a new local wrapper.

/- Definition 28.5.1 (1): a scheme `X` is locally Noetherian via the canonical mathlib predicate
`IsLocallyNoetherian X`, whose affine incarnation is detected by Noetherian coordinate rings. -/
#check AlgebraicGeometry.IsLocallyNoetherian

/- Companion recall: for an affine scheme `Spec R`, local Noetherianity is equivalent to the ring
`R` being Noetherian. -/
#check AlgebraicGeometry.isLocallyNoetherian_Spec

/- Definition 28.5.1 (2): a scheme `X` is Noetherian via the canonical mathlib predicate
`IsNoetherian X`; for schemes this is equivalent to being locally Noetherian and quasi-compact,
encoded topologically as `CompactSpace X`. -/
#check AlgebraicGeometry.IsNoetherian

/- Companion recall: the canonical scheme-level characterization of Noetherian schemes is local
Noetherianity together with quasi-compactness. -/
#check AlgebraicGeometry.isNoetherian_iff

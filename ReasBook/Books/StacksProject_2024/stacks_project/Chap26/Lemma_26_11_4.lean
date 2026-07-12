import Mathlib.AlgebraicGeometry.Properties

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Lemma 26.11.4:
- `source-facing`: the underlying topological space of a scheme is locally quasi-compact;
- `core/canonical`: the owner class `LocallyCompactSpace`, obtained for schemes by applying the
  generic instance `instLocallyCompactSpaceOfPrespectralSpace` to the canonical scheme instance
  `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`;
- `bridge/view`: the source-facing scheme statement is the specialization
  `LocallyCompactSpace X` of that canonical owner. -/

namespace AlgebraicGeometry.Scheme

/-- Lemma 26.11.4: the underlying topological space of any scheme is locally quasi-compact. Via
Definition 5.13.1, the repository formalizes this property by the canonical owner
`LocallyCompactSpace`; for schemes this is the canonical ambient instance obtained from the
scheme prespectral-space instance
`AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`. -/
@[stacks 01IV]
theorem locallyCompactSpace (X : Scheme) : LocallyCompactSpace X :=
  inferInstance

end AlgebraicGeometry.Scheme

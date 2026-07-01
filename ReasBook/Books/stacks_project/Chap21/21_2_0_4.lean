import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.2.0.4:
- primary domain: right derived functors in abelian sheaf categories, computed from injective
  resolutions;
- sampled owner API:
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedToHomotopyCategoryObj`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- primitive data: an additive functor and a chosen injective resolution `I : InjectiveResolution X`;
- derived API: the canonical isomorphism from `((F.rightDerived i).obj X)` to the degree-`i`
  homology of `F` applied termwise to `I.cocomplex`.

Source/core/bridge triage:
- `source-facing`: higher direct images computed by pushing forward a chosen injective resolution;
- `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: specialization of that owner theorem to the direct-image functor `f_*`.

This item adds no new mathematical data beyond recalling the canonical owner theorem, so the main
entry should remain a direct recall rather than a local wrapper. -/

/- 21.2.0.4: the higher direct image `R^i f_* \mathcal F` is computed by choosing an injective
resolution `\mathcal F \to \mathcal I^\bullet` and taking the `i`th cohomology of the pushed
forward complex `f_* \mathcal I^\bullet`; in mathlib this is the canonical isomorphism computing
the `i`th right derived object of a functor from a chosen injective resolution. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

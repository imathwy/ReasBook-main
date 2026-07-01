import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 21.2.0.7:
- primary domain: higher direct images of sheaves as right derived objects of sheaf pushforward;
- sampled owner API:
  `CategoryTheory.Functor.sheafPushforwardContinuous`,
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- primitive data: an additive functor and a chosen injective resolution `I :
  CategoryTheory.InjectiveResolution ℱ`;
- derived API: the canonical isomorphism computing the right-derived value from the pushed-forward
  injective complex.

Source/core/bridge triage:
- `source-facing`: the higher direct image of a sheaf along `F`;
- `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the sheaf-pushforward specialization of that owner theorem.

This item is only a specialization of the canonical owner theorem, so it should not introduce a
parallel named wrapper and tautological equality theorem. -/

/- 21.2.0.7: the higher direct image of a sheaf is computed by the degree-`i` homology of the
pushforward of an injective resolution. This is exactly the specialization of
`InjectiveResolution.isoRightDerivedObj` to the sheaf-pushforward functor. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 20.2.0.4:
- primary domain: right derived functors in abelian categories, computed from injective
  resolutions;
- sampled owner declarations:
  `CategoryTheory.Functor.rightDerived`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj_hom_naturality`;
- best owner abstraction: the canonical injective-resolution computation
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- primitive data: an additive functor `F` and an injective resolution `I` of an object `X`;
- derived API: the comparison isomorphism `R^i F(X) ≅ H^i(F(I^•))` and its naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the formula computing higher direct images from an injective resolution;
- `core/canonical`: `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- `bridge/view`: the specialization to sheaf/module pushforward functors.

This item adds no new mathematical data beyond that canonical owner, so the refined file should
recall it directly rather than introduce any local wrapper or duplicate chapter-level alias.
-/

/- 20.2.0.4: the `i`th higher direct image module is computed by taking the `i`th cohomology
object of the pushforward of an injective resolution. In the general abelian-category form, for an
additive functor `F` and an injective resolution `I`, this is the canonical isomorphism
`R^i F(X) ≅ H^i(F(I^•))`; for the direct image functor on sheaves of modules this is the formula
`R^i f_* \mathcal F = H^i(f_* \mathcal I^\bullet)`. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

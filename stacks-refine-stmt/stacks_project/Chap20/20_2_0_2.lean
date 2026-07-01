import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- 20.2.0.2: the `i`th higher direct image is computed by taking the `i`th cohomology object of
the pushforward of an injective resolution. In the general abelian-category form, for an additive
functor `F` and an injective resolution `I`, this is the canonical isomorphism
`R^i F(X) ≅ H^i(F(I^•))`; for `F = f_*` this is the formula
`R^i f_* \mathcal F = H^i(f_* \mathcal I^\bullet)`. -/
recall CategoryTheory.InjectiveResolution.isoRightDerivedObj

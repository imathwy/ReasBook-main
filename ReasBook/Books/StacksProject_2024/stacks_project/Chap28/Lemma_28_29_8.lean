import Mathlib.AlgebraicGeometry.SpreadingOut

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Semantic recall / source-core-bridge triage:
- `core/canonical`: `Mathlib.AlgebraicGeometry.SpreadingOut` owns the canonical owner
  `Scheme.IsGermInjective`, with the three source cases already exposed upstream as standard
  consequences.
- `source-facing`: Lemma 28.29.8 records these three standard source cases.
- `bridge/view`: each clause is therefore a direct recall of the canonical upstream API.
-/

namespace AlgebraicGeometry.Scheme

/- Lemma 28.29.8 (1): an integral scheme is germ-injective. -/
#check Scheme.isGermInjective_of_isIntegral

/- Lemma 28.29.8 (2): a locally Noetherian scheme is germ-injective. -/
#check Scheme.isGermInjective_of_isLocallyNoetherian

/- Lemma 28.29.8 (3): a reduced scheme with finitely many irreducible components is
germ-injective. -/
#check Scheme.isGermInjective_of_isReduced_of_finite_irreducibleComponents

end AlgebraicGeometry.Scheme

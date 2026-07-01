import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: localization/base change for first cotangent homology of commutative algebras;
- sampled owner declarations:
  `Algebra.H1Cotangent.map`,
  `Algebra.tensorH1CotangentOfFlat`,
  `Algebra.tensorH1CotangentOfIsLocalization`,
  `Algebra.H1Cotangent.isLocalizedModule`;
- best owner abstraction: `Algebra.tensorH1CotangentOfIsLocalization`;
- primitive data: a commutative `A`-algebra `B` together with a multiplicative subset
  `S : Submonoid B`;
- derived API: the canonical localization equivalence on `H¹(L_{B/A})`;
- layer triage:
  - `source-facing`: the quasi-isomorphism
    `NL_{B/A} ⊗_B S⁻¹B → NL_{S⁻¹B/A}`;
  - `core/canonical`: `Algebra.tensorH1CotangentOfIsLocalization`;
  - `bridge/view`: none; this item is a direct owner recall.
-/

/- Lemma 10.134.13: localizing the first cotangent homology along a multiplicative subset
`S ⊂ B` identifies it with the first cotangent homology of the localization `S⁻¹B`. This is the
library-facing consequence of the source statement that the canonical map
`NL_{B/A} ⊗_B S⁻¹B → NL_{S⁻¹B/A}` is a quasi-isomorphism. -/
recall Algebra.tensorH1CotangentOfIsLocalization

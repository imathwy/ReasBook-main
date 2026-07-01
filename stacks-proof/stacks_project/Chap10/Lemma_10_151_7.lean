import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: local commutative algebra of unramified morphisms at a prime;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`,
  `Localization.AtPrime.map_eq_maximalIdeal`;
- best owner abstraction: `Algebra.IsUnramifiedAt`;
- source/core/bridge triage:
  `source-facing`: the Stacks criterion for unramifiedness at a prime in terms of the residue
  extension and the maximal ideal after localization;
  `core/canonical`: `Algebra.IsUnramifiedAt R q`;
  `bridge/view`: `Algebra.isUnramifiedAt_iff_map_eq`;
- primitive data vs derived API: the primitive local data are the prime `q` over `p`, the
  separability of `κ(q) / κ(p)`, and the equality `pS_q = maximalIdeal S_q`. The finite
  dimensionality of `κ(q) / κ(p)` is derived from `Algebra.IsUnramifiedAt R q`, so it is not part
  of the canonical owner criterion.
-/

/- Lemma 10.151.7: for an essentially finite type algebra, the source criterion for unramifiedness
at a prime is exactly the canonical owner theorem `Algebra.isUnramifiedAt_iff_map_eq`. In this
owner formulation, the source's finite residue-field hypothesis is redundant and is therefore not
kept as primitive public data. -/
recall Algebra.isUnramifiedAt_iff_map_eq

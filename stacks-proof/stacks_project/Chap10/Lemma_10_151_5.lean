import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling for Lemma 10.151.5:
- primary domain: local commutative algebra of unramified morphisms at a prime, together with the
  induced residue-field extension;
- sampled owner declarations:
  `Algebra.IsUnramifiedAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `[Algebra.IsUnramifiedAt R q] → Algebra.IsSeparable p.ResidueField q.ResidueField`,
  `[Algebra.IsUnramifiedAt R q] → Module.Finite p.ResidueField q.ResidueField`;
- best owner abstraction: `Algebra.IsUnramifiedAt R q`;
- primitive data vs derived API: the primitive local content is the canonical owner theorem
  `Algebra.isUnramifiedAt_iff_map_eq`, whose two components are residue-field separability and the
  equality `pS_q = maximalIdeal S_q`; finite-dimensionality of `κ(q) / κ(p)` is derived from the
  owner through the canonical module-finite instance and the usual field-specialized
  `FiniteDimensional` bridge.

Source/core/bridge triage:
- `source-facing`: the three Stacks consequences of unramifiedness at a prime;
- `core/canonical`: `Algebra.IsUnramifiedAt R q`;
- `bridge/view`: `Algebra.isUnramifiedAt_iff_map_eq` for parts `(1)` and `(3)`, and the instance
  chain to `FiniteDimensional p.ResidueField q.ResidueField` for part `(2)`.

Since this file only records canonical consequences already owned upstream, it should reuse those
owners directly rather than keep parallel chapter-local theorem names. -/

/- Lemma 10.151.5 (1) and (3): for an essentially finite type algebra, unramifiedness at `q` is
equivalent to the canonical pair consisting of residue-field separability and the equality
`p.map (algebraMap R (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q)`. These are
exactly the first and second components of `Algebra.isUnramifiedAt_iff_map_eq`. -/
recall Algebra.isUnramifiedAt_iff_map_eq

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.EssFiniteType R S]
variable (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra.IsUnramifiedAt R q]

/- Lemma 10.151.5 (2): under the same hypotheses, the residue-field extension `κ(q) / κ(p)` is
finite; in the canonical field-level owner language, this is the instance
`FiniteDimensional p.ResidueField q.ResidueField`. -/
#check (inferInstance : FiniteDimensional p.ResidueField q.ResidueField)

end

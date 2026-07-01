import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {G : Type u} {K : Type v}
variable [Group G] [Field K] [MulSemiringAction G K]

/- Domain-style sampling for Lemma 9.21.6:
- primary domain: finite group actions on fields, fixed fields, and Galois-group realizations;
- sampled owner declarations:
  `FixedPoints.subfield`,
  `IsGaloisGroup`,
  `IsGaloisGroup.fixedPoints`,
  `IsGaloisGroup.mulEquivAlgEquiv`;
- best owner abstraction: the canonical owner predicate `IsGaloisGroup G F K` for a group action on
  a field `K` with fixed field `F`;
- primitive data: the group `G`, the field `K`, the action `MulSemiringAction G K`, and the
  upstream finiteness and faithfulness assumptions needed by the owner instance;
- derived API: the Galoisness of `K / FixedPoints.subfield G K`, the degree formula
  `Module.finrank (FixedPoints.subfield G K) K = Nat.card G`, and the comparison
  `G ≃* Gal(K / FixedPoints.subfield G K)` come from the owner theorems built on that instance.

Layer triage:
- `source-facing`: the textbook statement that a finite faithful action on a field realizes the
  acting group as the Galois group over the fixed field;
- `core/canonical`: the instance `IsGaloisGroup.fixedPoints`;
- `bridge/view`: downstream consequences such as `IsGaloisGroup.isGalois`,
  `IsGaloisGroup.card_eq_finrank`, and `IsGaloisGroup.mulEquivAlgEquiv`.

This item is therefore a pure canonical-recall surface. There is no additional source-facing data
to define locally, so the refined file should reuse the owner instance directly instead of
introducing a parallel theorem or wrapper. -/
/- Lemma 9.21.6: if a finite group `G` acts faithfully on a field `K`, then the extension
`K / FixedPoints.subfield G K` has `G` as its Galois group. This is the canonical mathlib
instance `IsGaloisGroup.fixedPoints`, from which the textbook consequences follow: the extension is
Galois, its degree is `|G|`, and `G ≃* Gal(K / FixedPoints.subfield G K)`. -/
recall IsGaloisGroup.fixedPoints

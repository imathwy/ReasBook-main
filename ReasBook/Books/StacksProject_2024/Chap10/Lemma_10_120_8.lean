import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.120.8 lies in the ACCP / factorization-theory domain for integral domains.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the source hypothesis.
- `WfDvdMonoid` is the core owner abstraction for well-founded strict divisibility.
- `Ideal.setOf_isPrincipal_wellFoundedOn_gt` is the canonical bridge from that owner abstraction to
  the ascending chain condition on principal ideals.
- `WfDvdMonoid.of_setOf_isPrincipal_wellFoundedOn_gt` is the converse bridge already used earlier
  in the chapter.

Layer triage:
- `source-facing`: the UFD implies ACCP corollary below.
- `core/canonical`: `WfDvdMonoid`.
- `bridge/view`: `Ideal.setOf_isPrincipal_wellFoundedOn_gt`.

Primitive data are exactly the `UniqueFactorizationMonoid R` instance; the principal-ideal
well-foundedness statement is derived API, so this file should reuse the owner bridge directly
rather than keep a parallel local proof wrapper. -/
/- Lemma 10.120.8: a unique factorization domain satisfies the ascending chain condition on
principal ideals. Mathlib's owner bridge is the more canonical theorem
`Ideal.setOf_isPrincipal_wellFoundedOn_gt`, stated for any `WfDvdMonoid` domain; the textbook UFD
case is its direct specialization via the canonical `UniqueFactorizationMonoid.toWfDvdMonoid`
instance. -/
recall Ideal.setOf_isPrincipal_wellFoundedOn_gt

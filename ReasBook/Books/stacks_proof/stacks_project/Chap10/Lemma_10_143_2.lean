import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-
Domain-style sampling for Lemma 10.143.2:
- primary domain: commutative-algebraic smoothness and étaleness for `R`-algebras;
- sampled owner declarations:
  `Algebra.Etale`,
  `Algebra.IsStandardSmoothOfRelativeDimension`,
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`;
- best owner abstraction: the algebra-level equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- primitive data: the owner predicates `Etale R S` and `IsStandardSmoothOfRelativeDimension 0 R S`;
- derived API: the forward and backward implications, plus the ring-hom bridge theorem.

Layer triage:
- `source-facing`: the Stacks lemma asserting that étale implies standard smooth of relative
  dimension `0`;
- `core/canonical`: the upstream equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- `bridge/view`: the ring-hom reformulation
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`.

This item adds no new mathematical content beyond the existing owner equivalence, and nothing
downstream depends on a local theorem name, so the canonical refinement is a direct recall rather
than a parallel wrapper for one implication.
-/

/- Lemma 10.143.2: an `R`-algebra is étale if and only if it is standard smooth of relative
dimension `0`; the stated implication is the forward direction of this canonical owner theorem. -/
recall Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

end Algebra

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]

/- Domain-style sampling for adically complete henselian pairs:
- primary domain: commutative algebra of adic completeness and henselian ideals
- sampled same-domain owner declarations:
  `HenselianRing`,
  `HenselianRing.is_henselian`,
  `IsAdicComplete.henselianRing`,
  `localRing_henselian_of_isCompleteLocalRing`
- best owner abstraction: the canonical owner for the target conclusion is `HenselianRing A I`,
  and the canonical bridge from the source hypothesis is the mathlib instance
  `IsAdicComplete.henselianRing`
- primitive data: a commutative ring `A`, an ideal `I`, and the owner hypothesis
  `[IsAdicComplete I A]`
- derived API: the induced henselian structure on `(A, I)`

Layer triage:
- `source-facing`: the Stacks statement that an `I`-adically complete pair `(A, I)` is henselian
- `core/canonical`: the owner `HenselianRing A I`
- `bridge/view`: the instance `IsAdicComplete.henselianRing`

This item adds no new mathematical content beyond that canonical bridge, so the correct refined
surface is a direct `recall` of the owner-level instance rather than a local wrapper theorem or
alias.
-/
/- Lemma 15.11.4: if `A` is `I`-adically complete, then the pair `(A, I)` is henselian. This is
exactly the canonical mathlib instance `IsAdicComplete.henselianRing`. -/
recall IsAdicComplete.henselianRing

end

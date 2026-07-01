import Mathlib
import stacks_project.Chap10.Definition_10_160_1
import stacks_project.Chap10.Definition_10_162_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: commutative algebra of Nagata rings and the complete-local criterion for the
  `N-2` condition on prime quotients;
- sampled owner declarations of the same kind:
  `IsCompleteLocalRing`,
  `NagataRing`,
  `quotient_isCompleteLocalRing`,
  `IsN2Ring`;
- best owner abstraction: `NagataRing` is the source-facing owner for this item, with complete
  locality and Noetherianity as primitive hypotheses and the prime-quotient `N-2` conditions as
  derived owner data;
- primitive data vs. derived API:
  the primitive inputs are only `[IsCompleteLocalRing R]` and `[IsNoetherianRing R]`,
  while the quotient-by-prime `IsN2Ring` instances belong to the `NagataRing` owner API.

Source/core/bridge triage:
- `source-facing`: the complete-local criterion proving `NagataRing R`;
- `core/canonical`: the owner class `NagataRing` together with its quotient field
  `quotient_isN2Ring`;
- `bridge/view`: the quotient stability theorem `quotient_isCompleteLocalRing`, which supplies the
  canonical complete-local input on each prime quotient.
-/
-- Proof sketch: for each prime ideal `p`, the quotient `R ⧸ p` is again complete local by
-- `quotient_isCompleteLocalRing`, and it is Noetherian by the canonical quotient instance. Hence
-- it remains to show that a
-- Noetherian complete local domain is `N-2`; reduce by the Cohen structure theorem and the finite
-- extension reduction to formal power series rings over a field or a Cohen ring, then apply the
-- power-series and Tate lemmas to reduce to the field case.
/-- Lemma 10.162.8: a Noetherian complete local ring is a Nagata ring. -/
instance nagataRing_of_noetherian_completeLocalRing : NagataRing R := sorry

end

import StacksProject_2024.Chap10.Definition_10_67_1
import StacksProject_2024.Chap10.Definition_10_157_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain triage:
* source-facing: the equivalence between Serre's condition `(S_1)` and having no embedded
  associated primes;
* core/canonical: `Module.SerreConditionS R M 1` for `(S_1)` and `embeddedAssociatedPrimes R M`
  for the no-embedded-primes condition;
* bridge/view: the theorem below, which keeps the source-facing equivalence as a thin companion of
  those owners.

Primitive data live in the owner abstractions above. The localized regular-element criterion and
the "every associated prime is minimal" wording are derived API and should not remain separate
owners in this file.
-/

-- Proof sketch: if `M` has an embedded associated prime `p`, localizing at `p` gives depth `0`
-- while the support dimension stays at least `1`, so `(S_1)` fails. Conversely, if `(S_1)` fails
-- at some prime `p`, then `depth(M_p) = 0` makes `p` associated after localization and descent,
-- while support dimension at least `1` produces a smaller prime in the support; a minimal such
-- prime is associated, so `p` is embedded.
/-- Lemma 10.157.2: a finite module over a Noetherian ring has no embedded associated primes if
and only if it satisfies Serre's condition `(S_1)`. -/
theorem embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one :
    embeddedAssociatedPrimes R M = ∅ ↔ Module.SerreConditionS R M 1 := sorry

end

end Module

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Example 9.3.2:
- primary domain: prime fields and the canonical finite field owner `ZMod p`;
- sampled owner API:
  `Int.quotientSpanNatEquivZMod`,
  `ZMod.instField`,
  `Nat.card_zmod`,
  `Int.ideal_span_isMaximal_of_prime`;
- best owner abstraction: the field `ZMod p` itself, with `Int.quotientSpanNatEquivZMod` as the
  bridge from the quotient presentation `ℤ/(p)`;
- primitive data: `p : ℕ` together with `[Fact p.Prime]`;
- derived API: the field structure on `ZMod p`, the bridge equivalence
  `ℤ ⧸ Ideal.span {(p : ℤ)} ≃+* ZMod p`, and the cardinality statement
  `Nat.card (ZMod p) = p`.

Primitive-vs-derived split:
- primitive owner data: the prime field object `ZMod p`;
- bridge/view data: the quotient presentation `ℤ/(p)` and the equivalence
  `Int.quotientSpanNatEquivZMod p`;
- derived consequences: `ZMod.instField` and `Nat.card_zmod`.

Source/core/bridge triage:
- `source-facing`: the example that the quotient ring `ℤ/(p)` is the usual prime field `𝔽_p`;
- `core/canonical`: `ZMod p` with its canonical field instance `ZMod.instField`;
- `bridge/view`: `Int.quotientSpanNatEquivZMod`.

The quotient maximality theorem `Int.ideal_span_isMaximal_of_prime` explains why the bridge model is
a field, but it is support for the quotient presentation rather than the owner-level public API for
`𝔽_p`, so the refined file should stop at `ZMod.instField` and `Nat.card_zmod`.
-/

/- Example 9.3.2 (Prime fields): the quotient ring `ℤ/(n)` is canonically identified with
`ZMod n`; for prime `p`, this is the usual model for `𝔽_p`. -/
recall Int.quotientSpanNatEquivZMod (n : ℕ) : ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n

section

variable (p : ℕ) [Fact p.Prime]

/- Example 9.3.2, core/canonical recall: for prime `p`, the prime field `𝔽_p` is the canonical
owner `ZMod p`, equipped with the standard field structure. The quotient-ring presentation
`ℤ/(p)` is only a bridge to this owner via `Int.quotientSpanNatEquivZMod p`. -/
recall ZMod.instField (p : ℕ) [Fact p.Prime] : Field (ZMod p)

end

/- Example 9.3.2, owner-level consequence: the prime field `𝔽_p = ZMod p` has exactly `p`
elements. The quotient cardinality of `ℤ/(p)` is recovered by transporting this statement across
`Int.quotientSpanNatEquivZMod p`, not vice versa. -/
recall Nat.card_zmod (n : ℕ) : Nat.card (ZMod n) = n

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Cardinal

section

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/- Domain-style sampling for Lemma 9.8.9:
- primary domain: cardinality bounds for algebraic extensions;
- sampled owner declarations:
  `Algebra.IsAlgebraic.cardinalMk_le_max`,
  `Algebra.IsAlgebraic.lift_cardinalMk_le_max`,
  `IsTranscendenceBasis.cardinalMk_eq`,
  `Algebra.trdeg`;
- best owner abstraction: `Algebra.IsAlgebraic.cardinalMk_le_max`;
- primitive data: the field extension `F ⟶ E` together with the algebraicity hypothesis;
- derived API: textbook rewrites such as commuting the `max` arguments are mere consequences, not a
  second owner theorem.

Source/core/bridge triage:
- `source-facing`: the field-theoretic cardinality bound in Tag `09GK`;
- `core/canonical`: `Algebra.IsAlgebraic.cardinalMk_le_max`;
- `bridge/view`: none needed here, since the source statement is exactly the canonical owner theorem
  specialized to fields. -/

/- Lemma 9.8.9 (Tag 09GK): if `E / F` is an algebraic extension of fields, then
`|E| ≤ max (|F|, ℵ₀)`; this is the canonical mathlib theorem
`Algebra.IsAlgebraic.cardinalMk_le_max`, already tagged `[stacks 09GK]`. -/
recall Algebra.IsAlgebraic.cardinalMk_le_max

end

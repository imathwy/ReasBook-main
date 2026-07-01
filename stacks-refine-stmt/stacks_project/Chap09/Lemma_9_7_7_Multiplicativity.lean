import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap09.Definition_9_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped FieldExtensionDegree

universe u

/- Domain-style sampling for Lemma 9.7.7:
- primary domain: towers of field extensions and cardinal extension degree;
- sampled owner declarations:
  `Module.rank`,
  the chapter notation `[F : E]` from Definition 9.7.1,
  `rank_mul_rank`,
  `Module.finrank_mul_finrank`;
- best owner abstraction: the canonical tower-law owner is `rank_mul_rank`, while `[F : E]` is
  only the source-facing notation for `Module.rank E F`;
- primitive data: the tower `k ⟶ E ⟶ F`;
- derived API: the degree formula in textbook notation.

Layer triage:
- `source-facing`: the displayed equality `[F : k] = [F : E] * [E : k]`;
- `core/canonical`: `rank_mul_rank`;
- `bridge/view`: the notation from Definition 9.7.1 rewriting `Module.rank` into degree notation.
-/

variable {k E F : Type u} [Field k] [Field E] [Field F]
variable [Algebra k E] [Algebra E F] [Algebra k F] [IsScalarTower k E F]

/- Lemma 9.7.7 (Multiplicativity): for a tower of fields `F / E / k`, the extension degrees
multiply:
`[F : k] = [F : E] * [E : k]`. This is exactly the canonical mathlib tower law `rank_mul_rank`,
viewed through the chapter notation `[L : K] = Module.rank K L`. -/
recall rank_mul_rank

import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G]
variable (hG : IsPGroup p G)
variable (X : Type v) [MulAction G X] [Finite X]

/- Lemma 8-8.3-6: if a `p`-group `G` acts on a finite set `X`, then the cardinality of `X` is
congruent modulo `p` to the cardinality of the fixed-point set `fixedPoints G X`.
This is exactly the canonical mathlib theorem `IsPGroup.card_modEq_card_fixedPoints`. -/
recall IsPGroup.card_modEq_card_fixedPoints

end

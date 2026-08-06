module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Recall

public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (G : Type u) (S : Type v) [Group G]

/- Definition 3.4.1: A left action of a group `G` on a set `S` is the canonical mathlib typeclass
`MulAction G S`, written using the action notation `g • s`, with axioms `1 • s = s` and
`(g' * g) • s = g' • (g • s)`. -/
recall MulAction (G : Type u) (S : Type v) [Monoid G] : Type _

/- The defining left-action axioms are the canonical theorems `one_smul` and `mul_smul`. -/
recall one_smul (M : Type u) {α : Type v} [Monoid M] [MulAction M α] (b : α) : (1 : M) • b = b

/- The action of a product `g' * g` is the iterated action of `g` followed by `g'`. -/
recall mul_smul {M : Type u} {α : Type v} [Semigroup M] [SemigroupAction M α] (g' g : M)
    (s : α) : (g' * g) • s = g' • (g • s)

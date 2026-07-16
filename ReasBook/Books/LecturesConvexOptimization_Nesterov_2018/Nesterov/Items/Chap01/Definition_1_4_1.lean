import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap01.Definition_1_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.4.1 is a source-facing recall in the order-theoretic monotonicity domain.

Layer targeted by this refinement:
* source-facing recall of the Chapter 1 owner theorem for decreasing sequences on `ℕ`

Primary domain:
* monotonicity of sequences on preorders, specialized here to real sequences on `ℕ`

Relevant owner-style declarations sampled before refining:
* `Antitone`, the canonical owner predicate for decreasing maps on a preorder;
* `antitone_nat_of_succ_le`, the canonical `ℕ` constructor from the one-step decrease condition;
* `antitone_nat_iff_succ_le` in `Nesterov/Chap01/Definition_1_4_1.lean`, the chapter bridge
  theorem already packaging the textbook successor-step criterion;
* `bounded_relaxation_sequence_tendsto_infimum` in `Nesterov/Chap01/Proposition_1_4_2.lean`, the
  direct downstream theorem that consumes the chapter bridge instead of a local item-level copy.

Best owner abstraction:
* source-facing recall: `Antitone` specialized to sequences `ℕ → ℝ`;
* core/canonical owner: `Antitone`;
* bridge/view: `antitone_nat_iff_succ_le`.

Primitive data:
* a sequence `a : ℕ → ℝ`;
* the owner predicate `Antitone a`.

Derived API:
* the textbook one-step decrease criterion `∀ k, a (k + 1) ≤ a k`.

This item therefore reuses the exact Chapter 1 owner/bridge surface directly and introduces no
parallel local copy of the successor-step equivalence. -/

/- Definition 1.4.1: a relaxation sequence is exactly the canonical predicate `Antitone`
specialized to real sequences indexed by `ℕ`. -/
#check (Antitone : (ℕ → ℝ) → Prop)

/- On `ℕ`, the owner predicate `Antitone` is equivalent to the textbook one-step decrease
criterion for real sequences. -/
section

variable {a : ℕ → ℝ}

#check (antitone_nat_iff_succ_le : Antitone a ↔ ∀ n : ℕ, a (n + 1) ≤ a n)

end

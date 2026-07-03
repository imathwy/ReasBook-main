import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap01.Proposition_1_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

/- Proposition 1.4.2 lies in the order-theoretic monotone-convergence domain.

Relevant owner-style declarations sampled before refining:
* `Antitone`, the canonical owner predicate for decreasing sequences;
* `antitone_nat_iff_succ_le` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Definition_1_4_1.lean`, the chapter bridge from
  the textbook one-step decrease condition to `Antitone`;
* `tendsto_atTop_ciInf`, the canonical monotone-convergence owner theorem for antitone
  bounded-below sequences;
* `relaxationSequence_tendsto_inf` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_4_2.lean`, the chapter
  source-facing owner already expressing this proposition.

Best owner abstraction:
* source-facing: a real relaxation sequence `a : ℕ → ℝ` with the textbook successor-step decrease
  hypothesis and a lower bound on its range;
* core/canonical: `relaxationSequence_tendsto_inf`, built from `Antitone` and
  `tendsto_atTop_ciInf`;
* bridge/view: `antitone_nat_iff_succ_le`.

Primitive data:
* a real sequence `a : ℕ → ℝ`;
* the one-step decrease hypothesis `∀ n, a (n + 1) ≤ a n`;
* the bounded-below hypothesis `BddBelow (Set.range a)`.

Derived API:
* convergence of `a` to `sInf (Set.range a)`.

This item is recall-first: the chapter file already owns the source-faithful proposition, so the
item file reuses that owner directly instead of keeping parallel local theorem copies specialized
to `ℝ`. -/

/- Proposition 1.4.2: a bounded-below relaxation sequence converges to the infimum of its
range. The textbook real-sequence statement is the specialization `α = ℝ`. -/
recall relaxationSequence_tendsto_inf {α : Type*} [TopologicalSpace α]
    [ConditionallyCompletePartialOrderInf α] [InfConvergenceClass α] {a : ℕ → α}
    (ha : ∀ n : ℕ, a (n + 1) ≤ a n) (hbdd : BddBelow (Set.range a)) :
    Tendsto a atTop (nhds (sInf (Set.range a)))

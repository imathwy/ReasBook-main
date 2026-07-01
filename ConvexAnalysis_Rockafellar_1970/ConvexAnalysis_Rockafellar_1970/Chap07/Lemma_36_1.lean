import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w}
variable [CompleteLattice β]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 36.1 is the basic minimax inequality
  `sup_{u ∈ C} inf_{v ∈ D} K(u, v) ≤ inf_{v ∈ D} sup_{u ∈ C} K(u, v)`.
- `core/canonical`: the Chapter 36 owner theorem is
  `Bifunction.maximin_le_minimax_on`, stated directly in terms of the canonical complete-lattice
  owners `maximinValueOn` and `minimaxValueOn`.
- `bridge/view`: this file contributes no additional mathematics beyond recalling that owner
  theorem, so the correct public surface is direct reuse rather than a parallel local theorem
  shell.

Primary mathematical domain:
- minimax inequalities for complete-lattice-valued bifunctions.

Domain-style sampling used here:
- `Bifunction.maximinValueOn` from `Definition_36_0_1`;
- `Bifunction.minimaxValueOn` from `Definition_36_0_1`;
- `Bifunction.maximin_le_minimax_on` from `Definition_36_0_1`;
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7` as the nearby owner abstraction
  governing the Chapter 36 saddle-value API.

Primitive data vs derived API:
- primitive data: the sets `C`, `D`, and the bifunction `K`;
- primitive owner layer: the Chapter 36 value operators `maximinValueOn` and `minimaxValueOn`;
- derived API: the minimax inequality itself.

Layer target: `bridge/view`. This item is a recall-only bridge to the canonical Chapter 36 owner.
-/

/- Lemma 36.1: for a bifunction on a product set, the maximin value
`sup_{u ∈ C} inf_{v ∈ D} K(u, v)` is bounded above by the minimax value
`inf_{v ∈ D} sup_{u ∈ C} K(u, v)`. The source's nonemptiness assumption is redundant once this is
expressed through the Chapter 36 complete-lattice owners. -/
recall Bifunction.maximin_le_minimax_on
    (C : Set E) (D : Set F) (K : E → F → β) :
    Bifunction.maximinValueOn C D K ≤ Bifunction.minimaxValueOn C D K

end

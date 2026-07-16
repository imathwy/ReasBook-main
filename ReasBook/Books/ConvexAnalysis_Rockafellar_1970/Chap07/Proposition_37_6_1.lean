import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Theorem_37_6

/-!
Proposition 37.6.1 (source label), canonicalized as a pure recall bridge.

Abstraction commitments of this source-facing item:
- codomain layer: inherited from the owner theorem at `WithBotTop α` (not `EReal`);
- scalar/ambient structure: inherited from the owner theorem's generalized `R`-based layer
  (not fixed to `ℝ`);
- topology language: inherited via relative-interior hypotheses `ri[R](...)` and conclusion in
  `dom`, rather than introducing a new ambient-topology wrapper statement.

This file intentionally introduces no local owner alias and no local proof. Any unresolved proof
work is upstream in `Theorem_37_6.lean`; this proposition only re-exposes that canonical owner
under the textbook source label.
-/
recall SaddleFunction.exists_pair_saddlePoint_mem_dom_of_no_common_recession_directions

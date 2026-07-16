import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.6 recalls Rockafellar's `0/+∞` indicator function of a set.
- `core/canonical`: this project already owns that notion at the Chapter 1 notation/API layer
  `δ[α](· | C)`, with intrinsic owner `indicator` and bridge APIs
  `indicator_eq_piecewise` / `indicator_def`.
- `bridge/view`: no new mathematics is introduced here, so the faithful refinement is direct
  canonical recall rather than a second alias.

Primary mathematical domain: set indicators on the canonical ordered-extended codomain layer
`WithTopBot α`.

Domain-style sampling used here:
- `indicator`;
- `indicator_eq_piecewise`;
- `indicator_def`;
- `indicator_of_mem` / `indicator_of_notMem`;
- `Set.piecewise`;
- the notation `δ(· | C)`.

Primitive data:
- a set `C : Set E`.

Derived API:
- owner-level indicator notation plus the pointwise `if` formula.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.27.6: Rockafellar's indicator is recalled at the Chapter 1 canonical notation/API
surface `δ[α](· | C)`, with primitive owner `indicator`. -/
recall indicator

/- Owner bridge: the chapter indicator is exactly the `Set.piecewise` two-branch surface. -/
recall indicator_eq_piecewise

/- The source pointwise formula is exactly the canonical unfolding theorem `indicator_def`; this
item reuses it directly instead of introducing a local wrapper theorem. -/
recall indicator_def

/- Branch-level source consequences: on-set value `0` and off-set value `+∞`. -/
recall indicator_of_mem
recall indicator_of_notMem

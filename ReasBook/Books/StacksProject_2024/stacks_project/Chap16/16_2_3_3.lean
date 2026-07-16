import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for `16_2_3_3`:
- primary domain: Jacobian minors and strictly standard elements attached to a finite presentation
  in `Algebra.Presentation`;
- sampled owner API:
  `Algebra.Presentation.jacobianColumnMinor`,
  `Algebra.Presentation.IsStrictlyStandardElement`,
  `Algebra.IsStrictlyStandard`;
- best owner abstraction: the presentation-level owner
  `Algebra.Presentation.IsStrictlyStandardElement`;
- primitive data: the finite presentation `P`, the bound `c ≤ m`, and the canonical minor
  `P.jacobianColumnMinor hcₘ I` indexed by `c`-element subsets of variables;
- derived API: the displayed Jacobian-minor expansion
  `a = ∑ I, aI I * algebraMap P.Ring A (P.jacobianColumnMinor hcₘ I)` appears as one conjunct in
  the witness data for `P.IsStrictlyStandardElement a`.

Source/core/bridge triage:
- `source-facing`: the first displayed Jacobian-minor expansion in the Stacks definition of strict
  standardness;
- `core/canonical`: the owner predicate `Algebra.Presentation.IsStrictlyStandardElement` together
  with the canonical minor owner `jacobianColumnMinor`;
- `bridge/view`: this file only recalls that the source clause uses the same canonical
  Jacobian-minor expression already built into the owner API.
-/

/- 16.2.3.3: the first displayed clause of the strict standard condition uses the chapter's
canonical Jacobian-column minors attached to a finite presentation. -/
recall Algebra.Presentation.jacobianColumnMinor

/- Companion recall: the owner predicate `Algebra.Presentation.IsStrictlyStandardElement`
packages the displayed Jacobian-minor expansion as part of its witness data. -/
recall Algebra.Presentation.IsStrictlyStandardElement

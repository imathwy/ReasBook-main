import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.8.4:
- primary domain: algebraic elements and algebraic extensions in a tower of field extensions;
- sampled owner declarations:
  `IsAlgebraic`,
  `Algebra.IsAlgebraic`;
- sampled derived API:
  `IsAlgebraic.tower_top`,
  `Algebra.IsAlgebraic.tower_top`;
- best owner abstraction: the pointwise owner `IsAlgebraic`, with the extension-level owner
  `Algebra.IsAlgebraic` for the quantified version;
- primitive data: none locally, since the tower-stability statements are already canonical
  mathlib theorems on these owners;
- derived API: the two `tower_top` theorems.

Source/core/bridge triage:
- `source-facing`: algebraicity descends along the base field in a tower `F ⟶ E ⟶ K`;
- `core/canonical`: `IsAlgebraic` and `Algebra.IsAlgebraic`;
- `bridge/view`: `IsAlgebraic.tower_top` and `Algebra.IsAlgebraic.tower_top`, which express the
  tower-stability property for the pointwise and extension-level owners.

This file should therefore stay recall-only: a local theorem shell would duplicate the canonical
owner-derived API without adding new mathematics or improving the statement surface. -/

/- Lemma 9.8.4: in a tower of field extensions `K/E/F`, any element of `K` that is algebraic
over `F` is also algebraic over `E`; this is the canonical theorem `IsAlgebraic.tower_top`. -/
recall IsAlgebraic.tower_top

/- Companion recall: if the extension `K/F` is algebraic, then the extension `K/E` is algebraic;
this is the canonical theorem `Algebra.IsAlgebraic.tower_top`. -/
recall Algebra.IsAlgebraic.tower_top

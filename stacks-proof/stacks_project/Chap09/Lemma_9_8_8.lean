import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.8.8:
- primary domain: transitivity of algebraic field extensions in a tower;
- sampled owner declarations:
  `IsAlgebraic.restrictScalars`,
  `Algebra.IsAlgebraic.trans`,
  `Algebra.IsAlgebraic.tower_top`;
- best owner abstraction: `Algebra.IsAlgebraic.trans`;
- primitive data: a tower of field extensions with algebraicity hypotheses on the two stages;
- derived API: the pointwise restriction-of-scalars route proving the top extension is algebraic.

Source/core/bridge triage:
- `source-facing`: algebraicity of the composite field extension;
- `core/canonical`: `Algebra.IsAlgebraic.trans`;
- `bridge/view`: `IsAlgebraic.restrictScalars`, which is the pointwise mechanism used by the owner
  theorem.

This file should therefore remain a pure recall surface: the source statement is already exactly
the canonical owner theorem, so any local theorem restating transitivity would only duplicate
upstream API. -/

/- Lemma 9.8.8 (Tag 09GJ): if `E / k` and `F / E` are algebraic extensions of fields, then
`F / k` is an algebraic extension of fields; this is the canonical transitivity theorem
`Algebra.IsAlgebraic.trans`. -/
recall Algebra.IsAlgebraic.trans

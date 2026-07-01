import stacks_project.Chap09.Definition_9_8_1
import stacks_project.Chap09.Definition_9_12_2
import stacks_project.Chap09.Definition_9_14_1
import stacks_project.Chap09.Definition_9_15_1
import stacks_project.Chap09.Definition_9_21_1
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 9.28.1:
- primary domain: field-extension properties in commutative algebra / field theory;
- sampled representative Chapter 9 owner files:
  `Definition_9_8_1`,
  `Definition_9_12_2`,
  `Definition_9_15_1`,
  `Definition_9_21_1`;
- sampled representative owner declarations:
  `Algebra.IsAlgebraic`,
  `Algebra.IsSeparable`,
  `Normal`,
  `IsGalois`;
- sampled derived/specification API:
  `Algebra.isAlgebraic_def`,
  `Algebra.isSeparable_iff`,
  `isPurelyInseparable_iff_pow_mem`,
  `normal_iff`,
  `isGalois_iff`;
- best owner abstraction: no new owner lives in this review file; it should reuse the canonical
  extension-level owners already recalled earlier in Chapter 9, without rebuilding their
  specification surface in this aggregate review item;
- primitive data: none locally, since every notion named in the source is already owned upstream;
- derived API: the earlier owner files already expose the companion textbook characterizations, so
  this file should aggregate the owner layer only.

Source/core/bridge triage:
- `source-facing`: the review list of textbook notions "algebraic / separable / purely
  inseparable / normal / Galois";
- `core/canonical`: the upstream Chapter 9 recalls of the mathlib owners named above;
- `bridge/view`: the companion recall theorems already provided in the earlier owner files.

This item should therefore remain a pure review-recall file, reusing the chapter's earlier owner
entries rather than repeating companion characterizations or introducing any parallel wrapper. -/

/- Definition 9.28.1: this review item simply recollects the earlier Chapter 9 canonical owner
notions for algebraic, separable, purely inseparable, normal, and Galois field extensions:
`Algebra.IsAlgebraic`, `Algebra.IsSeparable`, `IsPurelyInseparable`, `Normal`, and `IsGalois`. -/
recall Algebra.IsAlgebraic

/- Definition 9.28.1: the textbook notion that an algebraic field extension is separable is the
canonical mathlib typeclass `Algebra.IsSeparable`; algebraicity is absorbed canonically by the
pointwise separability condition. -/
recall Algebra.IsSeparable

/- Definition 9.28.1: in positive characteristic, the textbook notion that an algebraic field
extension is purely inseparable is the canonical mathlib typeclass `IsPurelyInseparable`, which
again packages algebraicity canonically. -/
recall IsPurelyInseparable

/- Definition 9.28.1: the textbook notion that an algebraic field extension is normal is the
canonical field-extension class `Normal`, which already packages algebraicity. -/
recall Normal

/- Definition 9.28.1: a Galois extension is the canonical field-extension class `IsGalois`. -/
recall IsGalois

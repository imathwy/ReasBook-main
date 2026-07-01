import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2

noncomputable section

namespace Bifunction

/-!
Source/core/bridge triage:
- `source-facing`: Lemma33.0.3 has two atomic clauses, asserting separately that the lower and
  upper Chapter 33 simple extensions agree with the original bifunction on `C × D`.
- `core/canonical`: the exact owner theorems already exist upstream as
  `lowerSimpleExtension_apply` and `upperSimpleExtension_apply` in
  `Definition33.0.2`.
- `bridge/view`: this item is therefore a pure recall of those canonical intrinsic evaluation
  theorems, rather than a new wrapper theorem or a conjunction-valued package.

Domain-style sampling:
- `Bifunction.lowerSimpleExtension` from `Definition33.0.2`;
- `Bifunction.upperSimpleExtension` from `Definition33.0.2`;
- `lowerSimpleExtension_apply` from `Definition33.0.2`;
- `upperSimpleExtension_apply` from `Definition33.0.2`.

Primitive data vs derived API:
- primitive data: a bifunction `K : C → D → β` together with the minimal codomain structure
  `[Bot β] [Top β]` needed by the Chapter 33 simple-extension owners;
- derived API: the two pointwise agreement clauses on `C × D`.

Layer target: `source-facing`, via exact reuse of the canonical owner theorems.
-/

/- Lemma33.0.3 (1): on subtype points `(u, v) : C × D`, the intrinsic lower simple extension
agrees with the original bifunction `K`. -/
recall lowerSimpleExtension_apply

/- Lemma33.0.3 (2): on subtype points `(u, v) : C × D`, the intrinsic upper simple extension
agrees with the original bifunction `K`. -/
recall upperSimpleExtension_apply

end Bifunction

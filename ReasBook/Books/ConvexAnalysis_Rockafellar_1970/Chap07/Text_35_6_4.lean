import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_6_3

noncomputable section

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.4 names the set-valued mapping `(u, v) ↦ ∂K(u, v)` with no extra
  ambient carrier parameters.
- `core/canonical`: the primitive owner remains the pairing-level product owner
  `Bifunction.subdifferentialAt` from `Text_35_6_3`.
- `bridge/view`: `Bifunction.subdifferentialAtDual` is the canonical strong-dual bridge of that
  primitive owner, and this file keeps both surfaces coherent in recall form.

Primary mathematical domain:
- convex analysis of saddle bifunctions and their saddle subdifferentials.

Domain-style sampling:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `Bifunction.subdifferential2At` from `Text_35_5_2`;
- `Bifunction.subdifferentialAt` from `Text_35_6_3`;
- `Bifunction.mem_subdifferentialAt` from `Text_35_6_3`;
- `Bifunction.subdifferentialAtDual` and `Bifunction.mem_subdifferentialAtDual` from
  `Text_35_6_3`.

Primitive data vs derived API:
- primitive owner data already exist upstream in the chapter at `Text_35_6_3`;
- derived API here: recall of the owner and companion theorem at the pairing layer, together with
  recall of the no-parameter strong-dual bridge surface used in source-facing notation.

Layer target: owner-first pairing surface with coherent strong-dual bridge recall.
This file intentionally avoids rebinding local scalar/ambient assumptions; those abstractions are
owned upstream by the recalled declarations.
-/

namespace Bifunction

/- Text 35.6.4 pairing-level owner recall. -/
recall subdifferentialAt

/- Pairing-level coordinate membership companion recall. -/
recall mem_subdifferentialAt

/- Strong-dual bridge owner recall, using plain source notation `∂ₛ K(u, v)`. -/
recall subdifferentialAtDual

/- Strong-dual coordinate membership companion recall. -/
recall mem_subdifferentialAtDual

end Bifunction

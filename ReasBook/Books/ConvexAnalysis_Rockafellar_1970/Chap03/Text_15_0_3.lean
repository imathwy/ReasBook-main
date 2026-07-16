import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage:
- `source-facing`: Text 15.0.3 restates the gauge-recovery formula for the unit sublevel set
  `C = {x | k x ≤ 1}` attached to a gauge `k`.
- `core/canonical`: the ambient owner abstractions are the gauge class `IsGauge` from
  Text 15.0.1 and the canonical set gauge `egauge ℝ≥0`; the exact theorem-level owner is the
  imported `IsGauge.eq_egauge_unitSublevel`.
- `bridge/view`: no new bridge is needed here; the source statement has the exact interface of the
  imported owner theorem, so introducing a local theorem shell would only duplicate upstream API.

Domain-style sampling used here:
- `IsGauge`;
- `egauge`;
- `egauge_eq_sInf_nonneg_dilates`;
- `IsGauge.eq_egauge_unitSublevel`.

Primitive data vs derived API:
- there is no new primitive datum beyond the gauge `k`;
- the displayed equality is already the canonical theorem-level API from Text 15.0.2.

Layer target: `core/canonical` direct reuse. This item adds no new mathematical content beyond the
exact upstream theorem, so the refined file should reuse that theorem verbatim rather than keep a
parallel local declaration.
-/

/- Text 15.0.3: if `k` is a gauge on `R^n` and `C = {x | k x ≤ 1}`, then the gauge
`γ(· | C)`, formalized as `egauge ℝ≥0 C` and coerced to `EReal`, agrees with `k` as a function.
This is exactly the preceding owner theorem `IsGauge.eq_egauge_unitSublevel`, so this item is a
direct canonical recall rather than a parallel local theorem shell. -/
recall IsGauge.eq_egauge_unitSublevel

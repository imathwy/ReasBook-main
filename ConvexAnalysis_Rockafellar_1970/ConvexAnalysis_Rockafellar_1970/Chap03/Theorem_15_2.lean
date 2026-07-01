import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped GaugePolar RealInnerProductSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.2 identifies norms with symmetric closed bounded convex unit balls
  whose interior contains `0`, and then states that the polar of a norm is again a norm. The
  source specialization to `R^n` is recovered by taking `E = EuclideanSpace ℝ (Fin n)`.
- `core/canonical`: the Chapter 15 owner abstractions are the norm-gauge predicate `IsGaugeNorm`,
  the canonical unit sublevel `gaugeUnitSublevel`, and the polar-gauge owner `kᵒ`.
- `bridge/view`: the set side is expressed through the canonical unit sublevel
  `gaugeUnitSublevel k`; its closed/convex/bounded content is read directly through the canonical
  set predicates `IsClosed`, `Convex ℝ`, `Bornology.IsBounded`, `Balanced ℝ`, and `interior`.

Domain-style sampling used here:
- `gauge` from mathlib's Minkowski-functional API;
- `Function.Even` as the canonical symmetry predicate for functions;
- `Balanced ℝ` from the locally convex API as the canonical symmetry predicate for convex sets;
- the Chapter 15 owners `gaugeUnitSublevel`, `IsGaugeNorm`, and `gauge_polar`;
- `interior` as the canonical interior predicate.

Primitive data vs derived API:
- primitive input: a gauge `k : E → EReal`, owned by `IsGauge`;
- derived set-side view: the canonical unit sublevel `gaugeUnitSublevel k = {x | k x ≤ 1}`;
- derived outputs: the norm-gauge property of `k`, the source-facing convex-body conditions on
  `gaugeUnitSublevel k`, and the norm-gauge property of `kᵒ`.

The source sentence on correspondence and the sentence on polar norms are split into two atomic
declarations.
-/

namespace IsGaugeNorm

-- Proof sketch: the source correspondence is carried canonically by `gaugeUnitSublevel k`.
-- For `→`, the norm-gauge axioms give a finite convex gauge, hence a closed bounded convex unit
-- sublevel set; symmetry makes that set balanced, and strict positivity away from `0` forces the
-- origin into its interior. For `←`, the ambient gauge hypothesis is essential: the right-hand
-- side only constrains the unit sublevel set, so one must recover `k` from that set through the
-- owner bridge `IsGauge.eq_egauge_unitSublevel` before applying the norm/unit-ball criterion.
/-- Theorem 15.2 (1): on a finite-dimensional real normed space, a gauge `k` is a norm exactly
when its canonical unit sublevel set `gaugeUnitSublevel k = {x | k x ≤ 1}` is a balanced closed
bounded convex set whose interior contains `0`. This keeps the full convex-body content of the
source norm/unit-ball
correspondence instead of only its symmetry and interior-origin consequences. Specializing to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `R^n` statement. -/
theorem iff_unitSublevel_isClosed_convex_isBounded_balanced_zero_mem_interior
    (k : E → EReal) [IsGauge k] :
    IsGaugeNorm k ↔
      IsClosed (gaugeUnitSublevel k) ∧
      Convex ℝ (gaugeUnitSublevel k) ∧
      Bornology.IsBounded (gaugeUnitSublevel k) ∧
      Balanced ℝ (gaugeUnitSublevel k) ∧
      (0 : E) ∈ interior (gaugeUnitSublevel k) := sorry

-- Proof sketch: apply Theorem 15.1 to identify `gauge_polar k` with the gauge of the polar of
-- the unit sublevel set of `k`. Clause (1) shows that this unit sublevel set is a balanced closed
-- bounded convex body with interior containing `0`, and the set-polar results from Chapter 14
-- preserve these properties. Applying clause (1) again to the polar body yields that `kᵒ` is a
-- norm-gauge.

end IsGaugeNorm

section

variable [InnerProductSpace ℝ E]

namespace IsGaugeNorm

/-- Theorem 15.2 (2): on a finite-dimensional real inner-product space, the polar of a norm-gauge
`k` is again a norm-gauge. -/
theorem polar (k : E → EReal) [IsGaugeNorm k] :
    IsGaugeNorm kᵒ := sorry

end IsGaugeNorm

end

end

import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_14

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Rockafellar

variable {α : Type u} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [DenselyOrdered α]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜]
    [ClosedIciTopology 𝕜] [Zero 𝕜]

/-!
Source/core/bridge triage:

- `source-facing`: Text 7.0.13 is the half-line specialization of Rockafellar's statement that the
  lower-semicontinuous hull of an open-set indicator fills in the boundary.
- `core/canonical`: the owner abstraction in this chapter is
  `lowerSemicontinuousHull_indicator_eq_indicator_closure`.
- `bridge/view`: the only extra step here is the order-topology identity
  `closure (Set.Ioi a) = Set.Ici a` from local nonemptiness of `Set.Ioi a`.

Domain-style sampling used here:
- `lowerSemicontinuousHull_indicator_eq_indicator_closure`;
- `closure_Ioi'`;
- the indicator owner `δ[𝕜](· | C)`.

Layer target: this file first records the canonical `a`-level half-line owner and then recovers
the textbook `0`-specialization as a direct instance.
-/

/-- Canonical half-line owner: for any `a`, the lower-semicontinuous hull of the indicator of
`(a, ∞)` is the indicator of `[a, ∞)`. -/
theorem lowerSemicontinuousHull_indicator_Ioi_eq_indicator_Ici (a : α)
    (ha : (Set.Ioi a).Nonempty) :
    cl((δ[𝕜](· | Set.Ioi a))) = (δ[𝕜](· | Set.Ici a)) := by
  simpa [closure_Ioi' (a := a) ha] using
    lowerSemicontinuousHull_indicator_eq_indicator_closure (Set.Ioi a)

-- Proof sketch: instantiate the canonical `a`-level theorem at `a = 0`.
/-- Text 7.0.13: the lower-semicontinuous hull of the indicator of `(0, ∞)` is the indicator of
`[0, ∞)`. -/
theorem lowerSemicontinuousHull_zero_on_pos_top_on_nonpos
    [Zero α] (h0 : (Set.Ioi (0 : α)).Nonempty)
    :
    cl((δ[𝕜](· | Set.Ioi (0 : α)))) = (δ[𝕜](· | Set.Ici (0 : α))) := by
  simpa using
    lowerSemicontinuousHull_indicator_Ioi_eq_indicator_Ici (a := (0 : α)) h0

end

import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: Definition 10.0.1 names continuity relative to a subset.
- `core/canonical`: the owner is `ContinuousOn`.
- `bridge/view`: the intrinsic bridge is continuity of the restriction to the subtype,
  using `continuousOn_iff_continuous_restrict` and `continuous_iff_continuousAt`.

Abstraction checks:
- codomain/ambient/scalar layers are already fully generic;
- no concrete model owner is introduced;
- for pointwise statements, prefer the intrinsic subtype view over ambient phrasing.
-/
/- Definition 10.0.1: A function is continuous relative to a subset precisely in the canonical
mathlib sense of being `ContinuousOn` on that subset. -/
recall ContinuousOn

/- Intrinsic pointwise continuity of the restriction is the canonical companion view. -/
recall continuous_iff_continuousAt

section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Companion bridge for Definition 10.0.1: relative continuity on `S` is equivalent to
pointwise continuity of the restriction on the subtype `S`. -/
theorem continuousOn_iff_forall_continuousAt_restrict
    {f : X → Y} {S : Set X} :
    ContinuousOn f S ↔ ∀ x : S, ContinuousAt (S.restrict f) x := by
  rw [continuousOn_iff_continuous_restrict, continuous_iff_continuousAt]

end

/- Subtype-restriction continuity is the canonical bridge view of relative continuity. -/
recall continuousOn_iff_continuous_restrict

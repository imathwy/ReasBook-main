import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Set
open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.3.2 is Helly's theorem for an arbitrary family of closed convex
  sets, assuming that every subfamily with at most `Module.finrank ℝ E + 1` members intersects and
  that the family has no common nonzero recession direction.
- `core/canonical`: the owner abstraction is the Chapter 21 source-facing inequality corollary
  `exists_point_of_small_subsystems_strictly_feasible`, together with the project bridge theorems
  `indicatorFunction_isClosedProperConvex_of_nonempty` and
  `functionRecessionCone_indicatorFunction_eq_recessionCone`.
- `bridge/view`: the source family of sets is passed to the Chapter 21 owner theorem through the
  canonical indicator family `fun i ↦ δ(· | C i)`. The common-recession hypothesis is
  transferred through the canonical bridge
  `functionRecessionCone_indicatorFunction_eq_recessionCone`, while closed/proper/convexity of the
  indicator family comes from `indicatorFunction_isClosedProperConvex_of_nonempty`.

Domain-style sampling used here:
- `exists_point_of_small_subsystems_strictly_feasible`;
- `indicatorFunction_isClosedProperConvex_of_nonempty`;
- `functionRecessionCone_indicatorFunction_eq_recessionCone`;
- `indicatorFunction` with source-facing notation `δ(· | ·)`.

Primitive data vs derived API:
- primitive inputs: the family `C`, closedness and convexity of each member, the triviality of the
  common recession cone, and nonemptiness of every finite subintersection of size at most
  `Module.finrank ℝ E + 1`;
- derived output: nonemptiness of the total intersection.

Layer target: `source-facing`, stated directly for the family of sets as a thin bridge to the
Chapter 21 owner theorem rather than via a parallel local recession-direction package or a
duplicate local Helly alternative.
-/

-- Proof sketch: apply `exists_point_of_small_subsystems_strictly_feasible` to the indicator family
-- `fun i ↦ δ(· | C i)` on ambient set `univ`. For a closed convex set, the
-- indicator is a closed proper convex function by
-- `indicatorFunction_isClosedProperConvex_of_nonempty`, its function recession cone is
-- `0⁺[ℝ] (C i)`
-- by `functionRecessionCone_indicatorFunction_eq_recessionCone`, and strict feasibility of a
-- finite subsystem at any level `ε > 0` is exactly nonemptiness of the corresponding finite
-- intersection. The resulting joint nonpositive point is therefore a point of `⋂ i, C i`.

/-- Corollary 21.3.2 (Helly's Theorem): let `(C i)_{i ∈ I}` be a family of closed convex sets in a
finite-dimensional real normed space. If the common recession cone `⋂ i, 0⁺[ℝ] (C i)` is trivial and
every subcollection of at most `Module.finrank ℝ E + 1` sets has nonempty intersection, then the
whole family has nonempty intersection. Specializing to `E = EuclideanSpace ℝ (Fin n)` recovers
the textbook `R^n` bound `n + 1`. -/
theorem helly_theorem_of_trivial_common_recessionCone
    (C : I → Set E) (hC_closed : ∀ i : I, IsClosed (C i)) (hC_convex : ∀ i : I, Convex ℝ (C i))
    (h_common_recession : (⋂ i, 0⁺[ℝ] (C i)) = ({0} : Set E))
    (h_small_intersection :
      ∀ J : Finset I, J.card ≤ Module.finrank ℝ E + 1 → (⋂ i ∈ (J : Set I), C i).Nonempty) :
    (⋂ i, C i).Nonempty := sorry

end

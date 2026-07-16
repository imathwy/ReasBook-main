import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.3 says that norm powers `x ↦ ‖x‖ ^ p` are convex for `p ≥ 1`.
- `core/canonical`: the natural owner layer is the real-valued convex-function predicate
  `ConvexOn ℝ s f`; the primitive theorem here is `ConvexOn.norm_rpow`, while
  `convexOn_norm` is the bridge that supplies the norm branch from set convexity.
- `bridge/view`: this file keeps the abstract real normed-space form; concrete coordinate
  specializations are downstream views. The case `p = 1` is norm convexity, and `p > 1` is the
  strict-exponent corollary of `ConvexOn.rpow` from Text 5.1.2.

Domain-style sampling used here:
- `convexOn_norm`;
- `ConvexOn.rpow`;
- `ConvexOn.norm_rpow` (introduced here as the owner-level API).
-/

namespace ConvexOn

-- Proof sketch: apply Text 5.1.2 (`ConvexOn.rpow`) to the norm branch; the nonnegativity side
-- condition is immediate from `norm_nonneg`.
/-- Canonical owner form behind Text 5.1.3: if the norm map is convex on `s`, then every real
power `x ↦ ‖x‖ ^ p` with `p ≥ 1` is convex on `s`. -/
theorem norm_rpow {s : Set E} (hnorm : ConvexOn ℝ s (fun x : E ↦ ‖x‖)) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ ‖x‖ ^ p) := by
  refine hnorm.rpow ?_ hp
  intro x _
  exact norm_nonneg x

end ConvexOn

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: feed `convexOn_norm hs` into the canonical owner theorem
-- `ConvexOn.norm_rpow`.
/-- Text 5.1.3: on every convex set, `x ↦ ‖x‖ ^ p` is convex for every exponent `p ≥ 1`. -/
theorem convexOn_norm_rpow {s : Set E} (hs : Convex ℝ s) {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ s (fun x ↦ ‖x‖ ^ p) :=
  (convexOn_norm hs).norm_rpow hp

-- Proof sketch: specialize `convexOn_norm_rpow` to `Set.univ`.
/-- Text 5.1.3: for every exponent `p ≥ 1`, the map `x ↦ ‖x‖ ^ p` is convex on the whole space. -/
theorem convexOn_univ_norm_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p) := by
  simpa using (convexOn_norm_rpow (s := Set.univ) convex_univ hp :
    ConvexOn ℝ Set.univ (fun x : E ↦ ‖x‖ ^ p))

end

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section Core

variable {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

open LinearMap

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 6.2 says that on `ℝ^n` the Euclidean metric `d(x, y)` is a convex
  function of the pair `(x, y)`, hence a convex function on `ℝ^(2n) = ℝ^n × ℝ^n`.
- `core/canonical`: the primitive owner-side bridge is composition with the linear difference map
  `(x, y) ↦ x - y` for an arbitrary owner theorem `hf : ConvexOn 𝕜 s f`; norm and distance are
  source-facing specializations.
- `bridge/view`: the pair-distance function is the norm composed with the linear difference map
  `(x, y) ↦ x - y`, expressed in Lean by `fst 𝕜 E E - snd 𝕜 E E`; this matches the source wording
  through `dist_eq_norm`.
- Primitive data vs derived API: the primitive owner bridge is convexity on `E` plus linear
  composition along subtraction on `E × E`; pairwise distance is derived by specializing to
  `f := norm`.
- Ambient minimization: the primitive bridge uses only additive/module assumptions on `E` and an
  ordered additive codomain `β` acted on by `𝕜`. Seminormed assumptions appear only in the
  distance specialization.
- Layer target: `bridge/view`, stated directly in canonical `ConvexOn` language.

Domain-style sampling used here:
- `convexOn_univ_norm`;
- `convexOn_dist`;
- `convexOn_univ_dist`;
- `ConvexOn.comp_linearMap`.
-/

/- The primitive bridge is the canonical owner API `ConvexOn.comp_linearMap`. -/
recall ConvexOn.comp_linearMap

-- Proof sketch: apply `ConvexOn.comp_linearMap` with the linear map `(x, y) ↦ x - y`.
/-- Primitive bridge for Text 6.2: composing a convex function with the pair-difference map
`(x, y) ↦ x - y` preserves convexity on the pulled-back domain. -/
theorem ConvexOn.comp_sub {s : Set E} {f : E → β} (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 ((fun p : E × E ↦ p.1 - p.2) ⁻¹' s) (fun p : E × E ↦ f (p.1 - p.2)) := by
  simpa using hf.comp_linearMap (fst 𝕜 E E - snd 𝕜 E E)

end Core

section Dist

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace ConvexOn

-- Proof sketch: specialize `ConvexOn.comp_sub` to `f := norm`, then rewrite by `dist_eq_norm`.
/-- Owner-level distance bridge for Text 6.2: on any convex set `s`, the pair-distance map is
convex on the pullback set under `(x, y) ↦ x - y`. -/
theorem comp_sub_dist {s : Set E} (hs : Convex ℝ s) :
    ConvexOn ℝ ((fun p : E × E ↦ p.1 - p.2) ⁻¹' s) (fun p : E × E ↦ dist p.1 p.2) := by
  simpa [dist_eq_norm] using (convexOn_norm (s := s) hs).comp_sub

end ConvexOn

/-- Text 6.2 at the source-facing distance surface: the pair-distance map on `E × E` is convex on
all of `E × E`.

The source states this for `ℝ^n`; the theorem is kept at the canonical owner layer
`[NormedSpace ℝ E]`. -/
theorem convexOn_univ_pairDist :
    ConvexOn ℝ Set.univ (fun p : E × E ↦ dist p.1 p.2) := by
  simpa [Set.preimage_univ] using
    (ConvexOn.comp_sub_dist (E := E) (s := Set.univ) convex_univ)

end Dist

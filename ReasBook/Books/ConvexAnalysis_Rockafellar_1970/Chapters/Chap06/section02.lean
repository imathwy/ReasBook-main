import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_2 (from Chap02) -/
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

/-! ### Theorem_6_2 (from Chap02) -/
section

open Set Topology
open scoped Rockafellar

variable {𝕜 E : Type*} [Field 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.2 says that the relative interior of a convex set is convex.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, `intrinsicInterior 𝕜`, and the
  interior-convexity bridge `convex_iff_segment_subset` +
  `Convex.combo_interior_self_mem_interior`.
- `bridge/view`: Rockafellar's chapter notation `ri[𝕜](C)` is represented canonically by
  `intrinsicInterior 𝕜 C`.
- Domain-style sampling used here: `intrinsicInterior`, `convex_iff_segment_subset`,
  `Convex.combo_interior_self_mem_interior`, `Convex.affine_preimage`,
  and `Convex.affine_image`.
- Best owner abstraction: convexity of relative interior belongs directly on the `Convex`
  owner abstraction, with `intrinsicInterior` as the canonical relative-interior operator.
- Primitive data vs derived API: the only primitive datum is `hC : Convex 𝕜 C`; convexity of
  `intrinsicInterior 𝕜 C` is derived owner API and should not be routed through the stronger
  finite-dimensional theorem `Theorem_6_1`.
- Layer target: this item stays `source-facing`, but its public statement is refined to the
  weakest owner-style topological-module assumptions supported by the canonical proof.
- Ambient-space refinement: the textbook finite-dimensional coordinate model is presentation only
  here. After passing to
  the affine span and translating by a chosen point, interior convexity is proved at the weaker
  scalar layer by a segment criterion + interior-combo owner bridge.
-/

namespace Convex

/-- Internal bridge: convexity of ordinary interior at the ordered-field layer.
Kept private so the public owner surface remains `Convex.intrinsicInterior`. -/
private theorem interior_of_field {s : Set E} (hs : Convex 𝕜 s) :
    Convex 𝕜 (interior s) := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by simpa [ha0] using hab
    simpa [ha0, hb1] using hy
  · have ha_ne : a ≠ 0 := by simpa using ha0
    have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha_ne)
    exact hs.combo_interior_self_mem_interior hx (interior_subset hy) ha_pos hb hab

/-- Theorem 6.2: the relative interior of a convex set is convex. The source presents this in a
finite-dimensional coordinate model; the canonical owner theorem only needs the weaker
topological-module assumptions below. -/
-- Proof sketch: view `intrinsicInterior 𝕜 C` as the image of the ordinary interior of the section
-- of `C` inside its affine span. After choosing one point of that affine span, translate to the
-- direction space via `AffineEquiv.vaddConst`; there interior convexity is obtained from
-- `convex_iff_segment_subset` and `Convex.combo_interior_self_mem_interior`. Transport the
-- resulting convex interior back through the affine equivalence and then through the
-- affine-span subtype map.
theorem intrinsicInterior {C : Set E} (hC : Convex 𝕜 C) :
    Convex 𝕜 (ri[𝕜](C)) := by
  obtain rfl | ⟨x, hx⟩ := C.eq_empty_or_nonempty
  · simpa using (convex_empty : Convex 𝕜 (∅ : Set E))
  let S := affineSpan 𝕜 C
  let p : S := ⟨x, subset_affineSpan 𝕜 C hx⟩
  letI : Nonempty S := ⟨p⟩
  letI : ContinuousConstSMul 𝕜 S.direction :=
    { continuous_const_smul := fun c ↦ by
        rw [IsEmbedding.subtypeVal.continuous_iff]
        simpa using (continuous_subtype_val.const_smul c) }
  let e : S.direction ≃ᵃ[𝕜] S := AffineEquiv.vaddConst 𝕜 p
  let A : S.direction →ᵃ[𝕜] E := S.subtype.comp e.toAffineMap
  let s : Set S := ((↑) : S → E) ⁻¹' C
  let t : Set S.direction := e ⁻¹' s
  have ht : Convex 𝕜 t := by
    simpa [A, s, t, e] using hC.affine_preimage A
  have hts : e '' t = s := by
    change e '' (e ⁻¹' s) = s
    exact image_preimage_eq_of_subset fun u hu ↦ ⟨e.symm u, by simp⟩
  have hinter : e '' interior t = interior s := by
    let h : S.direction ≃ₜ S := Homeomorph.vaddConst p
    calc
      e '' interior t = h '' interior t := by rfl
      _ = interior (h '' t) := by simpa using h.image_interior t
      _ = interior s := by
        rw [show h '' t = s by simpa [h] using hts]
  have hA : A '' interior t = ri[𝕜](C) := by
    calc
      A '' interior t = ((↑) '' (e '' interior t)) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨e y, ⟨y, hy, rfl⟩, rfl⟩
        · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, rfl⟩
      _ = ri[𝕜](C) := by
        rw [hinter, _root_.intrinsicInterior]
  rw [← hA]
  exact Convex.affine_image A ht.interior_of_field

end Convex

end

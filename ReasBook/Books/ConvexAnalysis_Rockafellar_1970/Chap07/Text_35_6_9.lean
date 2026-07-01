import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_1
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_5
import ConvexAnalysis_Rockafellar_1970.Chap07.Text_35_5_2

noncomputable section

universe u v

open Set
open SaddleFunction
open scoped Rockafellar

namespace Bifunction

section FirstPartial

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable {K : U → V → WithTopBot ℝ} {u : U} {v : V}

/-!
Source/core/bridge triage:

- `source-facing`: Text 35.6.9 states that at an interior point of the effective domain of a
  saddle-function, the two partial subdifferentials are nonempty, closed, bounded, and convex.
- `core/canonical`: the chapter owner declarations are `Bifunction.subdifferential1At`,
  `Bifunction.subdifferential2At`, the Chapter 34 domain owner `dom K`, and the slice-domain
  interior bridges from `Text_35_6_8`.
- `bridge/view`: this section states the first-partial conclusions directly on the intrinsic
  first-partial owner with the canonical strong-dual notation `∂₁ K(u, v)`.

Domain-style sampling used here:
- `Bifunction.subdifferential1At` from `Text_35_5_1`;
- `SaddleFunction.mem_interior_dom_firstSlice_of_mem_interior_dom₂` and
  `SaddleFunction.mem_interior_dom_secondSlice_of_mem_interior_dom₂` from
  `Text_35_6_8`;
- `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` and the finite convex
  subdifferential regularity statements of `Corollary_23_4_1`, which are the one-variable owners
  behind the two partial conclusions.

Primitive data vs derived API:

- primitive owner data: first-slice concavity of `fun u' ↦ K u' v` and coordinate-domain
  memberships `u ∈ dom₁ K`, `v ∈ dom₂ K`;
- derived API: the first-partial regularity properties at `(u, v)`.
- source-facing bridge: the same conclusion under the textbook hypothesis
  `(u, v) ∈ interior (dom K)`, obtained by reducing to the coordinate-domain owner layer.

Layer target: `source-facing`.

Scalar/codomain boundary:
- this item remains on the real branch because the upstream finite-dimensional nonempty/bounded
  owner route reused here is currently available on `StrongDual ℝ` / `WithTopBot ℝ`; scalar
  weakening of this boundedness layer should be repaired upstream first.

Redundant-source-assumption elimination:

- the primitive owner theorem below does not keep the stronger interior-domain product hypothesis,
  because the first-partial nonempty/bounded clause only needs first-slice concavity and the
  coordinate-domain owners `u ∈ dom₁ K`, `v ∈ dom₂ K`;
- the textbook adjective “proper” is omitted from both owner and bridge theorem surfaces.
-/

-- Proof sketch: `v ∈ dom₂ K` gives the no-`⊤` side on the first slice, while `u ∈ dom₁ K`
-- gives a finite-point witness for that slice; together these supply properness of the convex
-- negated first slice. Then apply Theorem 23.4 and translate through the sign-change bridge to
-- `∂₁ K(u,v)`.
/-- Text 35.6.9 (1), owner form: if the first-variable slice `fun u' ↦ K u' v` is concave on the
whole space and `(u, v)` lies in the coordinate-domain owner layer
`u ∈ dom₁ K`, `v ∈ dom₂ K`, then the first partial subdifferential is nonempty and bounded. -/
theorem subdifferential1At_nonempty_and_bounded_of_isConcave_firstSlice_of_mem_dom₂
    (hK_concave : ConcaveOn ℝ Set.univ (fun u' ↦ K u' v))
    (hu : u ∈ dom₁ K)
    (hv : v ∈ dom₂ K) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := sorry

variable [AddCommMonoid V] [SMul ℝ V]

/-- Concave-convex bridge for Text 35.6.9 (1) on the coordinate-domain owner
`u ∈ dom₁ K`, `v ∈ dom₂ K`. -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ dom₂ K) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := by
  rcases (SaddleFunction.isConcaveConvex_iff (𝕜 := ℝ) K).1 hK_shape with ⟨hConcave, _⟩
  exact subdifferential1At_nonempty_and_bounded_of_isConcave_firstSlice_of_mem_dom₂
    (hK_concave := hConcave v) hu hv

variable [TopologicalSpace V]

/-- Source-facing interior-`dom₂` bridge for Text 35.6.9 (1). -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) :=
  subdifferential1At_nonempty_and_bounded_of_mem_dom₂
    (hK_shape := hK_shape) hu (interior_subset hv)

-- Proof sketch: project `(u, v) ∈ interior (dom K)` to `v ∈ interior (dom₂ K)` using
-- `SaddleFunction.mem_interior_dom`, then apply the interior-`dom₂` bridge above.
/-- Text 35.6.9 (1), source-facing bridge: at an interior point of `dom K` of a concave-convex
saddle-function, the first partial subdifferential is nonempty and bounded. -/
theorem subdifferential1At_nonempty_and_bounded_of_mem_interior_dom
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (huv : (u, v) ∈ interior (dom K)) :
    (∂₁ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₁ K(u, v)) := by
  have hmem : u ∈ interior (SaddleFunction.dom₁ K) :=
    (SaddleFunction.mem_interior_dom.mp huv).1
  have hu : u ∈ dom₁ K := interior_subset hmem
  exact subdifferential1At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape := hK_shape) hu ((SaddleFunction.mem_interior_dom.mp huv).2)

end FirstPartial

/- Text 35.6.9 (2): the first partial subdifferential clause is a direct owner recall.
For every slice `fun u' ↦ K u' v`, the intrinsic owner
`_root_.concaveSubdifferentialAt (fun u' ↦ K u' v) u` is already closed and convex upstream, and
`∂₁ K(u, v)` is definitionally that owner. -/
recall _root_.concaveSubdifferentialAt_isClosed
recall _root_.concaveSubdifferentialAt_convex

section SecondPartial

variable {U : Type u} {V : Type v}
variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable {K : U → V → WithTopBot ℝ} {u : U} {v : V}

-- Proof sketch: from `u ∈ dom₁ K`, the second slice `K u` is nowhere `⊥`. Together with
-- `v ∈ interior (dom₂ K)`, we get `v ∈ dom₂ K`, hence `K u v < ⊤` and therefore a finite point of
-- `K u`; this yields properness of the slice. Then place `v` in the interior of `dom(K u)` and
-- apply Theorem 23.4 to the convex proper second slice `K u`.
/-- Text 35.6.9 (3), owner form: if the second-variable slice `K u` is convex on the whole space
and `(u, v)` lies in the coordinate-domain owner layer
`u ∈ dom₁ K`, `v ∈ interior (dom₂ K)`, then the second partial subdifferential is nonempty and
bounded. -/
theorem subdifferential2At_nonempty_and_bounded_of_isConvex_secondSlice_of_mem_interior_dom₂
    (hKu_convex : ConvexOn ℝ Set.univ (K u))
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := sorry

variable [AddCommMonoid U] [SMul ℝ U]

/-- Concave-convex bridge for Text 35.6.9 (3) on the coordinate-domain owner
`u ∈ dom₁ K`, `v ∈ interior (dom₂ K)`. -/
theorem subdifferential2At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (hu : u ∈ dom₁ K)
    (hv : v ∈ interior (dom₂ K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := by
  rcases (SaddleFunction.isConcaveConvex_iff (𝕜 := ℝ) K).1 hK_shape with ⟨_, hConvex⟩
  exact subdifferential2At_nonempty_and_bounded_of_isConvex_secondSlice_of_mem_interior_dom₂
    (hKu_convex := hConvex u) hu hv

variable [TopologicalSpace U]

-- Proof sketch: project `(u, v) ∈ interior (dom K)` to `v ∈ interior (dom₂ K)` using
-- `SaddleFunction.mem_interior_dom`, then apply the interior-`dom₂` bridge above.
/-- Text 35.6.9 (3), source-facing bridge: at an interior point of `dom K` of a concave-convex
saddle-function, the second partial subdifferential is nonempty and bounded. -/
theorem subdifferential2At_nonempty_and_bounded_of_mem_interior_dom
    (hK_shape : SaddleFunction.IsConcaveConvex ℝ K)
    (huv : (u, v) ∈ interior (dom K)) :
    (∂₂ K(u, v)).Nonempty ∧
      Bornology.IsBounded (∂₂ K(u, v)) := by
  have hmem : u ∈ interior (SaddleFunction.dom₁ K) :=
    (SaddleFunction.mem_interior_dom.mp huv).1
  have hu : u ∈ dom₁ K := interior_subset hmem
  exact subdifferential2At_nonempty_and_bounded_of_mem_interior_dom₂
    (hK_shape := hK_shape) hu ((SaddleFunction.mem_interior_dom.mp huv).2)

end SecondPartial

end Bifunction

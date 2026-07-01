import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_7
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-- Rockafellar's scalar-annotated notation for relative interior. -/
scoped[Rockafellar] notation "ri[" 𝕜 "](" C ")" => intrinsicInterior 𝕜 C

section

open scoped Rockafellar

variable
    {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {P : Type*} [TopologicalSpace P] [AddTorsor V P]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.8 defines the relative interior of a convex subset as the
  interior taken inside its affine hull, and then rewrites this as a positive-radius closed-ball
  condition inside that affine hull.
- `core/canonical`: mathlib's owner notion for relative interior is `intrinsicInterior`.
- `bridge/view`: the companion theorem below rewrites membership in the canonical owner notion,
  written on the theorem surface as `ri[𝕜](C)`, in the textbook's closed-ball language.
- Primitive data vs derived API: no new data is introduced here; the convexity adjective is
  redundant for the definition itself, so the public API is stated for arbitrary subsets.
- Domain-style sampling used here: `intrinsicInterior`, `mem_intrinsicInterior`,
  `Metric.mem_interior_iff_exists_pos_closedBall_subset`, and `affineSpan`.
- Layer target: the main labeled entry is `core/canonical`, while the closed-ball theorem below is
  a `bridge/view` characterization.
- Ambient-space refinement: the core theorem only uses `intrinsicInterior 𝕜`, `affineSpan 𝕜`, and
  `interior`, so it lives at the intrinsic topological affine layer; only the closed-ball bridge
  requires a pseudometric structure.
- Source-facing owner notation: the reusable chapter notation is `ri[𝕜](C)`.
-/

/- Text 6.8: the relative interior of a convex set is mathlib's canonical
`intrinsicInterior`, written on the chapter theorem surface as `ri[𝕜](C)`. It is the interior of
the set when it is regarded as a subset of its affine hull. The present statement is given in the
equivalent coordinate-free ambient setting of a topological affine space. -/
recall intrinsicInterior

/-- Core intrinsic-topology form of Text 6.8: for a point of the affine hull, membership in
`ri[𝕜](C)` is equivalent to belonging to the ordinary interior of `C` in that affine-hull
subtype. This is the primary owner-level statement; ambient-coordinate forms are bridges. -/
theorem mem_ri_iff_mem_interior_affineSpan_preimage
    {C : Set P} {x : affineSpan 𝕜 C} :
    (x : P) ∈ ri[𝕜](C) ↔ x ∈ interior ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
  rw [mem_intrinsicInterior]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end

section

open Metric
open scoped Rockafellar

variable
    {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {P : Type*} [PseudoMetricSpace P] [AddTorsor V P]

/-- Canonical relative-topology bridge for Text 6.8: for a point in the affine hull, membership in
`ri[𝕜](C)` is equivalent to containing a positive-radius closed ball in the affine-hull subtype.
This keeps the statement on the intrinsic affine-hull space rather than ambient intersections. -/
theorem mem_ri_iff_exists_pos_closedBall_subset
    {C : Set P} {x : affineSpan 𝕜 C} :
    (x : P) ∈ ri[𝕜](C) ↔
      ∃ ε > 0, closedBall x ε ⊆ ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
  simpa [mem_ri_iff_mem_interior_affineSpan_preimage] using
    (Metric.mem_interior_iff_exists_pos_closedBall_subset
      (C := ((↑) ⁻¹' C : Set (affineSpan 𝕜 C))) (x := x))

/-- Primitive ambient-point bridge for Text 6.8: for a point already known to lie in the affine
hull, membership in `ri[𝕜](C)` is equivalent to containing a positive closed ball in the affine
hull, expressed in ambient coordinates. -/
theorem mem_ri_iff_exists_pos_closedBall_inter_subset
    {C : Set P} {x : P} (hx : x ∈ affineSpan 𝕜 C) :
    x ∈ ri[𝕜](C) ↔
      ∃ ε > 0, closedBall x ε ∩ affineSpan 𝕜 C ⊆ C := by
  constructor
  · intro hxri
    have hxri' : ((⟨x, hx⟩ : affineSpan 𝕜 C) : P) ∈ ri[𝕜](C) := by
      simpa using hxri
    rcases (mem_ri_iff_exists_pos_closedBall_subset (C := C) (x := ⟨x, hx⟩)).1 hxri' with
      ⟨ε, hε, hεC⟩
    refine ⟨ε, hε, ?_⟩
    intro z hz
    have hz' : (⟨z, hz.2⟩ : affineSpan 𝕜 C) ∈ closedBall (⟨x, hx⟩ : affineSpan 𝕜 C) ε := by
      simpa [Subtype.dist_eq] using hz.1
    exact hεC hz'
  · rintro ⟨ε, hε, hball⟩
    have hball' :
        closedBall (⟨x, hx⟩ : affineSpan 𝕜 C) ε ⊆ ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) := by
      intro y hy
      exact hball <| by
        refine ⟨?_, y.property⟩
        simpa [Subtype.dist_eq] using hy
    have hxInterior :
        (⟨x, hx⟩ : affineSpan 𝕜 C) ∈ interior ((↑) ⁻¹' C : Set (affineSpan 𝕜 C)) :=
      (Metric.mem_interior_iff_exists_pos_closedBall_subset).2 ⟨ε, hε, hball'⟩
    have hxri :
        ((⟨x, hx⟩ : affineSpan 𝕜 C) : P) ∈ ri[𝕜](C) :=
      (mem_ri_iff_mem_interior_affineSpan_preimage (C := C) (x := ⟨x, hx⟩)).2 hxInterior
    simpa using hxri

/-- Packaged ambient-point form of Text 6.8: membership in `ri[𝕜](C)` is equivalent to lying in
the affine hull and containing a positive closed ball in that affine hull. -/
theorem mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset
    {C : Set P} {x : P} :
    x ∈ ri[𝕜](C) ↔
      x ∈ affineSpan 𝕜 C ∧
        ∃ ε > 0, closedBall x ε ∩ affineSpan 𝕜 C ⊆ C := by
  constructor
  · intro hxri
    have hx : x ∈ affineSpan 𝕜 C := subset_affineSpan 𝕜 C (intrinsicInterior_subset hxri)
    exact ⟨hx, (mem_ri_iff_exists_pos_closedBall_inter_subset (C := C) (x := x) hx).1 hxri⟩
  · rintro ⟨hx, hball⟩
    exact (mem_ri_iff_exists_pos_closedBall_inter_subset (C := C) (x := x) hx).2 hball

end

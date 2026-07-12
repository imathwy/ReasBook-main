import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_11
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_17
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open AffineMap
open scoped Convex Rockafellar

section Interval

variable {𝕜 : Type*} [Ring 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [DenselyOrdered 𝕜] [IsStrictOrderedRing 𝕜]

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] in
private theorem affineSpan_Icc_zero_one_eq_top :
    affineSpan 𝕜 (Set.Icc (0 : 𝕜) 1) = ⊤ := by
  refine top_unique ?_
  intro t _
  have h0 : (0 : 𝕜) ∈ affineSpan 𝕜 (Set.Icc (0 : 𝕜) 1) :=
    subset_affineSpan 𝕜 (Set.Icc (0 : 𝕜) 1) (by simp)
  have h1 : (1 : 𝕜) ∈ affineSpan 𝕜 (Set.Icc (0 : 𝕜) 1) :=
    subset_affineSpan 𝕜 (Set.Icc (0 : 𝕜) 1) (by simp)
  have ht : lineMap (0 : 𝕜) 1 t = t := by
    simp [lineMap_apply_ring]
  rw [← ht]
  exact lineMap_mem t h0 h1

private theorem intrinsicInterior_Icc_zero_one :
    ri[𝕜](Set.Icc (0 : 𝕜) 1) = Set.Ioo (0 : 𝕜) 1 := by
  rw [intrinsicInterior_eq_interior_of_affineSpan_eq_top affineSpan_Icc_zero_one_eq_top,
    interior_Icc]

end Interval

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Canonical segment bridge: the intrinsic interior of a segment is the corresponding open
segment. -/
@[simp] theorem intrinsicInterior_segment_eq_openSegment (u v : E) :
    ri[𝕜]([u -[𝕜] v]) = openSegment 𝕜 u v := by
  let A : 𝕜 →ₗ[𝕜] E :=
    { toFun := fun t ↦ t • (v - u)
      map_add' := by
        intro a b
        simp [add_smul]
      map_smul' := by
        intro a b
        simp [mul_smul] }
  have hsegment :
      (AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Icc (0 : 𝕜) 1) = [u -[𝕜] v] := by
    calc
      (AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Icc (0 : 𝕜) 1) =
          lineMap u v '' Set.Icc (0 : 𝕜) 1 := by
        ext x
        constructor
        · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t, ht, by
            change lineMap u v t = u + t • (v - u)
            simp [lineMap_apply_module', add_comm]⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨A t, ⟨t, ht, rfl⟩, by
            change u + t • (v - u) = lineMap u v t
            simp [lineMap_apply_module', add_comm]⟩
      _ = [u -[𝕜] v] := (segment_eq_image_lineMap 𝕜 u v).symm
  have hopen :
      (AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Ioo (0 : 𝕜) 1) = openSegment 𝕜 u v := by
    calc
      (AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Ioo (0 : 𝕜) 1) =
          lineMap u v '' Set.Ioo (0 : 𝕜) 1 := by
        ext x
        constructor
        · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨t, ht, by
            change lineMap u v t = u + t • (v - u)
            simp [lineMap_apply_module', add_comm]⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨A t, ⟨t, ht, rfl⟩, by
            change u + t • (v - u) = lineMap u v t
            simp [lineMap_apply_module', add_comm]⟩
      _ = openSegment 𝕜 u v := (openSegment_eq_image_lineMap 𝕜 u v).symm
  have hriA : ri[𝕜](A '' Set.Icc (0 : 𝕜) 1) = A '' Set.Ioo (0 : 𝕜) 1 := by
    simpa [intrinsicInterior_Icc_zero_one] using
      (convex_Icc (0 : 𝕜) 1).intrinsicInterior_linear_image A
  calc
    ri[𝕜]([u -[𝕜] v]) =
        ri[𝕜]((AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Icc (0 : 𝕜) 1)) := by
      rw [hsegment.symm]
    _ =
        (AffineIsometryEquiv.constVAdd 𝕜 E u) '' ri[𝕜](A '' Set.Icc (0 : 𝕜) 1) := by
      simpa using
        AffineIsometry.image_intrinsicInterior
          ((AffineIsometryEquiv.constVAdd 𝕜 E u).toAffineIsometry) (A '' Set.Icc (0 : 𝕜) 1)
    _ =
        (AffineIsometryEquiv.constVAdd 𝕜 E u) '' (A '' Set.Ioo (0 : 𝕜) 1) := by
      rw [hriA]
    _ = openSegment 𝕜 u v := by
      exact hopen

/-!
Source/core/bridge triage:

- `source-facing`: Text 18.2.1 characterizes when two points of a set `C` lie together in some
  relatively open convex subset of `C`; the source phrases this for distinct points, but that
  hypothesis is formally redundant here.
- `core/canonical`: the owner notions are `Convex 𝕜 D`, the chapter-wide source-facing predicate
  `IsRelativelyOpen 𝕜 D`, and the canonical segment owners `[u -[𝕜] v]` and
  `openSegment 𝕜 u v`.
- `bridge/view`: Rockafellar's clause "both points lie in `ri(S)` for a line segment `S`" is
  kept on the standard segment owner, with `openSegment 𝕜 u v` as the established surface for the
  relative interior of that segment.

Domain-style sampling used here:
- `IsRelativelyOpen` from `Chap02.Text_6_11`;
- `intrinsicInterior_eq_interior_of_affineSpan_eq_top` from `Chap02.Text_6_12`;
- `isRelativelyOpen_ri` from `Chap02.Text_6_17`;
- `Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior` from `Chap02.Theorem_6_4`;
- `Convex.intrinsicInterior_linear_image` from `Chap02.Theorem_6_6`.

Best owner abstraction:
- the relatively-open-convex witness should be stated directly as primitive data
  `D ⊆ C ∧ Convex 𝕜 D ∧ IsRelativelyOpen 𝕜 D`, with direct point-membership hypotheses
  `{x, y} ⊆ D`, not via a local wrapper or by repeating the owner equality
  `intrinsicInterior 𝕜 D = D`;
- the segment witness should remain a plain segment owner `[u -[𝕜] v] ⊆ C`, with direct
  set-pair inclusion `{x, y} ⊆ ri[𝕜]([u -[𝕜] v])`; the `openSegment 𝕜 u v` form is a theorem-level
  bridge
  via `intrinsicInterior_segment_eq_openSegment`.

Primitive data vs derived API:
- primitive source-facing content: the equivalence between the relatively-open-convex witness
  `∃ D, D ⊆ C ∧ Convex 𝕜 D ∧ IsRelativelyOpen 𝕜 D ∧ ({x, y} ⊆ D)` and the segment
  witness `∃ u v, [u -[𝕜] v] ⊆ C ∧ ({x, y} ⊆ ri[𝕜]([u -[𝕜] v]))`;
- derived packaging to avoid: wrapper predicates for "admissible subsets/pairs". The source content
  is existential and is stated directly as such below.

Redundant-source-assumption elimination:
- the binder `x ≠ y` is redundant in the formalized statement, because mathlib has
  `ri[𝕜]([x -[𝕜] x]) = {x}`, so the degenerate segment already handles the coincident-point case
  canonically.

The source assumes `C` is convex, but that ambient hypothesis is redundant for this equivalence:
each clause already supplies the convex object that matters (`D` in (1), a segment in (2)), both
contained in `C`.

Ambient refinement: the declarations only use convexity, relative interior, and segment owners in a
linearly ordered normed field module. The concrete model `EuclideanSpace ℝ (Fin n)` is therefore
not part of the public content; specializing to `𝕜 = ℝ` and `E = R^n` recovers the textbook
presentation.
-/

/-- Text 18.2.1, owner-primary form: there is a relatively open convex subset of `C` containing
both `x` and `y` if and only if there is a segment contained in `C` whose relative interior
contains both points. The left-hand side uses the source-facing owner predicate
`IsRelativelyOpen 𝕜 D`, with symmetric pair-membership encoded intrinsically as
`({x, y} : Set E) ⊆ D`; the source's distinct-point clause is redundant because the degenerate
segment case is already handled canonically. -/
-- Proof sketch: for `(2) → (1)`, take `D` to be the relative interior of the chosen segment,
-- which is convex, relatively open in its affine span, and contained in `C`. For `(1) → (2)`,
-- start from a relatively open convex set `D ⊆ C` containing `x` and `y`; relative openness lets
-- one prolong the segment `[x,y]` slightly past both endpoints while staying inside `D`, yielding
-- a larger segment whose open segment contains both `x` and `y`, and hence whose relative
-- interior contains them by `intrinsicInterior_segment_eq_openSegment`.
theorem exists_relativelyOpenConvex_iff_exists_segment_points_mem_ri
    {C : Set E} {x y : E} :
    (∃ D, D ⊆ C ∧ Convex 𝕜 D ∧ IsRelativelyOpen 𝕜 D ∧ ({x, y} : Set E) ⊆ D) ↔
      ∃ u v, [u -[𝕜] v] ⊆ C ∧ ({x, y} : Set E) ⊆ ri[𝕜]([u -[𝕜] v]) := by
  constructor
  · rintro ⟨D, hDC, hD_convex, hD_open, hxyD⟩
    have hxD : x ∈ D := hxyD (by simp)
    have hyD : y ∈ D := hxyD (by simp)
    have hxri : x ∈ ri[𝕜](D) := by
      simpa [hD_open] using hxD
    have hyri : y ∈ ri[𝕜](D) := by
      simpa [hD_open] using hyD
    rcases Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hxri y hyD with
      ⟨μ, hμ, huD⟩
    rcases Convex.forall_exists_gt_one_lineMap_mem_of_mem_intrinsicInterior hyri x hxD with
      ⟨ν, hν, hvD⟩
    set u : E := lineMap y x μ
    set v : E := lineMap x y ν
    have huvC : [u -[𝕜] v] ⊆ C := by
      simpa [u, v] using (hD_convex.segment_subset huD hvD).trans hDC
    have hx_open : x ∈ openSegment 𝕜 u v := by
      let a : 𝕜 := (μ - 1) / (μ + ν - 1)
      have hd : 0 < μ + ν - 1 := by
        linarith
      have ha : a ∈ Set.Ioo (0 : 𝕜) 1 := by
        refine ⟨by
          have hμ' : 0 < μ - 1 := by
            linarith
          exact div_pos hμ' hd, by
          have hlt : μ - 1 < μ + ν - 1 := by
            linarith
          exact (div_lt_one hd).2 hlt⟩
      have ha0 : lineMap (1 - μ) ν a = (0 : 𝕜) := by
        rw [lineMap_apply_ring]
        dsimp [a]
        field_simp [hd.ne']
        ring
      rw [openSegment_eq_image_lineMap]
      refine ⟨a, ha, ?_⟩
      calc
        lineMap (lineMap y x μ) (lineMap x y ν) a =
            lineMap x y (lineMap (1 - μ) ν a) := by
          rw [← lineMap_apply_one_sub x y μ, ← (lineMap x y).apply_lineMap (1 - μ) ν a]
        _ = lineMap x y (0 : 𝕜) := by rw [ha0]
        _ = x := lineMap_apply_zero x y
    have hy_open : y ∈ openSegment 𝕜 u v := by
      let b : 𝕜 := μ / (μ + ν - 1)
      have hd : 0 < μ + ν - 1 := by
        linarith
      have hb : b ∈ Set.Ioo (0 : 𝕜) 1 := by
        refine ⟨by
          have hμ0 : 0 < μ := by
            linarith
          exact div_pos hμ0 hd, by
          have hlt : μ < μ + ν - 1 := by
            linarith
          exact (div_lt_one hd).2 hlt⟩
      have hb1 : lineMap (1 - μ) ν b = (1 : 𝕜) := by
        rw [lineMap_apply_ring]
        dsimp [b]
        field_simp [hd.ne']
        ring
      rw [openSegment_eq_image_lineMap]
      refine ⟨b, hb, ?_⟩
      calc
        lineMap (lineMap y x μ) (lineMap x y ν) b =
            lineMap x y (lineMap (1 - μ) ν b) := by
          rw [← lineMap_apply_one_sub x y μ, ← (lineMap x y).apply_lineMap (1 - μ) ν b]
        _ = lineMap x y (1 : 𝕜) := by rw [hb1]
        _ = y := lineMap_apply_one x y
    refine ⟨u, v, huvC, ?_⟩
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · simpa [intrinsicInterior_segment_eq_openSegment u v] using hx_open
    · simpa [intrinsicInterior_segment_eq_openSegment u v] using hy_open
  · rintro ⟨u, v, huvC, hxy⟩
    refine ⟨ri[𝕜]([u -[𝕜] v]), intrinsicInterior_subset.trans huvC,
      (convex_segment u v).intrinsicInterior, isRelativelyOpen_ri [u -[𝕜] v],
      hxy⟩

/-- Text 18.2.1, segment-view bridge: the owner-primary relative-interior statement rewrites to
the open-segment formulation via `intrinsicInterior_segment_eq_openSegment`. -/
theorem exists_relativelyOpenConvex_iff_exists_segment_points_mem_openSegment
    {C : Set E} {x y : E} :
    (∃ D, D ⊆ C ∧ Convex 𝕜 D ∧ IsRelativelyOpen 𝕜 D ∧ ({x, y} : Set E) ⊆ D) ↔
      ∃ u v, [u -[𝕜] v] ⊆ C ∧ ({x, y} : Set E) ⊆ openSegment 𝕜 u v := by
  simpa [intrinsicInterior_segment_eq_openSegment] using
    (exists_relativelyOpenConvex_iff_exists_segment_points_mem_ri (𝕜 := 𝕜)
      (C := C) (x := x) (y := y))

end

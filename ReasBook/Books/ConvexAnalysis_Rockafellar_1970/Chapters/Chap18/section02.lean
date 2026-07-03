import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_18_2_1 (from Chap04) -/
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

/-! ### Theorem_18_2 (from Chap04) -/
namespace Set.IsFace

section RiNonemptyFaceFamily

open scoped Rockafellar

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable (𝕜)

/-- Rockafellar's Chapter 18 family `𝒰`: relative interiors of the nonempty faces of `C`. -/
def riNonemptyFaces (C : Set E) : Set (Set E) :=
  (fun F : Set E ↦ ri[𝕜](F)) '' {F : Set E | F.IsFace 𝕜 C ∧ F.Nonempty}

@[simp] theorem mem_riNonemptyFaces_iff {C U : Set E} :
    U ∈ riNonemptyFaces 𝕜 C ↔
      ∃ F : Set E, F.IsFace 𝕜 C ∧ F.Nonempty ∧ U = ri[𝕜](F) := by
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, hF.1, hF.2, rfl⟩
  · rintro ⟨F, hF_face, hF_nonempty, rfl⟩
    exact ⟨F, ⟨hF_face, hF_nonempty⟩, rfl⟩

@[simp] theorem mem_riNonemptyFaces_iff_exists_mem_faces {C U : Set E} :
    U ∈ riNonemptyFaces 𝕜 C ↔
      ∃ F : Set E, F ∈ 𝓕[𝕜](C) ∧ F.Nonempty ∧ U = ri[𝕜](F) := by
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F, Set.IsFace.mem_faces_iff.mpr hF.1, hF.2, rfl⟩
  · rintro ⟨F, hF_faces, hF_nonempty, rfl⟩
    exact ⟨F, ⟨Set.IsFace.mem_faces_iff.mp hF_faces, hF_nonempty⟩, rfl⟩

end RiNonemptyFaceFamily

end Set.IsFace

/-- Rockafellar's Chapter 18 notation for the family of relative interiors of nonempty faces. -/
scoped[Rockafellar] notation "𝒰[" 𝕜 "](" C ")" =>
  Set.IsFace.riNonemptyFaces 𝕜 C

namespace Set

section RelativelyOpenConvexFamily

open scoped Rockafellar

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable (𝕜)

/-- Family of relatively open convex subsets of `C`. -/
def relOpenConvexSubsets (C : Set E) : Set (Set E) :=
  {V : Set E | V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V}

@[simp] theorem mem_relOpenConvexSubsets_iff {C V : Set E} :
    V ∈ relOpenConvexSubsets 𝕜 C ↔
      V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V :=
  Iff.rfl

end RelativelyOpenConvexFamily

end Set

/-- Family notation for relatively open convex subsets of `C`. -/
scoped[Rockafellar] notation "𝒪[" 𝕜 "](" C ")" =>
  Set.relOpenConvexSubsets 𝕜 C

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Set.IsFace

/-- Distinct faces of `C` have disjoint relative interiors. This is the owner-level core behind
Theorem 18.2 (1); the source-facing nonempty-face family is then obtained by restricting this
canonical face-family theorem. -/
theorem pairwiseDisjoint_riFaces {C : Set E} :
    (𝓕[𝕜](C)).PairwiseDisjoint (fun F ↦ ri[𝕜](F)) := by
  rw [Set.pairwiseDisjoint_iff]
  intro F hF G hG hri
  simpa using (show F.IsFace 𝕜 C from hF).eq_of_nonempty_inter_ri (show G.IsFace 𝕜 C from hG) hri

/-- Owner-level bridge behind Theorem 18.2 (1): relative interiors indexed by
`𝒰[𝕜](C)` are pairwise disjoint. -/
theorem pairwiseDisjoint_riNonemptyFaces {C : Set E} :
    (𝒰[𝕜](C)).PairwiseDisjoint id := by
  rw [Set.pairwiseDisjoint_iff]
  intro U hU V hV hUV
  rcases (mem_riNonemptyFaces_iff (𝕜 := 𝕜) (C := C) (U := U)).1 hU with
    ⟨F, hF_face, -, rfl⟩
  rcases (mem_riNonemptyFaces_iff (𝕜 := 𝕜) (C := C) (U := V)).1 hV with
    ⟨G, hG_face, -, rfl⟩
  have hFG : F = G := hF_face.eq_of_nonempty_inter_ri hG_face hUV
  simp [hFG]

end Set.IsFace

open Set.IsFace

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 18.2 studies Rockafellar's family `𝒰` of relative interiors of the
  nonempty faces of a convex set `C`, asserting that these pieces partition `C`, absorb every
  relatively open convex subset of `C`, and are exactly the maximal relatively open convex subsets
  of `C`.
- `core/canonical`: the source-facing owner notions are `Set.IsFace.faces` (surface notation
  `𝓕[𝕜](C)`), `Set.IsFace.riNonemptyFaces` (surface notation `𝒰[𝕜](C)`),
  `Set.relOpenConvexSubsets` (surface notation `𝒪[𝕜](C)`),
  `ri[𝕜](·) = intrinsicInterior 𝕜`,
  `IsRelativelyOpen 𝕜`, `Set.PairwiseDisjoint`, `⋃₀`, and `Maximal` on `Set E`.
- `bridge/view`: the family `𝒰[𝕜](C)` packages the source set-builder
  `{ri[𝕜](F) | F ∈ 𝓕[𝕜](C), F.Nonempty}` directly at the owner level, while `𝒪[𝕜](C)` packages
  the recurring predicate `V ⊆ C ∧ Convex 𝕜 V ∧ IsRelativelyOpen 𝕜 V`.

Domain-style sampling used here:
- `Set.IsFace.sInter`;
- `Set.IsFace.eq_of_nonempty_inter_ri`;
- `IsExtreme.subset`;
- `IsRelativelyOpen 𝕜 U`.

Primitive data vs derived API:
- primitive source-facing content: a nonempty face `F` of `C` and its relative interior
  `ri[𝕜](F)`;
- derived API: pairwise disjointness of the family `𝒰[𝕜](C)`, covering `C`, the absorption
  theorem for members of `𝒪[𝕜](C)`, and the maximality
  characterization in that same primitive owner language.

Layer target: `source-facing`, stated directly in the owner face and relative-interior API.

Ambient refinement: part (1) only uses the chapter face API and `ri[𝕜](·)`, so it lives on the
same scalar-generic ordered nontrivially normed field layer as
`Set.IsFace.eq_of_nonempty_inter_ri`. Part (2) uses the chapter's finite-dimensional
minimal-face and affine-dimension owner machinery, so its statement is kept on the same
scalar-generic finite-dimensional ordered nontrivially normed field layer rather than being
specialized to `ℝ`. Parts (3) and (4) are also source-facing finite-dimensional face statements:
their public content only involves faces, convexity, inclusion, relative interior, relative
openness, and maximality. The older real specialization came only from one Chapter 11 proof route
through supporting hyperplanes, so it is removed from the statement surface rather than preserved
as ambient API debt.
-/

/-- Theorem 18.2 (1): the members of `𝒰[𝕜](C)` are pairwise disjoint. -/
-- Proof sketch: if `U, V ∈ 𝒰[𝕜](C)`, write `U = ri[𝕜](F₁)` and `V = ri[𝕜](F₂)` with nonempty
-- faces `F₁`, `F₂` of `C`. If `U ∩ V` is nonempty, Corollary 18.1.2 gives `F₁ = F₂`, hence
-- `U = V`. This is exactly `Set.PairwiseDisjoint` for the family `𝒰[𝕜](C)`.
theorem pairwiseDisjoint_ri_nonempty_faces
    {C : Set E} :
    (𝒰[𝕜](C)).PairwiseDisjoint id := by
  simpa using (Set.IsFace.pairwiseDisjoint_riNonemptyFaces (𝕜 := 𝕜) (C := C))

end

section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

section FiniteDimensionalFaces

variable [FiniteDimensional 𝕜 E]

namespace Set.IsFace

/-- Owner-level form behind Theorem 18.2 (2): the family `𝒰[𝕜](C)` covers `C`. -/
theorem sUnion_riNonemptyFaces_eq
    {C : Set E} (hC : Convex 𝕜 C) :
    ⋃₀ 𝒰[𝕜](C) = C := sorry

end Set.IsFace

/-- Theorem 18.2 (2): for a convex set `C`, the union of the family `𝒰[𝕜](C)` is exactly `C`.
The source adds `C ≠ ∅`, but that binder is redundant for this owner-level covering statement;
the finite-dimensional ordered normed-field layer is not redundant here because the minimal-face
proof route uses the chapter affine-dimension machinery. -/
-- Proof sketch: every member of `𝒰[𝕜](C)` has the form `ri[𝕜](F)` for a nonempty face `F` of
-- `C`, hence is contained in `C`. Conversely, if `x ∈ C`, let `F` be the intersection of all
-- faces of `C` containing `x`. This is a nonempty face by `Set.IsFace.sInter`, and in
-- finite-dimensional spaces Rockafellar's minimal-face argument shows `x ∈ ri[𝕜](F)`. Hence
-- every point of `C` lies in `⋃₀ 𝒰[𝕜](C)`.
theorem sUnion_ri_nonempty_faces_eq
    {C : Set E} (hC : Convex 𝕜 C) :
    ⋃₀ 𝒰[𝕜](C) = C := by
  simpa using (Set.IsFace.sUnion_riNonemptyFaces_eq (𝕜 := 𝕜) (C := C) hC)

end FiniteDimensionalFaces

section FiniteDimensionalRelativelyOpenFaces

variable [FiniteDimensional 𝕜 E]

namespace Set.IsFace

/-- Owner-level form behind Theorem 18.2 (3): a relatively open convex subset of a nonempty convex
set is contained in some member of `𝒰[𝕜](C)`. -/
theorem exists_riNonemptyFaces_superset_of_relativelyOpenConvex
    {C D : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty)
    (hD : D ∈ 𝒪[𝕜](C)) :
    ∃ U : Set E, U ∈ 𝒰[𝕜](C) ∧ D ⊆ U := sorry

/-- Owner-level form behind Theorem 18.2 (4): `U` belongs to `𝒰[𝕜](C)` iff it is
maximal among relatively open convex subsets of `C`. -/
theorem mem_riNonemptyFaces_iff_maximal_relativelyOpenConvex
    {C U : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (U ∈ 𝒰[𝕜](C)) ↔
      Maximal (· ∈ 𝒪[𝕜](C)) U := sorry

end Set.IsFace

/-- Theorem 18.2 (3): every relatively open convex subset `D` of a nonempty convex set `C` is
contained in some member of `𝒰[𝕜](C)`. The public surface uses the canonical family owner
`𝒪[𝕜](C)` for relatively open convex subsets of `C`. -/
-- Proof sketch: if `D = ∅`, choose any point of the nonempty convex set `C` and use part (2) to
-- place that point in some member of `𝒰[𝕜](C)`, which then trivially contains `D`. Otherwise let
-- `F` be the intersection of all faces of `C` containing `D`. If `D` were contained in the
-- relative boundary of `F`, a finite-dimensional supporting-functional boundary-cut argument would
-- produce a proper face of `F`, hence a smaller face of `C` still containing `D`, contradicting
-- minimality. Therefore `D` meets `ri[𝕜](F)`, and Corollary 6.5.2 upgrades that meeting point to
-- inclusion in that member of `𝒰[𝕜](C)`.
theorem exists_mem_ri_nonempty_faces_superset_of_relativelyOpenConvex
    {C D : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty)
    (hD : D ∈ 𝒪[𝕜](C)) :
    ∃ U : Set E, U ∈ 𝒰[𝕜](C) ∧ D ⊆ U := by
  simpa using
    (Set.IsFace.exists_riNonemptyFaces_superset_of_relativelyOpenConvex
      (𝕜 := 𝕜) (C := C) (D := D) hC hC_nonempty hD)

/-- Theorem 18.2 (4): for a nonempty convex set `C`, a subset `U` is in `𝒰[𝕜](C)` exactly when
`U` is a maximal relatively open convex subset of `C`.
Maximality is taken with respect to inclusion inside the canonical family owner `𝒪[𝕜](C)`. -/
-- Proof sketch: if `U ∈ 𝒰[𝕜](C)`, write `U = ri[𝕜](F)` for a nonempty face `F` of `C`; then `U`
-- is relatively open and convex, and part (3) shows maximality. Conversely, if `U` is maximal
-- among relatively open convex subsets of `C`, part (3) puts `U` inside some member of
-- `𝒰[𝕜](C)`; maximality forces equality, so `U ∈ 𝒰[𝕜](C)`.
theorem mem_ri_nonempty_faces_iff_maximal_relativelyOpenConvex
    {C U : Set E} (hC : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    (U ∈ 𝒰[𝕜](C)) ↔
      Maximal (· ∈ 𝒪[𝕜](C)) U := by
  simpa using
    (Set.IsFace.mem_riNonemptyFaces_iff_maximal_relativelyOpenConvex
      (𝕜 := 𝕜) (C := C) (U := U) hC hC_nonempty)

end FiniteDimensionalRelativelyOpenFaces

end

import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] {I : Sort v}

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.5 identifies the convex hull of an arbitrary family of functions with
  the vertical infimum attached to the convex hull of the union of their scalar epigraphs.
- `core/canonical`: besides `conv(g)` from Text 5.5.1, theorem surfaces stay directly on the
  existing canonical set owners `_root_.convexHull` and `epi`.
- `bridge/view`: the indexed-family source expression is the canonical owner expression itself:
  `_root_.convexHull 𝕜 (⋃ i, epi (f i))`.
- Primitive data vs derived API: the indexed family `f : I → E → WithTopBot 𝕜` is primitive; the
  vertical-infimum identity for `conv(⨅ i, f i)` is the source-facing bridge theorem, and the
  intrinsic `verticalHeights` value formula is its canonical companion.

Domain-style sampling used here:
- `Function.convexHull`;
- `Function.isGreatest_conv_minorant`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`;
- `_root_.convexHull`;
- `epi`.
- Ambient minimization: the family convex-hull construction only uses convex hulls and pointwise
  infima in `E × 𝕜`, so it should live on the same arbitrary `𝕜`-module ambient as the
  single-function owner `Function.convexHull`.
- Layer target: `core/canonical` on existing owners without introducing a new owner alias.
-/

/-- Text 5.5.5: the convex hull of the pointwise infimum of a family is the vertical infimum
attached to the convex hull of the union of the scalar epigraphs. -/
theorem conv_iInf_eq_verticalInfimum_convexHull_iUnion_epi
    (f : I → E → WithTopBot 𝕜) :
    conv(⨅ i, f i) =
      verticalInfimum (_root_.convexHull 𝕜 (⋃ i, epi (f i))) := by
  let g : E → WithTopBot 𝕜 := ⨅ i : I, f i
  let U : Set (E × 𝕜) := ⋃ i, epi (f i)
  have hmain : conv(g) = verticalInfimum (_root_.convexHull 𝕜 U) := by
    refine le_antisymm ?_ ?_
    · refine le_verticalInfimum_of_subset_epi ?_
      apply convexHull_min
      · intro p hp
        rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
        rcases mem_epi_restrict_iff.mp hi with ⟨_, hip⟩
        have hconv : conv(g) ≤ f i :=
          (Function.conv_le g).trans (iInf_le (fun j ↦ f j) i)
        exact mem_epi_restrict_iff.mpr ⟨by simp, (hconv p.1).trans hip⟩
      · simpa [epi_univ_eq_setOf_le] using
          (isConvex_conv g).convex_epigraph
    · exact Function.le_conv_of_le
        (Function.isConvex_verticalInfimum (convex_convexHull 𝕜 U))
        (by
          refine le_iInf fun i ↦ ?_
          exact verticalInfimum_le_of_epi_subset <|
            Set.Subset.trans
              (by intro p hp; exact Set.mem_iUnion.mpr ⟨i, hp⟩)
              (subset_convexHull 𝕜 U))
  simpa [g, U] using hmain

-- Proof sketch: Text 5.5.5 identifies the family convex hull with the vertical infimum attached
-- to `_root_.convexHull 𝕜 (⋃ i, epi (f i))`.
-- The displayed formula is then the intrinsic owner-level
-- specification `verticalInfimum_eq_sInf_verticalHeights`.
/-- The value of `conv(⨅ i, f i)` at `x` is the infimum of the intrinsic height owner
`Function.verticalHeights` above `x` for the convex hull of the family epigraph union. -/
theorem conv_iInf_apply_eq_sInf_verticalHeights_convexHull_iUnion_epi
    (f : I → E → WithTopBot 𝕜) (x : E) :
    conv(⨅ i, f i) x =
      sInf (verticalHeights (_root_.convexHull 𝕜 (⋃ i, epi (f i))) x) := by
  rw [conv_iInf_eq_verticalInfimum_convexHull_iUnion_epi,
    verticalInfimum_eq_sInf_verticalHeights]

end Function

end

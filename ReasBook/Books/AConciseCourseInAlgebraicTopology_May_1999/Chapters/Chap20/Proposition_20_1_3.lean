import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Homology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Comparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Orientation

open AlgebraicTopology CategoryTheory Limits
open scoped Manifold Topology

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [Fact (Module.finrank ℝ E = n)]

/-- Helper for Proposition 20.1.3: intersecting a compatible representative atlas with
`inducedROrientationAtlas z` preserves the same-orientation relation. -/
theorem sameOrientation_atlasInterInduced_left
    (o : ROrientedManifold R I n M)
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassFor o z) :
    ROrientedManifold.SameOrientation o (atlasInterInducedROrientedManifold o hz) := by
  -- Every chart in the intersection atlas is already a chart of `o`, so compatibility comes from
  -- the original oriented atlas.
  intro x U V hU hxU hV hxV
  exact o.pairwise_compatible hU hV.1 hxU hxV

/-- Helper for Proposition 20.1.3: the intersection atlas attached to a compatible representative
and the canonical induced atlas of `z` are same-oriented. -/
theorem sameOrientation_atlasInterInduced_induced
    [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz0 : IsRFundamentalClass R n M z)
    {o : ROrientedManifold R I n M}
    (hz : IsRFundamentalClassFor o z) :
    ROrientedManifold.SameOrientation
      (atlasInterInducedROrientedManifold o hz)
      (inducedROrientedManifold hz0) := by
  -- Both atlases lie inside `inducedROrientationAtlas z`, so the induced-atlas compatibility
  -- theorem supplies the required overlap compatibility.
  intro x U V hU hxU hV hxV
  exact inducedROrientationAtlas_pairwiseCompatible_of_isRFundamentalClass
    I hz0 hU.2 hV hxU hxV

/-- Helper for Proposition 20.1.3: a chosen representative `R`-oriented atlas determines a unique
compatible `R`-fundamental class `z ∈ H_n(M; R)`. -/
theorem existsUnique_rFundamentalClassFor_of_representative_rOrientedManifold
    [CompactSpace M]
    (h_oriented : ROrientedManifold R I n M) :
    ∃! z : rSingularHomology R n (TopCat.of.{u} M),
      IsRFundamentalClassFor h_oriented z := by
  -- First construct the unique normalized `Set.univ` relative class attached to the oriented
  -- atlas.
  have hRelative :
      ∃! η : relativeTopHomologyGroup R n M Set.univ, IsUnivRelativeClassFor h_oriented η :=
    existsUnique_univRelativeClass_compatible_of_rOrientedManifold h_oriented
  -- Then transport that unique class across the absolute-relative comparison.
  exact existsUnique_rFundamentalClassFor_of_existsUnique_univRelativeClass
    h_oriented hRelative

/-- Proposition 20.1.3 (1). For a compact `n`-manifold `M`, an `R`-orientation
determines a unique compatible `R`-fundamental class `z ∈ H_n(M; R)`. -/
theorem existsUnique_rFundamentalClassFor_of_rOrientedManifold
    [CompactSpace M]
    (h_oriented : ROrientedManifold.GlobalOrientation R I n M) :
    ∃! z : rSingularHomology R n (TopCat.of.{u} M),
      IsRFundamentalClassForGlobalOrientation h_oriented z := sorry

/-- Proposition 20.1.3 (2). For a compact `n`-manifold `M`, an `R`-fundamental class
`z ∈ H_n(M; R)` determines a unique compatible `R`-orientation. -/
theorem exists_rOrientedManifoldFor_of_isRFundamentalClass
    [CompactSpace M] [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ∃! o : ROrientedManifold.GlobalOrientation R I n M,
      IsRFundamentalClassForGlobalOrientation o z := sorry

/-- The compact-manifold orientation/fundamental-class correspondence yields the existence-level
formulation used later in orientability statements. -/
theorem nonempty_rOrientedManifold_iff_exists_rFundamentalClass
    [CompactSpace M] [IsManifold I ⊤ M] :
    Nonempty (ROrientedManifold R I n M) ↔
      ∃ z : rSingularHomology R n (TopCat.of.{u} M), IsRFundamentalClass R n M z := sorry

end

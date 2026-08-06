import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3.Comparison

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

/-- Any `R`-orientation compatible with `z` contains a covering subatlas of charts whose chosen
identifications send the local image of `z` to `1 : R` everywhere on their domains. -/
theorem cover_atlas_inter_inducedROrientationAtlas_of_isRFundamentalClassFor
    {o : ROrientedManifold R I n M} {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassFor o z) :
    ∀ x : M, ∃ U ∈ o.atlas ∩ inducedROrientationAtlas z, x ∈ U.domain := by
  sorry

/-- Intersecting an orientation atlas with `inducedROrientationAtlas z` preserves pairwise
compatibility. -/
theorem pairwiseCompatible_atlas_inter_inducedROrientationAtlas
    (o : ROrientedManifold R I n M) (z : rSingularHomology R n (TopCat.of.{u} M))
    {U V : LocalTopHomologyTrivialization R n M}
    (hU : U ∈ o.atlas ∩ inducedROrientationAtlas z)
    (hV : V ∈ o.atlas ∩ inducedROrientationAtlas z) :
    U.OrientationCompatible V :=
  o.pairwise_compatible hU.1 hV.1

/-- Helper for Proposition 20.1.3: if a global class is already compatible with a chosen
`R`-orientation, then the subatlas `o.atlas ∩ inducedROrientationAtlas z` is itself an
`R`-orientation on `M`. -/
@[reducible] def atlasInterInducedROrientedManifold
    (o : ROrientedManifold R I n M)
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassFor o z) :
    ROrientedManifold R I n M where
  toIsManifold := o.toIsManifold
  atlas := o.atlas ∩ inducedROrientationAtlas z
  cover := fun x ↦ cover_atlas_inter_inducedROrientationAtlas_of_isRFundamentalClassFor hz x
  pairwise_compatible := fun hU hV ↦
    pairwiseCompatible_atlas_inter_inducedROrientationAtlas o z hU hV

/-- Helper for Proposition 20.1.3: the intersection orientation produced from a compatible global
class still has `z` as a compatible `R`-fundamental class. -/
theorem isRFundamentalClassFor_atlasInterInducedROrientedManifold
    (o : ROrientedManifold R I n M)
    {z : rSingularHomology R n (TopCat.of.{u} M)}
    (hz : IsRFundamentalClassFor o z) :
    IsRFundamentalClassFor (atlasInterInducedROrientedManifold o hz) z := by
  sorry

/-- The pointwise atlas extracted from a fundamental class covers `M`. -/
theorem inducedROrientationAtlas_cover_of_isRFundamentalClass
    (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ∀ x : M, ∃ U ∈ inducedROrientationAtlas z, x ∈ U.domain := by
  sorry

/-- The pointwise atlas extracted from a fundamental class is pairwise compatible on overlaps. -/
theorem inducedROrientationAtlas_pairwiseCompatible_of_isRFundamentalClass
    (I : ModelWithCorners ℝ E H) [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ∀ ⦃U V : LocalTopHomologyTrivialization R n M⦄,
      U ∈ inducedROrientationAtlas z → V ∈ inducedROrientationAtlas z →
        U.OrientationCompatible V := by
  sorry

/-- The `R`-orientation canonically induced by an `R`-fundamental class uses the atlas whose local
identifications send the local image of the class to `1 : R`. -/
@[reducible] def inducedROrientedManifold [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ROrientedManifold R I n M where
  toIsManifold := ‹IsManifold I ⊤ M›
  atlas := inducedROrientationAtlas z
  cover := fun x ↦ inducedROrientationAtlas_cover_of_isRFundamentalClass I hz x
  pairwise_compatible := fun hU hV ↦
    inducedROrientationAtlas_pairwiseCompatible_of_isRFundamentalClass I hz hU hV

/-- Helper for Proposition 20.1.3: the canonical atlas induced by an `R`-fundamental class is
compatible with that class. -/
theorem isRFundamentalClassFor_inducedROrientedManifold_of_isRFundamentalClass
    [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    IsRFundamentalClassFor (inducedROrientedManifold hz : ROrientedManifold R I n M) z := by
  sorry

/-- Helper for Proposition 20.1.3: any `R`-fundamental class yields an `R`-oriented atlas for
which `z` is compatible. -/
theorem exists_rOrientedManifold_of_isRFundamentalClass
    [IsManifold I ⊤ M]
    {z : rSingularHomology R n (TopCat.of.{u} M)} (hz : IsRFundamentalClass R n M z) :
    ∃ o : ROrientedManifold R I n M, IsRFundamentalClassFor o z := by
  sorry

end

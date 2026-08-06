import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Proposition_7_5_3

open CategoryTheory
open TopCat
open scoped ContinuousMap

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} B]

-- Chapter 7 precedent identifies `mappingPathSpaceInclusion_homotopyEquiv` as the canonical
-- homotopy-equivalence owner for the mapping path factorization. This file keeps only the
-- source-facing map over `B` and its companion instance/theorem surfaces.

/-- The canonical map `E → N_p` regarded as a morphism over `B`. -/
def mappingPathSpaceInclusionOver (p : C(E, B)) :
    SpaceOver.mk p ⟶ SpaceOver.mk (mappingPathSpaceProjection p) :=
  SpaceOver.homMk (mappingPathSpaceInclusion p)
    (mappingPathSpaceProjection_comp_mappingPathSpaceInclusion p)

/-- Helper for Example 7.5.4: if `p : C(E, B)` is a fibration, then the canonical map
`E → N_p = MappingPathSpace p` is a fiber homotopy equivalence over `B`. -/
private theorem mappingPathSpaceInclusionOver_isFiberHomotopyEquivalence
    (p : C(E, B)) [IsFibration.{u, u, u} p] :
    IsFiberHomotopyEquivalence (mappingPathSpaceInclusionOver p) := by
  -- Route correction: use the existing mapping-path homotopy equivalence directly, and let Lean
  -- infer the universe and fibration parameters instead of forcing an explicit application.
  have hp : IsFibration p := inferInstance
  let _ : CompactlyGeneratedWeakHausdorffSpace.{u, u} (MappingPathSpace p) :=
    mappingPathSpaceCompactlyGeneratedWeakHausdorffSpace p
  have hq : IsFibration (mappingPathSpaceProjection p) := inferInstance
  have he :
      (mappingPathSpaceInclusion_homotopyEquiv p).toFun =
        (mappingPathSpaceInclusionOver p).left.hom := by
  -- The over-map is the same underlying continuous map as the forward homotopy equivalence map.
    simpa [mappingPathSpaceInclusionOver] using
      mappingPathSpaceInclusion_homotopyEquiv_toFun_spaceOver_homMk p
  exact isFiberHomotopyEquivalence_of_homotopyEquiv hp hq
    (mappingPathSpaceInclusionOver p)
    (mappingPathSpaceInclusion_homotopyEquiv p) he

/-- Helper for Example 7.5.4: forgetting the base condition on a homotopy over `B` yields an
ordinary homotopy of the underlying continuous maps. -/
private theorem homotopicOfHomotopicOver
    {X Y : SpaceOver B} {f₀ f₁ : X ⟶ Y}
    (h : HomotopicOver f₀ f₁) :
    f₀.left.hom.Homotopic f₁.left.hom := by
  -- Unpack the homotopy-over witness and retain only its underlying homotopy.
  rcases h with ⟨H⟩
  exact ⟨H.toHomotopy⟩

/-- Helper for Example 7.5.4: a left homotopy inverse and a right homotopy inverse of the same
map are homotopic to each other. -/
private theorem homotopicInverseUnique
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {g h : C(Y, X)}
    (hg : (g.comp f).Homotopic (ContinuousMap.id X))
    (hh : (f.comp h).Homotopic (ContinuousMap.id Y)) :
    g.Homotopic h := by
  -- First insert the right inverse homotopy on the source side of `g`.
  have hToTriple : g.Homotopic (g.comp (f.comp h)) := by
    simpa [ContinuousMap.comp_assoc] using
      ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g) hh.symm
  -- Then collapse the left inverse homotopy on the target side.
  have hCollapse : (g.comp (f.comp h)).Homotopic h := by
    simpa [ContinuousMap.comp_assoc] using
      ContinuousMap.Homotopic.comp hg (ContinuousMap.Homotopic.refl h)
  exact hToTriple.trans hCollapse

/-- Example 7.5.4 (2): if `p : C(E, B)` is a fibration, then the evident projection
`N_p = MappingPathSpace p → E` is homotopic to a two-sided homotopy inverse over `B` for the
canonical map `E → N_p`. -/
theorem mappingPathSpacePointProjection_homotopic_to_overInverse
    (p : C(E, B)) [IsFibration.{u, u, u} p] :
    ∃ g : SpaceOver.mk (mappingPathSpaceProjection p) ⟶ SpaceOver.mk p,
      (mappingPathSpacePointProjection p).Homotopic g.left.hom ∧
        HomotopicOver (g ≫ mappingPathSpaceInclusionOver p)
          (𝟙 (SpaceOver.mk (mappingPathSpaceProjection p))) ∧
          HomotopicOver (mappingPathSpaceInclusionOver p ≫ g)
            (𝟙 (SpaceOver.mk p)) := by
  -- Route correction: extract the over-inverse from Example 7.5.4 (1), then compare its
  -- underlying map with the canonical point projection by ordinary homotopy-inverse uniqueness.
  rcases
      (isFiberHomotopyEquivalence_iff.mp
        (mappingPathSpaceInclusionOver_isFiberHomotopyEquivalence p)) with
    ⟨g, hRightOver, hLeftOver⟩
  -- Forget the over-structure on the left inverse homotopy.
  have hLeft :
      (g.left.hom.comp (mappingPathSpaceInclusion p)).Homotopic (ContinuousMap.id E) := by
    simpa [mappingPathSpaceInclusionOver] using homotopicOfHomotopicOver hLeftOver
  -- The canonical point projection already gives the standard right inverse homotopy.
  have hRight :
      ((mappingPathSpaceInclusion p).comp (mappingPathSpacePointProjection p)).Homotopic
        (ContinuousMap.id (MappingPathSpace p)) :=
    mappingPathSpaceInclusionPointProjection_homotopic_id p
  -- Compare the two inverse candidates through the common inclusion map.
  have hProjection :
      g.left.hom.Homotopic (mappingPathSpacePointProjection p) :=
    homotopicInverseUnique (f := mappingPathSpaceInclusion p) hLeft hRight
  refine ⟨g, hProjection.symm, hRightOver, hLeftOver⟩

instance instIsFiberHomotopyEquivalence_mappingPathSpaceInclusionOver
    (p : C(E, B)) [IsFibration.{u, u, u} p] :
    IsFiberHomotopyEquivalence (mappingPathSpaceInclusionOver p) := by
  exact mappingPathSpaceInclusionOver_isFiberHomotopyEquivalence p

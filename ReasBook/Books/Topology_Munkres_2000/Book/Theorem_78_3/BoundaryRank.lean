module

public import Topology_Munkres_2000.Book.Theorem_78_3.OpenEdgeCollar
public import Topology_Munkres_2000.Book.Exercise_78_2

open scoped Manifold SurfaceBoundary

public section

universe u

namespace Topology

/-- Helper for Theorem 78.3: a continuous injective planar map whose image lies
in the canonical closed half-plane has strictly positive normal coordinate. -/
theorem normalCoordinate_pos_of_planarEmbedding_into_halfSpace
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → EuclideanSpace ℝ (Fin 2)) (hfContinuous : Continuous f)
    (hfInjective : Function.Injective f)
    (hfRange : Set.range f ⊆ Set.range (𝓡∂ 2)) (p : U) :
    0 < f p 0 := by
  have hRangeOpen : IsOpen (Set.range f) :=
    (invarianceOfDomainPlane hU f hfContinuous hfInjective).isOpen_range
  have hRangeInterior :
      Set.range f ⊆ interior (Set.range (𝓡∂ 2)) :=
    interior_maximal hfRange hRangeOpen
  -- The chosen image lies in this open subset of the half-plane, whose
  -- interior is exactly the strict positive-normal locus.
  have hpInterior : f p ∈ interior (Set.range (𝓡∂ 2)) :=
    hRangeInterior (Set.mem_range_self p)
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hpInterior
  exact hpInterior

end Topology

namespace Topology

/-- Helper for Theorem 78.3: a point in a continuous injective planar patch of
a topological surface cannot lie on the manifold boundary. -/
theorem planarEmbeddingAt_not_mem_surfaceBoundary
    {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace (EuclideanHalfSpace 2) Y] [IsManifold (𝓡∂ 2) 0 Y]
    [T2Space Y] [SecondCountableTopology Y]
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : IsOpen U)
    (f : U → Y) (hfContinuous : Continuous f)
    (hfInjective : Function.Injective f) (p : U) :
    f p ∉ (∂Y : Set Y) := by
  intro hpBoundary
  obtain ⟨chart, hpSource, hpFace⟩ :=
    (memBoundary_iff_exists_halfSpaceChart (f p)).mp hpBoundary
  let domain : Set U := f ⁻¹' chart.source
  have hdomainOpen : IsOpen domain :=
    chart.open_source.preimage hfContinuous
  let inclusion : domain → EuclideanSpace ℝ (Fin 2) :=
    (Subtype.val : U → EuclideanSpace ℝ (Fin 2)) ∘
      (Subtype.val : domain → U)
  have hInclusionOpen : IsOpenEmbedding inclusion := by
    -- Both subtype inclusions have open image, so their composite identifies
    -- the restricted chart domain with an open planar set.
    dsimp only [inclusion]
    exact hU.isOpenEmbedding_subtypeVal.comp
      hdomainOpen.isOpenEmbedding_subtypeVal
  let domainEquiv : domain ≃ₜ Set.range inclusion :=
    hInclusionOpen.isEmbedding.toHomeomorph
  let coordinateMap : domain → EuclideanHalfSpace 2 :=
    fun q ↦ chart (f q.1)
  have hCoordinateContinuous : Continuous coordinateMap := by
    -- Restrict the surface chart to points mapped into its source.
    exact chart.continuousOn.comp_continuous
      (hfContinuous.comp continuous_subtype_val) (fun q ↦ q.2)
  let planarMap : Set.range inclusion → EuclideanSpace ℝ (Fin 2) :=
    fun q ↦ (𝓡∂ 2) (coordinateMap (domainEquiv.symm q))
  have hPlanarContinuous : Continuous planarMap := by
    exact (𝓡∂ 2).continuous.comp
      (hCoordinateContinuous.comp domainEquiv.symm.continuous)
  have hPlanarInjective : Function.Injective planarMap := by
    intro q r hqr
    apply domainEquiv.symm.injective
    apply Subtype.ext
    apply hfInjective
    apply chart.injOn
      (domainEquiv.symm q).2 (domainEquiv.symm r).2
    apply EuclideanHalfSpace.ext
    exact hqr
  have hPlanarRange : Set.range planarMap ⊆ Set.range (𝓡∂ 2) := by
    rintro z ⟨q, rfl⟩
    exact ⟨coordinateMap (domainEquiv.symm q), rfl⟩
  let pDomain : domain := ⟨p, hpSource⟩
  let pRange : Set.range inclusion := domainEquiv pDomain
  have hpPositive : 0 < planarMap pRange 0 :=
    normalCoordinate_pos_of_planarEmbedding_into_halfSpace
      hInclusionOpen.isOpen_range planarMap hPlanarContinuous hPlanarInjective
        hPlanarRange pRange
  have hpPlanarMap : planarMap pRange = (𝓡∂ 2) (chart (f p)) := by
    -- The chosen restricted-domain point maps back to the original point `p`.
    dsimp only [planarMap, pRange, coordinateMap, pDomain]
    rw [domainEquiv.symm_apply_apply]
  rw [hpPlanarMap, hpFace] at hpPositive
  exact (lt_irrefl 0) hpPositive

end Topology

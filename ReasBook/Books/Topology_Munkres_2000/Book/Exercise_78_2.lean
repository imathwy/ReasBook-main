module

public import Topology_Munkres_2000.Book.Theorem_62_3
public import Topology_Munkres_2000.Book.Definition_78_3

open scoped Manifold SurfaceBoundary

public section

universe u

/-- Helper for Exercise 78.2: the canonical half-space model maps its interior source to the
interior of its range. -/
private lemma halfSpaceInterior_map_source
    (p : EuclideanHalfSpace 2)
    (hp : p ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2) p ∈ interior (Set.range (𝓡∂ 2)) :=
  hp

/-- Helper for Exercise 78.2: the inverse of the canonical half-space model maps an interior
point of its range back to the interior source. -/
private lemma halfSpaceInterior_map_target
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2).symm y ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2)) := by
  have hyRange : y ∈ Set.range (𝓡∂ 2) := interior_subset hy
  rw [Set.mem_preimage, (𝓡∂ 2).right_inv hyRange]
  exact hy

/-- Helper for Exercise 78.2: the canonical half-space model inverse is a left inverse on the
interior source. -/
private lemma halfSpaceInterior_left_inv
    (p : EuclideanHalfSpace 2)
    (_hp : p ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2).symm ((𝓡∂ 2) p) = p := by
  exact (𝓡∂ 2).left_inv p

/-- Helper for Exercise 78.2: the canonical half-space model is a right inverse on the interior
of its range. -/
private lemma halfSpaceInterior_right_inv
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2) ((𝓡∂ 2).symm y) = y := by
  exact (𝓡∂ 2).right_inv (interior_subset hy)

/-- Helper for Exercise 78.2: the interior source of the canonical half-space model is open. -/
private lemma isOpen_halfSpaceInterior_source :
    IsOpen ((𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :=
  isOpen_interior.preimage (𝓡∂ 2).continuous

/-- Helper for Exercise 78.2: the interior of the canonical half-space model range is open. -/
private lemma isOpen_halfSpaceInterior_target :
    IsOpen (interior (Set.range (𝓡∂ 2))) :=
  isOpen_interior

/-- Helper for Exercise 78.2: the canonical model identifies the interior of
`EuclideanHalfSpace 2` with an open subset of `EuclideanSpace ℝ (Fin 2)`. -/
private noncomputable def halfSpaceInteriorPartialHomeomorph :
    OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)) where
  toFun := 𝓡∂ 2
  invFun := (𝓡∂ 2).symm
  source := (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))
  target := interior (Set.range (𝓡∂ 2))
  map_source' := halfSpaceInterior_map_source
  map_target' := halfSpaceInterior_map_target
  left_inv' := halfSpaceInterior_left_inv
  right_inv' := halfSpaceInterior_right_inv
  continuousOn_toFun := (𝓡∂ 2).continuous.continuousOn
  continuousOn_invFun := (𝓡∂ 2).continuous_symm.continuousOn
  open_source := isOpen_halfSpaceInterior_source
  open_target := isOpen_halfSpaceInterior_target

/-- A point of `EuclideanHalfSpace 2` lies on its boundary face exactly when it is a
boundary point for the canonical model with corners. -/
theorem halfSpace_isBoundaryPoint_iff (p : EuclideanHalfSpace 2) :
    (𝓡∂ 2).IsBoundaryPoint p ↔ (𝓡∂ 2) p 0 = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  simp [eq_comm]

/-- Helper for Exercise 78.2: a point of the half-space admitting a Euclidean chart lies in
the interior of the canonical half-space model range. -/
private lemma mem_interior_halfSpace_of_mem_euclideanChart
    (p : EuclideanHalfSpace 2)
    (e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)))
    (hp : p ∈ e.source) :
    (𝓡∂ 2) p ∈ interior (Set.range (𝓡∂ 2)) := by
  -- Apply invariance of domain to the inverse chart, viewed in ambient Euclidean coordinates.
  let f : e.target → EuclideanSpace ℝ (Fin 2) := fun y ↦ (𝓡∂ 2) (e.symm y)
  have htarget : ∀ y : e.target, (y : EuclideanSpace ℝ (Fin 2)) ∈ e.target := by
    intro y
    exact y.property
  have hsymmContinuous : Continuous (fun y : e.target ↦ e.symm y) :=
    e.continuousOn_symm.comp_continuous continuous_subtype_val htarget
  have hfContinuous : Continuous f := by
    exact (𝓡∂ 2).continuous.comp hsymmContinuous
  have hfInjective : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    apply e.symm.injOn y.property z.property
    apply EuclideanHalfSpace.ext
    exact hyz
  have hfOpen : IsOpen (Set.range f) :=
    (invarianceOfDomainPlane e.open_target f hfContinuous hfInjective).isOpen_range
  -- The open image stays in the half-space model range.
  have hRangeSubset : Set.range f ⊆ Set.range (𝓡∂ 2) := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    dsimp only [f]
    exact Set.mem_range_self (e.symm y)
  have hRangeInterior : Set.range f ⊆ interior (Set.range (𝓡∂ 2)) :=
    interior_maximal hRangeSubset hfOpen
  -- The chosen point is in that open image by the chart inverse law.
  have hepTarget : e p ∈ e.target := e.map_source hp
  let ep : e.target := ⟨e p, hepTarget⟩
  have hpRange : (𝓡∂ 2) p ∈ Set.range f := by
    refine Set.mem_range.2 ?_
    use ep
    dsimp only [f, ep]
    rw [e.left_inv hp]
  exact hRangeInterior hpRange

/-- Exercise 78.2 (1). A point on the boundary face of `EuclideanHalfSpace 2` has no
neighborhood homeomorphic to an open subset of `ℝ²`. -/
theorem boundaryFace_hasNoEuclideanChart
    (p : EuclideanHalfSpace 2) (hp : (𝓡∂ 2) p 0 = 0) :
    ¬ ∃ e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)),
      p ∈ e.source := by
  -- Any such chart would force the boundary-face point into the model-range interior.
  rintro ⟨e, hpe⟩
  have hpInterior := mem_interior_halfSpace_of_mem_euclideanChart p e hpe
  rw [interior_range_modelWithCornersEuclideanHalfSpace] at hpInterior
  -- Interior membership gives a strictly positive normal coordinate, contradicting `hp`.
  have hpPositive : 0 < (𝓡∂ 2) p 0 := hpInterior
  rw [hp] at hpPositive
  exact (lt_irrefl 0) hpPositive

/-- A boundary point of `EuclideanHalfSpace 2` has no neighborhood homeomorphic to an open
subset of `ℝ²`. -/
theorem isBoundaryPoint_hasNoEuclideanChart
    (p : EuclideanHalfSpace 2) (hp : (𝓡∂ 2).IsBoundaryPoint p) :
    ¬ ∃ e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)),
      p ∈ e.source := by
  exact boundaryFace_hasNoEuclideanChart p ((halfSpace_isBoundaryPoint_iff p).mp hp)

/-- Exercise 78.2 (2). A point of a surface with boundary belongs to its boundary exactly
when a half-space chart sends it to the boundary face. -/
theorem memBoundary_iff_exists_halfSpaceChart
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    [IsManifold (𝓡∂ 2) 0 X] [T2Space X] [SecondCountableTopology X] (x : X) :
    x ∈ ∂X ↔
      ∃ e : OpenPartialHomeomorph X (EuclideanHalfSpace 2),
        x ∈ e.source ∧ (𝓡∂ 2) (e x) 0 = 0 := by
  constructor
  · intro hx
    -- The canonical chart contains `x`.
    -- Boundary membership locates its image on the half-space face.
    let e : OpenPartialHomeomorph X (EuclideanHalfSpace 2) :=
      chartAt (EuclideanHalfSpace 2) x
    have hxSource : x ∈ e.source := by
      dsimp only [e]
      exact mem_chart_source (EuclideanHalfSpace 2) x
    refine Exists.intro e ?_
    constructor
    · exact hxSource
    · have hxBoundary : (𝓡∂ 2).IsBoundaryPoint x := hx
      rw [ModelWithCorners.isBoundaryPoint_iff,
        frontier_range_modelWithCornersEuclideanHalfSpace] at hxBoundary
      simp only [Set.mem_setOf_eq, extChartAt_coe, Function.comp_apply] at hxBoundary
      dsimp only [e]
      exact hxBoundary.symm
  · rintro ⟨e, hxe, hface⟩
    -- A Euclidean chart at `x` would pull back along `e.symm` to one at the boundary-face point.
    rw [mem_surfaceBoundary_iff_noEuclideanChart]
    rintro ⟨d, hxd⟩
    have hNoChart := boundaryFace_hasNoEuclideanChart (e x) hface
    apply hNoChart
    refine Exists.intro (e.symm.trans d) ?_
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · exact e.map_source hxe
    · have hleft : e.symm (e x) = x := e.left_inv hxe
      have hpreimage : e.symm (e x) ∈ d.source := by
        rw [hleft]
        exact hxd
      exact hpreimage

/-- Helper for Exercise 78.2: every half-space chart sends a boundary point in its source to the
boundary face of the model half-space. -/
private lemma halfSpaceChart_image_boundaryFace
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    [IsManifold (𝓡∂ 2) 0 X] (x : X) (hx : x ∈ ∂X)
    (e : atlas (EuclideanHalfSpace 2) X) (hxe : x ∈ e.1.source) :
    (𝓡∂ 2) (e.1 x) 0 = 0 := by
  -- A positive normal coordinate would compose with the model interior chart to give a
  -- Euclidean chart at the purported boundary point.
  by_contra hface
  have hnonnegative : 0 ≤ (𝓡∂ 2) (e.1 x) 0 := (e.1 x).property
  have hzeroNe : 0 ≠ (𝓡∂ 2) (e.1 x) 0 := fun hzero ↦ hface hzero.symm
  have hpositive : 0 < (𝓡∂ 2) (e.1 x) 0 := lt_of_le_of_ne hnonnegative hzeroNe
  have hinterior : (𝓡∂ 2) (e.1 x) ∈ interior (Set.range (𝓡∂ 2)) := by
    rw [interior_range_modelWithCornersEuclideanHalfSpace]
    exact hpositive
  have htransSource : x ∈ (e.1.trans halfSpaceInteriorPartialHomeomorph).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hxe, hinterior⟩
  have hNoEuclideanChart := (mem_surfaceBoundary_iff_noEuclideanChart x).mp hx
  exact hNoEuclideanChart ⟨e.1.trans halfSpaceInteriorPartialHomeomorph, htransSource⟩

/-- A point of a surface with boundary lies in its manifold boundary exactly when some
half-space chart sends it to a boundary point of the canonical model with corners. -/
theorem memBoundary_iff_exists_boundaryPoint_chart
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    [IsManifold (𝓡∂ 2) 0 X] [T2Space X] [SecondCountableTopology X] (x : X) :
    x ∈ ∂X ↔
      ∃ e : OpenPartialHomeomorph X (EuclideanHalfSpace 2),
        x ∈ e.source ∧ (𝓡∂ 2).IsBoundaryPoint (e x) := by
  rw [memBoundary_iff_exists_halfSpaceChart]
  exact exists_congr fun e ↦ and_congr_right fun _ ↦ (halfSpace_isBoundaryPoint_iff (e x)).symm

namespace Surface.boundary

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]

/-- Helper for Exercise 78.2: forget the normal coordinate on the boundary face of
`EuclideanHalfSpace 2`. -/
noncomputable def faceProjection (p : EuclideanHalfSpace 2) :
    EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm
    (Fin.tail (EuclideanSpace.equiv (Fin 2) ℝ p.1))

/-- Helper for Exercise 78.2: the vector obtained by adjoining a zero normal coordinate belongs
to `EuclideanHalfSpace 2`. -/
private lemma faceInclusion_mem (y : EuclideanSpace ℝ (Fin 1)) :
    0 ≤ ((EuclideanSpace.equiv (Fin 2) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin 1) ℝ y))) 0 := by
  simp

/-- Helper for Exercise 78.2: include `EuclideanSpace ℝ (Fin 1)` as the boundary face of
`EuclideanHalfSpace 2`. -/
noncomputable def faceInclusion (y : EuclideanSpace ℝ (Fin 1)) : EuclideanHalfSpace 2 :=
  ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm
      (Fin.cons 0 (EuclideanSpace.equiv (Fin 1) ℝ y)), faceInclusion_mem y⟩

/-- Helper for Exercise 78.2: projecting after including a point of the boundary face is the
identity. -/
private lemma faceProjection_faceInclusion (y : EuclideanSpace ℝ (Fin 1)) :
    faceProjection (faceInclusion y) = y := by
  apply (EuclideanSpace.equiv (Fin 1) ℝ).injective
  rw [faceProjection, ContinuousLinearEquiv.apply_symm_apply]
  rw [faceInclusion, ContinuousLinearEquiv.apply_symm_apply]
  simp only [Fin.tail_cons]

/-- Helper for Exercise 78.2: a two-coordinate vector with zero head is reconstructed by
adjoining zero to its tail. -/
private lemma finCons_zero_tail_eq_of_head_eq_zero (v : Fin 2 → ℝ) (hv : v 0 = 0) :
    Fin.cons 0 (Fin.tail v) = v := by
  calc
    Fin.cons 0 (Fin.tail v) = Fin.cons (v 0) (Fin.tail v) :=
      congrArg (fun a ↦ Fin.cons a (Fin.tail v)) hv.symm
    _ = v := Fin.cons_self_tail v

/-- Helper for Exercise 78.2: including the projection of a point on the boundary face recovers
that point. -/
private lemma faceInclusion_faceProjection (p : EuclideanHalfSpace 2)
    (hp : (𝓡∂ 2) p 0 = 0) :
    faceInclusion (faceProjection p) = p := by
  apply Subtype.ext
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  rw [faceInclusion, ContinuousLinearEquiv.apply_symm_apply]
  rw [faceProjection, ContinuousLinearEquiv.apply_symm_apply]
  have hhead : (EuclideanSpace.equiv (Fin 2) ℝ p.1) 0 = 0 := hp
  exact finCons_zero_tail_eq_of_head_eq_zero (EuclideanSpace.equiv (Fin 2) ℝ p.1) hhead

/-- Helper for Exercise 78.2: every included point has zero normal coordinate. -/
private lemma faceInclusion_normal (y : EuclideanSpace ℝ (Fin 1)) :
    (𝓡∂ 2) (faceInclusion y) 0 = 0 := by
  change (EuclideanSpace.equiv (Fin 2) ℝ (faceInclusion y).1) 0 = 0
  rw [faceInclusion, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Helper for Exercise 78.2: projection from the half-space boundary face is continuous. -/
private lemma continuous_faceProjection : Continuous faceProjection := by
  unfold faceProjection
  fun_prop

/-- Helper for Exercise 78.2: inclusion into the half-space boundary face is continuous. -/
private lemma continuous_faceInclusion : Continuous faceInclusion := by
  unfold faceInclusion
  fun_prop

/-- Helper for Exercise 78.2: the inverse image under an ambient chart of an included face point
in the chart target belongs to the surface boundary. -/
private lemma chartSymm_faceInclusion_mem_boundary [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (e : atlas (EuclideanHalfSpace 2) X) (y : EuclideanSpace ℝ (Fin 1))
    (hy : faceInclusion y ∈ e.1.target) :
    e.1.symm (faceInclusion y) ∈ ∂X := by
  apply (memBoundary_iff_exists_halfSpaceChart (e.1.symm (faceInclusion y))).2
  refine ⟨e.1, e.1.map_target hy, ?_⟩
  rw [e.1.right_inv hy]
  exact faceInclusion_normal y

/-- Helper for Exercise 78.2: a boundary chart inverse agrees with the ambient inverse on its
target and uses the chart center elsewhere. -/
noncomputable def chartInv [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X)
    (y : EuclideanSpace ℝ (Fin 1)) : ∂X :=
  @dite (∂X) (faceInclusion y ∈ e.1.target) (Classical.propDecidable _)
    (fun hy ↦ ⟨e.1.symm (faceInclusion y), chartSymm_faceInclusion_mem_boundary e y hy⟩)
    (fun _ ↦ x)

/-- Helper for Exercise 78.2: the boundary-chart forward map sends its source into its target. -/
private lemma chart_map_source [IsManifold (𝓡∂ 2) 0 X]
    (_x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) (z : ∂X)
    (hz : z ∈ {z : ∂X | z.1 ∈ e.1.source}) :
    faceProjection (e.1 z.1) ∈ {y | faceInclusion y ∈ e.1.target} := by
  have hface : (𝓡∂ 2) (e.1 z.1) 0 = 0 :=
    halfSpaceChart_image_boundaryFace z.1 z.2 e hz
  rw [Set.mem_setOf_eq, faceInclusion_faceProjection (e.1 z.1) hface]
  exact e.1.map_source hz

/-- Helper for Exercise 78.2: the boundary-chart inverse sends its target into its source. -/
private lemma chart_map_target [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) (y : EuclideanSpace ℝ (Fin 1))
    (hy : y ∈ {y | faceInclusion y ∈ e.1.target}) :
    chartInv x e y ∈ {z : ∂X | z.1 ∈ e.1.source} := by
  simp only [Set.mem_setOf_eq] at hy ⊢
  rw [chartInv, dif_pos hy]
  exact e.1.map_target hy

/-- Helper for Exercise 78.2: the boundary-chart inverse is a left inverse on the chart source. -/
private lemma chart_left_inv [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) (z : ∂X)
    (hz : z ∈ {z : ∂X | z.1 ∈ e.1.source}) :
    chartInv x e (faceProjection (e.1 z.1)) = z := by
  have hface : (𝓡∂ 2) (e.1 z.1) 0 = 0 :=
    halfSpaceChart_image_boundaryFace z.1 z.2 e hz
  have htarget : faceInclusion (faceProjection (e.1 z.1)) ∈ e.1.target := by
    rw [faceInclusion_faceProjection (e.1 z.1) hface]
    exact e.1.map_source hz
  -- Reduce to the ambient chart inverse law after reconstructing the face point.
  apply Subtype.ext
  simp only [chartInv, dif_pos htarget, Subtype.coe_mk]
  calc
    e.1.symm (faceInclusion (faceProjection (e.1 z.1))) = e.1.symm (e.1 z.1) :=
      congrArg e.1.symm (faceInclusion_faceProjection (e.1 z.1) hface)
    _ = z.1 := e.1.left_inv hz

/-- Helper for Exercise 78.2: the boundary-chart forward map is a right inverse on the chart
target. -/
private lemma chart_right_inv [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) (y : EuclideanSpace ℝ (Fin 1))
    (hy : y ∈ {y | faceInclusion y ∈ e.1.target}) :
    faceProjection (e.1 (chartInv x e y).1) = y := by
  simp only [Set.mem_setOf_eq] at hy
  rw [chartInv, dif_pos hy, e.1.right_inv hy]
  exact faceProjection_faceInclusion y

/-- Helper for Exercise 78.2: the source of a boundary chart is open in the boundary subtype. -/
private lemma chart_open_source (e : atlas (EuclideanHalfSpace 2) X) :
    IsOpen {z : ∂X | z.1 ∈ e.1.source} :=
  e.1.open_source.preimage continuous_subtype_val

/-- Helper for Exercise 78.2: the target of a boundary chart is open in
`EuclideanSpace ℝ (Fin 1)`. -/
private lemma chart_open_target (e : atlas (EuclideanHalfSpace 2) X) :
    IsOpen {y : EuclideanSpace ℝ (Fin 1) | faceInclusion y ∈ e.1.target} :=
  e.1.open_target.preimage continuous_faceInclusion

/-- Helper for Exercise 78.2: the forward map of a boundary chart is continuous on its source. -/
private lemma chart_continuousOn_toFun [IsManifold (𝓡∂ 2) 0 X]
    (e : atlas (EuclideanHalfSpace 2) X) :
    ContinuousOn (fun z : ∂X ↦ faceProjection (e.1 z.1))
      {z : ∂X | z.1 ∈ e.1.source} := by
  apply continuous_faceProjection.comp_continuousOn'
  exact e.1.continuousOn.comp continuous_subtype_val.continuousOn fun z hz ↦ hz

/-- Helper for Exercise 78.2: the inverse map of a boundary chart is continuous on its target. -/
private lemma chart_continuousOn_invFun [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) :
    ContinuousOn (chartInv x e) {y | faceInclusion y ∈ e.1.target} := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  apply ContinuousOn.congr
      (e.1.continuousOn_symm.comp continuous_faceInclusion.continuousOn fun y hy ↦ hy)
  intro y hy
  change faceInclusion y ∈ e.1.target at hy
  simp only [Function.comp_apply, chartInv, dif_pos hy, Subtype.coe_mk]

/-- Helper for Exercise 78.2: a half-space chart centered at a boundary point restricts to a
one-dimensional boundary chart. -/
noncomputable def chart [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X]
    (x : ∂X) (e : atlas (EuclideanHalfSpace 2) X) :
    OpenPartialHomeomorph (∂X) (EuclideanSpace ℝ (Fin 1)) where
  toFun z := faceProjection (e.1 z.1)
  invFun := chartInv x e
  source := {z | z.1 ∈ e.1.source}
  target := {y | faceInclusion y ∈ e.1.target}
  map_source' := chart_map_source x e
  map_target' := chart_map_target x e
  left_inv' := chart_left_inv x e
  right_inv' := chart_right_inv x e
  continuousOn_toFun := chart_continuousOn_toFun e
  continuousOn_invFun := chart_continuousOn_invFun x e
  open_source := chart_open_source e
  open_target := chart_open_target e

/-- Helper for Exercise 78.2: the preferred boundary chart contains its center. -/
lemma mem_boundaryChart_source [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X] (x : ∂X) :
    x ∈ (chart x (achart (EuclideanHalfSpace 2) x.1)).source :=
  mem_chart_source (EuclideanHalfSpace 2) x.1

/-- Helper for Exercise 78.2: every preferred boundary chart belongs to the boundary atlas. -/
lemma boundaryChart_mem_atlas [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X] (x : ∂X) :
    chart x (achart (EuclideanHalfSpace 2) x.1) ∈
      Set.range (fun z : ∂X ↦ chart z (achart (EuclideanHalfSpace 2) z.1)) :=
  Set.mem_range_self x

/-- Helper for Exercise 78.2: the boundary of a surface carries the atlas induced by its
half-space charts. -/
noncomputable instance instChartedSpace [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X] :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) (∂X) where
  atlas := Set.range fun x : ∂X ↦ chart x (achart (EuclideanHalfSpace 2) x.1)
  chartAt x := chart x (achart (EuclideanHalfSpace 2) x.1)
  mem_chart_source := mem_boundaryChart_source
  chart_mem_atlas := boundaryChart_mem_atlas

/-- Exercise 78.2 (3). The boundary of a topological surface with boundary is canonically a
topological one-dimensional manifold. -/
instance instIsManifold [IsManifold (𝓡∂ 2) 0 X] [T2Space X]
    [SecondCountableTopology X] : IsManifold (𝓡 1) 0 (∂X) := by
  infer_instance

end Surface.boundary

/- Exercise 78.2 (3). The boundary of a surface with boundary has its canonical structure of a
topological one-dimensional manifold. -/
#check fun (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 2) X] [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X] ↦
  (Surface.boundary.instIsManifold : IsManifold (𝓡 1) 0 (∂X))

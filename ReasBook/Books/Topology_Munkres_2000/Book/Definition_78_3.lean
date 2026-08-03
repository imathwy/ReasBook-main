module

public import Topology_Munkres_2000.Book.Definition_78_3.Boundary
public import Topology_Munkres_2000.Book.Theorem_62_3

open scoped Manifold SurfaceBoundary

public section

universe u

/-- Helper for Definition 78.3: the canonical half-space model maps its interior source to
the interior of its range. -/
private lemma halfSpaceInterior_map_source
    (p : EuclideanHalfSpace 2)
    (hp : p ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2) p ∈ interior (Set.range (𝓡∂ 2)) :=
  hp

/-- Helper for Definition 78.3: the inverse canonical half-space model maps the interior of
its range back to the interior source. -/
private lemma halfSpaceInterior_map_target
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2).symm y ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2)) := by
  -- First pass from the interior to the model range, where the inverse law applies.
  have hyRange : y ∈ Set.range (𝓡∂ 2) := interior_subset hy
  rw [Set.mem_preimage, (𝓡∂ 2).right_inv hyRange]
  exact hy

/-- Helper for Definition 78.3: the canonical half-space model inverse is a left inverse on
the interior source. -/
private lemma halfSpaceInterior_left_inv
    (p : EuclideanHalfSpace 2)
    (_hp : p ∈ (𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2).symm ((𝓡∂ 2) p) = p := by
  -- The global left-inverse law restricts directly to the chosen source.
  exact (𝓡∂ 2).left_inv p

/-- Helper for Definition 78.3: the canonical half-space model is a right inverse on the
interior of its range. -/
private lemma halfSpaceInterior_right_inv
    (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ interior (Set.range (𝓡∂ 2))) :
    (𝓡∂ 2) ((𝓡∂ 2).symm y) = y := by
  -- Interior membership supplies the range hypothesis of the global inverse law.
  exact (𝓡∂ 2).right_inv (interior_subset hy)

/-- Helper for Definition 78.3: the interior source of the canonical half-space model is
open. -/
private lemma isOpen_halfSpaceInterior_source :
    IsOpen ((𝓡∂ 2) ⁻¹' interior (Set.range (𝓡∂ 2))) :=
  isOpen_interior.preimage (𝓡∂ 2).continuous

/-- Helper for Definition 78.3: the interior of the canonical half-space model range is
open. -/
private lemma isOpen_halfSpaceInterior_target :
    IsOpen (interior (Set.range (𝓡∂ 2))) :=
  isOpen_interior

/-- Helper for Definition 78.3: the canonical model identifies the interior of
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

/-- Helper for Definition 78.3: a half-space point admitting a Euclidean chart maps into
the interior of the canonical model range. -/
private lemma mem_interior_halfSpace_of_mem_euclideanChart
    (p : EuclideanHalfSpace 2)
    (e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)))
    (hp : p ∈ e.source) :
    (𝓡∂ 2) p ∈ interior (Set.range (𝓡∂ 2)) := by
  -- Apply invariance of domain to the inverse chart in ambient Euclidean coordinates.
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
  -- The open image lies in the half-space model range and hence in its interior.
  have hRangeSubset : Set.range f ⊆ Set.range (𝓡∂ 2) := by
    intro z hz
    rcases hz with ⟨y, rfl⟩
    dsimp only [f]
    exact Set.mem_range_self (e.symm y)
  have hRangeInterior : Set.range f ⊆ interior (Set.range (𝓡∂ 2)) :=
    interior_maximal hRangeSubset hfOpen
  -- The inverse law places the chosen point in this open image.
  have hepTarget : e p ∈ e.target := e.map_source hp
  let ep : e.target := ⟨e p, hepTarget⟩
  have hpRange : (𝓡∂ 2) p ∈ Set.range f := by
    refine Set.mem_range.2 ?_
    use ep
    dsimp only [f, ep]
    rw [e.left_inv hp]
  exact hRangeInterior hpRange

/-- Helper for Definition 78.3: a half-space point is interior exactly when it admits a
Euclidean-plane chart. -/
private lemma halfSpaceInterior_iff_exists_euclideanChart
    (p : EuclideanHalfSpace 2) :
    (𝓡∂ 2) p ∈ interior (Set.range (𝓡∂ 2)) ↔
      ∃ e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanSpace ℝ (Fin 2)),
        p ∈ e.source := by
  constructor
  · intro hp
    -- Restricting the canonical model to its interior supplies the forward chart.
    exact ⟨halfSpaceInteriorPartialHomeomorph, hp⟩
  · rintro ⟨e, hp⟩
    -- Invariance of domain forces every Euclidean chart point into the model interior.
    exact mem_interior_halfSpace_of_mem_euclideanChart p e hp

/-- Helper for Definition 78.3: a point of a half-space-charted surface is a model interior
point exactly when it admits a Euclidean-plane chart. -/
private lemma surfaceIsInteriorPoint_iff_exists_euclideanChart
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    (x : X) :
    (𝓡∂ 2).IsInteriorPoint x ↔
      ∃ e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)), x ∈ e.source := by
  constructor
  · intro hx
    -- Read interiority in the preferred half-space chart, then append its Euclidean chart.
    have hChartInterior :
        (𝓡∂ 2) (chartAt (EuclideanHalfSpace 2) x x) ∈
          interior (Set.range (𝓡∂ 2)) := by
      simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, Function.comp_apply] using hx
    rcases (halfSpaceInterior_iff_exists_euclideanChart
      (chartAt (EuclideanHalfSpace 2) x x)).mp hChartInterior with ⟨e, he⟩
    refine ⟨(chartAt (EuclideanHalfSpace 2) x).trans e, ?_⟩
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source (EuclideanHalfSpace 2) x, he⟩
  · rintro ⟨e, hxe⟩
    -- Pull the Euclidean chart back through the inverse preferred chart.
    let c : OpenPartialHomeomorph X (EuclideanHalfSpace 2) :=
      chartAt (EuclideanHalfSpace 2) x
    have hxc : x ∈ c.source := by
      dsimp only [c]
      exact mem_chart_source (EuclideanHalfSpace 2) x
    have hcxTarget : c x ∈ c.target := c.map_source hxc
    have hcxSource : c x ∈ (c.symm.trans e).source := by
      rw [OpenPartialHomeomorph.trans_source]
      constructor
      · exact hcxTarget
      · have hpreimage : c.symm (c x) ∈ e.source := by
          rw [c.left_inv hxc]
          exact hxe
        exact hpreimage
    have hChartInterior :
        (𝓡∂ 2) (c x) ∈ interior (Set.range (𝓡∂ 2)) :=
      (halfSpaceInterior_iff_exists_euclideanChart (c x)).mpr ⟨c.symm.trans e, hcxSource⟩
    dsimp only [c] at hChartInterior
    simpa only [ModelWithCorners.IsInteriorPoint, extChartAt_coe, Function.comp_apply] using
      hChartInterior

/- Definition 78.3: The boundary `∂X` consists of the points having no neighborhood
homeomorphic to an open subset of `ℝ²`; its canonical realization is the
model-with-corners boundary for `EuclideanHalfSpace 2`. -/
#check fun (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 2) X] [IsManifold (𝓡∂ 2) 0 X]
    [T2Space X] [SecondCountableTopology X] ↦ ∂X

/-- A point of a surface with boundary lies in its boundary exactly when it has no
neighborhood homeomorphic to an open subset of `ℝ²`. -/
theorem mem_surfaceBoundary_iff_noEuclideanChart
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanHalfSpace 2) X]
    [IsManifold (𝓡∂ 2) 0 X] (x : X) :
    x ∈ ∂X ↔
      ¬ ∃ e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 2)), x ∈ e.source := by
  -- Boundary points are precisely the complement of the model interior points.
  exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint (I := 𝓡∂ 2) x).trans
    (not_congr (surfaceIsInteriorPoint_iff_exists_euclideanChart x))

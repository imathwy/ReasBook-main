import Mathlib.Geometry.Manifold.Bordism
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

open Set WithLp
open scoped Manifold

-- Semantic recall / analogue search: `lean_leansearch` surfaced `SingularManifold`,
-- `SingularManifold.sum`, `ModelWithCorners.boundary`, and `Diffeomorph`. Mathlib does not yet
-- expose a ready cobordism owner matching the source-facing disjoint-union presentation, so this
-- item keeps the boundary subtype and records the smooth boundary equivalence there directly.

/-- A closed smooth `n`-manifold, presented through the canonical mathlib owner
`SingularManifold PUnit ⊤ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))`. -/
structure ClosedSmoothManifold (n : ℕ) extends
    SingularManifold.{0} PUnit ⊤ (𝓡 n) where
  t2Space : T2Space M

/-- A closed smooth manifold carries the Hausdorff property on its underlying manifold type. -/
instance ClosedSmoothManifold.instT2Space {n : ℕ} (M : ClosedSmoothManifold n) : T2Space M.M :=
  M.t2Space

/-- A closed smooth manifold carries the topological-space structure of its underlying singular
manifold. -/
instance ClosedSmoothManifold.instTopologicalSpace {n : ℕ} (M : ClosedSmoothManifold n) :
    TopologicalSpace M.M :=
  M.toSingularManifold.topSpaceM

/-- A closed smooth manifold carries the canonical charted-space structure on its underlying
manifold type. -/
instance ClosedSmoothManifold.instChartedSpace {n : ℕ} (M : ClosedSmoothManifold n) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) M.M :=
  M.toSingularManifold.chartedSpace

/-- A closed smooth manifold is an `n`-dimensional smooth manifold on its underlying type. -/
instance ClosedSmoothManifold.instIsManifold {n : ℕ} (M : ClosedSmoothManifold n) :
    IsManifold (𝓡 n) ⊤ M.M :=
  M.toSingularManifold.isManifold

/-- A closed smooth manifold is compact on its underlying manifold type. -/
instance ClosedSmoothManifold.instCompactSpace {n : ℕ} (M : ClosedSmoothManifold n) :
    CompactSpace M.M :=
  M.toSingularManifold.compactSpace

/-- A closed smooth manifold is boundaryless on its underlying manifold type. -/
instance ClosedSmoothManifold.instBoundarylessManifold {n : ℕ} (M : ClosedSmoothManifold n) :
    BoundarylessManifold (𝓡 n) M.M :=
  M.toSingularManifold.boundaryless

/-- The disjoint union of two closed smooth `n`-manifolds is again a closed smooth
`n`-manifold. -/
noncomputable def ClosedSmoothManifold.sum {n : ℕ}
    (M N : ClosedSmoothManifold n) : ClosedSmoothManifold n where
  toSingularManifold := M.toSingularManifold.sum N.toSingularManifold
  t2Space := by
    simpa [SingularManifold.sum_M] using (inferInstance : T2Space (Sum M.M N.M))

/-- A boundary smooth structure on a compact smooth `(n + 1)`-manifold with boundary `W` is the
induced smooth `n`-manifold structure on the boundary subtype `(𝓡∂ (n + 1)).boundary W`. This is
the boundary owner needed by cobordism witnesses before the oriented boundary API is introduced. -/
abbrev BoundaryModel (n : ℕ) :=
  { y : EuclideanHalfSpace (n + 1) // y.1 0 = 0 }

/-- Helper for Definition 25.1.1: forget the distinguished boundary coordinate of a boundary-model
point. -/
noncomputable def boundaryModelToEuclidean (n : ℕ) :
    BoundaryModel n → EuclideanSpace ℝ (Fin n) :=
  fun y ↦ show EuclideanSpace ℝ (Fin n) from toLp 2 fun i ↦ y.1.1 (Fin.succ i)

/-- Helper for Definition 25.1.1: the inserted boundary coordinate is nonnegative. -/
lemma boundaryModelFromEuclidean_nonneg (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ (show EuclideanSpace ℝ (Fin (n + 1)) from toLp 2 (Fin.cons 0 v)) 0 := by
  simp

/-- Helper for Definition 25.1.1: the inserted boundary coordinate is exactly `0`. -/
lemma boundaryModelFromEuclidean_firstCoordinate_zero (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    ((⟨show EuclideanSpace ℝ (Fin (n + 1)) from toLp 2 (Fin.cons 0 v),
        boundaryModelFromEuclidean_nonneg n v⟩ : EuclideanHalfSpace (n + 1))).1 0 = 0 := by
  simp

/-- Helper for Definition 25.1.1: insert a zero boundary coordinate into `EuclideanSpace ℝ (Fin n)`.
-/
noncomputable def boundaryModelFromEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin n) → BoundaryModel n :=
  fun v ↦
    ⟨⟨show EuclideanSpace ℝ (Fin (n + 1)) from toLp 2 (Fin.cons 0 v),
        boundaryModelFromEuclidean_nonneg n v⟩,
      boundaryModelFromEuclidean_firstCoordinate_zero n v⟩

/-- Helper for Definition 25.1.1: deleting and then reinserting the boundary coordinate recovers
the original boundary-model point. -/
lemma boundaryModelFromEuclidean_left_inverse (n : ℕ) :
    Function.LeftInverse (boundaryModelFromEuclidean n) (boundaryModelToEuclidean n) := by
  intro y
  -- Compare coordinates in the half-space model.
  apply Subtype.ext
  apply EuclideanHalfSpace.ext
  ext i
  cases i using Fin.cases with
  | zero =>
      simp [boundaryModelFromEuclidean, boundaryModelToEuclidean, y.2]
  | succ i =>
      simp [boundaryModelFromEuclidean, boundaryModelToEuclidean]

/-- Helper for Definition 25.1.1: reinserting and then deleting the boundary coordinate recovers
the original Euclidean vector. -/
lemma boundaryModelFromEuclidean_right_inverse (n : ℕ) :
    Function.RightInverse (boundaryModelFromEuclidean n) (boundaryModelToEuclidean n) := by
  intro v
  -- The surviving coordinates are untouched by the insertion.
  ext i
  simp [boundaryModelFromEuclidean, boundaryModelToEuclidean]

/-- Helper for Definition 25.1.1: deleting the boundary coordinate varies continuously. -/
lemma continuous_boundaryModelToEuclidean (n : ℕ) :
    Continuous (boundaryModelToEuclidean n) := by
  -- The target is assembled coordinatewise from the ambient half-space coordinates.
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact continuous_pi fun i ↦
    (PiLp.continuous_apply 2 _ (Fin.succ i)).comp
      (continuous_subtype_val.comp continuous_subtype_val)

/-- Helper for Definition 25.1.1: inserting a zero boundary coordinate is continuous. -/
lemma continuous_boundaryModelFromEuclidean (n : ℕ) :
    Continuous (boundaryModelFromEuclidean n) := by
  -- The insertion map is coordinatewise continuous, then cod-restricted twice.
  refine Continuous.subtype_mk ?_ ?_
  refine Continuous.subtype_mk ?_ ?_
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact continuous_pi fun i ↦ by
    cases i using Fin.cases with
    | zero =>
        simpa using
          (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
    | succ i =>
        simpa using (PiLp.continuous_apply 2 _ i)

/-- The boundary hyperplane in `EuclideanHalfSpace (n + 1)` is canonically homeomorphic to
`EuclideanSpace ℝ (Fin n)` by deleting the distinguished boundary coordinate. -/
noncomputable def boundaryModelHomeomorph
    (n : ℕ) : BoundaryModel n ≃ₜ EuclideanSpace ℝ (Fin n) where
  toFun := boundaryModelToEuclidean n
  invFun := boundaryModelFromEuclidean n
  left_inv := boundaryModelFromEuclidean_left_inverse n
  right_inv := boundaryModelFromEuclidean_right_inverse n
  continuous_toFun := continuous_boundaryModelToEuclidean n
  continuous_invFun := continuous_boundaryModelFromEuclidean n

section BoundarySmoothStructureAPI

variable {n : ℕ} {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
variable [IsManifold (𝓡∂ (n + 1)) ⊤ W]

noncomputable abbrev boundaryAmbientChart (x : ((𝓡∂ (n + 1)).boundary W)) :
    OpenPartialHomeomorph W (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

noncomputable def boundaryChartTarget (x : ((𝓡∂ (n + 1)).boundary W)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (boundaryModelHomeomorph n).symm ⁻¹'
    { y : BoundaryModel n | y.1 ∈ (boundaryAmbientChart x).target }

lemma boundaryChart_firstCoordinate_zero (x z : ((𝓡∂ (n + 1)).boundary W))
    (hz : z.1 ∈ (boundaryAmbientChart x).source) :
    0 = ((boundaryAmbientChart x z.1) : EuclideanHalfSpace (n + 1)).1 0 := by
  let e := boundaryAmbientChart x
  have hz_frontier :
      e.extend (𝓡∂ (n + 1)) z.1 ∈ frontier (e.extend (𝓡∂ (n + 1))).target :=
    by
      simpa [boundaryAmbientChart] using
        ((𝓡∂ (n + 1)).isBoundaryPoint_iff_of_mem_atlas
          (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
          (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1)
          (by simpa [boundaryAmbientChart] using hz)).1 z.2
  have hz_target : (e z.1 : EuclideanHalfSpace (n + 1)) ∈ e.target :=
    e.map_source hz
  have h_not_mem_interior_range :
      e.extend (𝓡∂ (n + 1)) z.1 ∉ interior (Set.range (𝓡∂ (n + 1))) := by
    intro hz_int
    have hz_int_target :
        e.extend (𝓡∂ (n + 1)) z.1 ∈ interior (e.extend (𝓡∂ (n + 1))).target :=
      e.mem_interior_extend_target hz_target hz_int
    have hz_not_int_target :
        e.extend (𝓡∂ (n + 1)) z.1 ∉ interior (e.extend (𝓡∂ (n + 1))).target := by
      rw [frontier] at hz_frontier
      exact hz_frontier.2
    exact hz_not_int_target hz_int_target
  have h_not_pos : ¬ 0 < ((e z.1 : EuclideanHalfSpace (n + 1)).1 0) := by
    intro hpos
    apply h_not_mem_interior_range
    simpa [OpenPartialHomeomorph.extend_coe, interior_range_modelWithCornersEuclideanHalfSpace]
      using hpos
  have h_nonneg : 0 ≤ ((e z.1 : EuclideanHalfSpace (n + 1)).1 0) :=
    (e z.1).2
  linarith

lemma boundaryPoint_of_boundaryModelTarget (x : ((𝓡∂ (n + 1)).boundary W))
    {v : BoundaryModel n}
    (hv : v.1 ∈ (boundaryAmbientChart x).target) :
    (𝓡∂ (n + 1)).IsBoundaryPoint
      ((boundaryAmbientChart x).symm v.1) := by
  let e := boundaryAmbientChart x
  have hv_source : e.symm v.1 ∈ e.source :=
    e.map_target hv
  have hv_target :
      e.extend (𝓡∂ (n + 1)) (e.symm v.1) ∈ (e.extend (𝓡∂ (n + 1))).target :=
    (e.extend (𝓡∂ (n + 1))).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hv_source
  have h_not_mem_interior_target :
      e.extend (𝓡∂ (n + 1)) (e.symm v.1) ∉ interior (e.extend (𝓡∂ (n + 1))).target := by
    intro hv_int
    have hv_int_range :
        e.extend (𝓡∂ (n + 1)) (e.symm v.1) ∈ interior (Set.range (𝓡∂ (n + 1))) :=
      e.interior_extend_target_subset_interior_range hv_int
    have h_zero :
        0 = ((e (e.symm v.1) : EuclideanHalfSpace (n + 1)).1 0) := by
      simpa [eq_comm, e.right_inv hv] using v.2
    have h_not_pos : ¬ 0 < ((e (e.symm v.1) : EuclideanHalfSpace (n + 1)).1 0) := by
      linarith
    exact h_not_pos <| by
      simpa [OpenPartialHomeomorph.extend_coe, interior_range_modelWithCornersEuclideanHalfSpace]
        using hv_int_range
  have hv_frontier :
      e.extend (𝓡∂ (n + 1)) (e.symm v.1) ∈ frontier (e.extend (𝓡∂ (n + 1))).target := by
    rw [frontier]
    exact ⟨subset_closure hv_target, h_not_mem_interior_target⟩
  simpa [boundaryAmbientChart] using
    ((𝓡∂ (n + 1)).isBoundaryPoint_iff_of_mem_atlas
      (by simp : (⊤ : WithTop ℕ∞) ≠ 0)
      (chart_mem_atlas (EuclideanHalfSpace (n + 1)) x.1)
      (by simpa [boundaryAmbientChart] using hv_source)).2 hv_frontier

/-- Helper for Definition 25.1.1: on the ambient preferred chart source, being a boundary point is
equivalent to lying on the half-space boundary slice `x₀ = 0`. -/
lemma boundaryAmbientChart_boundary_iff_firstCoordinate_zero
    (x : ((𝓡∂ (n + 1)).boundary W)) {z : W}
    (hz : z ∈ (boundaryAmbientChart x).source) :
    (𝓡∂ (n + 1)).IsBoundaryPoint z ↔
      0 = ((boundaryAmbientChart x z : EuclideanHalfSpace (n + 1)).1 0) := by
  constructor
  · intro hz_boundary
    -- Upgrade `z` to the boundary subtype and reuse the boundary-coordinate lemma there.
    let zBoundary : ((𝓡∂ (n + 1)).boundary W) := ⟨z, hz_boundary⟩
    simpa [zBoundary] using boundaryChart_firstCoordinate_zero x zBoundary hz
  · intro hz_zero
    -- Package the chart image as a boundary-model point and pull it back through the chart.
    let v : BoundaryModel n := ⟨boundaryAmbientChart x z, hz_zero.symm⟩
    have hv : v.1 ∈ (boundaryAmbientChart x).target := by
      simpa [v] using (boundaryAmbientChart x).map_source hz
    simpa [v, (boundaryAmbientChart x).left_inv hz] using
      boundaryPoint_of_boundaryModelTarget x hv

omit [IsManifold (𝓡∂ (n + 1)) ⊤ W] in
/-- Helper for Definition 25.1.1: the target condition is exactly the ambient-target condition
transported through `boundaryModelHomeomorph`. -/
lemma boundaryChartTarget_mem_iff (x : ((𝓡∂ (n + 1)).boundary W))
    (v : EuclideanSpace ℝ (Fin n)) :
    v ∈ boundaryChartTarget x ↔
      ((boundaryModelHomeomorph n).symm v).1 ∈ (boundaryAmbientChart x).target := by
  simp [boundaryChartTarget]

/-- Helper for Definition 25.1.1: the source of the induced boundary chart is the ambient chart
source restricted to the boundary subtype. -/
def boundaryChartSourceSet (x : ((𝓡∂ (n + 1)).boundary W)) :
    Set ((𝓡∂ (n + 1)).boundary W) :=
  { z | z.1 ∈ (boundaryAmbientChart x).source }

omit [IsManifold (𝓡∂ (n + 1)) ⊤ W] in
/-- Helper for Definition 25.1.1: the restricted boundary-chart source is open in the boundary
subtype. -/
lemma isOpen_boundaryChartSourceSet (x : ((𝓡∂ (n + 1)).boundary W)) :
    IsOpen (boundaryChartSourceSet x) := by
  -- The source is the preimage of the ambient open source under the boundary inclusion.
  simpa [boundaryChartSourceSet] using
    (boundaryAmbientChart x).open_source.preimage continuous_subtype_val

/-- Helper for Definition 25.1.1: the restricted boundary-chart source packaged as an open set. -/
noncomputable def boundaryChartSourceOpens (x : ((𝓡∂ (n + 1)).boundary W)) :
    TopologicalSpace.Opens ((𝓡∂ (n + 1)).boundary W) :=
  ⟨boundaryChartSourceSet x, isOpen_boundaryChartSourceSet x⟩

omit [IsManifold (𝓡∂ (n + 1)) ⊤ W] in
/-- Helper for Definition 25.1.1: the induced boundary-chart target is open in
`EuclideanSpace ℝ (Fin n)`. -/
lemma isOpen_boundaryChartTarget (x : ((𝓡∂ (n + 1)).boundary W)) :
    IsOpen (boundaryChartTarget x) := by
  let s : Set (BoundaryModel n) :=
    { y | y.1 ∈ (boundaryAmbientChart x).target }
  have hs : IsOpen s := by
    -- The target condition is just openness pulled back along the boundary-model projection.
    let f : BoundaryModel n → EuclideanHalfSpace (n + 1) := fun y ↦ y.1
    have hf : Continuous f := by
      simpa [f] using (continuous_subtype_val :
        Continuous fun y : BoundaryModel n ↦ (y : EuclideanHalfSpace (n + 1)))
    simpa [s, f] using (boundaryAmbientChart x).open_target.preimage hf
  change IsOpen (((boundaryModelHomeomorph n).symm) ⁻¹' s)
  simpa [s] using ((boundaryModelHomeomorph n).symm.continuous.isOpen_preimage s hs)

/-- Helper for Definition 25.1.1: the induced boundary-chart target packaged as an open set. -/
noncomputable def boundaryChartTargetOpens (x : ((𝓡∂ (n + 1)).boundary W)) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨boundaryChartTarget x, isOpen_boundaryChartTarget x⟩

omit [IsManifold (𝓡∂ (n + 1)) ⊤ W] in
/-- Helper for Definition 25.1.1: the preferred boundary point itself lies in the boundary-chart
source. -/
lemma boundaryChartSourceOpens_nonempty (x : ((𝓡∂ (n + 1)).boundary W)) :
    Nonempty (boundaryChartSourceOpens x) := by
  -- The preferred ambient chart is defined at its base point.
  refine ⟨⟨x, ?_⟩⟩
  change x ∈ boundaryChartSourceSet x
  simpa only [boundaryChartSourceSet] using
    (mem_chart_source (EuclideanHalfSpace (n + 1)) x.1)

/-- Helper for Definition 25.1.1: the forward boundary-chart map lands in the transported target
open set. -/
lemma boundaryChartSourceForward_mem (x : ((𝓡∂ (n + 1)).boundary W))
    (z : boundaryChartSourceOpens x) :
    boundaryModelHomeomorph n
        ⟨boundaryAmbientChart x z.1.1,
          (boundaryChart_firstCoordinate_zero x z.1 z.2).symm⟩ ∈
      boundaryChartTarget x := by
  -- Unfold the target once and use that the ambient chart sends source to target.
  rw [boundaryChartTarget_mem_iff]
  simpa using (boundaryAmbientChart x).map_source z.2

/-- Helper for Definition 25.1.1: evaluate the ambient chart on the boundary source and drop the
distinguished boundary coordinate. -/
noncomputable def boundaryChartSourceForward (x : ((𝓡∂ (n + 1)).boundary W)) :
    boundaryChartSourceOpens x → boundaryChartTargetOpens x :=
  fun z ↦
    ⟨boundaryModelHomeomorph n
        ⟨boundaryAmbientChart x z.1.1,
          (boundaryChart_firstCoordinate_zero x z.1 z.2).symm⟩,
      boundaryChartSourceForward_mem x z⟩

omit [IsManifold (𝓡∂ (n + 1)) ⊤ W] in
/-- Helper for Definition 25.1.1: the inverse boundary-chart map first reinserts the boundary
coordinate and then applies the inverse ambient chart. -/
lemma boundaryChartSourceInverseTargetMem
    (x : ((𝓡∂ (n + 1)).boundary W)) (v : boundaryChartTargetOpens x) :
    ((boundaryModelHomeomorph n).symm v.1).1 ∈ (boundaryAmbientChart x).target :=
  (boundaryChartTarget_mem_iff (x := x) v.1).1 v.2

/-- Helper for Definition 25.1.1: pull a target point back to the boundary subtype. -/
noncomputable def boundaryChartSourceInverse (x : ((𝓡∂ (n + 1)).boundary W)) :
    boundaryChartTargetOpens x → boundaryChartSourceOpens x :=
  fun v ↦
    ⟨⟨(boundaryAmbientChart x).symm ((boundaryModelHomeomorph n).symm v.1).1,
        boundaryPoint_of_boundaryModelTarget x
          (boundaryChartSourceInverseTargetMem x v)⟩,
      (boundaryAmbientChart x).map_target (boundaryChartSourceInverseTargetMem x v)⟩

/-- Helper for Definition 25.1.1: the forward and inverse boundary-source maps are mutual
inverses on the source open set. -/
lemma boundaryChartSourceLeftInv (x : ((𝓡∂ (n + 1)).boundary W)) :
    Function.LeftInverse (boundaryChartSourceInverse x) (boundaryChartSourceForward x) := by
  intro z
  -- Both nested subtype layers reduce to the ambient chart left inverse.
  apply Subtype.ext
  apply Subtype.ext
  simpa [boundaryChartSourceForward, boundaryChartSourceInverse,
    boundaryChartSourceInverseTargetMem] using
    (boundaryAmbientChart x).left_inv z.2

/-- Helper for Definition 25.1.1: the forward and inverse boundary-source maps are mutual
inverses on the target open set. -/
lemma boundaryChartSourceRightInv (x : ((𝓡∂ (n + 1)).boundary W)) :
    Function.RightInverse (boundaryChartSourceInverse x) (boundaryChartSourceForward x) := by
  intro v
  let y : BoundaryModel n := (boundaryModelHomeomorph n).symm v.1
  have hy_target : y.1 ∈ (boundaryAmbientChart x).target :=
    boundaryChartSourceInverseTargetMem x v
  have hy_zero :
      (boundaryAmbientChart x ((boundaryAmbientChart x).symm y.1) :
        EuclideanHalfSpace (n + 1)).1 0 = 0 := by
    -- The inverse ambient chart lands back on the original boundary-model point.
    simpa [y, (boundaryAmbientChart x).right_inv hy_target] using y.2
  have hy_boundaryModel :
      (⟨boundaryAmbientChart x ((boundaryAmbientChart x).symm y.1), hy_zero⟩ :
        BoundaryModel n) = y := by
    -- The ambient chart right inverse identifies the boundary-model point uniquely.
    apply Subtype.ext
    simpa [y] using (boundaryAmbientChart x).right_inv hy_target
  apply Subtype.ext
  -- Push the BoundaryModel equality forward through `boundaryModelHomeomorph`.
  simpa [boundaryChartSourceForward, boundaryChartSourceInverse, y] using
    congrArg (boundaryModelHomeomorph n) hy_boundaryModel

/-- Helper for Definition 25.1.1: the forward boundary-source map is continuous. -/
lemma continuous_boundaryChartSourceForward (x : ((𝓡∂ (n + 1)).boundary W)) :
    Continuous (boundaryChartSourceForward (n := n) x) := by
  have hchart :
      Continuous fun z : boundaryChartSourceOpens x ↦
        (boundaryAmbientChart x) z.1.1 := by
    -- The ambient chart is continuous on its source, and every point in the source-open subtype
    -- satisfies that source condition by construction.
    exact (boundaryAmbientChart x).continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun z ↦ z.2
  have hboundaryModel :
      Continuous fun z : boundaryChartSourceOpens x ↦
        (⟨boundaryAmbientChart x z.1.1,
          (boundaryChart_firstCoordinate_zero x z.1 z.2).symm⟩ : BoundaryModel n) := by
    -- The boundary slice condition is bundled into the codomain subtype.
    exact Continuous.subtype_mk hchart fun z ↦
      (boundaryChart_firstCoordinate_zero x z.1 z.2).symm
  exact Continuous.subtype_mk
    ((boundaryModelHomeomorph n).continuous_toFun.comp hboundaryModel)
    (boundaryChartSourceForward_mem x)

/-- Helper for Definition 25.1.1: the inverse boundary-source map is continuous. -/
lemma continuous_boundaryChartSourceInverse (x : ((𝓡∂ (n + 1)).boundary W)) :
    Continuous (boundaryChartSourceInverse (n := n) x) := by
  have hboundaryModel :
      Continuous fun v : boundaryChartTargetOpens x ↦
        (((boundaryModelHomeomorph n).symm v.1 : BoundaryModel n).1) := by
    -- First move back to the boundary model, then forget the subtype wrapper once.
    exact continuous_subtype_val.comp
      ((boundaryModelHomeomorph n).continuous_invFun.comp continuous_subtype_val)
  have hambient :
      Continuous fun v : boundaryChartTargetOpens x ↦
        (boundaryAmbientChart x).symm (((boundaryModelHomeomorph n).symm v.1).1) := by
    -- The inverse ambient chart is continuous on its target, and our points lie there by design.
    exact (boundaryAmbientChart x).continuousOn_symm.comp_continuous hboundaryModel
      (boundaryChartSourceInverseTargetMem x)
  have hboundary :
      Continuous fun v : boundaryChartTargetOpens x ↦
        (⟨(boundaryAmbientChart x).symm (((boundaryModelHomeomorph n).symm v.1).1),
          boundaryPoint_of_boundaryModelTarget x
            (boundaryChartSourceInverseTargetMem x v)⟩ :
          ((𝓡∂ (n + 1)).boundary W)) := by
    -- The previous step lands in the ambient boundary subtype.
    exact Continuous.subtype_mk hambient fun v ↦
      boundaryPoint_of_boundaryModelTarget x (boundaryChartSourceInverseTargetMem x v)
  exact Continuous.subtype_mk hboundary fun v ↦
    (boundaryAmbientChart x).map_target (boundaryChartSourceInverseTargetMem x v)

/-- Helper for Definition 25.1.1: the boundary chart is a homeomorphism between the open source
boundary slice and the transported Euclidean target slice. -/
noncomputable def boundaryChartSourceHomeomorph (x : ((𝓡∂ (n + 1)).boundary W)) :
    boundaryChartSourceOpens x ≃ₜ boundaryChartTargetOpens x where
  toFun := boundaryChartSourceForward x
  invFun := boundaryChartSourceInverse x
  left_inv := boundaryChartSourceLeftInv x
  right_inv := boundaryChartSourceRightInv x
  continuous_toFun := continuous_boundaryChartSourceForward x
  continuous_invFun := continuous_boundaryChartSourceInverse x

/-- Helper for Definition 25.1.1: the Euclidean target slice is nonempty because the preferred
boundary point lies in the source slice. -/
lemma boundaryChartTargetOpens_nonempty (x : ((𝓡∂ (n + 1)).boundary W)) :
    Nonempty (boundaryChartTargetOpens x) := by
  -- Transport the canonical source point across the source-target homeomorphism.
  exact ⟨boundaryChartSourceHomeomorph x
    (Classical.choice (boundaryChartSourceOpens_nonempty x))⟩

/-- The preferred induced boundary chart coming from the ambient preferred chart at a boundary
point. The coordinate map itself is canonical; only its manifold compatibility proofs are deferred
to later proof stages. -/
noncomputable def boundaryChartAt (x : ((𝓡∂ (n + 1)).boundary W)) :
    OpenPartialHomeomorph ((𝓡∂ (n + 1)).boundary W) (EuclideanSpace ℝ (Fin n)) :=
  -- Route correction: assemble the chart from the source-target homeomorphism instead of a
  -- manual `if`-based partial-homeomorphism record.
  ((((boundaryChartSourceOpens x).openPartialHomeomorphSubtypeCoe
      (boundaryChartSourceOpens_nonempty x)).symm).transHomeomorph
      (boundaryChartSourceHomeomorph x)).trans
    ((boundaryChartTargetOpens x).openPartialHomeomorphSubtypeCoe
      (boundaryChartTargetOpens_nonempty x))

/-- Helper for Definition 25.1.1: the assembled boundary chart has the expected source set. -/
lemma boundaryChartAt_source (x : ((𝓡∂ (n + 1)).boundary W)) :
    (boundaryChartAt (n := n) x).source = boundaryChartSourceSet x := by
  -- The outer subtype-coe charts contribute the source/target bookkeeping.
  simp [boundaryChartAt, boundaryChartSourceOpens, boundaryChartSourceSet]

/-- The boundary subtype of a manifold-with-boundary carries the charted-space structure induced
from the ambient preferred charts. -/
noncomputable abbrev inducedBoundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary W) where
  atlas := Set.range boundaryChartAt
  chartAt := boundaryChartAt
  mem_chart_source := by
    intro x
    rw [boundaryChartAt_source]
    change x.1 ∈ (boundaryAmbientChart x).source
    exact mem_chart_source (EuclideanHalfSpace (n + 1)) x.1
  chart_mem_atlas := by
    intro x
    exact ⟨x, rfl⟩

noncomputable instance boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary W) :=
  inducedBoundaryChartedSpace

/-- A boundary smooth structure on a compact smooth `(n + 1)`-manifold with boundary `W` consists
of the manifold laws for the boundary charted-space structure canonically induced from the ambient
preferred charts. -/
class BoundarySmoothStructure (n : ℕ) (W : Type) [TopologicalSpace W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] [IsManifold (𝓡∂ (n + 1)) ⊤ W] where
  isManifold : IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W)
  boundaryless : BoundarylessManifold (𝓡 n) ((𝓡∂ (n + 1)).boundary W)

instance [h : BoundarySmoothStructure n W] :
    IsManifold (𝓡 n) ⊤ ((𝓡∂ (n + 1)).boundary W) :=
  h.isManifold

instance [h : BoundarySmoothStructure n W] :
    BoundarylessManifold (𝓡 n) ((𝓡∂ (n + 1)).boundary W) :=
  h.boundaryless

end BoundarySmoothStructureAPI

/-- A cobordism witness between two closed smooth `n`-manifolds is a compact smooth
`(n + 1)`-manifold with boundary together with a smooth identification of the disjoint union with
the boundary subtype of the ambient manifold. The source-facing orientation convention can be
imposed later on this smooth boundary identification when the relevant oriented API is available. -/
structure CobordismWitness (n : ℕ) (M N : ClosedSmoothManifold n) where
  W : Type
  topologicalSpaceW : TopologicalSpace W
  t2SpaceW : T2Space W
  chartedSpaceW : ChartedSpace (EuclideanHalfSpace (n + 1)) W
  isManifoldW : IsManifold (𝓡∂ (n + 1)) ⊤ W
  compactSpaceW : CompactSpace W
  [boundarySmoothStructure : BoundarySmoothStructure n W]
  boundaryDiffeomorph :
    Diffeomorph (𝓡 n) (𝓡 n) (M.sum N).M ((𝓡∂ (n + 1)).boundary W) ⊤

section CobordismWitnessAPI

variable {n : ℕ} {M N : ClosedSmoothManifold n}

instance (B : CobordismWitness n M N) : TopologicalSpace B.W := B.topologicalSpaceW

/-- A cobordism witness is Hausdorff on its ambient compact manifold-with-boundary. -/
instance (B : CobordismWitness n M N) : T2Space B.W := B.t2SpaceW

instance (B : CobordismWitness n M N) : ChartedSpace (EuclideanHalfSpace (n + 1)) B.W :=
  B.chartedSpaceW

instance (B : CobordismWitness n M N) :
    IsManifold (𝓡∂ (n + 1)) ⊤ B.W :=
  B.isManifoldW

instance (B : CobordismWitness n M N) : CompactSpace B.W := B.compactSpaceW

instance (B : CobordismWitness n M N) : BoundarySmoothStructure n B.W :=
  B.boundarySmoothStructure

/-- The boundary subtype of the ambient compact smooth `(n + 1)`-manifold appearing in a
cobordism witness. -/
abbrev CobordismWitness.boundary (B : CobordismWitness n M N) := (𝓡∂ (n + 1)).boundary B.W

noncomputable instance (B : CobordismWitness n M N) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) B.boundary :=
  inferInstance

instance (B : CobordismWitness n M N) :
    IsManifold (𝓡 n) ⊤ B.boundary :=
  inferInstance

instance (B : CobordismWitness n M N) :
    BoundarylessManifold (𝓡 n) B.boundary :=
  inferInstance

/-- The smooth boundary equivalence of a cobordism witness, viewed as a homeomorphism. -/
noncomputable abbrev CobordismWitness.boundaryIdentification (B : CobordismWitness n M N) :
    (M.sum N).M ≃ₜ B.boundary :=
  B.boundaryDiffeomorph.toHomeomorph

end CobordismWitnessAPI

/-- Definition 25.1.1. Two smooth closed `n`-manifolds are cobordant when their disjoint union is
identified smoothly with the boundary of a compact smooth `(n + 1)`-manifold. In the oriented
variant, the second summand is understood with reversed boundary orientation. -/
def cobordant (n : ℕ) (M N : ClosedSmoothManifold n) : Prop :=
  Nonempty (CobordismWitness n M N)

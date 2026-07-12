import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01_05.Definition_1_5_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold

universe uM

noncomputable section

variable {M : Type uM} [TopologicalSpace M]

section

variable (n : ℕ) [TopologicalManifoldWithBoundary n M]

/- Proposition 1.38 (1) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, the manifold interior is open. -/
theorem manifoldInterior_isOpen :
    IsOpen ((leeBoundaryModelWithCorners n).interior M) := sorry

/- Proposition 1.38 (3) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, the manifold boundary is closed. -/
theorem manifoldBoundary_isClosed :
    IsClosed ((leeBoundaryModelWithCorners n).boundary M) := sorry

end

section

variable (n : ℕ)
variable [h : TopologicalManifoldWithBoundary (n + 1) M]

private noncomputable abbrev succInteriorAmbientChart
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

private theorem succInterior_inv_mem
    (x : ↥((𝓡∂ (n + 1)).interior M))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : 0 ≤ z 0) :
    (succInteriorAmbientChart n x).symm ⟨z, hz⟩ ∈ (𝓡∂ (n + 1)).interior M := by
  sorry

private noncomputable def succInteriorInvFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    EuclideanSpace ℝ (Fin (n + 1)) → ↥((𝓡∂ (n + 1)).interior M)
  | z =>
      if hz : 0 ≤ z 0 then
        ⟨(succInteriorAmbientChart n x).symm ⟨z, hz⟩, succInterior_inv_mem n x hz⟩
      else x

private def succInteriorSource
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set ↥((𝓡∂ (n + 1)).interior M) :=
  { y | y.1 ∈ (succInteriorAmbientChart n x).source }

private def succInteriorTarget
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Set.range fun y : succInteriorSource n x ↦ ((succInteriorAmbientChart n x) y.1.1).1

private theorem succInteriorChart_map_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.MapsTo
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x)
      (succInteriorTarget n x) := by
  intro y hy
  exact ⟨⟨y, hy⟩, rfl⟩

private theorem succInteriorChart_map_target
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.MapsTo (succInteriorInvFun n x) (succInteriorTarget n x) (succInteriorSource n x) := by
  sorry

private theorem succInteriorChart_left_inv
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.LeftInvOn (succInteriorInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x) := by
  sorry

private theorem succInteriorChart_right_inv
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.RightInvOn (succInteriorInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorTarget n x) := by
  sorry

private theorem succInteriorChart_open_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    IsOpen (succInteriorSource n x) := by
  sorry

private theorem succInteriorChart_open_target
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    IsOpen (succInteriorTarget n x) := by
  sorry

private theorem succInteriorChart_continuousOn_toFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    ContinuousOn
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x) := by
  sorry

private theorem succInteriorChart_continuousOn_invFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    ContinuousOn (succInteriorInvFun n x) (succInteriorTarget n x) := by
  sorry

private noncomputable def succInteriorChart
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).interior M)
      (EuclideanSpace ℝ (Fin (n + 1))) :=
  { toFun := fun y ↦ ((succInteriorAmbientChart n x) y.1).1
    invFun := succInteriorInvFun n x
    source := succInteriorSource n x
    target := succInteriorTarget n x
    map_source' := succInteriorChart_map_source n x
    map_target' := succInteriorChart_map_target n x
    left_inv' := succInteriorChart_left_inv n x
    right_inv' := succInteriorChart_right_inv n x
    open_source := succInteriorChart_open_source n x
    open_target := succInteriorChart_open_target n x
    continuousOn_toFun := succInteriorChart_continuousOn_toFun n x
    continuousOn_invFun := succInteriorChart_continuousOn_invFun n x }

private theorem succInteriorChartedSpace_mem_chart_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    x ∈ succInteriorSource n x := by
  simp [succInteriorSource, succInteriorAmbientChart]

private theorem succInteriorChartedSpace_chart_mem_atlas
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    succInteriorChart n x ∈ ⋃ y : ↥((𝓡∂ (n + 1)).interior M), {succInteriorChart n y} := by
  simp

@[reducible] private noncomputable def succInteriorChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1)))
      ↥((𝓡∂ (n + 1)).interior M) where
  atlas := ⋃ x : ↥((𝓡∂ (n + 1)).interior M), { succInteriorChart n x }
  chartAt := succInteriorChart n
  mem_chart_source := succInteriorChartedSpace_mem_chart_source n
  chart_mem_atlas := succInteriorChartedSpace_chart_mem_atlas n

private noncomputable def boundaryCoords :
    EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin n) :=
  fun z ↦
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun j ↦ z.1 (Fin.succ j))

private noncomputable def boundaryCoordsInv :
    EuclideanSpace ℝ (Fin n) → EuclideanHalfSpace (n + 1) :=
  fun y ↦
    ⟨(EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (Fin.insertNth (0 : Fin (n + 1)) (0 : ℝ) ((EuclideanSpace.equiv (Fin n) ℝ) y)),
      by simp⟩

private noncomputable abbrev boundaryAmbientChart
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

private theorem boundary_inv_mem
    (x : ↥((𝓡∂ (n + 1)).boundary M)) (z : EuclideanSpace ℝ (Fin n)) :
    (boundaryAmbientChart n x).symm (boundaryCoordsInv n z) ∈ (𝓡∂ (n + 1)).boundary M := by
  sorry

private noncomputable def boundaryInvFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    EuclideanSpace ℝ (Fin n) → ↥((𝓡∂ (n + 1)).boundary M)
  | z => ⟨(boundaryAmbientChart n x).symm (boundaryCoordsInv n z), boundary_inv_mem n x z⟩

private def boundarySource
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set ↥((𝓡∂ (n + 1)).boundary M) :=
  { y | y.1 ∈ (boundaryAmbientChart n x).source }

private def boundaryTarget
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  Set.range fun y : boundarySource n x ↦
    boundaryCoords n ((boundaryAmbientChart n x) y.1.1)

private theorem boundaryChart_map_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.MapsTo
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x)
      (boundaryTarget n x) := by
  intro y hy
  exact ⟨⟨y, hy⟩, rfl⟩

private theorem boundaryChart_map_target
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.MapsTo (boundaryInvFun n x) (boundaryTarget n x) (boundarySource n x) := by
  sorry

private theorem boundaryChart_left_inv
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.LeftInvOn (boundaryInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x) := by
  sorry

private theorem boundaryChart_right_inv
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.RightInvOn (boundaryInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundaryTarget n x) := by
  sorry

private theorem boundaryChart_open_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    IsOpen (boundarySource n x) := by
  sorry

private theorem boundaryChart_open_target
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    IsOpen (boundaryTarget n x) := by
  sorry

private theorem boundaryChart_continuousOn_toFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    ContinuousOn
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x) := by
  sorry

private theorem boundaryChart_continuousOn_invFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    ContinuousOn (boundaryInvFun n x) (boundaryTarget n x) := by
  sorry

private noncomputable def boundaryChart (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) :=
  { toFun := fun y ↦ boundaryCoords n ((boundaryAmbientChart n x) y.1)
    invFun := boundaryInvFun n x
    source := boundarySource n x
    target := boundaryTarget n x
    map_source' := boundaryChart_map_source n x
    map_target' := boundaryChart_map_target n x
    left_inv' := boundaryChart_left_inv n x
    right_inv' := boundaryChart_right_inv n x
    open_source := boundaryChart_open_source n x
    open_target := boundaryChart_open_target n x
    continuousOn_toFun := boundaryChart_continuousOn_toFun n x
    continuousOn_invFun := boundaryChart_continuousOn_invFun n x }

private theorem boundaryChartedSpace_mem_chart_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    x ∈ boundarySource n x := by
  simp [boundarySource, boundaryAmbientChart]

private theorem boundaryChartedSpace_chart_mem_atlas
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    boundaryChart n x ∈ ⋃ y : ↥((𝓡∂ (n + 1)).boundary M), {boundaryChart n y} := by
  simp

@[reducible] private noncomputable def boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) where
  atlas := ⋃ x : ↥((𝓡∂ (n + 1)).boundary M), { boundaryChart n x }
  chartAt := boundaryChart n
  mem_chart_source := boundaryChartedSpace_mem_chart_source n
  chart_mem_atlas := boundaryChartedSpace_chart_mem_atlas n

/-
Proposition 1.38 (4) (`source-facing`): the boundary subtype carries the induced
`n`-dimensional topological-manifold owner.
-/
noncomputable instance boundaryTopologicalManifold :
    TopologicalManifold n ↥((𝓡∂ (n + 1)).boundary M) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) :=
    boundaryChartedSpace n
  exact topologicalManifoldOfChartedSpace n ↥((𝓡∂ (n + 1)).boundary M)

/-- Proposition 1.38 (4) (companion): with its induced `TopologicalManifold n` structure, the
boundary subtype is boundaryless for the Euclidean owner `𝓡 n`. -/
theorem manifoldBoundary_boundaryless :
    BoundarylessManifold (𝓡 n) ↥((𝓡∂ (n + 1)).boundary M) :=
  inferInstance

end

/-
Proposition 1.38 (2) (`source-facing`): the manifold interior, regarded as its canonical open
submanifold, carries the induced `n`-dimensional topological-manifold owner.
-/
noncomputable instance manifoldInteriorTopologicalManifold
    (n : ℕ) [TopologicalManifoldWithBoundary n M] :
    TopologicalManifold n
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) := by
  cases n with
  | zero =>
      letI : TopologicalManifold 0 M := topologicalManifoldOfChartedSpace 0 M
      infer_instance
  | succ n =>
      let U : Opens M := ⟨(𝓡∂ (n + 1)).interior M, manifoldInterior_isOpen (n + 1)⟩
      change TopologicalManifold (n + 1) U
      letI : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) U := by
        change ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) ↥((𝓡∂ (n + 1)).interior M)
        exact succInteriorChartedSpace n
      exact topologicalManifoldOfChartedSpace (n + 1) U

section

variable (n : ℕ) [TopologicalManifoldWithBoundary n M]

/-- Proposition 1.38 (2) (companion): with its induced `TopologicalManifold n` structure on the
canonical open interior submanifold, the manifold interior is boundaryless for the Euclidean owner
`𝓡 n`. -/
theorem manifoldInterior_boundaryless :
    BoundarylessManifold (𝓡 n)
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) := by
  letI : TopologicalManifold n
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) :=
    manifoldInteriorTopologicalManifold n
  infer_instance

end

section

variable (n : ℕ) [ChartedSpace (LeeBoundaryModelSpace n) M]

/- Proposition 1.38 (5) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, empty manifold boundary is exactly
`ModelWithCorners.Boundaryless.iff_boundary_eq_empty`. -/
recall ModelWithCorners.Boundaryless.iff_boundary_eq_empty

end

section

variable [TopologicalManifoldWithBoundary 0 M]

/- Proposition 1.38 (6) (core/canonical): in dimension `0`, Lee's boundary model is `𝓡 0`, so
empty manifold boundary is the direct specialization of
`ModelWithCorners.Boundaryless.boundary_eq_empty`. -/
#check (ModelWithCorners.Boundaryless.boundary_eq_empty : (𝓡 0).boundary M = ∅)

/- Proposition 1.38 (7) (bridge/view): in dimension `0`, the boundaryless manifold structure is
the canonical instance on manifolds modelled on the boundaryless owner `𝓡 0`. -/
#synth BoundarylessManifold (𝓡 0) M

end

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_15_extra_1 (from Chap03/Sec03_15) -/
noncomputable section

open scoped Manifold

-- Semantic search note: the `lean_leansearch` MCP tool was unavailable in this session, so this
-- file uses local repository precedent together with mathlib's maximal-atlas chart derivative API.

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- A chart in the `C^1` maximal atlas is manifold-differentiable on its source and its inverse is
manifold-differentiable on its target. -/
theorem chart_mdifferentiable_of_mem_maximalAtlas
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M) :
    e.MDifferentiable I I := sorry

/-- Definition 3.15-extra-1: the `i`-th coordinate vector at `p` associated to a smooth chart `e`
is the preimage of the `i`-th standard coordinate vector under the chart differential at `p`. -/
noncomputable def chart_coordinate_vector
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : M) (hp : p ∈ e.source) (i : Fin n) : TangentSpace I p :=
  let de : TangentSpace I p ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    OpenPartialHomeomorph.MDifferentiable.mfderiv
      (chart_mdifferentiable_of_mem_maximalAtlas e he) hp
  de.symm (EuclideanSpace.basisFun (Fin n) ℝ i)

/-- Applying the chart differential to the `i`-th coordinate vector recovers the `i`-th standard
coordinate direction in the model space. -/
theorem mfderiv_chart_coordinate_vector
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : M) (hp : p ∈ e.source) (i : Fin n) :
    OpenPartialHomeomorph.MDifferentiable.mfderiv
        (chart_mdifferentiable_of_mem_maximalAtlas e he) hp
        (chart_coordinate_vector e he p hp i) =
      EuclideanSpace.basisFun (Fin n) ℝ i := sorry

/-! ### Definition_3_15_extra_2 (from Chap03/Sec03_15) -/
noncomputable section

open scoped Manifold

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/- Definition 3.15-extra-2: the preferred coordinate basis at `p` is the chapter-level owner
`chart_coordinate_vectors_basis`, specialized to the preferred chart `chartAt H p`. -/
#check chart_coordinate_vectors_basis

/-- The preferred coordinate components of a tangent vector at `p`. -/
noncomputable def preferred_coordinate_components
    (p : M) (v : TangentSpace I p) : Fin n → ℝ :=
  (chart_coordinate_vectors_basis (chartAt H p) (IsManifold.chart_mem_maximalAtlas p) p
    (mem_chart_source H p)).repr v

/- The coordinate expansion of `v : TangentSpace I p` in preferred coordinates is the basis
representation for the canonical source-facing basis
`chart_coordinate_vectors_basis (chartAt H p) (IsManifold.chart_mem_maximalAtlas p) p
  (mem_chart_source H p)`. This keeps the preferred-coordinate API as derived data from the
chapter-level owner declaration rather than a parallel coordinate-trivialization wrapper. -/

/-! ### Remark_3_15_extra_3 (from Chap03/Sec03_15) -/
/- Remark 3.15-extra-3: for a smooth map between manifolds with corners, `MDifferentiableAt.mfderiv`
identifies the manifold derivative with the derivative in preferred coordinates of
`writtenInExtChartAt I I' p F`, taken as `fderivWithin` on the model range `range I` at
`extChartAt I p p`. This is the correct general coordinate statement: outside the model-space case
one should not read it as an unrestricted Fréchet derivative on the whole ambient model vector
space. The companion recall `mfderiv_eq_fderiv` is the specialization to the trivial/model-space
manifold structure, where the coordinate representative is just `F`, so one recovers the usual
total derivative and, in Euclidean coordinates, the Jacobian matrix. -/
recall MDifferentiableAt.mfderiv

recall mfderiv_eq_fderiv

/-! ### Remark_3_15_extra_4 (from Chap03/Sec03_15) -/
open Bundle
open scoped Manifold

section

universe u_𝕜 u_E u_H u_M

variable {𝕜 : Type u_𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type u_E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type u_H} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u_M} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/- Remark 3.15-extra-4: in mathlib, the change-of-coordinates rule for tangent vectors is packaged
by `tangentCoordChange I x y z`. The theorem `tangentCoordChange_def` identifies this linear map
with the derivative of the chart transition map `extChartAt I y ∘ (extChartAt I x).symm`, which is
the basis-free form of equation (3.11); applying this linear map to a coordinate vector gives the
component transformation law (3.12). -/
#check tangentCoordChange_def

/-- Changing tangent coordinates from the chart centered at `x` to the chart centered at `y` is
given by the tangent coordinate change linear map. -/
  theorem tangent_coordinates_change
    {x y z : M} (hxy : z ∈ (chartAt H x).source ∩ (chartAt H y).source) :
    (trivializationAt E (TangentSpace I) x).coordChangeL 𝕜
        (trivializationAt E (TangentSpace I) y) z =
      tangentCoordChange I x y z := by
  ext v
  simpa [tangentCoordChange] using
    (tangentBundleCore I M).trivializationAt_coordChange_eq hxy v

end

/-! ### Remark_3_15_extra_5 (from Chap03/Sec03_15) -/
/- Remark 3.15-extra-5: in Lean, the coordinate vectors attached to a local coordinate system are
encoded by the differential of the inverse chart map on the tangent bundle. Thus the vector
corresponding to the `i`-th coordinate direction is determined by the whole inverse chart, not by
the single coordinate function `x^i` alone; changing the remaining coordinate functions can change
the resulting tangent vector. This chart-level dependence is expressed by
`tangentMap_chart_symm`. -/
recall tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap I I (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q)

end

/-! ### Proposition_3_15 (from Chap03/Sec03_15) -/
noncomputable section

open Set
open scoped Manifold

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem chart_mdifferentiable_of_mem_maximalAtlas
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M) :
    OpenPartialHomeomorph.MDifferentiable I I e := by
  refine ⟨?_, ?_⟩
  · exact
      (show ContMDiffOn I I 1 e e.source from
        contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero
  · exact
      (show ContMDiffOn I I 1 e.symm e.target from
        contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero

/- Proposition 3.15 (1): the tangent space at a point of a smooth `n`-manifold has dimension
`n`. This is already the canonical earlier chapter theorem
`tangentSpace_finrank_eq_of_n_dimensional_manifold`. -/
#check tangentSpace_finrank_eq_of_n_dimensional_manifold

/-- Proposition 3.15 (2): a smooth chart containing `p` determines the coordinate-vector basis of
`TangentSpace I p` by transporting the standard basis of `EuclideanSpace ℝ (Fin n)` through the
inverse chart differential. -/
noncomputable def chart_coordinate_vectors_basis
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : M) (hp : p ∈ e.source) :
    Module.Basis (Fin n) ℝ (TangentSpace I p) :=
  let de : TangentSpace I p ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    OpenPartialHomeomorph.MDifferentiable.mfderiv
      (chart_mdifferentiable_of_mem_maximalAtlas e he) hp
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map de.symm.toLinearEquiv

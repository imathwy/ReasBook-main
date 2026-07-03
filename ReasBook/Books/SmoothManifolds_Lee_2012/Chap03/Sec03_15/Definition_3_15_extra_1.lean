import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

-- Declarations for this item will be appended below by the statement pipeline.

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

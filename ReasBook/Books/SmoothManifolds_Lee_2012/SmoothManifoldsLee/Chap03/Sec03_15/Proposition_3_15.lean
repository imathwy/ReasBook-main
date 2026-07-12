import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

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
    {e : OpenPartialHomeomorph M H} (he : e.MDifferentiable I I) (p : M) (hp : p ∈ e.source) :
    Module.Basis (Fin n) ℝ (TangentSpace I p) :=
  let de : TangentSpace I p ≃L[ℝ] EuclideanSpace ℝ (Fin n) := he.mfderiv hp
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map de.symm.toLinearEquiv

import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_15.Proposition_3_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

-- Domain sampling pass: this item lies in the smooth-manifold tangent-space / chart-derivative
-- API. The source-facing owner is the chapter declaration `chart_coordinate_vectors_basis`; the
-- core/canonical ambient API is `OpenPartialHomeomorph.MDifferentiable.mfderiv` together with the
-- model-space basis `EuclideanSpace.basisFun`. Primitive data is the chart differential linear
-- equivalence; the individual coordinate vectors are derived by evaluating the owner basis.

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- Definition 3.15-extra-1: the `i`-th coordinate vector determined by a smooth chart is
characterized by equation (3.8): applying the chart differential sends it to the `i`-th standard
coordinate direction in the model space. -/
theorem mfderiv_chart_coordinate_vectors_basis
    {e : OpenPartialHomeomorph M H} (he : e.MDifferentiable I I)
    (p : M) (hp : p ∈ e.source) (i : Fin n) :
    he.mfderiv hp (chart_coordinate_vectors_basis he p hp i) =
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  let de : TangentSpace I p ≃L[ℝ] EuclideanSpace ℝ (Fin n) := he.mfderiv hp
  simpa [chart_coordinate_vectors_basis, de] using
    de.apply_symm_apply ((EuclideanSpace.basisFun (Fin n) ℝ) i)

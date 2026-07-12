import Mathlib
import SmoothManifolds_Lee_2012.Chap02.Sec02_09.Example_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open TopologicalSpace

noncomputable section

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item uses
-- the canonical chart API `smoothChartDiffeomorph`, together with `VectorField.mpullback` and
-- `NormedSpace.fromTangentSpace`.

section

variable {n : ℕ}
variable {M : Type*} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : ℕ∞ω) M]

/-- The constant `i`th standard-basis vector field on an open subset of `ℝ^n`. -/
def model_coordinate_vector_field
    (U : Opens (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    ∀ y : U, TangentSpace (𝓡 n) y :=
  fun y ↦
    ((NormedSpace.fromTangentSpace (y : EuclideanSpace ℝ (Fin n)) :
        TangentSpace (𝓡 n) y ≃L[ℝ] EuclideanSpace ℝ (Fin n)).symm)
      ((EuclideanSpace.basisFun (Fin n) ℝ) i)

/-- Helper for Example 8.2: under the canonical tangent-space identification, the model
coordinate vector field has constant coordinates. -/
@[simp] lemma fromTangentSpace_model_coordinate_vector_field
    (U : Opens (EuclideanSpace ℝ (Fin n))) (i : Fin n) (y : U) :
    ((NormedSpace.fromTangentSpace (y : EuclideanSpace ℝ (Fin n)) :
        TangentSpace (𝓡 n) y ≃L[ℝ] EuclideanSpace ℝ (Fin n))
      (model_coordinate_vector_field U i y)) =
      (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  -- Unfold the model field and cancel the tangent-space equivalence with its inverse.
  simp [model_coordinate_vector_field]

/-- Helper for Example 8.2: on an open subset of the model space, tangent-bundle trivializations
reduce to the canonical `fromTangentSpace` coordinates. -/
@[simp] lemma openSubset_trivializationAt_apply_eq_fromTangentSpace
    (U : Opens (EuclideanSpace ℝ (Fin n))) (x y : U) (v : TangentSpace (𝓡 n) y) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x ⟨y, v⟩).2 =
      ((NormedSpace.fromTangentSpace (y : EuclideanSpace ℝ (Fin n)) :
          TangentSpace (𝓡 n) y ≃L[ℝ] EuclideanSpace ℝ (Fin n)) v) := by
  let e : OpenPartialHomeomorph U (EuclideanSpace ℝ (Fin n)) :=
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n))).subtypeRestr ⟨x⟩
  have hchartx : chartAt (EuclideanSpace ℝ (Fin n)) x = e := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  have hcharty : chartAt (EuclideanSpace ℝ (Fin n)) y = e := by
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  -- Rewrite both open-subset charts as the same restricted identity chart.
  rw [TangentBundle.trivializationAt_apply, hchartx, hcharty]
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply]
  have hy_source : y ∈ e.source := by
    simp [e]
  have hy_target : e y ∈ e.target := e.map_source hy_source
  have hEqOn :
      Set.EqOn (((id ∘ ↑e) ∘ ↑e.symm ∘ id) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) id e.target := by
    intro z hz
    -- On the target of the restricted chart, the chart and its inverse cancel.
    simpa using e.right_inv hz
  have hEq :
      (((id ∘ ↑e) ∘ ↑e.symm ∘ id) :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =ᶠ[nhds (id (e y))] id :=
    hEqOn.eventuallyEq_of_mem (e.open_target.mem_nhds hy_target)
  -- The derivative of this local identity map is the derivative of `id`.
  rw [hEq.fderivWithin_eq_of_nhds]
  simp [Set.range_id, NormedSpace.fromTangentSpace]

/-- Helper for Example 8.2: every tangent-bundle trivialization sees the model coordinate vector
field as the same constant standard basis vector. -/
@[simp] lemma trivializationAt_model_coordinate_vector_field
    (U : Opens (EuclideanSpace ℝ (Fin n))) (i : Fin n) (x y : U) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
      ⟨y, model_coordinate_vector_field U i y⟩).2 =
      (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  -- First rewrite the trivialized tangent coordinate to the canonical ambient coordinate.
  rw [openSubset_trivializationAt_apply_eq_fromTangentSpace]
  -- Then use the constant-coordinate formula of the model vector field itself.
  exact fromTangentSpace_model_coordinate_vector_field U i y

/-- Example 8.2: the constant `i`th standard-basis vector field on an open subset of `ℝ^n`
is smooth. -/
theorem model_coordinate_vector_field_smooth
    (U : Opens (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (T% (model_coordinate_vector_field U i)) := by
  intro p
  -- Reduce tangent-bundle smoothness to the Euclidean coordinate map in the trivialization at `p`.
  rw [Bundle.contMDiffAt_section p]
  -- The trivialized coordinate map is the constant basis vector `eᵢ`.
  simpa using
    (contMDiffAt_const :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞
        (fun _ : U ↦ (EuclideanSpace.basisFun (Fin n) ℝ) i) p)

/-- Helper for Example 8.2: if `e` is any smooth chart on an `n`-manifold, then pulling back the
constant `i`th standard-basis vector field on the chart image defines the `i`th coordinate vector
field on the chart source, denoted `∂ / ∂x^i`. -/
def smooth_chart_coordinate_vector_field
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M) (i : Fin n) :
    ∀ x : (⟨e.source, e.open_source⟩ : Opens M), TangentSpace (𝓡 n) x :=
  VectorField.mpullback (𝓡 n) (𝓡 n) (smoothChartDiffeomorph e he)
    (model_coordinate_vector_field (⟨e.target, e.open_target⟩ : Opens (EuclideanSpace ℝ (Fin n))) i)

/-- Helper for Example 8.2: the derivative of a smooth chart diffeomorphism is invertible at every
point of its source open set. -/
lemma smoothChartDiffeomorph_mfderiv_isInvertible
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M)
    (x : (⟨e.source, e.open_source⟩ : Opens M)) :
    (mfderiv (𝓡 n) (𝓡 n) (smoothChartDiffeomorph e he) x).IsInvertible := by
  let Φ := smoothChartDiffeomorph e he
  let φx := Φ.mfderivToContinuousLinearEquiv (by simp) x
  -- Use the diffeomorphism API to package the manifold derivative as a linear equivalence.
  refine ⟨φx, ?_⟩
  simpa [Φ, φx] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (Φ := Φ) (x := x) (hn := by simp)).symm

/-- Helper for Example 8.2: the coordinate vector field associated to a smooth chart is smooth
because its coordinate component functions are constants on the chart image. -/
theorem smooth_chart_coordinate_vector_field_smooth
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : ℕ∞ω) M) (i : Fin n) :
    ContMDiff (𝓡 n) (𝓡 n).tangent ∞ (T% (smooth_chart_coordinate_vector_field e he i)) := by
  let Φ := smoothChartDiffeomorph e he
  -- Transport smoothness from the model field along the chart diffeomorphism.
  simpa [smooth_chart_coordinate_vector_field, Φ] using
    (ContMDiff.mpullback_vectorField
      (I := 𝓡 n) (I' := 𝓡 n)
      (f := Φ)
      (V := model_coordinate_vector_field
        (⟨e.target, e.open_target⟩ : Opens (EuclideanSpace ℝ (Fin n))) i)
      (m := ∞) (n := ∞)
      (model_coordinate_vector_field_smooth
        (⟨e.target, e.open_target⟩ : Opens (EuclideanSpace ℝ (Fin n))) i)
      Φ.contMDiff
      (smoothChartDiffeomorph_mfderiv_isInvertible e he)
      (by simp))

end

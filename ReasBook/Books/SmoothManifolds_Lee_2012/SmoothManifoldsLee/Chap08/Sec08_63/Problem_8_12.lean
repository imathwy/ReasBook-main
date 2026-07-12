import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_9
import SmoothManifolds_Lee_2012.Chap01.Sec01_04.Example_1_33
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped LinearAlgebra.Projectivization Manifold ContDiff

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "SmoothProjectiveVectorField" =>
  Cₛ^∞⟮𝓡 2; R2, fun q : RealProjectiveSpace 2 ↦ TangentSpace (𝓡 2) q⟯

-- Domain sampling:
-- * primary domain: smooth tangent vector fields on manifolds and their relatedness along smooth
--   maps;
-- * relevant upstream owners sampled before refinement:
--   `Cₛ^∞⟮𝓡 2; R2, fun q : RealProjectiveSpace 2 ↦ TangentSpace (𝓡 2) q⟯`,
--   `VectorField.f_related`, `VectorField.f_related_apply`,
--   and the affine-chart owner `realProjectiveChart`;
-- * owner abstraction: the chapter's bundled smooth-vector-field owner on `ℝP²`, with
--   `VectorField.f_related` as the relation layer;
-- * primitive data here: the source field on `ℝ²` and the lifted smooth vector field on `ℝP²`;
--   smoothness of the lift is carried by the bundled owner, while the three chart formulas remain
--   derived specification clauses in the existence theorem.

-- Semantic recall note: `lean_leansearch` pointed back to `tangentMap` and chart-tangent owners,
-- and this item uses the local `RealProjectiveSpace`/`realProjectiveChart` API from Chapter 1
-- together with the Chapter 8 predicate `VectorField.f_related`.

/-- The vector field `X = x ∂/∂y - y ∂/∂x` on `ℝ²`. -/
def problem_8_12_X (p : R2) : TangentSpace (𝓡 2) p :=
  (NormedSpace.fromTangentSpace p).symm (WithLp.toLp 2 ![-p 1, p 0])

/-- Under the canonical tangent-space identification on `ℝ²`, the field `problem_8_12_X` has
coordinate vector `(-y, x)`. -/
theorem fromTangentSpace_problem_8_12_X (p : R2) :
    NormedSpace.fromTangentSpace p (problem_8_12_X p) =
      WithLp.toLp 2 ![-p 1, p 0] := by
  -- Unfold the definition and simplify the inverse tangent-space identification.
  simp [problem_8_12_X]

/-- The source vector field `problem_8_12_X` is smooth. -/
theorem problem_8_12_X_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% problem_8_12_X) := by
  -- On a vector space, smoothness of a tangent field is just smoothness of its coordinate map.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each coordinate is a polynomial in the ambient affine coordinates.
  simpa [problem_8_12_X] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · simpa using
          ((contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R2 ↦ p 1)).neg
      · simpa using
          (contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R2 ↦ p 0))

/-- The chart-coordinate vector field for the `x ≠ 0` affine chart on `ℝP²`. -/
def problem_8_12_chart0_vectorField (u : R2) : TangentSpace (𝓡 2) u :=
  (NormedSpace.fromTangentSpace u).symm
    (WithLp.toLp 2 ![1 + u 0 ^ (2 : ℕ), u 0 * u 1])

/-- In the `x ≠ 0` chart, the lifted vector field has coordinate vector
`(1 + u₀², u₀ u₁)`. -/
theorem fromTangentSpace_problem_8_12_chart0_vectorField (u : R2) :
    NormedSpace.fromTangentSpace u (problem_8_12_chart0_vectorField u) =
      WithLp.toLp 2 ![1 + u 0 ^ (2 : ℕ), u 0 * u 1] := by
  -- Unfold the chart-field definition and cancel the tangent-space equivalence.
  simp [problem_8_12_chart0_vectorField]

/-- Helper for Problem 8-12: the coordinate field used in the `x ≠ 0` chart is smooth on `ℝ²`. -/
theorem problem_8_12_chart0_vectorField_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% problem_8_12_chart0_vectorField) := by
  -- On a vector space, it suffices to prove smoothness of the explicit coordinate formula.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each component is polynomial in the ambient affine coordinates.
  simpa [problem_8_12_chart0_vectorField] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · simpa using
          contDiff_const.add
            ((contDiff_piLp_apply (2 : ENNReal) :
              ContDiff ℝ ∞ fun p : R2 ↦ p 0).pow 2)
      · simpa using
          (contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R2 ↦ p 0).mul
            (contDiff_piLp_apply (2 : ENNReal) :
              ContDiff ℝ ∞ fun p : R2 ↦ p 1))

/-- The chart-coordinate vector field for the `y ≠ 0` affine chart on `ℝP²`. -/
def problem_8_12_chart1_vectorField (u : R2) : TangentSpace (𝓡 2) u :=
  (NormedSpace.fromTangentSpace u).symm
    (WithLp.toLp 2 ![-(1 + u 0 ^ (2 : ℕ)), -(u 0 * u 1)])

/-- In the `y ≠ 0` chart, the lifted vector field has coordinate vector
`(-(1 + u₀²), -u₀ u₁)`. -/
theorem fromTangentSpace_problem_8_12_chart1_vectorField (u : R2) :
    NormedSpace.fromTangentSpace u (problem_8_12_chart1_vectorField u) =
      WithLp.toLp 2 ![-(1 + u 0 ^ (2 : ℕ)), -(u 0 * u 1)] := by
  -- Unfold the chart-field definition and cancel the tangent-space equivalence.
  simp [problem_8_12_chart1_vectorField]

/-- Helper for Problem 8-12: the coordinate field used in the `y ≠ 0` chart is smooth on `ℝ²`. -/
theorem problem_8_12_chart1_vectorField_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% problem_8_12_chart1_vectorField) := by
  -- On a vector space, it suffices to prove smoothness of the explicit coordinate formula.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each component is again polynomial, up to a sign.
  simpa [problem_8_12_chart1_vectorField, neg_add, add_comm, add_left_comm, add_assoc] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · convert
          (contDiff_const.add
            ((contDiff_piLp_apply (2 : ENNReal) :
              ContDiff ℝ ∞ fun p : R2 ↦ p 0).pow 2)).neg using 1
      · simpa using
          ((contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R2 ↦ p 0).mul
            (contDiff_piLp_apply (2 : ENNReal) :
              ContDiff ℝ ∞ fun p : R2 ↦ p 1)).neg)

/-- The chart-coordinate vector field for the `z ≠ 0` affine chart on `ℝP²`. -/
def problem_8_12_chart2_vectorField (u : R2) : TangentSpace (𝓡 2) u :=
  (NormedSpace.fromTangentSpace u).symm (WithLp.toLp 2 ![-u 1, u 0])

/-- In the `z ≠ 0` chart, the lifted vector field has coordinate vector `(-u₁, u₀)`. -/
theorem fromTangentSpace_problem_8_12_chart2_vectorField (u : R2) :
    NormedSpace.fromTangentSpace u (problem_8_12_chart2_vectorField u) =
      WithLp.toLp 2 ![-u 1, u 0] := by
  -- Unfold the chart-field definition and cancel the tangent-space equivalence.
  simp [problem_8_12_chart2_vectorField]

/-- Helper for Problem 8-12: the `z ≠ 0` chart field is the same smooth rotation field as
`problem_8_12_X`. -/
theorem problem_8_12_chart2_vectorField_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% problem_8_12_chart2_vectorField) := by
  -- This is the same coordinate formula as the original field on `ℝ²`.
  simpa [problem_8_12_chart2_vectorField, problem_8_12_X] using problem_8_12_X_contMDiff

/-- Helper for Problem 8-12: each standard affine chart on `ℝP²` belongs to the smooth maximal
atlas. -/
theorem problem_8_12_realProjectiveChart_mem_maximalAtlas (i : Fin 3) :
    realProjectiveChart 2 i ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (RealProjectiveSpace 2) := by
  -- The standard affine charts are exactly the atlas used to define the smooth structure.
  have hAtlas : realProjectiveChart 2 i ∈ atlas R2 (RealProjectiveSpace 2) := by
    change realProjectiveChart 2 i ∈ { e |
      ∃ j : Fin (2 + 1), e = realProjectiveChart 2 j }
    exact ⟨i, rfl⟩
  exact IsManifold.subset_maximalAtlas hAtlas

/-- Helper for Problem 8-12: push a Euclidean chart vector field forward through the inverse of a
standard affine chart to obtain a tangent-bundle map on `ℝP²`. -/
def problem_8_12_localLift (i : Fin 3) (V : ∀ u : R2, TangentSpace (𝓡 2) u)
    (u : R2) : TangentBundle (𝓡 2) (RealProjectiveSpace 2) :=
  tangentMap (𝓡 2) (𝓡 2) (realProjectiveChart 2 i).symm
    ((T% V) u)

/-- Helper for Problem 8-12: the lifted tangent-bundle map attached to a smooth Euclidean chart
field is smooth. -/
theorem problem_8_12_localLift_contMDiff (i : Fin 3)
    {V : ∀ u : R2, TangentSpace (𝓡 2) u}
    (hV : ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% V)) :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (problem_8_12_localLift i V) := by
  -- The local lift is the tangent map of the inverse chart composed with the smooth Euclidean
  -- section `u ↦ (u, V u)`.
  have hsymm : ContMDiff (𝓡 2) (𝓡 2) ∞ (realProjectiveChart 2 i).symm := by
    intro u
    simpa using
      contMDiffAt_symm_of_mem_maximalAtlas
        (problem_8_12_realProjectiveChart_mem_maximalAtlas i) (by simp : u ∈ Set.univ)
  have hT :
      ContMDiff (𝓡 2).tangent (𝓡 2).tangent ∞
        (tangentMap (𝓡 2) (𝓡 2) (realProjectiveChart 2 i).symm) := by
    simpa using hsymm.contMDiff_tangentMap le_rfl
  simpa [problem_8_12_localLift, Function.comp_apply] using hT.comp hV

omit [IsManifold (𝓡 2) (∞ : ℕ∞ω) R2] in
/-- Helper for Problem 8-12: pushing the pullback of an ambient vector field along an open
inclusion recovers the original ambient field. -/
theorem problem_8_12_tangentMap_subtype_val_pullback_eq
    (U : TopologicalSpace.Opens R2)
    (X : ∀ p : R2, TangentSpace (𝓡 2) p)
    (p : U) :
    tangentMap (𝓡 2) (𝓡 2) (Subtype.val : U → R2)
      (T% (VectorField.mpullback (𝓡 2) (𝓡 2) (Subtype.val : U → R2) X) p) =
      T% X p.1 := by
  -- The pullback field was defined using the inverse derivative of the open inclusion.
  simp only [tangentMap, VectorField.mpullback_apply, Bundle.TotalSpace.mk_inj]
  exact (mfderiv_open_subset_inclusion_isInvertible (I := 𝓡 2) U p).self_apply_inverse (X p.1)

/-- Helper for Problem 8-12: the three standard affine chart formulas for a lifted vector field on
`ℝP²`. -/
structure Problem812ChartFormulas (Y : SmoothProjectiveVectorField) : Prop where
  chart0 :
    ∀ u : R2,
      Y ((realProjectiveChart 2 (0 : Fin 3)).symm u) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm u
          (problem_8_12_chart0_vectorField u)
  chart1 :
    ∀ u : R2,
      Y ((realProjectiveChart 2 (1 : Fin 3)).symm u) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm u
          (problem_8_12_chart1_vectorField u)
  chart2 :
    ∀ u : R2,
      Y ((realProjectiveChart 2 (Fin.last 2)).symm u) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm u
          (problem_8_12_chart2_vectorField u)

/-- Helper for Problem 8-12: the deterministic global tangent-bundle lift uses the `z ≠ 0` chart
whenever possible, then the `x ≠ 0` chart, and finally the `y ≠ 0` chart. -/
def problem_8_12_roughLift (q : RealProjectiveSpace 2) :
    TangentBundle (𝓡 2) (RealProjectiveSpace 2) := by
  classical
  exact
    if h2 : q ∈ realProjectiveChartDomain 2 (Fin.last 2) then
      problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField
        ((realProjectiveChart 2 (Fin.last 2)) q)
    else if h0 : q ∈ realProjectiveChartDomain 2 (0 : Fin 3) then
      problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField
        ((realProjectiveChart 2 (0 : Fin 3)) q)
    else
      problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField
        ((realProjectiveChart 2 (1 : Fin 3)) q)

/-- Helper for Problem 8-12: on the `(2,0)` chart overlap, the first `z ≠ 0` coordinate is
nonzero, so the explicit transition formula has nonvanishing denominator. -/
theorem problem_8_12_chart20_denominator_ne_zero
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3)) :
    (u : R2) 0 ≠ 0 := by
  -- Rewrite overlap membership into the nonvanishing homogeneous coordinate condition.
  simpa [realProjectiveChartInvVector] using
    (mem_realProjectiveChartOverlap_iff 2 (Fin.last 2) (0 : Fin 3) (u : R2)).1 u.2

/-- Helper for Problem 8-12: on the `(2,1)` chart overlap, the second `z ≠ 0` coordinate is
nonzero, so the explicit transition formula has nonvanishing denominator. -/
theorem problem_8_12_chart21_denominator_ne_zero
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3)) :
    (u : R2) 1 ≠ 0 := by
  -- Rewrite overlap membership into the nonvanishing homogeneous coordinate condition.
  simpa [realProjectiveChartInvVector] using
    (mem_realProjectiveChartOverlap_iff 2 (Fin.last 2) (1 : Fin 3) (u : R2)).1 u.2

/-- Helper for Problem 8-12: on the `(0,1)` chart overlap, the first `x ≠ 0` coordinate is
nonzero, so the explicit transition formula has nonvanishing denominator. -/
theorem problem_8_12_chart01_denominator_ne_zero
    (u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3)) :
    (u : R2) 0 ≠ 0 := by
  -- Rewrite overlap membership into the nonvanishing homogeneous coordinate condition.
  simpa [realProjectiveChartInvVector] using
    (mem_realProjectiveChartOverlap_iff 2 (0 : Fin 3) (1 : Fin 3) (u : R2)).1 u.2

/-- Helper for Problem 8-12: on the `(2,0)` overlap, the chart transition is
`(a, b) ↦ (b / a, 1 / a)`. -/
theorem problem_8_12_chart20_transition_apply
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3)) :
    realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u =
      WithLp.toLp 2 ![(u : R2) 1 / (u : R2) 0, 1 / (u : R2) 0] := by
  -- Reduce the generic homogeneous-coordinate formula to the concrete `Fin 2` coordinates.
  ext i
  fin_cases i
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]

/-- Helper for Problem 8-12: on the `(2,1)` overlap, the chart transition is
`(a, b) ↦ (a / b, 1 / b)`. -/
theorem problem_8_12_chart21_transition_apply
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3)) :
    realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u =
      WithLp.toLp 2 ![(u : R2) 0 / (u : R2) 1, 1 / (u : R2) 1] := by
  -- Again, specialize the generic overlap formula to the concrete `Fin 2` coordinates.
  ext i
  fin_cases i
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]

/-- Helper for Problem 8-12: on the `(0,1)` overlap, the chart transition is
`(s, t) ↦ (1 / s, t / s)`. -/
theorem problem_8_12_chart01_transition_apply
    (u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3)) :
    realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u =
      WithLp.toLp 2 ![1 / (u : R2) 0, (u : R2) 1 / (u : R2) 0] := by
  -- Specialize the generic overlap formula to the concrete `Fin 2` coordinates.
  ext i
  fin_cases i
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]
  · simp [realProjectiveChartTransitionPartialHomeomorph_apply, realProjectiveChartInvVector,
      Fin.insertNth, Fin.succAboveCases]

/-- Helper for Problem 8-12: differentiating `(a, b) ↦ (b / a, 1 / a)` along `(-b, a)` produces
the `x ≠ 0` chart formula. -/
theorem problem_8_12_chart20_ambient_deriv
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2) (fun q : R2 ↦ WithLp.toLp 2 ![q 1 / q 0, 1 / q 0]) (u : R2)
        (problem_8_12_chart2_vectorField (u : R2)) =
      problem_8_12_chart0_vectorField
        (WithLp.toLp 2 ![(u : R2) 1 / (u : R2) 0, 1 / (u : R2) 0]) := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hu0 : (u : R2) 0 ≠ 0 := problem_8_12_chart20_denominator_ne_zero u
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (u : R2) := by
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (u : R2) := by
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 0)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0) (u : R2) := by
    -- Differentiate the reciprocal of the first coordinate at the overlap point.
    simpa [proj0] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (u : R2) 0) hu0).comp (u : R2) h0
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ q 1 / q 0)
        (((u : R2) 0)⁻¹ • proj1 +
          ((u : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp
            proj0)) (u : R2) := by
    -- Rewrite `b / a` as `b * a⁻¹` and differentiate product-wise.
    simpa [div_eq_mul_inv, proj0, proj1, add_comm, add_left_comm, add_assoc] using h1.mul hInv
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ 1 / q 0)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0) (u : R2) := by
    -- The second coordinate is just the reciprocal of the first source coordinate.
    simpa [one_div] using hInv
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 =>
        ((u : R2) 0)⁻¹ • proj1 +
          ((u : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp
            proj0)
    | 1 => (ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ (![q 1 / q 0, 1 / q 0] : Fin 2 → ℝ) i)
        (ContinuousLinearMap.pi f') (u : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt (fun q : R2 ↦ WithLp.toLp 2 ![q 1 / q 0, 1 / q 0])
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (u : R2) := by
    -- Transport the derivative from plain product coordinates back to the `PiLp` model.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hEval :
      fderiv ℝ (fun q : R2 ↦ WithLp.toLp 2 ![q 1 / q 0, 1 / q 0]) (u : R2)
          (WithLp.toLp 2 ![-(u : R2) 1, (u : R2) 0]) =
        WithLp.toLp 2
          ![1 + ((u : R2) 1 / (u : R2) 0) ^ (2 : ℕ),
            ((u : R2) 1 / (u : R2) 0) * (1 / (u : R2) 0)] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · change ((ContinuousLinearMap.pi f') !₂[-(u : R2) 1, (u : R2) 0] 0) =
        1 + ((u : R2) 1 / (u : R2) 0) ^ (2 : ℕ)
      simp [f', proj0, proj1]
      field_simp [hu0]
      ring
    · change ((ContinuousLinearMap.pi f') !₂[-(u : R2) 1, (u : R2) 0] 1) =
        ((u : R2) 1 / (u : R2) 0) * (1 / (u : R2) 0)
      simp [f', proj0, proj1]
      field_simp [hu0]
      ring
  simpa [problem_8_12_chart2_vectorField, problem_8_12_chart0_vectorField, mfderiv_eq_fderiv] using
    hEval

/-- Helper for Problem 8-12: differentiating `(a, b) ↦ (a / b, 1 / b)` along `(-b, a)` produces
the `y ≠ 0` chart formula. -/
theorem problem_8_12_chart21_ambient_deriv
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2) (fun q : R2 ↦ WithLp.toLp 2 ![q 0 / q 1, 1 / q 1]) (u : R2)
        (problem_8_12_chart2_vectorField (u : R2)) =
      problem_8_12_chart1_vectorField
        (WithLp.toLp 2 ![(u : R2) 0 / (u : R2) 1, 1 / (u : R2) 1]) := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hu1 : (u : R2) 1 ≠ 0 := problem_8_12_chart21_denominator_ne_zero u
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (u : R2) := by
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (u : R2) := by
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 1)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 1 ^ 2)⁻¹)).comp proj1) (u : R2) := by
    -- Differentiate the reciprocal of the second coordinate at the overlap point.
    simpa [proj1] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (u : R2) 1) hu1).comp (u : R2) h1
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ q 0 / q 1)
        (((u : R2) 1)⁻¹ • proj0 +
          ((u : R2) 0) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 1 ^ 2)⁻¹)).comp
            proj1)) (u : R2) := by
    -- Rewrite `a / b` as `a * b⁻¹` and differentiate product-wise.
    simpa [div_eq_mul_inv, proj0, proj1, add_comm, add_left_comm, add_assoc] using h0.mul hInv
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ 1 / q 1)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 1 ^ 2)⁻¹)).comp proj1) (u : R2) := by
    -- The second coordinate is the reciprocal of the second source coordinate.
    simpa [one_div] using hInv
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 =>
        ((u : R2) 1)⁻¹ • proj0 +
          ((u : R2) 0) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 1 ^ 2)⁻¹)).comp
            proj1)
    | 1 => (ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 1 ^ 2)⁻¹)).comp proj1
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ (![q 0 / q 1, 1 / q 1] : Fin 2 → ℝ) i)
        (ContinuousLinearMap.pi f') (u : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt (fun q : R2 ↦ WithLp.toLp 2 ![q 0 / q 1, 1 / q 1])
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (u : R2) := by
    -- Transport the derivative from plain product coordinates back to the `PiLp` model.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hEval :
      fderiv ℝ (fun q : R2 ↦ WithLp.toLp 2 ![q 0 / q 1, 1 / q 1]) (u : R2)
          (WithLp.toLp 2 ![-(u : R2) 1, (u : R2) 0]) =
        WithLp.toLp 2
          ![-(1 + ((u : R2) 0 / (u : R2) 1) ^ (2 : ℕ)),
            -(((u : R2) 0 / (u : R2) 1) * (1 / (u : R2) 1))] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · change ((ContinuousLinearMap.pi f') !₂[-(u : R2) 1, (u : R2) 0] 0) =
        -(1 + ((u : R2) 0 / (u : R2) 1) ^ (2 : ℕ))
      simp [f', proj0, proj1]
      field_simp [hu1]
      ring
    · change ((ContinuousLinearMap.pi f') !₂[-(u : R2) 1, (u : R2) 0] 1) =
        -(((u : R2) 0 / (u : R2) 1) * (1 / (u : R2) 1))
      simp [f', proj0, proj1]
      field_simp [hu1]
      ring
  simpa [problem_8_12_chart2_vectorField, problem_8_12_chart1_vectorField, mfderiv_eq_fderiv] using
    hEval

/-- Helper for Problem 8-12: differentiating `(s, t) ↦ (1 / s, t / s)` along
`(1 + s², s t)` produces the `y ≠ 0` chart formula. -/
theorem problem_8_12_chart01_ambient_deriv
    (u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2) (fun q : R2 ↦ WithLp.toLp 2 ![1 / q 0, q 1 / q 0]) (u : R2)
        (problem_8_12_chart0_vectorField (u : R2)) =
      problem_8_12_chart1_vectorField
        (WithLp.toLp 2 ![1 / (u : R2) 0, (u : R2) 1 / (u : R2) 0]) := by
  let proj0 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0
  let proj1 : R2 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hu0 : (u : R2) 0 ≠ 0 := problem_8_12_chart01_denominator_ne_zero u
  have h0 : HasFDerivAt (fun q : R2 ↦ q 0) proj0 (u : R2) := by
    simpa [proj0] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 0)
  have h1 : HasFDerivAt (fun q : R2 ↦ q 1) proj1 (u : R2) := by
    simpa [proj1] using
      (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 2 ↦ ℝ) (f := (u : R2)) 1)
  have hInv :
      HasFDerivAt (fun q : R2 ↦ (q 0)⁻¹)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0) (u : R2) := by
    -- Differentiate the reciprocal of the first coordinate at the overlap point.
    simpa [proj0] using
      (hasFDerivAt_inv (𝕜 := ℝ) (x := (u : R2) 0) hu0).comp (u : R2) h0
  have hFirst :
      HasFDerivAt (fun q : R2 ↦ 1 / q 0)
        ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0) (u : R2) := by
    -- The first coordinate is the reciprocal of the first source coordinate.
    simpa [one_div] using hInv
  have hSecond :
      HasFDerivAt (fun q : R2 ↦ q 1 / q 0)
        (((u : R2) 0)⁻¹ • proj1 +
          ((u : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp
            proj0)) (u : R2) := by
    -- Rewrite `t / s` as `t * s⁻¹` and differentiate product-wise.
    simpa [div_eq_mul_inv, proj0, proj1, add_comm, add_left_comm, add_assoc] using h1.mul hInv
  let f' : Fin 2 → R2 →L[ℝ] ℝ := fun i =>
    match i with
    | 0 => (ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp proj0
    | 1 =>
        ((u : R2) 0)⁻¹ • proj1 +
          ((u : R2) 1) • ((ContinuousLinearMap.toSpanSingleton ℝ (-((u : R2) 0 ^ 2)⁻¹)).comp
            proj0)
  let toR2 : (Fin 2 → ℝ) ≃L[ℝ] R2 :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hAmbientPi :
      HasFDerivAt (fun q : R2 ↦ fun i : Fin 2 ↦ (![1 / q 0, q 1 / q 0] : Fin 2 → ℝ) i)
        (ContinuousLinearMap.pi f') (u : R2) := by
    -- Assemble the ambient derivative in plain product coordinates first.
    refine hasFDerivAt_pi.2 ?_
    intro i
    fin_cases i
    · simpa [f'] using hFirst
    · simpa [f'] using hSecond
  have hAmbient :
      HasFDerivAt (fun q : R2 ↦ WithLp.toLp 2 ![1 / q 0, q 1 / q 0])
        (toR2.toContinuousLinearMap.comp (ContinuousLinearMap.pi f')) (u : R2) := by
    -- Transport the derivative from plain product coordinates back to the `PiLp` model.
    simpa [toR2, Function.comp] using (toR2.comp_hasFDerivAt_iff.2 hAmbientPi)
  have hEval :
      fderiv ℝ (fun q : R2 ↦ WithLp.toLp 2 ![1 / q 0, q 1 / q 0]) (u : R2)
          (WithLp.toLp 2 ![1 + (u : R2) 0 ^ (2 : ℕ), (u : R2) 0 * (u : R2) 1]) =
        WithLp.toLp 2
          ![-(1 + (1 / (u : R2) 0) ^ (2 : ℕ)),
            -((1 / (u : R2) 0) * ((u : R2) 1 / (u : R2) 0))] := by
    rw [hAmbient.fderiv]
    ext i
    fin_cases i
    · change ((ContinuousLinearMap.pi f') !₂[1 + (u : R2) 0 ^ (2 : ℕ), (u : R2) 0 * (u : R2) 1] 0)
        = -(1 + (1 / (u : R2) 0) ^ (2 : ℕ))
      simp [f', proj0, proj1]
      field_simp [hu0]
      ring
    · change ((ContinuousLinearMap.pi f') !₂[1 + (u : R2) 0 ^ (2 : ℕ), (u : R2) 0 * (u : R2) 1] 1)
        = -((1 / (u : R2) 0) * ((u : R2) 1 / (u : R2) 0))
      simp [f', proj0, proj1]
      field_simp [hu0]
      ring
  simpa [problem_8_12_chart0_vectorField, problem_8_12_chart1_vectorField, mfderiv_eq_fderiv] using
    hEval

/-- Helper for Problem 8-12: the `(2,0)` chart transition pushes the `z ≠ 0` coordinate field to
the `x ≠ 0` coordinate field. -/
theorem problem_8_12_chart20_transition_pushforward
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u
        (VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2)
          problem_8_12_chart2_vectorField u) =
      problem_8_12_chart0_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u) := by
  let G : R2 → R2 := fun q ↦ WithLp.toLp 2 ![q 1 / q 0, 1 / q 0]
  let XU :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2)
          problem_8_12_chart2_vectorField
  have hEq :
      realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) =
        G ∘ (Subtype.val :
          realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) := by
    funext v
    simpa [G] using problem_8_12_chart20_transition_apply v
  rw [hEq]
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hG :
      MDifferentiableAt (𝓡 2) (𝓡 2) G (u : R2) := by
    have hGOn : ContDiffOn ℝ ∞ G (realProjectiveChartOverlap 2 (Fin.last 2) (0 : Fin 3)) := by
      refine (realProjectiveChartTransition_contDiffOn 2 (Fin.last 2) (0 : Fin 3)).congr ?_
      intro q hq
      simpa [G] using
        problem_8_12_chart20_transition_apply
          (u := ⟨q, hq⟩)
    have hGAt : ContDiffAt ℝ ∞ G (u : R2) := by
      exact hGOn.contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (Fin.last 2) (0 : Fin 3)).mem_nhds u.2)
    exact hGAt.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply (x := u) (g := G)
    (f := (Subtype.val :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2)) hG hsub (XU u)]
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart2_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3))
        problem_8_12_chart2_vectorField u
  simpa [G, XU] using hsubApply ▸ problem_8_12_chart20_ambient_deriv u

/-- Helper for Problem 8-12: the `(2,1)` chart transition pushes the `z ≠ 0` coordinate field to
the `y ≠ 0` coordinate field. -/
theorem problem_8_12_chart21_transition_pushforward
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u
        (VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2)
          problem_8_12_chart2_vectorField u) =
      problem_8_12_chart1_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u) := by
  let G : R2 → R2 := fun q ↦ WithLp.toLp 2 ![q 0 / q 1, 1 / q 1]
  let XU :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2)
          problem_8_12_chart2_vectorField
  have hEq :
      realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) =
        G ∘ (Subtype.val :
          realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) := by
    funext v
    simpa [G] using problem_8_12_chart21_transition_apply v
  rw [hEq]
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hG :
      MDifferentiableAt (𝓡 2) (𝓡 2) G (u : R2) := by
    have hGOn : ContDiffOn ℝ ∞ G (realProjectiveChartOverlap 2 (Fin.last 2) (1 : Fin 3)) := by
      refine (realProjectiveChartTransition_contDiffOn 2 (Fin.last 2) (1 : Fin 3)).congr ?_
      intro q hq
      simpa [G] using
        problem_8_12_chart21_transition_apply
          (u := ⟨q, hq⟩)
    have hGAt : ContDiffAt ℝ ∞ G (u : R2) := by
      exact hGOn.contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (Fin.last 2) (1 : Fin 3)).mem_nhds u.2)
    exact hGAt.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply (x := u) (g := G)
    (f := (Subtype.val :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2)) hG hsub (XU u)]
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart2_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3))
        problem_8_12_chart2_vectorField u
  simpa [G, XU] using hsubApply ▸ problem_8_12_chart21_ambient_deriv u

/-- Helper for Problem 8-12: the `(0,1)` chart transition pushes the `x ≠ 0` coordinate field to
the `y ≠ 0` coordinate field. -/
theorem problem_8_12_chart01_transition_pushforward
    (u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3)) :
    mfderiv (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u
        (VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2)
          problem_8_12_chart0_vectorField u) =
      problem_8_12_chart1_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u) := by
  let G : R2 → R2 := fun q ↦ WithLp.toLp 2 ![1 / q 0, q 1 / q 0]
  let XU :
      realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2)
          problem_8_12_chart0_vectorField
  have hEq :
      realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) =
        G ∘ (Subtype.val :
          realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) := by
    funext v
    simpa [G] using problem_8_12_chart01_transition_apply v
  rw [hEq]
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hG :
      MDifferentiableAt (𝓡 2) (𝓡 2) G (u : R2) := by
    have hGOn : ContDiffOn ℝ ∞ G (realProjectiveChartOverlap 2 (0 : Fin 3) (1 : Fin 3)) := by
      refine (realProjectiveChartTransition_contDiffOn 2 (0 : Fin 3) (1 : Fin 3)).congr ?_
      intro q hq
      simpa [G] using
        problem_8_12_chart01_transition_apply
          (u := ⟨q, hq⟩)
    have hGAt : ContDiffAt ℝ ∞ G (u : R2) := by
      exact hGOn.contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (0 : Fin 3) (1 : Fin 3)).mem_nhds u.2)
    exact hGAt.contMDiffAt.mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply (x := u) (g := G)
    (f := (Subtype.val :
      realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2)) hG hsub (XU u)]
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart0_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3))
        problem_8_12_chart0_vectorField u
  simpa [G, XU] using hsubApply ▸ problem_8_12_chart01_ambient_deriv u

/-- Helper for Problem 8-12: each inverse standard affine chart on `ℝP²` is smooth. -/
theorem problem_8_12_realProjectiveChart_symm_contMDiff (i : Fin 3) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (realProjectiveChart 2 i).symm := by
  intro u
  simpa using
    contMDiffAt_symm_of_mem_maximalAtlas
      (problem_8_12_realProjectiveChart_mem_maximalAtlas i) (by simp : u ∈ Set.univ)

/-- Helper for Problem 8-12: on the `(2,0)` overlap, the two chartwise local lifts agree. -/
theorem problem_8_12_chart20_localLift_eq
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3)) :
    problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField (u : R2) =
      problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u) := by
  let XU :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2)
          problem_8_12_chart2_vectorField
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hchart0 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (0 : Fin 3)).mdifferentiableAt
      (by simp)
  have hchart2 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (Fin.last 2)).mdifferentiableAt
      (by simp)
  have htransition :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u := by
    have hcont :
        ContDiffAt ℝ ∞
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u := by
      exact (realProjectiveChartTransition_contDiffOn 2 (Fin.last 2) (0 : Fin 3)).contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (Fin.last 2) (0 : Fin 3)).mem_nhds u.2)
    exact hcont.contMDiffAt.mdifferentiableAt (by simp)
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart2_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3))
        problem_8_12_chart2_vectorField u
  have hfun :
      (realProjectiveChart 2 (0 : Fin 3)).symm ∘
          realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) =
        (realProjectiveChart 2 (Fin.last 2)).symm ∘
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) := by
    funext v
    simp [realProjectiveChartTransitionPartialHomeomorph, OpenPartialHomeomorph.trans_apply]
  have hcomp :
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u
            (XU u)) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u
            (XU u)) := by
    calc
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u
            (XU u))
          =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (0 : Fin 3)).symm ∘
            realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u
          (XU u) := by
            symm
            simpa [Function.comp] using
              (mfderiv_comp_apply (x := u)
                (g := (realProjectiveChart 2 (0 : Fin 3)).symm)
                (f := realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3))
                hchart0 htransition (XU u))
      _ =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (Fin.last 2)).symm ∘
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2)) u
          (XU u) := by
            rw [hfun]
      _ =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u
            (XU u)) := by
              simpa [Function.comp] using
                (mfderiv_comp_apply (x := u)
                  (g := (realProjectiveChart 2 (Fin.last 2)).symm)
                  (f := (Subtype.val :
                    realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2))
                  hchart2 hsub (XU u))
  refine Bundle.TotalSpace.ext ?_ ?_
  · simpa [problem_8_12_localLift] using congrArg (fun f ↦ f u) hfun.symm
  · refine heq_of_eq ?_
    simpa [problem_8_12_localLift, XU] using
      calc
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
            (problem_8_12_chart2_vectorField (u : R2))
            =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
            (mfderiv (𝓡 2) (𝓡 2)
              (Subtype.val :
                realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) → R2) u
              (XU u)) := by rw [hsubApply.symm]
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u)
            (mfderiv (𝓡 2) (𝓡 2)
              (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3)) u
              (XU u)) := hcomp.symm
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u)
            (problem_8_12_chart0_vectorField
              (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (0 : Fin 3) u)) := by
                rw [problem_8_12_chart20_transition_pushforward]

/-- Helper for Problem 8-12: on the `(2,1)` overlap, the two chartwise local lifts agree. -/
theorem problem_8_12_chart21_localLift_eq
    (u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3)) :
    problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField (u : R2) =
      problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u) := by
  let XU :
      realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2)
          problem_8_12_chart2_vectorField
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hchart1 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (1 : Fin 3)).mdifferentiableAt
      (by simp)
  have hchart2 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (Fin.last 2)).mdifferentiableAt
      (by simp)
  have htransition :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u := by
    have hcont :
        ContDiffAt ℝ ∞
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u := by
      exact (realProjectiveChartTransition_contDiffOn 2 (Fin.last 2) (1 : Fin 3)).contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (Fin.last 2) (1 : Fin 3)).mem_nhds u.2)
    exact hcont.contMDiffAt.mdifferentiableAt (by simp)
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart2_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3))
        problem_8_12_chart2_vectorField u
  have hfun :
      (realProjectiveChart 2 (1 : Fin 3)).symm ∘
          realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) =
        (realProjectiveChart 2 (Fin.last 2)).symm ∘
          (Subtype.val : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) := by
    funext v
    simp [realProjectiveChartTransitionPartialHomeomorph, OpenPartialHomeomorph.trans_apply]
  have hcomp :
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u
            (XU u)) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u
            (XU u)) := by
    calc
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u
            (XU u))
          =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (1 : Fin 3)).symm ∘
            realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u
          (XU u) := by
            symm
            simpa [Function.comp] using
              (mfderiv_comp_apply (x := u)
                (g := (realProjectiveChart 2 (1 : Fin 3)).symm)
                (f := realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3))
                hchart1 htransition (XU u))
      _ =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (Fin.last 2)).symm ∘
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2)) u
          (XU u) := by
            rw [hfun]
      _ =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u
            (XU u)) := by
              simpa [Function.comp] using
                (mfderiv_comp_apply (x := u)
                  (g := (realProjectiveChart 2 (Fin.last 2)).symm)
                  (f := (Subtype.val :
                    realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2))
                  hchart2 hsub (XU u))
  refine Bundle.TotalSpace.ext ?_ ?_
  · simpa [problem_8_12_localLift] using congrArg (fun f ↦ f u) hfun.symm
  · refine heq_of_eq ?_
    simpa [problem_8_12_localLift, XU] using
      calc
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
            (problem_8_12_chart2_vectorField (u : R2))
            =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (Fin.last 2)).symm (u : R2)
            (mfderiv (𝓡 2) (𝓡 2)
              (Subtype.val :
                realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) → R2) u
              (XU u)) := by rw [hsubApply.symm]
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u)
            (mfderiv (𝓡 2) (𝓡 2)
              (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3)) u
              (XU u)) := hcomp.symm
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u)
            (problem_8_12_chart1_vectorField
              (realProjectiveChartTransitionPartialHomeomorph 2 (Fin.last 2) (1 : Fin 3) u)) := by
                rw [problem_8_12_chart21_transition_pushforward]

/-- Helper for Problem 8-12: on the `(0,1)` overlap, the two chartwise local lifts agree. -/
theorem problem_8_12_chart01_localLift_eq
    (u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3)) :
    problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField (u : R2) =
      problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField
        (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u) := by
  let XU :
      realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) →
        fun x ↦ TangentSpace (𝓡 2) x := VectorField.mpullback (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2)
          problem_8_12_chart0_vectorField
  have hsub :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u := by
    exact
      (contMDiff_subtype_val :
        ContMDiff (𝓡 2) (𝓡 2) ∞
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2))
        .mdifferentiableAt (by simp)
  have hchart1 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
        (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (1 : Fin 3)).mdifferentiableAt
      (by simp)
  have hchart0 :
      MDifferentiableAt (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm (u : R2) := by
    exact (problem_8_12_realProjectiveChart_symm_contMDiff (0 : Fin 3)).mdifferentiableAt
      (by simp)
  have htransition :
      MDifferentiableAt (𝓡 2) (𝓡 2)
        (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u := by
    have hcont :
        ContDiffAt ℝ ∞
          (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u := by
      exact (realProjectiveChartTransition_contDiffOn 2 (0 : Fin 3) (1 : Fin 3)).contDiffAt
        ((realProjectiveChartOverlap_isOpen 2 (0 : Fin 3) (1 : Fin 3)).mem_nhds u.2)
    exact hcont.contMDiffAt.mdifferentiableAt (by simp)
  have hsubApply :
      mfderiv (𝓡 2) (𝓡 2)
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u
          (XU u) =
        problem_8_12_chart0_vectorField (u : R2) := by
    simpa [XU, tangentMap] using
      problem_8_12_tangentMap_subtype_val_pullback_eq
        (realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3))
        problem_8_12_chart0_vectorField u
  have hfun :
      (realProjectiveChart 2 (1 : Fin 3)).symm ∘
          realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) =
        (realProjectiveChart 2 (0 : Fin 3)).symm ∘
          (Subtype.val : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) := by
    funext v
    simp [realProjectiveChartTransitionPartialHomeomorph, OpenPartialHomeomorph.trans_apply]
  have hcomp :
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u
            (XU u)) =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u
            (XU u)) := by
    calc
      mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
          (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u)
          (mfderiv (𝓡 2) (𝓡 2)
            (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u
            (XU u))
          =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (1 : Fin 3)).symm ∘
            realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u
          (XU u) := by
            symm
            simpa [Function.comp] using
              (mfderiv_comp_apply (x := u)
                (g := (realProjectiveChart 2 (1 : Fin 3)).symm)
                (f := realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3))
                hchart1 htransition (XU u))
      _ =
        mfderiv (𝓡 2) (𝓡 2)
          ((realProjectiveChart 2 (0 : Fin 3)).symm ∘
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2)) u
          (XU u) := by
            rw [hfun]
      _ =
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm (u : R2)
          (mfderiv (𝓡 2) (𝓡 2)
            (Subtype.val :
              realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u
            (XU u)) := by
              simpa [Function.comp] using
                (mfderiv_comp_apply (x := u)
                  (g := (realProjectiveChart 2 (0 : Fin 3)).symm)
                  (f := (Subtype.val :
                    realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2))
                  hchart0 hsub (XU u))
  refine Bundle.TotalSpace.ext ?_ ?_
  · simpa [problem_8_12_localLift] using congrArg (fun f ↦ f u) hfun.symm
  · refine heq_of_eq ?_
    simpa [problem_8_12_localLift, XU] using
      calc
        mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm (u : R2)
            (problem_8_12_chart0_vectorField (u : R2))
            =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (0 : Fin 3)).symm (u : R2)
            (mfderiv (𝓡 2) (𝓡 2)
              (Subtype.val :
                realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) → R2) u
              (XU u)) := by rw [hsubApply.symm]
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u)
            (mfderiv (𝓡 2) (𝓡 2)
              (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3)) u
              (XU u)) := hcomp.symm
        _ =
          mfderiv (𝓡 2) (𝓡 2) (realProjectiveChart 2 (1 : Fin 3)).symm
            (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u)
            (problem_8_12_chart1_vectorField
              (realProjectiveChartTransitionPartialHomeomorph 2 (0 : Fin 3) (1 : Fin 3) u)) := by
                rw [problem_8_12_chart01_transition_pushforward]

/-- Helper for Problem 8-12: on the `x ≠ 0` chart domain, `problem_8_12_roughLift` agrees with
the `x ≠ 0` local lift. -/
theorem problem_8_12_roughLift_eq_chart0
    (q : RealProjectiveSpace 2)
    (h0 : q ∈ realProjectiveChartDomain 2 (0 : Fin 3)) :
    problem_8_12_roughLift q =
      problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField
        ((realProjectiveChart 2 (0 : Fin 3)) q) := by
  by_cases h2 : q ∈ realProjectiveChartDomain 2 (Fin.last 2)
  · let u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (0 : Fin 3) :=
      ⟨(realProjectiveChart 2 (Fin.last 2)) q, by
        rw [realProjectiveChartOverlap, realProjectiveChartTransitionPartialHomeomorph,
          OpenPartialHomeomorph.trans_source]
        simpa [h2] using h0⟩
    simpa [problem_8_12_roughLift, h2, h0, u, realProjectiveChartTransitionPartialHomeomorph,
      OpenPartialHomeomorph.trans_apply] using problem_8_12_chart20_localLift_eq u
  · simp [problem_8_12_roughLift, h2, h0]

/-- Helper for Problem 8-12: on the `y ≠ 0` chart domain, `problem_8_12_roughLift` agrees with
the `y ≠ 0` local lift. -/
theorem problem_8_12_roughLift_eq_chart1
    (q : RealProjectiveSpace 2)
    (h1 : q ∈ realProjectiveChartDomain 2 (1 : Fin 3)) :
    problem_8_12_roughLift q =
      problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField
        ((realProjectiveChart 2 (1 : Fin 3)) q) := by
  by_cases h2 : q ∈ realProjectiveChartDomain 2 (Fin.last 2)
  · let u : realProjectiveChartOverlapOpens 2 (Fin.last 2) (1 : Fin 3) :=
      ⟨(realProjectiveChart 2 (Fin.last 2)) q, by
        rw [realProjectiveChartOverlap, realProjectiveChartTransitionPartialHomeomorph,
          OpenPartialHomeomorph.trans_source]
        simpa [h2] using h1⟩
    simpa [problem_8_12_roughLift, h2, h1, u, realProjectiveChartTransitionPartialHomeomorph,
      OpenPartialHomeomorph.trans_apply] using problem_8_12_chart21_localLift_eq u
  · by_cases h0 : q ∈ realProjectiveChartDomain 2 (0 : Fin 3)
    · let u : realProjectiveChartOverlapOpens 2 (0 : Fin 3) (1 : Fin 3) :=
        ⟨(realProjectiveChart 2 (0 : Fin 3)) q, by
          rw [realProjectiveChartOverlap, realProjectiveChartTransitionPartialHomeomorph,
            OpenPartialHomeomorph.trans_source]
          simpa [h0] using h1⟩
      simpa [problem_8_12_roughLift, h2, h0, h1, u, realProjectiveChartTransitionPartialHomeomorph,
        OpenPartialHomeomorph.trans_apply] using problem_8_12_chart01_localLift_eq u
    · simp [problem_8_12_roughLift, h2, h0]

/-- Helper for Problem 8-12: the piecewise-defined tangent-bundle lift is smooth because on each
standard affine chart domain it agrees with one smooth local lift. -/
theorem problem_8_12_roughLift_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ problem_8_12_roughLift := by
  refine contMDiff_of_locally_contMDiffOn ?_
  intro q
  rcases real_projective_space_has_standard_chart 2 q with ⟨i, hi⟩
  fin_cases i
  · refine ⟨realProjectiveChartDomain 2 (0 : Fin 3), realProjectiveChartDomain_isOpen 2 (0 : Fin 3),
      hi, ?_⟩
    have hchart :
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (realProjectiveChart 2 (0 : Fin 3))
          (realProjectiveChartDomain 2 (0 : Fin 3)) :=
      contMDiffOn_of_mem_maximalAtlas
        (problem_8_12_realProjectiveChart_mem_maximalAtlas (0 : Fin 3))
    have hlocal :
        ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞
          (problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField ∘
            realProjectiveChart 2 (0 : Fin 3))
          (realProjectiveChartDomain 2 (0 : Fin 3)) := by
      simpa [Function.comp] using
        (problem_8_12_localLift_contMDiff (0 : Fin 3)
          problem_8_12_chart0_vectorField_contMDiff).comp_contMDiffOn hchart
    exact hlocal.congr fun x hx ↦ (problem_8_12_roughLift_eq_chart0 x hx).symm
  · refine ⟨realProjectiveChartDomain 2 (1 : Fin 3), realProjectiveChartDomain_isOpen 2 (1 : Fin 3),
      hi, ?_⟩
    have hchart :
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (realProjectiveChart 2 (1 : Fin 3))
          (realProjectiveChartDomain 2 (1 : Fin 3)) :=
      contMDiffOn_of_mem_maximalAtlas
        (problem_8_12_realProjectiveChart_mem_maximalAtlas (1 : Fin 3))
    have hlocal :
        ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞
          (problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField ∘
            realProjectiveChart 2 (1 : Fin 3))
          (realProjectiveChartDomain 2 (1 : Fin 3)) := by
      simpa [Function.comp] using
        (problem_8_12_localLift_contMDiff (1 : Fin 3)
          problem_8_12_chart1_vectorField_contMDiff).comp_contMDiffOn hchart
    exact hlocal.congr fun x hx ↦ (problem_8_12_roughLift_eq_chart1 x hx).symm
  · refine ⟨realProjectiveChartDomain 2 (Fin.last 2),
      realProjectiveChartDomain_isOpen 2 (Fin.last 2), hi, ?_⟩
    have hchart :
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (realProjectiveChart 2 (Fin.last 2))
          (realProjectiveChartDomain 2 (Fin.last 2)) :=
      contMDiffOn_of_mem_maximalAtlas
        (problem_8_12_realProjectiveChart_mem_maximalAtlas (Fin.last 2))
    have hlocal :
        ContMDiffOn (𝓡 2) (𝓡 2).tangent ∞
          (problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField ∘
            realProjectiveChart 2 (Fin.last 2))
          (realProjectiveChartDomain 2 (Fin.last 2)) := by
      simpa [Function.comp] using
        (problem_8_12_localLift_contMDiff (Fin.last 2)
          problem_8_12_chart2_vectorField_contMDiff).comp_contMDiffOn hchart
    exact hlocal.congr fun x hx ↦ by
      simp [problem_8_12_roughLift, hx, Function.comp]

/-- Problem 8-12: there exists a smooth vector field `Y` on `ℝP²` that is related to
the standard affine inclusion `(realProjectiveChart 2 (Fin.last 2)).symm : ℝ² → ℝP²`
and to `problem_8_12_X`, and in the three standard affine charts of Example 1.5 its coordinate
representations are the vector fields recorded above. -/
theorem problem_8_12_exists_rotation_lift :
    ∃ Y : SmoothProjectiveVectorField,
      VectorField.f_related (realProjectiveChart 2 (Fin.last 2)).symm problem_8_12_X Y ∧
        Problem812ChartFormulas Y := by
  have hproj : ∀ q : RealProjectiveSpace 2, (problem_8_12_roughLift q).proj = q := by
    intro q
    rcases real_projective_space_has_standard_chart 2 q with ⟨i, hi⟩
    fin_cases i
    · calc
        (problem_8_12_roughLift q).proj =
          (problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField
            ((realProjectiveChart 2 (0 : Fin 3)) q)).proj := by
              simpa using congrArg Bundle.TotalSpace.proj
                (problem_8_12_roughLift_eq_chart0 q hi)
        _ = q := by
              simpa [problem_8_12_localLift] using
                (realProjectiveChart 2 (0 : Fin 3)).left_inv hi
    · calc
        (problem_8_12_roughLift q).proj =
          (problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField
            ((realProjectiveChart 2 (1 : Fin 3)) q)).proj := by
              simpa using congrArg Bundle.TotalSpace.proj
                (problem_8_12_roughLift_eq_chart1 q hi)
        _ = q := by
              simpa [problem_8_12_localLift] using
                (realProjectiveChart 2 (1 : Fin 3)).left_inv hi
    · calc
        (problem_8_12_roughLift q).proj =
          (problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField
            ((realProjectiveChart 2 (Fin.last 2)) q)).proj := by
              simp [problem_8_12_roughLift, hi]
        _ = q := by
              simpa [problem_8_12_localLift] using
                (realProjectiveChart 2 (Fin.last 2)).left_inv hi
  rcases smoothVectorFieldOfDescendedTangentMap
      (J := 𝓡 2) (N := RealProjectiveSpace 2)
      problem_8_12_roughLift_contMDiff hproj with ⟨Y, hYeq⟩
  refine ⟨Y, ?_, ?_⟩
  · refine ⟨problem_8_12_realProjectiveChart_symm_contMDiff (Fin.last 2), ?_⟩
    intro u
    have hTotal :
        ({ proj := (realProjectiveChart 2 (Fin.last 2)).symm u,
            snd := Y ((realProjectiveChart 2 (Fin.last 2)).symm u) } :
          TangentBundle (𝓡 2) (RealProjectiveSpace 2)) =
          problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField u := by
      calc
        ({ proj := (realProjectiveChart 2 (Fin.last 2)).symm u,
            snd := Y ((realProjectiveChart 2 (Fin.last 2)).symm u) } :
          TangentBundle (𝓡 2) (RealProjectiveSpace 2))
            =
          problem_8_12_roughLift ((realProjectiveChart 2 (Fin.last 2)).symm u) := by
              simpa using congrFun hYeq ((realProjectiveChart 2 (Fin.last 2)).symm u)
        _ = problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField u := by
              simp [problem_8_12_roughLift]
    simpa [problem_8_12_localLift, problem_8_12_chart2_vectorField, problem_8_12_X] using
      congrArg Bundle.TotalSpace.snd hTotal
  · refine ⟨?_, ?_, ?_⟩
    · intro u
      have hTotal :
          ({ proj := (realProjectiveChart 2 (0 : Fin 3)).symm u,
              snd := Y ((realProjectiveChart 2 (0 : Fin 3)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2)) =
            problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField u := by
        calc
          ({ proj := (realProjectiveChart 2 (0 : Fin 3)).symm u,
              snd := Y ((realProjectiveChart 2 (0 : Fin 3)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2))
              =
            problem_8_12_roughLift ((realProjectiveChart 2 (0 : Fin 3)).symm u) := by
                simpa using congrFun hYeq ((realProjectiveChart 2 (0 : Fin 3)).symm u)
          _ = problem_8_12_localLift (0 : Fin 3) problem_8_12_chart0_vectorField u := by
                simpa using
                  problem_8_12_roughLift_eq_chart0
                    ((realProjectiveChart 2 (0 : Fin 3)).symm u)
                    (realProjectiveChart_symm_mem_domain 2 (0 : Fin 3) u)
        simpa [problem_8_12_localLift] using congrArg Bundle.TotalSpace.snd hTotal
    · intro u
      have hTotal :
          ({ proj := (realProjectiveChart 2 (1 : Fin 3)).symm u,
              snd := Y ((realProjectiveChart 2 (1 : Fin 3)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2)) =
            problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField u := by
        calc
          ({ proj := (realProjectiveChart 2 (1 : Fin 3)).symm u,
              snd := Y ((realProjectiveChart 2 (1 : Fin 3)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2))
              =
            problem_8_12_roughLift ((realProjectiveChart 2 (1 : Fin 3)).symm u) := by
                simpa using congrFun hYeq ((realProjectiveChart 2 (1 : Fin 3)).symm u)
          _ = problem_8_12_localLift (1 : Fin 3) problem_8_12_chart1_vectorField u := by
                simpa using
                  problem_8_12_roughLift_eq_chart1
                    ((realProjectiveChart 2 (1 : Fin 3)).symm u)
                    (realProjectiveChart_symm_mem_domain 2 (1 : Fin 3) u)
        simpa [problem_8_12_localLift] using congrArg Bundle.TotalSpace.snd hTotal
    · intro u
      have hTotal :
          ({ proj := (realProjectiveChart 2 (Fin.last 2)).symm u,
              snd := Y ((realProjectiveChart 2 (Fin.last 2)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2)) =
            problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField u := by
        calc
          ({ proj := (realProjectiveChart 2 (Fin.last 2)).symm u,
              snd := Y ((realProjectiveChart 2 (Fin.last 2)).symm u) } :
            TangentBundle (𝓡 2) (RealProjectiveSpace 2))
              =
            problem_8_12_roughLift ((realProjectiveChart 2 (Fin.last 2)).symm u) := by
                simpa using congrFun hYeq ((realProjectiveChart 2 (Fin.last 2)).symm u)
          _ = problem_8_12_localLift (Fin.last 2) problem_8_12_chart2_vectorField u := by
                simp [problem_8_12_roughLift]
        simpa [problem_8_12_localLift] using congrArg Bundle.TotalSpace.snd hTotal

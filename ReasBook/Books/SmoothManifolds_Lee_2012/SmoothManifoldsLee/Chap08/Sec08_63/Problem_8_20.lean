import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Example_8_36
import SmoothManifolds_Lee_2012.Chap08.Sec08_63.Problem_8_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold Matrix
open NormedSpace

noncomputable section

-- Semantic recall note: `lean_leansearch` returned `ContDiff.lieBracket_vectorField`,
-- `VectorField.mlieBracket`, and `VectorField.mpullback_mlieBracket`; local chapter precedent in
-- `Example_8_36` packages the canonical Lie ring and Lie algebra structure on bundled smooth
-- vector fields, so the ambient owner here is the bundled smooth-vector-field type on `ℝ^3`.

local notation "R3" => Fin 3 → ℝ
local notation "R3Base" => EuclideanSpace ℝ (Fin 3)
local notation "R3Model" => 𝓘(ℝ, R3Base)
local notation "SmoothVectorField" =>
  Cₛ^∞⟮R3Model; R3Base, fun p : R3Base ↦ TangentSpace R3Model p⟯

attribute [local instance] Cross.lieRing Cross.lieAlgebra

/-- Helper for Problem 8-20: the derivative of a Euclidean coordinate projection extracts the
matching coordinate of the tangent vector. -/
private theorem problem_8_20_fderiv_coord_apply (p v : R3Base) (i : Fin 3) :
    fderiv ℝ (fun q : R3Base ↦ q i) p v = v i := by
  -- The coordinate projections are continuous linear maps, so their derivative is themselves.
  rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p i).fderiv]
  rfl

/-- Helper for Problem 8-20: the Euclidean coordinate vector field underlying `X`. -/
private def problem_8_20_XCoords (p : R3Base) : R3Base :=
  WithLp.toLp 2 ![(0 : ℝ), -p 2, p 1]

/-- Helper for Problem 8-20: the Euclidean coordinate vector field underlying `Y`. -/
private def problem_8_20_YCoords (p : R3Base) : R3Base :=
  WithLp.toLp 2 ![p 2, (0 : ℝ), -p 0]

/-- Helper for Problem 8-20: the Euclidean coordinate vector field underlying `Z`. -/
private def problem_8_20_ZCoords (p : R3Base) : R3Base :=
  WithLp.toLp 2 ![-p 1, p 0, (0 : ℝ)]

/-- Helper for Problem 8-20: the raw tangent-bundle section underlying
`X = y ∂/∂z - z ∂/∂y`. -/
private def problem_8_20_rawX (p : R3Base) : TangentSpace R3Model p :=
  (fromTangentSpace p).symm (problem_8_20_XCoords p)

/-- Helper for Problem 8-20: the raw section `problem_8_20_rawX` is smooth. -/
private theorem problem_8_20_rawX_contMDiff :
    ContMDiff R3Model (𝓘(ℝ, R3Base)).tangent ∞ (T% problem_8_20_rawX) := by
  -- On a vector space, smoothness of a tangent field is equivalent to ordinary smoothness.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each coordinate of `problem_8_20_XCoords` is polynomial in the ambient coordinates.
  simpa [problem_8_20_rawX, problem_8_20_XCoords] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : R3Base ↦ (0 : ℝ))
      · simpa using
          ((contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 2)).neg
      · simpa using
          (contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 1))

/-- The vector field `X = y ∂/∂z - z ∂/∂y` from Problem 8-20, bundled as a smooth vector field on
`ℝ^3`. -/
def problem_8_20_X : SmoothVectorField :=
  ⟨problem_8_20_rawX, problem_8_20_rawX_contMDiff⟩

/-- Coordinate formula for `problem_8_20_X` under the canonical Euclidean tangent-space
identification. -/
theorem problem_8_20_X_apply (p : R3Base) :
    fromTangentSpace p (problem_8_20_X p) = problem_8_20_XCoords p := rfl

/-- Helper for Problem 8-20: the raw tangent-bundle section underlying
`Y = z ∂/∂x - x ∂/∂z`. -/
private def problem_8_20_rawY (p : R3Base) : TangentSpace R3Model p :=
  (fromTangentSpace p).symm (problem_8_20_YCoords p)

/-- Helper for Problem 8-20: the raw section `problem_8_20_rawY` is smooth. -/
private theorem problem_8_20_rawY_contMDiff :
    ContMDiff R3Model (𝓘(ℝ, R3Base)).tangent ∞ (T% problem_8_20_rawY) := by
  -- On a vector space, smoothness of a tangent field is equivalent to ordinary smoothness.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each coordinate of `problem_8_20_YCoords` is polynomial in the ambient coordinates.
  simpa [problem_8_20_rawY, problem_8_20_YCoords] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · simpa using
          (contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 2)
      · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : R3Base ↦ (0 : ℝ))
      · simpa using
          ((contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 0)).neg)

/-- The vector field `Y = z ∂/∂x - x ∂/∂z` from Problem 8-20, bundled as a smooth vector field on
`ℝ^3`. -/
def problem_8_20_Y : SmoothVectorField :=
  ⟨problem_8_20_rawY, problem_8_20_rawY_contMDiff⟩

/-- Coordinate formula for `problem_8_20_Y` under the canonical Euclidean tangent-space
identification. -/
theorem problem_8_20_Y_apply (p : R3Base) :
    fromTangentSpace p (problem_8_20_Y p) = problem_8_20_YCoords p := rfl

/-- Helper for Problem 8-20: the raw tangent-bundle section underlying
`Z = x ∂/∂y - y ∂/∂x`. -/
private def problem_8_20_rawZ (p : R3Base) : TangentSpace R3Model p :=
  (fromTangentSpace p).symm (problem_8_20_ZCoords p)

/-- Helper for Problem 8-20: the raw section `problem_8_20_rawZ` is smooth. -/
private theorem problem_8_20_rawZ_contMDiff :
    ContMDiff R3Model (𝓘(ℝ, R3Base)).tangent ∞ (T% problem_8_20_rawZ) := by
  -- On a vector space, smoothness of a tangent field is equivalent to ordinary smoothness.
  rw [contMDiff_vectorSpace_iff_contDiff]
  -- Each coordinate of `problem_8_20_ZCoords` is polynomial in the ambient coordinates.
  simpa [problem_8_20_rawZ, problem_8_20_ZCoords] using
    (contDiff_piLp' (2 : ENNReal) fun i ↦ by
      fin_cases i
      · simpa using
          ((contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 1)).neg
      · simpa using
          (contDiff_piLp_apply (2 : ENNReal) :
            ContDiff ℝ ∞ fun p : R3Base ↦ p 0)
      · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : R3Base ↦ (0 : ℝ)))

/-- The vector field `Z = x ∂/∂y - y ∂/∂x` from Problem 8-20, bundled as a smooth vector field on
`ℝ^3`. -/
def problem_8_20_Z : SmoothVectorField :=
  ⟨problem_8_20_rawZ, problem_8_20_rawZ_contMDiff⟩

/-- Coordinate formula for `problem_8_20_Z` under the canonical Euclidean tangent-space
identification. -/
theorem problem_8_20_Z_apply (p : R3Base) :
    fromTangentSpace p (problem_8_20_Z p) = problem_8_20_ZCoords p := rfl

/-- Helper for Problem 8-20: the continuous linear equivalence sending a coordinate tuple in
`Fin 3 → ℝ` back to the Euclidean space `R3Base`. -/
private def problem_8_20_tupleToR3Base : (Fin 3 → ℝ) →L[ℝ] R3Base :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.toContinuousLinearMap

/-- Helper for Problem 8-20: the fixed linear map underlying the coordinate field `X`. -/
private def problem_8_20_XCoordsCLM : R3Base →L[ℝ] R3Base :=
  problem_8_20_tupleToR3Base.comp
    (ContinuousLinearMap.pi ![
      (0 : R3Base →L[ℝ] ℝ),
      -(PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2),
      PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1])

/-- Helper for Problem 8-20: the fixed linear map underlying the coordinate field `Y`. -/
private def problem_8_20_YCoordsCLM : R3Base →L[ℝ] R3Base :=
  problem_8_20_tupleToR3Base.comp
    (ContinuousLinearMap.pi ![
      PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 2,
      (0 : R3Base →L[ℝ] ℝ),
      -(PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0)])

/-- Helper for Problem 8-20: the fixed linear map underlying the coordinate field `Z`. -/
private def problem_8_20_ZCoordsCLM : R3Base →L[ℝ] R3Base :=
  problem_8_20_tupleToR3Base.comp
    (ContinuousLinearMap.pi ![
      -(PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1),
      PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0,
      (0 : R3Base →L[ℝ] ℝ)])

/-- Helper for Problem 8-20: the coordinate field `X` is the linear map
`problem_8_20_XCoordsCLM`. -/
private theorem problem_8_20_XCoords_eq_clm :
    problem_8_20_XCoords = problem_8_20_XCoordsCLM := by
  funext p
  ext i
  fin_cases i <;> simp [problem_8_20_XCoords, problem_8_20_XCoordsCLM,
    problem_8_20_tupleToR3Base]

/-- Helper for Problem 8-20: the coordinate field `Y` is the linear map
`problem_8_20_YCoordsCLM`. -/
private theorem problem_8_20_YCoords_eq_clm :
    problem_8_20_YCoords = problem_8_20_YCoordsCLM := by
  funext p
  ext i
  fin_cases i <;> simp [problem_8_20_YCoords, problem_8_20_YCoordsCLM,
    problem_8_20_tupleToR3Base]

/-- Helper for Problem 8-20: the coordinate field `Z` is the linear map
`problem_8_20_ZCoordsCLM`. -/
private theorem problem_8_20_ZCoords_eq_clm :
    problem_8_20_ZCoords = problem_8_20_ZCoordsCLM := by
  funext p
  ext i
  fin_cases i <;> simp [problem_8_20_ZCoords, problem_8_20_ZCoordsCLM,
    problem_8_20_tupleToR3Base]

/-- Helper for Problem 8-20: the derivative of `problem_8_20_XCoords` is the same fixed linear
map at every point. -/
private theorem problem_8_20_XCoords_hasFDerivAt (p : R3Base) :
    HasFDerivAt problem_8_20_XCoords problem_8_20_XCoordsCLM p := by
  -- The coordinate field is linear, so its derivative is constant.
  rw [problem_8_20_XCoords_eq_clm]
  simpa using problem_8_20_XCoordsCLM.hasFDerivAt

/-- Helper for Problem 8-20: the derivative of `problem_8_20_YCoords` is the same fixed linear
map at every point. -/
private theorem problem_8_20_YCoords_hasFDerivAt (p : R3Base) :
    HasFDerivAt problem_8_20_YCoords problem_8_20_YCoordsCLM p := by
  -- The coordinate field is linear, so its derivative is constant.
  rw [problem_8_20_YCoords_eq_clm]
  simpa using problem_8_20_YCoordsCLM.hasFDerivAt

/-- Helper for Problem 8-20: the derivative of `problem_8_20_ZCoords` is the same fixed linear
map at every point. -/
private theorem problem_8_20_ZCoords_hasFDerivAt (p : R3Base) :
    HasFDerivAt problem_8_20_ZCoords problem_8_20_ZCoordsCLM p := by
  -- The coordinate field is linear, so its derivative is constant.
  rw [problem_8_20_ZCoords_eq_clm]
  simpa using problem_8_20_ZCoordsCLM.hasFDerivAt

/-- Helper for Problem 8-20: in Euclidean coordinates, the bracket of the `X` and `Y` fields is
the coordinate field for `-Z`. -/
private theorem problem_8_20_coordBracket_XY :
    VectorField.lieBracket ℝ problem_8_20_XCoords problem_8_20_YCoords =
      fun p : R3Base ↦ WithLp.toLp 2 ![p 1, -p 0, (0 : ℝ)] := by
  -- TODO: finish the linear-map commutator computation after normalizing
  -- `problem_8_20_tupleToR3Base` to an explicit coordinate formula.
  sorry

/-- Helper for Problem 8-20: in Euclidean coordinates, the bracket of the `Y` and `Z` fields is
the coordinate field for `-X`. -/
private theorem problem_8_20_coordBracket_YZ :
    VectorField.lieBracket ℝ problem_8_20_YCoords problem_8_20_ZCoords =
      fun p : R3Base ↦ WithLp.toLp 2 ![(0 : ℝ), p 2, -p 1] := by
  -- TODO: finish the linear-map commutator computation after normalizing
  -- `problem_8_20_tupleToR3Base` to an explicit coordinate formula.
  sorry

/-- Helper for Problem 8-20: in Euclidean coordinates, the bracket of the `Z` and `X` fields is
the coordinate field for `-Y`. -/
private theorem problem_8_20_coordBracket_ZX :
    VectorField.lieBracket ℝ problem_8_20_ZCoords problem_8_20_XCoords =
      fun p : R3Base ↦ WithLp.toLp 2 ![-p 2, (0 : ℝ), p 0] := by
  -- TODO: finish the linear-map commutator computation after normalizing
  -- `problem_8_20_tupleToR3Base` to an explicit coordinate formula.
  sorry

/-- Helper for Problem 8-20: the bundled bracket of `X` and `Y` is `-Z`. -/
private theorem problem_8_20_lie_XY :
    ⁅problem_8_20_X, problem_8_20_Y⁆ = -problem_8_20_Z := by
  -- TODO: transfer `problem_8_20_coordBracket_XY` through `fromTangentSpace` to the bundled
  -- smooth vector-field bracket.
  sorry

/-- Helper for Problem 8-20: the bundled bracket of `Y` and `Z` is `-X`. -/
private theorem problem_8_20_lie_YZ :
    ⁅problem_8_20_Y, problem_8_20_Z⁆ = -problem_8_20_X := by
  -- TODO: transfer `problem_8_20_coordBracket_YZ` through `fromTangentSpace` to the bundled
  -- smooth vector-field bracket.
  sorry

/-- Helper for Problem 8-20: the bundled bracket of `Z` and `X` is `-Y`. -/
private theorem problem_8_20_lie_ZX :
    ⁅problem_8_20_Z, problem_8_20_X⁆ = -problem_8_20_Y := by
  -- TODO: transfer `problem_8_20_coordBracket_ZX` through `fromTangentSpace` to the bundled
  -- smooth vector-field bracket.
  sorry

/-- Helper for Problem 8-20: the three generators `X`, `Y`, and `Z` viewed as a subset of the
ambient smooth vector-field space. -/
private def problem_8_20_generatorSet : Set SmoothVectorField :=
  {problem_8_20_X, problem_8_20_Y, problem_8_20_Z}

/-- Helper for Problem 8-20: the bracket of two generators already lies in the span of
`{X, Y, Z}`. -/
private theorem problem_8_20_generatorBracket_mem_span {V W : SmoothVectorField}
    (hV : V ∈ problem_8_20_generatorSet)
    (hW : W ∈ problem_8_20_generatorSet) :
    ⁅V, W⁆ ∈ Submodule.span ℝ problem_8_20_generatorSet := by
  -- TODO: use the three structure-constant identities together with antisymmetry/self cases.
  sorry

/-- Helper for Problem 8-20: the span of `X`, `Y`, and `Z` is closed under the ambient Lie
bracket on smooth vector fields on `ℝ^3`. -/
private theorem problem_8_20_bracket_mem_span {V W : SmoothVectorField}
    (hV : V ∈ Submodule.span ℝ problem_8_20_generatorSet)
    (hW : W ∈ Submodule.span ℝ problem_8_20_generatorSet) :
    ⁅V, W⁆ ∈ Submodule.span ℝ problem_8_20_generatorSet := by
  -- TODO: run `Submodule.span_induction₂` once the generator-level bracket table is in place.
  sorry

/-- The Lie subalgebra `A` from Problem 8-20, whose underlying vector subspace is the span of
`X`, `Y`, and `Z` inside the bundled smooth vector fields on `ℝ^3`. -/
def problem_8_20_A : LieSubalgebra ℝ SmoothVectorField :=
  { Submodule.span ℝ problem_8_20_generatorSet with
    lie_mem' := fun hV hW ↦ problem_8_20_bracket_mem_span hV hW }

/-- The underlying submodule of `problem_8_20_A` is the span of the three generators. -/
theorem problem_8_20_A_toSubmodule :
    (problem_8_20_A : Submodule ℝ SmoothVectorField) =
      Submodule.span ℝ problem_8_20_generatorSet := rfl

/-- Helper for Problem 8-20: the explicit linear parametrization of the span of `X`, `Y`, and
`Z` before codomain restriction to `problem_8_20_A`. -/
private def problem_8_20_from_cross_linear : R3 →ₗ[ℝ] SmoothVectorField :=
  (LinearMap.proj 0).smulRight problem_8_20_X +
    (LinearMap.proj 1).smulRight problem_8_20_Y -
      (LinearMap.proj 2).smulRight problem_8_20_Z

/-- Helper for Problem 8-20: the explicit linear parametrization lands in the span
`problem_8_20_A`. -/
private theorem problem_8_20_from_cross_linear_mem (u : R3) :
    problem_8_20_from_cross_linear u ∈ problem_8_20_A := by
  -- Work in the underlying span description of `problem_8_20_A`.
  change problem_8_20_from_cross_linear u ∈ (problem_8_20_A : Submodule ℝ SmoothVectorField)
  rw [problem_8_20_A_toSubmodule]
  have hX :
      u 0 • problem_8_20_X ∈ Submodule.span ℝ problem_8_20_generatorSet := by
    exact Submodule.smul_mem (Submodule.span ℝ problem_8_20_generatorSet) (u 0)
      (Submodule.subset_span (by simp [problem_8_20_generatorSet]))
  have hY :
      u 1 • problem_8_20_Y ∈ Submodule.span ℝ problem_8_20_generatorSet := by
    exact Submodule.smul_mem (Submodule.span ℝ problem_8_20_generatorSet) (u 1)
      (Submodule.subset_span (by simp [problem_8_20_generatorSet]))
  have hZ :
      u 2 • problem_8_20_Z ∈ Submodule.span ℝ problem_8_20_generatorSet := by
    exact Submodule.smul_mem (Submodule.span ℝ problem_8_20_generatorSet) (u 2)
      (Submodule.subset_span (by simp [problem_8_20_generatorSet]))
  -- The explicit linear combination of the three generators therefore lies in the span.
  simpa [problem_8_20_from_cross_linear] using
    Submodule.sub_mem (Submodule.span ℝ problem_8_20_generatorSet)
      (Submodule.add_mem (Submodule.span ℝ problem_8_20_generatorSet) hX hY) hZ

/-- Helper for Problem 8-20: `problem_8_20_from_cross_linear` is expressed in the basis
`X`, `Y`, and `-Z`. -/
private theorem problem_8_20_from_cross_linear_apply (u : R3) :
    problem_8_20_from_cross_linear u =
      u 0 • problem_8_20_X + u 1 • problem_8_20_Y + u 2 • (-problem_8_20_Z) := by
  -- Rewrite the third term so the target basis matches the cross-product structure constants.
  simp [problem_8_20_from_cross_linear, sub_eq_add_neg, add_assoc]

/-- Helper for Problem 8-20: the explicit linear parametrization intertwines the cross-product
bracket on `R3` with the ambient Lie bracket of smooth vector fields. -/
private theorem problem_8_20_from_cross_linear_map_lie (u v : R3) :
    problem_8_20_from_cross_linear ⁅u, v⁆ =
      ⁅problem_8_20_from_cross_linear u, problem_8_20_from_cross_linear v⁆ := by
  -- TODO: expand in the basis `X`, `Y`, `-Z` after the bracket table is available.
  sorry

/-- Helper for Problem 8-20: the codomain-restricted linear map is a Lie algebra homomorphism. -/
private theorem problem_8_20_from_cross_map_lie (u v : R3) :
    ((problem_8_20_from_cross_linear.codRestrict
        (problem_8_20_A : Submodule ℝ SmoothVectorField)
        problem_8_20_from_cross_linear_mem : R3 →ₗ[ℝ] problem_8_20_A))
        ⁅u, v⁆ =
      ⁅((problem_8_20_from_cross_linear.codRestrict
          (problem_8_20_A : Submodule ℝ SmoothVectorField)
          problem_8_20_from_cross_linear_mem : R3 →ₗ[ℝ] problem_8_20_A)) u,
        ((problem_8_20_from_cross_linear.codRestrict
          (problem_8_20_A : Submodule ℝ SmoothVectorField)
          problem_8_20_from_cross_linear_mem : R3 →ₗ[ℝ] problem_8_20_A)) v⁆ := by
  -- TODO: push this equality to the ambient smooth-vector-field space once
  -- `problem_8_20_from_cross_linear_map_lie` is finished.
  sorry

/-- The explicit Lie algebra homomorphism from `R3` with the cross product to the span `A`,
sending the standard basis to `X`, `Y`, and `-Z`. -/
def problem_8_20_from_cross : R3 →ₗ⁅ℝ⁆ problem_8_20_A :=
  { toLinearMap := problem_8_20_from_cross_linear.codRestrict problem_8_20_A
      problem_8_20_from_cross_linear_mem
    map_lie' := problem_8_20_from_cross_map_lie }

/-- Forgetting the subtype on `problem_8_20_from_cross` recovers the explicit linear combination
of `X`, `Y`, and `-Z`. -/
theorem problem_8_20_from_cross_apply (u : R3) :
    ((problem_8_20_from_cross u : problem_8_20_A) : SmoothVectorField) =
      u 0 • problem_8_20_X + u 1 • problem_8_20_Y - u 2 • problem_8_20_Z := by
  -- The codomain restriction does not change the ambient smooth vector field.
  rfl

/-- Helper for Problem 8-20: the explicit Lie algebra homomorphism `problem_8_20_from_cross` is
bijection. -/
private theorem problem_8_20_from_cross_bijective :
    Function.Bijective problem_8_20_from_cross := by
  -- TODO: prove injectivity by evaluating at the points `(0, 1, 0)` and `(1, 0, 0)`, then prove
  -- surjectivity because each generator lies in the range and `A` is their span.
  sorry

/-- Problem 8-20: if `A` is the span of the vector fields
`X = y ∂/∂z - z ∂/∂y`, `Y = z ∂/∂x - x ∂/∂z`, and `Z = x ∂/∂y - y ∂/∂x` on `ℝ^3`, then `A` is
a Lie subalgebra of the smooth vector fields on `ℝ^3`, and the explicit map from `R3` with the
cross-product Lie algebra identifies `R3` with `A` as a Lie algebra. -/
noncomputable def problem_8_20_cross_equiv_A : R3 ≃ₗ⁅ℝ⁆ problem_8_20_A :=
  LieEquiv.ofBijective problem_8_20_from_cross problem_8_20_from_cross_bijective

/-- Applying `problem_8_20_cross_equiv_A` to `u : R3` yields the corresponding linear
combination of `X`, `Y`, and `-Z` in the Lie subalgebra `A`. -/
theorem problem_8_20_cross_equiv_A_apply (u : R3) :
    ((problem_8_20_cross_equiv_A u : problem_8_20_A) : SmoothVectorField) =
      u 0 • problem_8_20_X + u 1 • problem_8_20_Y - u 2 • problem_8_20_Z := by
  -- `LieEquiv.ofBijective` keeps the original forward map.
  simpa [problem_8_20_cross_equiv_A] using problem_8_20_from_cross_apply u

import Mathlib
import SmoothManifolds_Lee_2012.Chap08.Sec08_56.Definition_8_56_extra_2
import SmoothManifolds_Lee_2012.Chap08.Sec08_56.Notation_8_56_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

open NormedSpace

local notation "R2" => EuclideanSpace ℝ (Fin 2)
local notation "SmoothFunction" => C^∞⟮𝓡 2, R2; ℝ⟯
local notation "SmoothDerivation" => Derivation ℝ SmoothFunction SmoothFunction
local notation "SmoothVectorField" =>
  ContMDiffSection (𝓡 2) R2 ∞ (fun p : R2 ↦ TangentSpace (𝓡 2) p)

/-- Helper for Example 8.24: the raw constant vector field `∂/∂x` on `ℝ²`. -/
private def constantXDirection (p : R2) : TangentSpace (𝓡 2) p :=
  (fromTangentSpace p).symm (WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)])

/-- Helper for Example 8.24: every tangent-bundle trivialization sees `constantXDirection` as the
constant Euclidean vector `(1, 0)`. -/
@[simp] private theorem trivializationAt_constantXDirection (x y : R2) :
    (trivializationAt R2 (TangentSpace (𝓡 2)) x ⟨y, constantXDirection y⟩).2 =
      WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)] := by
  -- On the Euclidean model, tangent-bundle trivializations are the standard coordinates.
  rw [trivializationAt_model_space_apply (I := 𝓡 2) (p := ⟨y, constantXDirection y⟩) x]
  rfl

/-- Helper for Example 8.24: `constantXDirection` is a smooth section of the tangent bundle. -/
private theorem constantXDirection_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% constantXDirection) := by
  intro p
  -- Reduce section smoothness to the trivialized Euclidean coordinate.
  rw [Bundle.contMDiffAt_section p]
  -- The trivialized coordinate is constant.
  simpa using
    (contMDiffAt_const :
      ContMDiffAt (𝓡 2) (𝓡 2) ∞
        (fun _ : R2 ↦ WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]) p)

/-- The constant vector field `X = ∂/∂x` on `ℝ²`, bundled as a smooth vector field. -/
def example_8_24_X : SmoothVectorField :=
  ⟨constantXDirection, constantXDirection_contMDiff⟩

/-- Helper for Example 8.24: under `fromTangentSpace`, the field `X = ∂/∂x` has coordinate vector
`(1, 0)`. -/
@[simp] private theorem fromTangentSpace_example_8_24_X (p : R2) :
    fromTangentSpace p (example_8_24_X p) = WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)] := by
  -- The tangent-space equivalence cancels the explicit constructor.
  rfl

/-- Helper for Example 8.24: the raw vector field `x ∂/∂y` on `ℝ²`. -/
private def scaledYDirection (p : R2) : TangentSpace (𝓡 2) p :=
  (fromTangentSpace p).symm (WithLp.toLp 2 ![(0 : ℝ), p 0])

/-- Helper for Example 8.24: every tangent-bundle trivialization sees `scaledYDirection` as the
Euclidean vector `(0, x)`. -/
@[simp] private theorem trivializationAt_scaledYDirection (x y : R2) :
    (trivializationAt R2 (TangentSpace (𝓡 2)) x ⟨y, scaledYDirection y⟩).2 =
      WithLp.toLp 2 ![(0 : ℝ), y 0] := by
  -- On the Euclidean model, tangent-bundle trivializations are the standard coordinates.
  rw [trivializationAt_model_space_apply (I := 𝓡 2) (p := ⟨y, scaledYDirection y⟩) x]
  rfl

/-- Helper for Example 8.24: the Euclidean coordinate formula `(x, y) ↦ (0, x)` is smooth. -/
private theorem scaledYDirectionCoords_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (fun p : R2 ↦ WithLp.toLp 2 ![(0 : ℝ), p 0]) := by
  have hcoord : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun p : R2 ↦ p 0) := by
    simpa using
      (((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0) : R2 →L[ℝ] ℝ).contMDiff)
  have hconst : ContMDiff (𝓡 2) (𝓡 2) ∞
      (fun _ : R2 ↦ WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)]) :=
    contMDiff_const
  have hrewrite :
      (fun p : R2 ↦ WithLp.toLp 2 ![(0 : ℝ), p 0]) =
        fun p : R2 ↦ (p 0) • WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)] := by
    funext p
    ext i
    fin_cases i <;> simp
  -- Rewrite the coordinate map as a scalar multiple of a constant Euclidean vector.
  rw [hrewrite]
  exact hcoord.smul hconst

/-- Helper for Example 8.24: `scaledYDirection` is a smooth section of the tangent bundle. -/
private theorem scaledYDirection_contMDiff :
    ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (T% scaledYDirection) := by
  intro p
  -- Reduce section smoothness to the trivialized Euclidean coordinate.
  rw [Bundle.contMDiffAt_section p]
  -- The trivialized coordinate is the smooth map `(x, y) ↦ (0, x)`.
  simpa using scaledYDirectionCoords_contMDiff.contMDiffAt

/-- The vector field `Y = x ∂/∂y` on `ℝ²`, bundled as a smooth vector field. -/
def example_8_24_Y : SmoothVectorField :=
  ⟨scaledYDirection, scaledYDirection_contMDiff⟩

/-- Helper for Example 8.24: under `fromTangentSpace`, the field `Y = x ∂/∂y` has coordinate
vector `(0, x)`. -/
@[simp] private theorem fromTangentSpace_example_8_24_Y (p : R2) :
    fromTangentSpace p (example_8_24_Y p) = WithLp.toLp 2 ![(0 : ℝ), p 0] := by
  -- The tangent-space equivalence cancels the explicit constructor.
  rfl

/-- The coordinate function `x : ℝ² → ℝ`, regarded as a smooth function. -/
def example_8_24_x : SmoothFunction :=
  (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)

/-- The coordinate function `y : ℝ² → ℝ`, regarded as a smooth function. -/
def example_8_24_y : SmoothFunction :=
  (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ)

/-- Helper for Example 8.24: evaluating the smooth function `x` recovers the first coordinate. -/
@[simp] private theorem example_8_24_x_apply (p : R2) :
    example_8_24_x p = p 0 := rfl

/-- Helper for Example 8.24: evaluating the smooth function `y` recovers the second coordinate. -/
@[simp] private theorem example_8_24_y_apply (p : R2) :
    example_8_24_y p = p 1 := rfl

/-- The derivation of `C^∞(ℝ²)` associated to `X = ∂/∂x`. -/
def example_8_24_X_derivation : SmoothDerivation :=
  example_8_24_X.toDerivation

/-- The derivation of `C^∞(ℝ²)` associated to `Y = x ∂/∂y`. -/
def example_8_24_Y_derivation : SmoothDerivation :=
  example_8_24_Y.toDerivation

/-- Helper for Example 8.24: `X = ∂/∂x` differentiates the `x`-coordinate to `1`. -/
@[simp] private theorem example_8_24_X_derivation_x (p : R2) :
    example_8_24_X_derivation example_8_24_x p = 1 := by
  -- Unfold the derivation application and use the derivative of the first projection.
  rw [example_8_24_X_derivation, ContMDiffSection.toDerivation_apply, VectorField.apply_def]
  change
    mfderiv (𝓡 2) 𝓘(ℝ)
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) p
      ((fromTangentSpace p).symm (WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)])) = 1
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- Helper for Example 8.24: `X = ∂/∂x` differentiates the `y`-coordinate to `0`. -/
@[simp] private theorem example_8_24_X_derivation_y (p : R2) :
    example_8_24_X_derivation example_8_24_y p = 0 := by
  -- Unfold the derivation application and use the derivative of the second projection.
  rw [example_8_24_X_derivation, ContMDiffSection.toDerivation_apply, VectorField.apply_def]
  change
    mfderiv (𝓡 2) 𝓘(ℝ)
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ)) p
      ((fromTangentSpace p).symm (WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)])) = 0
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- Helper for Example 8.24: `Y = x ∂/∂y` annihilates the `x`-coordinate. -/
@[simp] private theorem example_8_24_Y_derivation_x (p : R2) :
    example_8_24_Y_derivation example_8_24_x p = 0 := by
  -- Unfold the derivation application and evaluate the first projection on `(0, x)`.
  rw [example_8_24_Y_derivation, ContMDiffSection.toDerivation_apply, VectorField.apply_def]
  change
    mfderiv (𝓡 2) 𝓘(ℝ)
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : R2 →L[ℝ] ℝ)) p
      ((fromTangentSpace p).symm (WithLp.toLp 2 ![(0 : ℝ), p 0])) = 0
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- Helper for Example 8.24: `Y = x ∂/∂y` differentiates the `y`-coordinate to `x`. -/
@[simp] private theorem example_8_24_Y_derivation_y (p : R2) :
    example_8_24_Y_derivation example_8_24_y p = p 0 := by
  -- Unfold the derivation application and evaluate the second projection on `(0, x)`.
  rw [example_8_24_Y_derivation, ContMDiffSection.toDerivation_apply, VectorField.apply_def]
  change
    mfderiv (𝓡 2) 𝓘(ℝ)
      ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : R2 →L[ℝ] ℝ)) p
      ((fromTangentSpace p).symm (WithLp.toLp 2 ![(0 : ℝ), p 0])) = p 0
  rw [ContinuousLinearMap.mfderiv_eq]
  rfl

/-- Helper for Example 8.24: applying `Y = x ∂/∂y` to `xy` gives `x²`. -/
private theorem example_8_24_Y_mul_coords (p : R2) :
    example_8_24_Y_derivation (example_8_24_x * example_8_24_y) p = p 0 * p 0 := by
  -- Use Leibniz and the first-order coordinate formulas for `Y`.
  rw [Derivation.leibniz]
  simp [mul_comm]

/-- The second-order operator `XY` on `C^∞(ℝ²)`, obtained by composing the derivations attached to
`Y` and `X`. -/
def example_8_24_XY : SmoothFunction →ₗ[ℝ] SmoothFunction :=
  example_8_24_X_derivation.toLinearMap.comp example_8_24_Y_derivation.toLinearMap

/-- The composition `XY` sends the product `xy` to the function `2x`. -/
theorem example_8_24_XY_mul_coords (p : R2) :
    example_8_24_XY (example_8_24_x * example_8_24_y) p = 2 * p 0 := by
  have hYxy :
      example_8_24_Y_derivation (example_8_24_x * example_8_24_y) =
        example_8_24_x * example_8_24_x := by
    -- Identify the first derivative `Y(xy)` with the smooth function `x²`.
    ext q
    rw [example_8_24_Y_mul_coords]
    simp
  -- Apply `X = ∂/∂x` to the already-computed first derivative.
  simp [example_8_24_XY, hYxy, Derivation.leibniz]
  ring_nf

/-- The Leibniz-rule right-hand side for the coordinate functions `x` and `y` evaluates to `x`. -/
theorem example_8_24_leibniz_rhs_coords (p : R2) :
    example_8_24_x p * example_8_24_XY example_8_24_y p +
        example_8_24_y p * example_8_24_XY example_8_24_x p =
      p 0 := by
  have hYy : example_8_24_Y_derivation example_8_24_y = example_8_24_x := by
    -- The first derivative `Y(y)` is exactly the coordinate function `x`.
    ext q
    rw [example_8_24_Y_derivation_y]
    simp
  have hYx : example_8_24_Y_derivation example_8_24_x = 0 := by
    -- The first derivative `Y(x)` vanishes identically.
    ext q
    simp
  -- Rewrite `XY` using the already-computed first derivatives of `x` and `y`.
  simp [example_8_24_XY, hYy, hYx]

/-- Example 8.24. The operator `XY` on `C^∞(ℝ²)` coming from the vector fields
`X = ∂/∂x` and `Y = x ∂/∂y` is not a derivation. -/
theorem example_8_24_XY_not_derivation :
    ¬ ∃ D : SmoothDerivation, D.toLinearMap = example_8_24_XY := by
  rintro ⟨D, hD⟩
  let p0 : R2 := WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]
  have hLeibniz :
      D (example_8_24_x * example_8_24_y) p0 =
        example_8_24_x p0 * D example_8_24_y p0 +
          example_8_24_y p0 * D example_8_24_x p0 := by
    -- Evaluate the Leibniz rule at the test point `(1, 0)`.
    exact congrArg (fun F : SmoothFunction => F p0) (D.leibniz example_8_24_x example_8_24_y)
  have hMul :
      D (example_8_24_x * example_8_24_y) p0 =
        example_8_24_XY (example_8_24_x * example_8_24_y) p0 := by
    -- Rewrite the hypothetical derivation on the test function `xy`.
    simpa using
      congrArg
        (fun L : SmoothFunction →ₗ[ℝ] SmoothFunction =>
          L (example_8_24_x * example_8_24_y) p0) hD
  have hx :
      D example_8_24_x p0 = example_8_24_XY example_8_24_x p0 := by
    -- Rewrite the hypothetical derivation on the coordinate function `x`.
    simpa using
      congrArg
        (fun L : SmoothFunction →ₗ[ℝ] SmoothFunction => L example_8_24_x p0) hD
  have hy :
      D example_8_24_y p0 = example_8_24_XY example_8_24_y p0 := by
    -- Rewrite the hypothetical derivation on the coordinate function `y`.
    simpa using
      congrArg
        (fun L : SmoothFunction →ₗ[ℝ] SmoothFunction => L example_8_24_y p0) hD
  -- Compare the two sides of the Leibniz rule at the witness point `(1, 0)`.
  rw [hMul, hy, hx, example_8_24_XY_mul_coords, example_8_24_leibniz_rhs_coords] at hLeibniz
  norm_num [p0] at hLeibniz

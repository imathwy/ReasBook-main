import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this session, so the canonical owner was checked locally:
-- for vector fields on `ℝ^3`, mathlib uses `VectorField.lieBracket`.

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The vector field `X` used in Example 8.27, written in standard coordinates on `ℝ^3`. -/
def example_8_27_X : R3 → R3 :=
  fun p ↦ !₂[p 0, 1, p 0 * (p 1 + 1)]

/-- Coordinate formula for the vector field `example_8_27_X`. -/
theorem example_8_27_X_apply (p : R3) :
    example_8_27_X p = !₂[p 0, 1, p 0 * (p 1 + 1)] := rfl

/-- The vector field `Y` used in Example 8.27, written in standard coordinates on `ℝ^3`. -/
def example_8_27_Y : R3 → R3 :=
  fun p ↦ !₂[1, 0, p 1]

/-- Coordinate formula for the vector field `example_8_27_Y`. -/
theorem example_8_27_Y_apply (p : R3) :
    example_8_27_Y p = !₂[1, 0, p 1] := rfl

/-- Helper for Example 8.27: the scalar polynomial `q ↦ q 0 * (q 1 + 1)` has the expected
product-rule derivative. -/
theorem fderiv_xMulYAddOne_apply (p v : R3) :
    fderiv ℝ (fun q : R3 ↦ q 0 * (q 1 + 1)) p v =
      v 0 * (p 1 + 1) + p 0 * v 1 := by
  have hx :
      HasFDerivAt (fun q : R3 ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0
  have hy :
      HasFDerivAt (fun q : R3 ↦ q 1 + 1)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 : R3 →L[ℝ] ℝ) p := by
    -- Differentiate the second coordinate and absorb the added constant.
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).const_add
        (1 : ℝ)
  have hmul :
      HasFDerivAt (fun q : R3 ↦ q 0 * (q 1 + 1))
        (p 0 • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 : R3 →L[ℝ] ℝ) +
          (p 1 + 1) • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 : R3 →L[ℝ] ℝ)) p := by
    -- Apply the scalar product rule and normalize the linear-map summands.
    simpa [smul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      hx.mul hy
  rw [hmul.fderiv]
  -- Evaluating the derivative linear map on `v` yields the advertised formula.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    smul_eq_mul]
  ring

/-- Helper for Example 8.27: the derivative of a coordinate projection picks out the matching
coordinate of the tangent vector. -/
theorem fderiv_coordFn_apply (p v : R3) (i : Fin 3) :
    fderiv ℝ (fun q : R3 ↦ q i) p v = v i := by
  rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p i).fderiv]
  rfl

/-- Example 8.27. For
`X = x ∂/∂x + ∂/∂y + x (y + 1) ∂/∂z` and `Y = ∂/∂x + y ∂/∂z` on `ℝ^3`,
their Lie bracket is the vector field `p ↦ !₂[-1, 0, -(p 1)]`. -/
theorem example_8_27_lie_bracket :
    VectorField.lieBracket ℝ example_8_27_X example_8_27_Y = fun p ↦ !₂[-(1 : ℝ), 0, -(p 1)] :=
  by
  let e1 : R3 → R3 := fun _ ↦ !₂[(1 : ℝ), 0, 0]
  let e2 : R3 → R3 := fun _ ↦ !₂[0, (1 : ℝ), 0]
  let e3 : R3 → R3 := fun _ ↦ !₂[0, 0, (1 : ℝ)]
  let x : R3 → ℝ := fun q ↦ q 0
  let y : R3 → ℝ := fun q ↦ q 1
  let z : R3 → ℝ := fun q ↦ q 0 * (q 1 + 1)
  let xE1 : R3 → R3 := fun q ↦ x q • e1 q
  let yE3 : R3 → R3 := fun q ↦ y q • e3 q
  let zE3 : R3 → R3 := fun q ↦ z q • e3 q
  have hX :
      example_8_27_X = xE1 + e2 + zE3 := by
    funext q
    ext i
    fin_cases i <;> simp [example_8_27_X, xE1, zE3, x, z, e1, e2, e3]
  have hY :
      example_8_27_Y = e1 + yE3 := by
    funext q
    ext i
    fin_cases i <;> simp [example_8_27_Y, yE3, y, e1, e3]
  funext p
  have hx : DifferentiableAt ℝ x p := by
    simpa [x] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0).differentiableAt
  have hy : DifferentiableAt ℝ y p := by
    simpa [y] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).differentiableAt
  have hz : DifferentiableAt ℝ z p := by
    simpa [z] using hx.mul (hy.add_const 1)
  have he1 : DifferentiableAt ℝ e1 p := by
    simp [e1]
  have he2 : DifferentiableAt ℝ e2 p := by
    simp [e2]
  have he3 : DifferentiableAt ℝ e3 p := by
    simp [e3]
  have hxE1 : DifferentiableAt ℝ xE1 p := by
    simpa [xE1] using hx.smul he1
  have hyE3 : DifferentiableAt ℝ yE3 p := by
    simpa [yE3] using hy.smul he3
  have hzE3 : DifferentiableAt ℝ zE3 p := by
    simpa [zE3] using hz.smul he3
  rw [hX, hY]
  rw [VectorField.lieBracket_add_left (hV := hxE1.add he2) (hV₁ := hzE3)]
  rw [VectorField.lieBracket_add_left (hV := hxE1) (hV₁ := he2)]
  rw [VectorField.lieBracket_add_right (hW := he1) (hW₁ := hyE3)]
  rw [VectorField.lieBracket_add_right (hW := he1) (hW₁ := hyE3)]
  rw [VectorField.lieBracket_add_right (hW := he1) (hW₁ := hyE3)]
  have hxE1_e1 : VectorField.lieBracket ℝ xE1 e1 p = - e1 p := by
    rw [VectorField.lieBracket_smul_left (V := e1) (W := e1) (f := x) (x := p) hx he1]
    have hx_e1 : fderiv ℝ x p (e1 p) = 1 := by
      rw [fderiv_coordFn_apply (p := p) (v := e1 p) (i := 0)]
      simp [e1]
    simp [hx_e1, e1, VectorField.lieBracket]
  have hxE1_yE3 : VectorField.lieBracket ℝ xE1 yE3 p = 0 := by
    rw [VectorField.lieBracket_smul_right (V := xE1) (W := e3) (f := y) (x := p) hy he3]
    have hy_xE1 : fderiv ℝ y p (xE1 p) = 0 := by
      rw [fderiv_coordFn_apply (p := p) (v := xE1 p) (i := 1)]
      simp [xE1, x, e1]
    have hxE1_e3 : VectorField.lieBracket ℝ xE1 e3 p = 0 := by
      rw [VectorField.lieBracket_smul_left (V := e1) (W := e3) (f := x) (x := p) hx he1]
      have hx_e3 : fderiv ℝ x p (e3 p) = 0 := by
        rw [fderiv_coordFn_apply (p := p) (v := e3 p) (i := 0)]
        simp [e3]
      simp [hx_e3, e1, e3, VectorField.lieBracket]
    simp [hy_xE1, hxE1_e3]
  have he2_e1 : VectorField.lieBracket ℝ e2 e1 p = 0 := by
    simp [e1, e2, VectorField.lieBracket]
  have he2_yE3 : VectorField.lieBracket ℝ e2 yE3 p = e3 p := by
    rw [VectorField.lieBracket_smul_right (V := e2) (W := e3) (f := y) (x := p) hy he3]
    have hy_e2 : fderiv ℝ y p (e2 p) = 1 := by
      rw [fderiv_coordFn_apply (p := p) (v := e2 p) (i := 1)]
      simp [e2]
    simp [hy_e2, e2, e3, VectorField.lieBracket]
  have hzE3_e1 : VectorField.lieBracket ℝ zE3 e1 p = -(p 1 + 1) • e3 p := by
    rw [VectorField.lieBracket_smul_left (V := e3) (W := e1) (f := z) (x := p) hz he3]
    have hz_e1 : fderiv ℝ z p (e1 p) = p 1 + 1 := by
      simpa [z, e1] using fderiv_xMulYAddOne_apply p (e1 p)
    simp [hz_e1, e1, e3, VectorField.lieBracket]
  have hzE3_yE3 : VectorField.lieBracket ℝ zE3 yE3 p = 0 := by
    rw [VectorField.lieBracket_smul_right (V := zE3) (W := e3) (f := y) (x := p) hy he3]
    have hy_zE3 : fderiv ℝ y p (zE3 p) = 0 := by
      rw [fderiv_coordFn_apply (p := p) (v := zE3 p) (i := 1)]
      simp [zE3, z, e3]
    have hzE3_e3 : VectorField.lieBracket ℝ zE3 e3 p = 0 := by
      rw [VectorField.lieBracket_smul_left (V := e3) (W := e3) (f := z) (x := p) hz he3]
      have hz_e3 : fderiv ℝ z p (e3 p) = 0 := by
        simpa [z, e3] using fderiv_xMulYAddOne_apply p (e3 p)
      simp [hz_e3, e3, VectorField.lieBracket]
    simp [hy_zE3, hzE3_e3]
  rw [hxE1_e1, hxE1_yE3, he2_e1, he2_yE3, hzE3_e1, hzE3_yE3]
  -- Combine the surviving basis-vector terms into the advertised coordinate formula.
  ext i
  fin_cases i <;> simp [e1, e3]

/-- Pointwise form of the Lie bracket computation in Example 8.27. -/
theorem example_8_27_lie_bracket_apply (p : R3) :
    VectorField.lieBracket ℝ example_8_27_X example_8_27_Y p = !₂[-(1 : ℝ), 0, -(p 1)] := by
  simpa using congrArg (fun Z ↦ Z p) example_8_27_lie_bracket

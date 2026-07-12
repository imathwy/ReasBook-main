import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the canonical owner
-- was checked locally against `Example_8_27.lean`, which uses `VectorField.lieBracket` for
-- coordinate vector fields on `ℝ^3`.

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "R3VF" => R3 → R3

/-- The vector field `X = y ∂/∂z - 2xy^2 ∂/∂y` from Problem 8-16(a), written in standard
coordinates on `ℝ^3`. -/
def problem_8_16_a_X : R3VF :=
  fun p ↦ !₂[(0 : ℝ), -(2 : ℝ) * p 0 * p 1 ^ (2 : ℕ), p 1]

/-- Coordinate formula for the vector field `problem_8_16_a_X`. -/
theorem problem_8_16_a_X_apply (p : R3) :
    problem_8_16_a_X p = !₂[(0 : ℝ), -(2 : ℝ) * p 0 * p 1 ^ (2 : ℕ), p 1] := rfl

/-- The vector field `Y = ∂/∂y` from Problem 8-16(a), written in standard coordinates on `ℝ^3`.
-/
def problem_8_16_a_Y : R3VF :=
  fun _ ↦ !₂[(0 : ℝ), (1 : ℝ), (0 : ℝ)]

/-- Coordinate formula for the vector field `problem_8_16_a_Y`. -/
theorem problem_8_16_a_Y_apply (p : R3) :
    problem_8_16_a_Y p = !₂[(0 : ℝ), (1 : ℝ), (0 : ℝ)] := rfl

/-- The computed Lie bracket in Problem 8-16(a), namely `4xy ∂/∂y - ∂/∂z`. -/
def problem_8_16_a_bracket : R3VF :=
  fun p ↦ !₂[(0 : ℝ), (4 : ℝ) * p 0 * p 1, -(1 : ℝ)]

/-- Coordinate formula for the vector field `problem_8_16_a_bracket`. -/
theorem problem_8_16_a_bracket_apply (p : R3) :
    problem_8_16_a_bracket p = !₂[(0 : ℝ), (4 : ℝ) * p 0 * p 1, -(1 : ℝ)] := rfl

/-- The vector field `X = x ∂/∂y - y ∂/∂x` from Problem 8-16(b), written in standard coordinates on
`ℝ^3`. -/
def problem_8_16_b_X : R3VF :=
  fun p ↦ !₂[-p 1, p 0, (0 : ℝ)]

/-- Coordinate formula for the vector field `problem_8_16_b_X`. -/
theorem problem_8_16_b_X_apply (p : R3) :
    problem_8_16_b_X p = !₂[-p 1, p 0, (0 : ℝ)] := rfl

/-- The vector field `Y = y ∂/∂z - z ∂/∂y` from Problem 8-16(b), written in standard coordinates on
`ℝ^3`. -/
def problem_8_16_b_Y : R3VF :=
  fun p ↦ !₂[(0 : ℝ), -p 2, p 1]

/-- Coordinate formula for the vector field `problem_8_16_b_Y`. -/
theorem problem_8_16_b_Y_apply (p : R3) :
    problem_8_16_b_Y p = !₂[(0 : ℝ), -p 2, p 1] := rfl

/-- The computed Lie bracket in Problem 8-16(b), namely `x ∂/∂z - z ∂/∂x`. -/
def problem_8_16_b_bracket : R3VF :=
  fun p ↦ !₂[-p 2, (0 : ℝ), p 0]

/-- Coordinate formula for the vector field `problem_8_16_b_bracket`. -/
theorem problem_8_16_b_bracket_apply (p : R3) :
    problem_8_16_b_bracket p = !₂[-p 2, (0 : ℝ), p 0] := rfl

/-- The vector field `Y = x ∂/∂y + y ∂/∂x` from Problem 8-16(c), written in standard coordinates on
`ℝ^3`. -/
def problem_8_16_c_Y : R3VF :=
  fun p ↦ !₂[p 1, p 0, (0 : ℝ)]

/-- Coordinate formula for the vector field `problem_8_16_c_Y`. -/
theorem problem_8_16_c_Y_apply (p : R3) :
    problem_8_16_c_Y p = !₂[p 1, p 0, (0 : ℝ)] := rfl

/-- The computed Lie bracket in Problem 8-16(c), namely `2x ∂/∂x - 2y ∂/∂y`. -/
def problem_8_16_c_bracket : R3VF :=
  fun p ↦ !₂[(2 : ℝ) * p 0, -(2 : ℝ) * p 1, (0 : ℝ)]

/-- Coordinate formula for the vector field `problem_8_16_c_bracket`. -/
theorem problem_8_16_c_bracket_apply (p : R3) :
    problem_8_16_c_bracket p = !₂[(2 : ℝ) * p 0, -(2 : ℝ) * p 1, (0 : ℝ)] := rfl

/-- Helper for Problem 8-16: differentiating a coordinate projection on `R3` returns the matching
coordinate of the tangent vector. -/
theorem fderiv_coordFn_apply (p v : R3) (i : Fin 3) :
    fderiv ℝ (fun q : R3 ↦ q i) p v = v i := by
  -- Rewrite the Fréchet derivative by the standard projection derivative on `PiLp`.
  rw [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p i).fderiv]
  rfl

/-- Helper for Problem 8-16: differentiating a negated coordinate projection negates the matching
coordinate of the tangent vector. -/
theorem fderiv_negCoordFn_apply (p v : R3) (i : Fin 3) :
    fderiv ℝ (fun q : R3 ↦ -q i) p v = -v i := by
  have hneg :
      HasFDerivAt (fun q : R3 ↦ -q i)
        (-(PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i : R3 →L[ℝ] ℝ)) p := by
    -- Differentiate the coordinate projection first and then negate the scalar-valued map.
    simpa using (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p i).neg
  rw [hneg.fderiv]
  rfl

/-- Helper for Problem 8-16: the `i`th coordinate of the derivative of an `R3`-valued map is the
directional derivative of its `i`th coordinate function. -/
theorem fderiv_coord_apply {F : R3 → R3} {p v : R3} (hF : DifferentiableAt ℝ F p) (i : Fin 3) :
    (fderiv ℝ F p v) i = fderiv ℝ (fun q : R3 ↦ F q i) p v := by
  have hcoord :
      HasFDerivAt (fun q : R3 ↦ F q i)
        ((PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) i).comp (fderiv ℝ F p)) p := by
    -- Compose the derivative of `F` with the coordinate projection on `R3`.
    exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) (F p) i).comp p
      hF.hasFDerivAt
  rw [hcoord.fderiv]
  rfl

/-- Helper for Problem 8-16: the scalar polynomial `q ↦ q 0 * q 1 ^ 2` has the expected product-rule
derivative. -/
theorem fderiv_xMulYSq_apply (p v : R3) :
    fderiv ℝ (fun q : R3 ↦ q 0 * q 1 ^ (2 : ℕ)) p v =
      v 0 * p 1 ^ (2 : ℕ) + p 0 * ((2 : ℝ) * p 1 * v 1) := by
  have hx :
      HasFDerivAt (fun q : R3 ↦ q 0)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0
  have hy :
      HasFDerivAt (fun q : R3 ↦ q 1)
        (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1) p :=
    PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1
  have hySq :
      HasFDerivAt (fun q : R3 ↦ q 1 ^ (2 : ℕ))
        (((2 : ℝ) * p 1) • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 : R3 →L[ℝ] ℝ)) p := by
    -- Differentiate the square `y^2` before applying the product rule.
    simpa using hy.pow 2
  have hxy :
      HasFDerivAt (fun q : R3 ↦ q 0 * q 1 ^ (2 : ℕ))
        (p 1 ^ (2 : ℕ) • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 0 : R3 →L[ℝ] ℝ) +
          p 0 • (((2 : ℝ) * p 1) • (PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) 1 : R3 →L[ℝ] ℝ))) p := by
    -- The scalar coefficient in part (a) is the only nonlinear derivative needed in the file.
    simpa [smul_add, smul_smul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hx.mul hySq
  rw [hxy.fderiv]
  -- Evaluate the resulting linear map on the tangent vector `v`.
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, PiLp.proj_apply,
    smul_eq_mul]
  ring

/-- Helper for Problem 8-16: pointwise form of the Lie bracket computation in part (a). -/
theorem problem_8_16_a_lie_bracket_apply (p : R3) :
    VectorField.lieBracket ℝ problem_8_16_a_X problem_8_16_a_Y p =
      !₂[(0 : ℝ), (4 : ℝ) * p 0 * p 1, -(1 : ℝ)] := by
  -- Route correction: compute the bracket through scalar coordinate derivatives instead of the
  -- earlier transport-heavy vector-valued Jacobian helpers.
  have hx : DifferentiableAt ℝ (fun q : R3 ↦ q 0) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0).differentiableAt
  have hy : DifferentiableAt ℝ (fun q : R3 ↦ q 1) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).differentiableAt
  have hxySq : DifferentiableAt ℝ (fun q : R3 ↦ q 0 * q 1 ^ (2 : ℕ)) p := by
    -- The nonlinear coefficient in part (a) is still just a polynomial in the coordinates.
    simpa using hx.mul (hy.pow 2)
  have hXCoord1 :
      DifferentiableAt ℝ (fun q : R3 ↦ problem_8_16_a_X q 1) p := by
    have hshape :
        (fun q : R3 ↦ problem_8_16_a_X q 1) = fun q : R3 ↦ -(2 : ℝ) * (q 0 * q 1 ^ (2 : ℕ)) := by
      funext q
      simp [problem_8_16_a_X]
      ring
    rw [hshape]
    exact hxySq.const_mul (-(2 : ℝ))
  have hX : DifferentiableAt ℝ problem_8_16_a_X p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_a_X] using differentiableAt_const (c := (0 : ℝ))
    · exact hXCoord1
    · simpa [problem_8_16_a_X] using hy
  have hY : DifferentiableAt ℝ problem_8_16_a_Y p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_a_Y] using differentiableAt_const (c := (0 : ℝ))
    · simpa [problem_8_16_a_Y] using differentiableAt_const (c := (1 : ℝ))
    · simpa [problem_8_16_a_Y] using differentiableAt_const (c := (0 : ℝ))
  have hscaled :
      fderiv ℝ (fun q : R3 ↦ -(2 : ℝ) * (q 0 * q 1 ^ (2 : ℕ))) p (problem_8_16_a_Y p) =
        -(4 : ℝ) * p 0 * p 1 := by
    -- Scale the derivative of `x * y^2` and evaluate it on `∂/∂y`.
    rw [fderiv_const_mul hxySq]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_xMulYSq_apply]
    simp [problem_8_16_a_Y]
    ring
  -- Compare the bracket coordinates after converting each derivative to a scalar one.
  ext i
  fin_cases i
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 0 -
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 0 = 0
    have hY0 :
        ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_Y q 0) p (problem_8_16_a_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_Y) (p := p) (v := problem_8_16_a_X p) hY 0)
    have hX0 :
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_X q 0) p (problem_8_16_a_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_X) (p := p) (v := problem_8_16_a_Y p) hX 0)
    rw [hY0, hX0]
    simp [problem_8_16_a_X, problem_8_16_a_Y]
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 1 -
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 1 =
      (4 : ℝ) * p 0 * p 1
    have hY1 :
        ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_Y q 1) p (problem_8_16_a_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_Y) (p := p) (v := problem_8_16_a_X p) hY 1)
    have hX1 :
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_X q 1) p (problem_8_16_a_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_X) (p := p) (v := problem_8_16_a_Y p) hX 1)
    rw [hY1, hX1]
    have hshape :
        (fun q : R3 ↦ problem_8_16_a_X q 1) = fun q : R3 ↦ -(2 : ℝ) * (q 0 * q 1 ^ (2 : ℕ)) := by
      funext q
      simp [problem_8_16_a_X]
      ring
    rw [hshape]
    have hconst :
        fderiv ℝ (fun q : R3 ↦ problem_8_16_a_Y q 1) p (problem_8_16_a_X p) = 0 := by
      simp [problem_8_16_a_Y]
    rw [hconst, hscaled]
    ring
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 2 -
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 2 = -(1 : ℝ)
    have hY2 :
        ((fderiv ℝ problem_8_16_a_Y p) (problem_8_16_a_X p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_Y q 2) p (problem_8_16_a_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_Y) (p := p) (v := problem_8_16_a_X p) hY 2)
    have hX2 :
        ((fderiv ℝ problem_8_16_a_X p) (problem_8_16_a_Y p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_a_X q 2) p (problem_8_16_a_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_a_X) (p := p) (v := problem_8_16_a_Y p) hX 2)
    rw [hY2, hX2]
    simp [problem_8_16_a_X, problem_8_16_a_Y, fderiv_coordFn_apply]

/-- Helper for Problem 8-16: pointwise form of the Lie bracket computation in part (b). -/
theorem problem_8_16_b_lie_bracket_apply (p : R3) :
    VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_b_Y p =
      !₂[-p 2, (0 : ℝ), p 0] := by
  have hx : DifferentiableAt ℝ (fun q : R3 ↦ q 0) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0).differentiableAt
  have hy : DifferentiableAt ℝ (fun q : R3 ↦ q 1) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).differentiableAt
  have hz : DifferentiableAt ℝ (fun q : R3 ↦ q 2) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 2).differentiableAt
  have hX : DifferentiableAt ℝ problem_8_16_b_X p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_b_X] using hy.neg
    · simpa [problem_8_16_b_X] using hx
    · simpa [problem_8_16_b_X] using differentiableAt_const (c := (0 : ℝ))
  have hY : DifferentiableAt ℝ problem_8_16_b_Y p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_b_Y] using differentiableAt_const (c := (0 : ℝ))
    · simpa [problem_8_16_b_Y] using hz.neg
    · simpa [problem_8_16_b_Y] using hy
  -- Rewrite the bracket through the scalar coordinate derivatives of `X` and `Y`.
  ext i
  fin_cases i
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 0 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 0 = -p 2
    have hY0 :
        ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_Y q 0) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_Y) (p := p) (v := problem_8_16_b_X p) hY 0)
    have hX0 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 0) p (problem_8_16_b_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_b_Y p) hX 0)
    rw [hY0, hX0]
    have hconst :
        fderiv ℝ (fun q : R3 ↦ problem_8_16_b_Y q 0) p (problem_8_16_b_X p) = 0 := by
      simp [problem_8_16_b_Y]
    have hneg :
        fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 0) p (problem_8_16_b_Y p) = p 2 := by
      simpa [problem_8_16_b_X, problem_8_16_b_Y] using
        (fderiv_negCoordFn_apply (p := p) (v := problem_8_16_b_Y p) (i := 1))
    rw [hconst, hneg]
    ring
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 1 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 1 = 0
    have hY1 :
        ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_Y q 1) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_Y) (p := p) (v := problem_8_16_b_X p) hY 1)
    have hX1 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 1) p (problem_8_16_b_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_b_Y p) hX 1)
    rw [hY1, hX1]
    simp [problem_8_16_b_X, problem_8_16_b_Y, fderiv_coordFn_apply, fderiv_negCoordFn_apply]
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 2 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 2 = p 0
    have hY2 :
        ((fderiv ℝ problem_8_16_b_Y p) (problem_8_16_b_X p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_Y q 2) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_Y) (p := p) (v := problem_8_16_b_X p) hY 2)
    have hX2 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_b_Y p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 2) p (problem_8_16_b_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_b_Y p) hX 2)
    rw [hY2, hX2]
    simp [problem_8_16_b_X, problem_8_16_b_Y, fderiv_coordFn_apply]

/-- Helper for Problem 8-16: pointwise form of the Lie bracket computation in part (c). -/
theorem problem_8_16_c_lie_bracket_apply (p : R3) :
    VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_c_Y p =
      !₂[(2 : ℝ) * p 0, -(2 : ℝ) * p 1, (0 : ℝ)] := by
  have hx : DifferentiableAt ℝ (fun q : R3 ↦ q 0) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 0).differentiableAt
  have hy : DifferentiableAt ℝ (fun q : R3 ↦ q 1) p := by
    simpa using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) (E := fun _ : Fin 3 ↦ ℝ) p 1).differentiableAt
  have hX : DifferentiableAt ℝ problem_8_16_b_X p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_b_X] using hy.neg
    · simpa [problem_8_16_b_X] using hx
    · simpa [problem_8_16_b_X] using differentiableAt_const (c := (0 : ℝ))
  have hY : DifferentiableAt ℝ problem_8_16_c_Y p := by
    refine (differentiableAt_piLp (𝕜 := ℝ) (p := 2)).2 ?_
    intro i
    fin_cases i
    · simpa [problem_8_16_c_Y] using hy
    · simpa [problem_8_16_c_Y] using hx
    · simpa [problem_8_16_c_Y] using differentiableAt_const (c := (0 : ℝ))
  -- Rewrite the bracket through the scalar coordinate derivatives of `X` and `Y`.
  ext i
  fin_cases i
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 0 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 0 = (2 : ℝ) * p 0
    have hY0 :
        ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_c_Y q 0) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_c_Y) (p := p) (v := problem_8_16_b_X p) hY 0)
    have hX0 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 0 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 0) p (problem_8_16_c_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_c_Y p) hX 0)
    rw [hY0, hX0]
    simp [problem_8_16_b_X, problem_8_16_c_Y, fderiv_coordFn_apply, fderiv_negCoordFn_apply]
    ring
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 1 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 1 = -(2 : ℝ) * p 1
    have hY1 :
        ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_c_Y q 1) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_c_Y) (p := p) (v := problem_8_16_b_X p) hY 1)
    have hX1 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 1 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 1) p (problem_8_16_c_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_c_Y p) hX 1)
    rw [hY1, hX1]
    simp [problem_8_16_b_X, problem_8_16_c_Y, fderiv_coordFn_apply, fderiv_negCoordFn_apply]
    ring
  · rw [VectorField.lieBracket]
    rw [PiLp.sub_apply]
    change ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 2 -
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 2 = 0
    have hY2 :
        ((fderiv ℝ problem_8_16_c_Y p) (problem_8_16_b_X p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_c_Y q 2) p (problem_8_16_b_X p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_c_Y) (p := p) (v := problem_8_16_b_X p) hY 2)
    have hX2 :
        ((fderiv ℝ problem_8_16_b_X p) (problem_8_16_c_Y p)) 2 =
          fderiv ℝ (fun q : R3 ↦ problem_8_16_b_X q 2) p (problem_8_16_c_Y p) := by
      simpa using
        (fderiv_coord_apply (F := problem_8_16_b_X) (p := p) (v := problem_8_16_c_Y p) hX 2)
    rw [hY2, hX2]
    simp [problem_8_16_b_X, problem_8_16_c_Y]

/-- Helper for Problem 8-16: in part (a), for
`X = y ∂/∂z - 2xy^2 ∂/∂y` and `Y = ∂/∂y` on `ℝ^3`, the Lie bracket is
`4xy ∂/∂y - ∂/∂z`, encoded by `problem_8_16_a_bracket`. -/
theorem problem_8_16_a_lie_bracket :
    VectorField.lieBracket ℝ problem_8_16_a_X problem_8_16_a_Y = problem_8_16_a_bracket := by
  -- Reassemble the global equality from the pointwise bracket computation.
  funext p
  simpa [problem_8_16_a_bracket] using problem_8_16_a_lie_bracket_apply p

/-- Helper for Problem 8-16: in part (b), for
`X = x ∂/∂y - y ∂/∂x` and `Y = y ∂/∂z - z ∂/∂y` on `ℝ^3`, the Lie bracket is
`x ∂/∂z - z ∂/∂x`, encoded by `problem_8_16_b_bracket`. -/
theorem problem_8_16_b_lie_bracket :
    VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_b_Y = problem_8_16_b_bracket := by
  -- Reassemble the global equality from the pointwise bracket computation.
  funext p
  simpa [problem_8_16_b_bracket] using problem_8_16_b_lie_bracket_apply p

/-- Helper for Problem 8-16: in part (c), for
`X = x ∂/∂y - y ∂/∂x` and `Y = x ∂/∂y + y ∂/∂x` on `ℝ^3`, the Lie bracket is
`2x ∂/∂x - 2y ∂/∂y`, where the same `X` as in part (b) is reused and the result is encoded by
`problem_8_16_c_bracket`. -/
theorem problem_8_16_c_lie_bracket :
    VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_c_Y = problem_8_16_c_bracket := by
  -- Reassemble the global equality from the pointwise bracket computation.
  funext p
  simpa [problem_8_16_c_bracket] using problem_8_16_c_lie_bracket_apply p

/-- Problem 8-16: for the three vector-field pairs listed in parts (a), (b),
and (c), the Lie
brackets are `problem_8_16_a_bracket`, `problem_8_16_b_bracket`, and `problem_8_16_c_bracket`,
respectively. -/
theorem problem_8_16_lie_bracket :
    VectorField.lieBracket ℝ problem_8_16_a_X problem_8_16_a_Y = problem_8_16_a_bracket ∧
      VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_b_Y = problem_8_16_b_bracket ∧
        VectorField.lieBracket ℝ problem_8_16_b_X problem_8_16_c_Y = problem_8_16_c_bracket := by
  -- Package the three component computations under the textbook item label.
  constructor
  · exact problem_8_16_a_lie_bracket
  constructor
  · exact problem_8_16_b_lie_bracket
  · exact problem_8_16_c_lie_bracket

import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.MilnorLineProjective

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the explicit diagonal path has a right inverse as a
polynomial matrix. -/
theorem equalEndpointSL2DiagonalPath_mul_inv (a : kˣ) :
    equalEndpointSL2DiagonalPath (k := k) a *
        (equalEndpointSL2DiagonalPathUnit (k := k) a).inv = 1 := by
  -- Replace the matrix path by the underlying value of the unit package, then use the unit law.
  rw [← equalEndpointSL2DiagonalPathUnit_coe (k := k) a]
  exact (equalEndpointSL2DiagonalPathUnit (k := k) a).val_inv

/-- Helper for Chap10 Example 10 55 5: the explicit diagonal path has a left inverse as a
polynomial matrix. -/
theorem equalEndpointSL2DiagonalPath_inv_mul (a : kˣ) :
    (equalEndpointSL2DiagonalPathUnit (k := k) a).inv *
        equalEndpointSL2DiagonalPath (k := k) a = 1 := by
  -- Replace the matrix path by the underlying value of the unit package, then use the unit law.
  rw [← equalEndpointSL2DiagonalPathUnit_coe (k := k) a]
  exact (equalEndpointSL2DiagonalPathUnit (k := k) a).inv_val

/-- Helper for Chap10 Example 10 55 5: the `i`-th row of a polynomial `2 × 2` matrix acts on
two polynomial-multiplication-owner coordinates by the usual dot product. -/
def equalEndpointMatrixRowAction
    (A : Matrix (Fin 2) (Fin 2) (Polynomial k)) (i : Fin 2)
    (x : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k) :
    equalEndpointPolynomialMulModule k :=
  ((A i 0 * equalEndpointPolynomialMulModule.toPolynomial k x.1 +
      A i 1 * equalEndpointPolynomialMulModule.toPolynomial k x.2 : Polynomial k) :
    equalEndpointPolynomialMulModule k)

/-- Helper for Chap10 Example 10 55 5: the first coordinate of the explicit diagonal path sends
`I_{uv} × I_1` into `I_u`. -/
theorem equalEndpointSL2DiagonalPath_pairAction_first_mem
    (u v : kˣ)
    (x : equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :
    equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k u := by
  let f : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.1 : equalEndpointPolynomialMulModule k)
  let g : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.2 : equalEndpointPolynomialMulModule k)
  have hf :
      f.eval 1 = ((u * v : kˣ) : k) * f.eval 0 := by
    -- The first input coordinate lies in `I_{uv}`, so its endpoint values differ by `uv`.
    have hx := (mem_equalEndpointLineSubmodule (k := k) (u * v)
      (x.1 : equalEndpointPolynomialMulModule k)).mp x.1.2
    simpa [f, equalEndpointLineCondition] using hx
  have hf' :
      Polynomial.eval 1 (x.1 : equalEndpointPolynomialMulModule k) =
        ((u * v : kˣ) : k) *
          Polynomial.eval 0 (x.1 : equalEndpointPolynomialMulModule k) := by
    -- Keep a copy of the endpoint-ratio equation in the unfolded normal form used below.
    simpa [f, equalEndpointPolynomialMulModule.toPolynomial] using hf
  have h00_0 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0 0).eval 0 = 1 := by
    have hA0 := equalEndpointSL2DiagonalPath_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) hA0
    simpa using h
  have h01_0 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0 1).eval 0 = 0 := by
    have hA0 := equalEndpointSL2DiagonalPath_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 1) hA0
    simpa using h
  have h00_1 :
      ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0 0).eval 1 = ((v⁻¹ : kˣ) : k) := by
    have hA1 := equalEndpointSL2DiagonalPath_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) hA1
    simpa using h
  have h01_1 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0 1).eval 1 = 0 := by
    have hA1 := equalEndpointSL2DiagonalPath_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 1) hA1
    simpa using h
  apply (mem_equalEndpointLineSubmodule (k := k) u
    (equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0
      ((x.1 : equalEndpointPolynomialMulModule k),
        (x.2 : equalEndpointPolynomialMulModule k)))).mpr
  -- Endpoint evaluation of the first row gives `v⁻¹ * (uv f(0)) = u f(0)`.
  dsimp [equalEndpointLineCondition, equalEndpointMatrixRowAction,
    equalEndpointPolynomialMulModule.toPolynomial, f, g]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h00_1, h01_1,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h00_0, h01_0,
    hf']
  simp only [zero_mul, add_zero, one_mul]
  have hcoeff : ((v⁻¹ : kˣ) : k) * ((u * v : kˣ) : k) = (u : k) := by
    rw [Units.val_inv_eq_inv_val]
    simp only [Units.val_mul]
    field_simp [Units.ne_zero v]
  rw [← mul_assoc, hcoeff]

/-- Helper for Chap10 Example 10 55 5: the second coordinate of the explicit diagonal path sends
`I_{uv} × I_1` into `I_v`. -/
theorem equalEndpointSL2DiagonalPath_pairAction_second_mem
    (u v : kˣ)
    (x : equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :
    equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k v := by
  let f : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.1 : equalEndpointPolynomialMulModule k)
  let g : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.2 : equalEndpointPolynomialMulModule k)
  have hg : g.eval 1 = g.eval 0 := by
    -- The second input coordinate lies in `I_1`, hence has equal endpoint values.
    have hx := (mem_equalEndpointLineSubmodule (k := k) 1
      (x.2 : equalEndpointPolynomialMulModule k)).mp x.2.2
    simpa [g, equalEndpointLineCondition] using hx
  have hg' :
      Polynomial.eval 1 (x.2 : equalEndpointPolynomialMulModule k) =
        Polynomial.eval 0 (x.2 : equalEndpointPolynomialMulModule k) := by
    -- Keep a copy of the ratio-one endpoint equation in the unfolded normal form used below.
    simpa [g, equalEndpointPolynomialMulModule.toPolynomial] using hg
  have h10_0 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1 0).eval 0 = 0 := by
    have hA0 := equalEndpointSL2DiagonalPath_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 0) hA0
    simpa using h
  have h11_0 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1 1).eval 0 = 1 := by
    have hA0 := equalEndpointSL2DiagonalPath_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 1) hA0
    simpa using h
  have h10_1 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1 0).eval 1 = 0 := by
    have hA1 := equalEndpointSL2DiagonalPath_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 0) hA1
    simpa using h
  have h11_1 : ((equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1 1).eval 1 = (v : k) := by
    have hA1 := equalEndpointSL2DiagonalPath_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 1) hA1
    simpa using h
  apply (mem_equalEndpointLineSubmodule (k := k) v
    (equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1
      ((x.1 : equalEndpointPolynomialMulModule k),
        (x.2 : equalEndpointPolynomialMulModule k)))).mpr
  -- Endpoint evaluation of the second row gives `v * g(1) = v * g(0)`.
  dsimp [equalEndpointLineCondition, equalEndpointMatrixRowAction,
    equalEndpointPolynomialMulModule.toPolynomial, f, g]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h10_1, h11_1,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h10_0, h11_0,
    hg']
  simp

/-- Helper for Chap10 Example 10 55 5: forgetting the multiplication owner to polynomials is
injective. -/
theorem equalEndpointPolynomialMulModule_toPolynomial_injective :
    Function.Injective (equalEndpointPolynomialMulModule.toPolynomial k) := by
  -- The multiplication owner is a transparent copy of `k[X]`, so the forgetful map is identity.
  intro f g h
  exact h

/-- Helper for Chap10 Example 10 55 5: a polynomial matrix row defines an `R`-linear map on
pairs in the polynomial multiplication owner. -/
noncomputable def equalEndpointMatrixRowLinearMap
    (A : Matrix (Fin 2) (Fin 2) (Polynomial k)) (i : Fin 2) :
    equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k →ₗ[R]
      equalEndpointPolynomialMulModule k :=
  (Algebra.lmul R (equalEndpointPolynomialMulModule k) (A i 0)).comp
      (LinearMap.fst R (equalEndpointPolynomialMulModule k) (equalEndpointPolynomialMulModule k)) +
    (Algebra.lmul R (equalEndpointPolynomialMulModule k) (A i 1)).comp
      (LinearMap.snd R (equalEndpointPolynomialMulModule k) (equalEndpointPolynomialMulModule k))

/-- Helper for Chap10 Example 10 55 5: the linear row map evaluates as the explicit dot-product
row action. -/
theorem equalEndpointMatrixRowLinearMap_apply
    (A : Matrix (Fin 2) (Fin 2) (Polynomial k)) (i : Fin 2)
    (x : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k) :
    equalEndpointMatrixRowLinearMap k A i x = equalEndpointMatrixRowAction k A i x := by
  -- This names the definitional computation so later linearity proofs do not unfold scalars.
  rfl

/-- Helper for Chap10 Example 10 55 5: composing two matrix row actions corresponds to matrix
multiplication. -/
theorem equalEndpointMatrixRowAction_mul
    (A B : Matrix (Fin 2) (Fin 2) (Polynomial k)) (i : Fin 2)
    (x : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k) :
    equalEndpointMatrixRowAction k A i
        (equalEndpointMatrixRowAction k B 0 x,
          equalEndpointMatrixRowAction k B 1 x) =
      equalEndpointMatrixRowAction k (A * B) i x := by
  -- Reduce to the two rows of a `2 × 2` matrix and expand the dot products.
  apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
  fin_cases i
  · dsimp [equalEndpointMatrixRowAction, Matrix.mul_apply,
      equalEndpointPolynomialMulModule.toPolynomial]
    simp [Fin.sum_univ_two]
    ring
  · dsimp [equalEndpointMatrixRowAction, Matrix.mul_apply,
      equalEndpointPolynomialMulModule.toPolynomial]
    simp [Fin.sum_univ_two]
    ring

/-- Helper for Chap10 Example 10 55 5: the first row of the identity matrix returns the first
coordinate. -/
theorem equalEndpointMatrixRowAction_one_zero
    (x : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k) :
    equalEndpointMatrixRowAction k (1 : Matrix (Fin 2) (Fin 2) (Polynomial k)) 0 x = x.1 := by
  -- The identity matrix has first row `(1, 0)`.
  apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
  simp [equalEndpointMatrixRowAction, equalEndpointPolynomialMulModule.toPolynomial]

/-- Helper for Chap10 Example 10 55 5: the second row of the identity matrix returns the second
coordinate. -/
theorem equalEndpointMatrixRowAction_one_one
    (x : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k) :
    equalEndpointMatrixRowAction k (1 : Matrix (Fin 2) (Fin 2) (Polynomial k)) 1 x = x.2 := by
  -- The identity matrix has second row `(0, 1)`.
  apply equalEndpointPolynomialMulModule_toPolynomial_injective (k := k)
  simp [equalEndpointMatrixRowAction, equalEndpointPolynomialMulModule.toPolynomial]

/-- Helper for Chap10 Example 10 55 5: the inverse matrix of the diagonal path also starts at
the identity. -/
theorem equalEndpointSL2DiagonalPath_inv_eval_zero (a : kˣ) :
    ((equalEndpointSL2DiagonalPathUnit (k := k) a).inv.map (Polynomial.evalRingHom 0)) =
      1 := by
  -- Evaluate the explicit inverse product at `X = 0`; all elementary factors become identities.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower]

/-- Helper for Chap10 Example 10 55 5: the inverse matrix of the diagonal path ends at the
inverse diagonal matrix. -/
theorem equalEndpointSL2DiagonalPath_inv_eval_one (a : kˣ) :
    ((equalEndpointSL2DiagonalPathUnit (k := k) a).inv.map (Polynomial.evalRingHom 1)) =
      !![((a⁻¹ : kˣ) : k), 0; 0, (a : k)] := by
  have ha0 : (a : k) ≠ 0 := Units.ne_zero a
  -- Evaluate the inverse elementary product at `X = 1`; the only nontrivial scalar cleanup is
  -- the unit inverse relation in the base field.
  ext i j
  fin_cases i
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
      field_simp [ha0]
      ring
  · fin_cases j
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
    · simp [equalEndpointSL2DiagonalPathUnit, equalEndpointElementaryUpperUnit,
        equalEndpointElementaryLowerUnit, equalEndpointElementaryUpper,
        equalEndpointElementaryLower, Units.val_inv_eq_inv_val]
      field_simp [ha0]
      ring

/-- Helper for Chap10 Example 10 55 5: the first row of the inverse diagonal path sends
`I_u × I_v` into `I_{uv}`. -/
theorem equalEndpointSL2DiagonalPath_inv_pairAction_first_mem
    (u v : kˣ)
    (x : equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :
    equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv 0
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k (u * v) := by
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let f : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.1 : equalEndpointPolynomialMulModule k)
  have hf : f.eval 1 = (u : k) * f.eval 0 := by
    -- The first input coordinate lies in `I_u`.
    have hx := (mem_equalEndpointLineSubmodule (k := k) u
      (x.1 : equalEndpointPolynomialMulModule k)).mp x.1.2
    simpa [f, equalEndpointLineCondition] using hx
  have hf' :
      Polynomial.eval 1 (x.1 : equalEndpointPolynomialMulModule k) =
        (u : k) * Polynomial.eval 0 (x.1 : equalEndpointPolynomialMulModule k) := by
    -- Keep the endpoint-ratio equation in the unfolded normal form used below.
    simpa [f, equalEndpointPolynomialMulModule.toPolynomial] using hf
  have h00_0 : (B 0 0).eval 0 = 1 := by
    have hA0 := equalEndpointSL2DiagonalPath_inv_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) hA0
    simpa [B] using h
  have h01_0 : (B 0 1).eval 0 = 0 := by
    have hA0 := equalEndpointSL2DiagonalPath_inv_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 1) hA0
    simpa [B] using h
  have h00_1 : (B 0 0).eval 1 = (v : k) := by
    have hA1 := equalEndpointSL2DiagonalPath_inv_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) hA1
    simpa [B] using h
  have h01_1 : (B 0 1).eval 1 = 0 := by
    have hA1 := equalEndpointSL2DiagonalPath_inv_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 1) hA1
    simpa [B] using h
  change equalEndpointMatrixRowAction k B 0
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k (u * v)
  apply (mem_equalEndpointLineSubmodule (k := k) (u * v)
    (equalEndpointMatrixRowAction k B 0
      ((x.1 : equalEndpointPolynomialMulModule k),
        (x.2 : equalEndpointPolynomialMulModule k)))).mpr
  -- Endpoint evaluation of the inverse first row gives `v * (u f(0)) = uv f(0)`.
  dsimp [equalEndpointLineCondition, equalEndpointMatrixRowAction,
    equalEndpointPolynomialMulModule.toPolynomial]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h00_1, h01_1,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h00_0, h01_0, hf']
  simp only [zero_mul, add_zero, one_mul]
  rw [← mul_assoc]
  simp [mul_comm, mul_assoc]

/-- Helper for Chap10 Example 10 55 5: the second row of the inverse diagonal path sends
`I_u × I_v` into `I_1`. -/
theorem equalEndpointSL2DiagonalPath_inv_pairAction_second_mem
    (u v : kˣ)
    (x : equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :
    equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv 1
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k 1 := by
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let g : Polynomial k :=
    equalEndpointPolynomialMulModule.toPolynomial k (x.2 : equalEndpointPolynomialMulModule k)
  have hg : g.eval 1 = (v : k) * g.eval 0 := by
    -- The second input coordinate lies in `I_v`.
    have hx := (mem_equalEndpointLineSubmodule (k := k) v
      (x.2 : equalEndpointPolynomialMulModule k)).mp x.2.2
    simpa [g, equalEndpointLineCondition] using hx
  have hg' :
      Polynomial.eval 1 (x.2 : equalEndpointPolynomialMulModule k) =
        (v : k) * Polynomial.eval 0 (x.2 : equalEndpointPolynomialMulModule k) := by
    -- Keep the endpoint-ratio equation in the unfolded normal form used below.
    simpa [g, equalEndpointPolynomialMulModule.toPolynomial] using hg
  have h10_0 : (B 1 0).eval 0 = 0 := by
    have hA0 := equalEndpointSL2DiagonalPath_inv_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 0) hA0
    simpa [B] using h
  have h11_0 : (B 1 1).eval 0 = 1 := by
    have hA0 := equalEndpointSL2DiagonalPath_inv_eval_zero (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 1) hA0
    simpa [B] using h
  have h10_1 : (B 1 0).eval 1 = 0 := by
    have hA1 := equalEndpointSL2DiagonalPath_inv_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 0) hA1
    simpa [B] using h
  have h11_1 : (B 1 1).eval 1 = ((v⁻¹ : kˣ) : k) := by
    have hA1 := equalEndpointSL2DiagonalPath_inv_eval_one (k := k) v⁻¹
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 1 1) hA1
    simpa [B] using h
  change equalEndpointMatrixRowAction k B 1
        ((x.1 : equalEndpointPolynomialMulModule k),
          (x.2 : equalEndpointPolynomialMulModule k)) ∈
      equalEndpointLineSubmodule k 1
  apply (mem_equalEndpointLineSubmodule (k := k) 1
    (equalEndpointMatrixRowAction k B 1
      ((x.1 : equalEndpointPolynomialMulModule k),
        (x.2 : equalEndpointPolynomialMulModule k)))).mpr
  -- Endpoint evaluation of the inverse second row gives `v⁻¹ * (v g(0)) = g(0)`.
  dsimp [equalEndpointLineCondition, equalEndpointMatrixRowAction,
    equalEndpointPolynomialMulModule.toPolynomial]
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h10_1, h11_1,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, h10_0, h11_0, hg']
  simp only [zero_mul, one_mul]
  rw [Units.val_inv_eq_inv_val]
  field_simp [Units.ne_zero v]

/-- Helper for Chap10 Example 10 55 5: the diagonal-path matrix action on line pairs. -/
def equalEndpointSL2DiagonalPath_pairMapToFun (u v : kˣ)
    (x : equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :
    equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v :=
  (⟨equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 0
      ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k)),
    equalEndpointSL2DiagonalPath_pairAction_first_mem (k := k) u v x⟩,
   ⟨equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPath (k := k) v⁻¹) 1
      ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k)),
    equalEndpointSL2DiagonalPath_pairAction_second_mem (k := k) u v x⟩)

/-- Helper for Chap10 Example 10 55 5: the inverse diagonal-path matrix action on line pairs. -/
def equalEndpointSL2DiagonalPath_inversePairMapToFun (u v : kˣ)
    (x : equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :
    equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1 :=
  (⟨equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv 0
      ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k)),
    equalEndpointSL2DiagonalPath_inv_pairAction_first_mem (k := k) u v x⟩,
   ⟨equalEndpointMatrixRowAction k (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv 1
      ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k)),
    equalEndpointSL2DiagonalPath_inv_pairAction_second_mem (k := k) u v x⟩)

/-- Helper for Chap10 Example 10 55 5: the diagonal-path pair action preserves addition. -/
theorem equalEndpointSL2DiagonalPath_pairMap_add
    (u v : kˣ)
    (x y : equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :
    equalEndpointSL2DiagonalPath_pairMapToFun k u v (x + y) =
      equalEndpointSL2DiagonalPath_pairMapToFun k u v x +
        equalEndpointSL2DiagonalPath_pairMapToFun k u v y := by
  let A := equalEndpointSL2DiagonalPath (k := k) v⁻¹
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  let y' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((y.1 : equalEndpointPolynomialMulModule k), (y.2 : equalEndpointPolynomialMulModule k))
  -- Additivity is inherited row-by-row from the ambient linear row map.
  ext
  · exact (equalEndpointMatrixRowLinearMap k A 0).map_add x' y'
  · exact (equalEndpointMatrixRowLinearMap k A 1).map_add x' y'

/-- Helper for Chap10 Example 10 55 5: the diagonal-path pair action preserves scalar
multiplication. -/
theorem equalEndpointSL2DiagonalPath_pairMap_smul
    (u v : kˣ)
    (r : R)
    (x : equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :
    equalEndpointSL2DiagonalPath_pairMapToFun k u v (r • x) =
      r • equalEndpointSL2DiagonalPath_pairMapToFun k u v x := by
  let A := equalEndpointSL2DiagonalPath (k := k) v⁻¹
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  -- Scalar compatibility is inherited row-by-row from the ambient linear row map.
  ext
  · exact (equalEndpointMatrixRowLinearMap k A 0).map_smul r x'
  · exact (equalEndpointMatrixRowLinearMap k A 1).map_smul r x'

/-- Helper for Chap10 Example 10 55 5: the inverse diagonal-path pair action preserves
addition. -/
theorem equalEndpointSL2DiagonalPath_inversePairMap_add
    (u v : kˣ)
    (x y : equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :
    equalEndpointSL2DiagonalPath_inversePairMapToFun k u v (x + y) =
      equalEndpointSL2DiagonalPath_inversePairMapToFun k u v x +
        equalEndpointSL2DiagonalPath_inversePairMapToFun k u v y := by
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  let y' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((y.1 : equalEndpointPolynomialMulModule k), (y.2 : equalEndpointPolynomialMulModule k))
  -- Additivity is inherited row-by-row from the ambient linear row map.
  ext
  · exact (equalEndpointMatrixRowLinearMap k B 0).map_add x' y'
  · exact (equalEndpointMatrixRowLinearMap k B 1).map_add x' y'

/-- Helper for Chap10 Example 10 55 5: the inverse diagonal-path pair action preserves scalar
multiplication. -/
theorem equalEndpointSL2DiagonalPath_inversePairMap_smul
    (u v : kˣ)
    (r : R)
    (x : equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :
    equalEndpointSL2DiagonalPath_inversePairMapToFun k u v (r • x) =
      r • equalEndpointSL2DiagonalPath_inversePairMapToFun k u v x := by
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  -- Scalar compatibility is inherited row-by-row from the ambient linear row map.
  ext
  · exact (equalEndpointMatrixRowLinearMap k B 0).map_smul r x'
  · exact (equalEndpointMatrixRowLinearMap k B 1).map_smul r x'

/-- Helper for Chap10 Example 10 55 5: the diagonal-path pair action as a linear map. -/
noncomputable def equalEndpointSL2DiagonalPath_pairLinearMap (u v : kˣ) :
    (equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) →ₗ[R]
      (equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) :=
  { toFun := equalEndpointSL2DiagonalPath_pairMapToFun k u v
    map_add' := equalEndpointSL2DiagonalPath_pairMap_add k u v
    map_smul' := equalEndpointSL2DiagonalPath_pairMap_smul k u v }

/-- Helper for Chap10 Example 10 55 5: the inverse diagonal-path pair action as a linear map. -/
noncomputable def equalEndpointSL2DiagonalPath_inversePairLinearMap (u v : kˣ) :
    (equalEndpointLineSubmodule k u × equalEndpointLineSubmodule k v) →ₗ[R]
      (equalEndpointLineSubmodule k (u * v) × equalEndpointLineSubmodule k 1) :=
  { toFun := equalEndpointSL2DiagonalPath_inversePairMapToFun k u v
    map_add' := equalEndpointSL2DiagonalPath_inversePairMap_add k u v
    map_smul' := equalEndpointSL2DiagonalPath_inversePairMap_smul k u v }

/-- Helper for Chap10 Example 10 55 5: applying the inverse pair map after the diagonal-path
pair map is the identity. -/
theorem equalEndpointSL2DiagonalPath_inverse_pairLinearMap_comp (u v : kˣ) :
    (equalEndpointSL2DiagonalPath_inversePairLinearMap k u v).comp
        (equalEndpointSL2DiagonalPath_pairLinearMap k u v) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  let A : Matrix (Fin 2) (Fin 2) (Polynomial k) := equalEndpointSL2DiagonalPath (k := k) v⁻¹
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  -- The inverse law is checked on the two subtype coordinates and then reduced to `B * A = 1`.
  apply Prod.ext
  · apply Subtype.ext
    change equalEndpointMatrixRowAction k B 0
        (equalEndpointMatrixRowAction k A 0 x', equalEndpointMatrixRowAction k A 1 x') = x.1
    rw [equalEndpointMatrixRowAction_mul]
    have hBA : B * A = 1 := by
      simpa [A, B] using equalEndpointSL2DiagonalPath_inv_mul (k := k) v⁻¹
    rw [hBA]
    exact equalEndpointMatrixRowAction_one_zero (k := k) x'
  · apply Subtype.ext
    change equalEndpointMatrixRowAction k B 1
        (equalEndpointMatrixRowAction k A 0 x', equalEndpointMatrixRowAction k A 1 x') = x.2
    rw [equalEndpointMatrixRowAction_mul]
    have hBA : B * A = 1 := by
      simpa [A, B] using equalEndpointSL2DiagonalPath_inv_mul (k := k) v⁻¹
    rw [hBA]
    exact equalEndpointMatrixRowAction_one_one (k := k) x'

/-- Helper for Chap10 Example 10 55 5: applying the diagonal-path pair map after its inverse
pair map is the identity. -/
theorem equalEndpointSL2DiagonalPath_pairLinearMap_comp_inverse (u v : kˣ) :
    (equalEndpointSL2DiagonalPath_pairLinearMap k u v).comp
        (equalEndpointSL2DiagonalPath_inversePairLinearMap k u v) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  let A : Matrix (Fin 2) (Fin 2) (Polynomial k) := equalEndpointSL2DiagonalPath (k := k) v⁻¹
  let B : Matrix (Fin 2) (Fin 2) (Polynomial k) :=
    (equalEndpointSL2DiagonalPathUnit (k := k) v⁻¹).inv
  let x' : equalEndpointPolynomialMulModule k × equalEndpointPolynomialMulModule k :=
    ((x.1 : equalEndpointPolynomialMulModule k), (x.2 : equalEndpointPolynomialMulModule k))
  -- The inverse law is checked on the two subtype coordinates and then reduced to `A * B = 1`.
  apply Prod.ext
  · apply Subtype.ext
    change equalEndpointMatrixRowAction k A 0
        (equalEndpointMatrixRowAction k B 0 x', equalEndpointMatrixRowAction k B 1 x') = x.1
    rw [equalEndpointMatrixRowAction_mul]
    have hAB : A * B = 1 := by
      simpa [A, B] using equalEndpointSL2DiagonalPath_mul_inv (k := k) v⁻¹
    rw [hAB]
    exact equalEndpointMatrixRowAction_one_zero (k := k) x'
  · apply Subtype.ext
    change equalEndpointMatrixRowAction k A 1
        (equalEndpointMatrixRowAction k B 0 x', equalEndpointMatrixRowAction k B 1 x') = x.2
    rw [equalEndpointMatrixRowAction_mul]
    have hAB : A * B = 1 := by
      simpa [A, B] using equalEndpointSL2DiagonalPath_mul_inv (k := k) v⁻¹
    rw [hAB]
    exact equalEndpointMatrixRowAction_one_one (k := k) x'

/-- Helper for Chap10 Example 10 55 5: the SL₂ diagonal path gives the stable comparison
between the line-pair `(I_{uv}, I_1)` and `(I_u, I_v)`. -/
noncomputable def equalEndpointSL2DiagonalPath_pairMap_linearEquiv (u v : kˣ) :
    ((equalEndpointLineProjectiveModule k (u * v)).obj × equalEndpointLineSubmodule k 1) ≃ₗ[R]
      ((equalEndpointLineProjectiveModule k u).obj ×
        (equalEndpointLineProjectiveModule k v).obj) :=
  LinearEquiv.ofLinear (equalEndpointSL2DiagonalPath_pairLinearMap k u v)
    (equalEndpointSL2DiagonalPath_inversePairLinearMap k u v)
    (equalEndpointSL2DiagonalPath_pairLinearMap_comp_inverse k u v)
    (equalEndpointSL2DiagonalPath_inverse_pairLinearMap_comp k u v)

/-- Helper for Chap10 Example 10 55 5: a stable direct-sum linear equivalence of Milnor lines
gives the corresponding projective `K₀` class equality. -/
theorem equalEndpointLineProjectiveModule_sum_mul_class_of_linearEquiv
    (u v : kˣ)
    (e :
      ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          (equalEndpointProjectiveFreeModule k).obj) ≃ₗ[R]
        ((equalEndpointLineProjectiveModule k u).obj ×
          (equalEndpointLineProjectiveModule k v).obj)) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v) := by
  let prodIso :
      equalEndpointProjectiveProductModule k
          (equalEndpointLineProjectiveModule k (u * v))
          (equalEndpointProjectiveFreeModule k) ≅
        equalEndpointProjectiveProductModule k
          (equalEndpointLineProjectiveModule k u)
          (equalEndpointLineProjectiveModule k v) :=
    CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R) e.toModuleIso
  -- The general product-object adapter turns this stable module isomorphism into the desired
  -- equality of projective `K₀` classes.
  simpa [equalEndpointProjectiveFreeClass] using
    equalEndpointProjectiveClass_prod_eq_of_iso (k := k) prodIso

/-- Helper for Chap10 Example 10 55 5: every equal-endpoint polynomial lies in the unit-ratio
line through the multiplication owner. -/
theorem equalEndpointLineSubmodule_one_coe_mem (r : R) :
    ((r : Polynomial k) : equalEndpointPolynomialMulModule k) ∈
      equalEndpointLineSubmodule k 1 := by
  -- The previous characterization reduces membership to the defining equal-endpoint property
  -- of `r`.
  apply (mem_equalEndpointLineSubmodule
    (k := k) 1 ((r : Polynomial k) : equalEndpointPolynomialMulModule k)).2
  unfold equalEndpointLineCondition equalEndpointPolynomialMulModule.toPolynomial
  have hr :
      (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 :=
    ((mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2).symm
  simpa [Polynomial.coeff_zero_eq_eval_zero] using hr

/-- Helper for Chap10 Example 10 55 5: an element of the unit-ratio line has an underlying
equal-endpoint polynomial. -/
theorem equalEndpointLineSubmodule_one_toSubring_mem
    (f : equalEndpointLineSubmodule k 1) :
    equalEndpointPolynomialMulModule.toPolynomial k f.1 ∈ R := by
  -- Use the ratio-one membership characterization to recover the equal-endpoint condition.
  exact (mem_equalEndpointLineSubmodule_one_iff (k := k) f.1).mp f.2

/-- Helper for Chap10 Example 10 55 5: the map from `R` into the ratio-one line. -/
def equalEndpointLineSubmodule_oneToLine (r : R) :
    equalEndpointLineSubmodule k 1 :=
  ⟨((r : Polynomial k) : equalEndpointPolynomialMulModule k),
    equalEndpointLineSubmodule_one_coe_mem (k := k) r⟩

/-- Helper for Chap10 Example 10 55 5: the map from the ratio-one line back to `R`. -/
def equalEndpointLineSubmodule_oneToSubring
    (f : equalEndpointLineSubmodule k 1) : R :=
  ⟨equalEndpointPolynomialMulModule.toPolynomial k f.1,
    equalEndpointLineSubmodule_one_toSubring_mem (k := k) f⟩

/-- Helper for Chap10 Example 10 55 5: the map from `R` to the ratio-one line preserves
addition. -/
theorem equalEndpointLineSubmodule_oneToLine_add (r s : R) :
    equalEndpointLineSubmodule_oneToLine k (r + s) =
      equalEndpointLineSubmodule_oneToLine k r +
        equalEndpointLineSubmodule_oneToLine k s := by
  -- The equality is extensional on the underlying polynomial owner.
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: the map from `R` to the ratio-one line preserves scalar
multiplication. -/
theorem equalEndpointLineSubmodule_oneToLine_smul (r s : R) :
    equalEndpointLineSubmodule_oneToLine k (r • s) =
      r • equalEndpointLineSubmodule_oneToLine k s := by
  -- Both scalar actions are ambient multiplication by the same equal-endpoint polynomial.
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: going from `R` to the ratio-one line and back is the
identity. -/
theorem equalEndpointLineSubmodule_oneToSubring_toLine (r : R) :
    equalEndpointLineSubmodule_oneToSubring k
      (equalEndpointLineSubmodule_oneToLine k r) = r := by
  -- The inverse calculation is extensional on the subring carrier.
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: going from the ratio-one line to `R` and back is the
identity. -/
theorem equalEndpointLineSubmodule_oneToLine_toSubring
    (f : equalEndpointLineSubmodule k 1) :
    equalEndpointLineSubmodule_oneToLine k
      (equalEndpointLineSubmodule_oneToSubring k f) = f := by
  -- The inverse calculation is extensional on the line-submodule carrier.
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line is linearly equivalent to the
free rank-one module `R`. -/
noncomputable def equalEndpointLineSubmodule_one_linearEquiv :
    R ≃ₗ[R] equalEndpointLineSubmodule k 1 :=
  { toFun := equalEndpointLineSubmodule_oneToLine k
    invFun := equalEndpointLineSubmodule_oneToSubring k
    map_add' := equalEndpointLineSubmodule_oneToLine_add k
    map_smul' := equalEndpointLineSubmodule_oneToLine_smul k
    left_inv := equalEndpointLineSubmodule_oneToSubring_toLine k
    right_inv := equalEndpointLineSubmodule_oneToLine_toSubring k }

/-- Helper for Chap10 Example 10 55 5: a stable product comparison using the ratio-one
Milnor line as the free summand gives the projective `K₀` product formula. -/
theorem equalEndpointLineProjectiveModule_sum_mul_class_of_lineOne_linearEquiv
    (u v : kˣ)
    (e :
      (((equalEndpointLineProjectiveModule k (u * v)).obj ×
          equalEndpointLineSubmodule k 1) ≃ₗ[R]
        ((equalEndpointLineProjectiveModule k u).obj ×
          (equalEndpointLineProjectiveModule k v).obj))) :
    projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k (u * v)) +
        equalEndpointProjectiveFreeClass k =
      projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k u) +
        projectiveGrothendieckGroupOf R (equalEndpointLineProjectiveModule k v) := by
  -- Replace the free rank-one summand by the ratio-one Milnor line, then reuse the existing
  -- stable-direct-sum adapter.
  let eDomain :
      ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          (equalEndpointProjectiveFreeModule k).obj) ≃ₗ[R]
        ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          equalEndpointLineSubmodule k 1) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R (equalEndpointLineProjectiveModule k (u * v)).obj)
      (equalEndpointLineSubmodule_one_linearEquiv k)
  exact equalEndpointLineProjectiveModule_sum_mul_class_of_linearEquiv (k := k) u v
    (eDomain.trans e)

/-- Helper for Chap10 Example 10 55 5: the stable product comparison exists when the left
endpoint-unit ratio is `1`. -/
theorem equalEndpointLineStableProductLinearEquiv_one_left (u : kˣ) :
    Nonempty (equalEndpointLineStableProductLinearEquiv k 1 u) := by
  -- After reducing the product ratio to `u`, swap the free summand to the left and identify it
  -- with the ratio-one Milnor line.
  refine ⟨?_⟩
  dsimp [equalEndpointLineStableProductLinearEquiv]
  rw [one_mul]
  exact (LinearEquiv.prodComm R (equalEndpointLineSubmodule k u) R).trans
    (LinearEquiv.prodCongr (equalEndpointLineSubmodule_one_linearEquiv k)
      (LinearEquiv.refl R (equalEndpointLineSubmodule k u)))

/-- Helper for Chap10 Example 10 55 5: the stable product comparison exists when the right
endpoint-unit ratio is `1`. -/
theorem equalEndpointLineStableProductLinearEquiv_one_right (u : kˣ) :
    Nonempty (equalEndpointLineStableProductLinearEquiv k u 1) := by
  -- After reducing the product ratio to `u`, identify the free summand with the ratio-one
  -- Milnor line in the second product factor.
  refine ⟨?_⟩
  dsimp [equalEndpointLineStableProductLinearEquiv]
  rw [mul_one]
  exact LinearEquiv.prodCongr (LinearEquiv.refl R (equalEndpointLineSubmodule k u))
    (equalEndpointLineSubmodule_one_linearEquiv k)

/-- Helper for Chap10 Example 10 55 5: the SL₂ diagonal path supplies a stable product
comparison for every pair of Milnor lines. -/
theorem equalEndpointLineStableProductLinearEquiv_all (u v : kˣ) :
    Nonempty (equalEndpointLineStableProductLinearEquiv k u v) := by
  -- Replace the free summand by the ratio-one line and then apply the matrix-pair equivalence.
  refine ⟨?_⟩
  dsimp [equalEndpointLineStableProductLinearEquiv]
  let eDomain :
      ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          (equalEndpointProjectiveFreeModule k).obj) ≃ₗ[R]
        ((equalEndpointLineProjectiveModule k (u * v)).obj ×
          equalEndpointLineSubmodule k 1) :=
    LinearEquiv.prodCongr
      (LinearEquiv.refl R (equalEndpointLineProjectiveModule k (u * v)).obj)
      (equalEndpointLineSubmodule_one_linearEquiv k)
  exact eDomain.trans (equalEndpointSL2DiagonalPath_pairMap_linearEquiv k u v)

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line, as a finitely generated
module, is isomorphic to the regular module. -/
noncomputable def equalEndpointLineFGModule_oneIso :
    FGModuleCat.of R R ≅ equalEndpointLineFGModule k 1 :=
  CategoryTheory.ObjectProperty.isoMk (P := ModuleCat.isFG R)
    (equalEndpointLineSubmodule_one_linearEquiv k).toModuleIso

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line has the same finite
Grothendieck-group class as the regular module. -/
theorem equalEndpointLineFGModule_one_class_eq_regular :
    finiteGrothendieckGroupOf R (equalEndpointLineFGModule k 1) =
      finiteGrothendieckGroupOf R (FGModuleCat.of R R) := by
  have h0 : ModuleCat.isFG R (ModuleCat.of R PUnit) := by
    -- The zero object is finitely generated, which is the base object required by `K₀` iso
    -- invariance.
    rw [ModuleCat.isFG_iff]
    infer_instance
  have h :
      ModulePropertyK0.of R (ModuleCat.isFG R) (FGModuleCat.of R R) =
        ModulePropertyK0.of R (ModuleCat.isFG R) (equalEndpointLineFGModule k 1) := by
    -- Transport the finite-module class across the explicit `R ≃ I_1` isomorphism.
    exact (@ModulePropertyK0.of_iso R _ (ModuleCat.isFG R) h0
      (FGModuleCat.of R R) (equalEndpointLineFGModule k 1)
      (equalEndpointLineFGModule_oneIso k))
  simpa [finiteGrothendieckGroupOf] using h.symm

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line is finitely generated over
`R`. -/
theorem equalEndpointLineSubmodule_one_finite :
    Module.Finite R (equalEndpointLineSubmodule k 1) := by
  -- Push finite generation of the free module `R` across the linear equivalence `R ≃ I_1`.
  exact Module.Finite.of_surjective
    (equalEndpointLineSubmodule_one_linearEquiv k).toLinearMap
    (equalEndpointLineSubmodule_one_linearEquiv k).surjective

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line is projective over `R`. -/
theorem equalEndpointLineSubmodule_one_projective :
    Module.Projective R (equalEndpointLineSubmodule k 1) := by
  -- Projectivity transfers along the linear equivalence from the free rank-one module.
  exact Module.Projective.of_equiv' (equalEndpointLineSubmodule_one_linearEquiv k)

/-- Helper for Chap10 Example 10 55 5: the ratio-one line packaged as a finite projective
module. -/
abbrev equalEndpointLineSubmodule_oneProjectiveModule : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R (equalEndpointLineSubmodule k 1),
    ⟨equalEndpointLineSubmodule_one_finite k,
      equalEndpointLineSubmodule_one_projective k⟩⟩

/-- Helper for Chap10 Example 10 55 5: the ratio-one Milnor line represents the free rank-one
class in projective `K₀`. -/
theorem equalEndpointLineSubmodule_one_class_eq_freeClass :
    projectiveGrothendieckGroupOf R
        (equalEndpointLineSubmodule_oneProjectiveModule k) =
      equalEndpointProjectiveFreeClass k := by
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    -- The zero module is finite projective, so isomorphic finite-projective modules have equal
    -- Grothendieck classes.
    exact ⟨inferInstance, inferInstance⟩
  let e : equalEndpointProjectiveFreeModule k ≅
      equalEndpointLineSubmodule_oneProjectiveModule k :=
    CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
      (equalEndpointLineSubmodule_one_linearEquiv k).toModuleIso
  have h :
      ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
        (equalEndpointProjectiveFreeModule k) =
      ModulePropertyK0.of R (finiteProjectiveModuleProperty R)
        (equalEndpointLineSubmodule_oneProjectiveModule k) := by
    -- Transport the class through the finite-projective subcategory isomorphism induced by
    -- `R ≃ I_1`.
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
      (equalEndpointProjectiveFreeModule k)
      (equalEndpointLineSubmodule_oneProjectiveModule k)
      e)
  simpa [projectiveGrothendieckGroupOf, equalEndpointProjectiveFreeClass,
    equalEndpointProjectiveFreeModule, equalEndpointLineSubmodule_oneProjectiveModule] using h.symm

/-- Helper for Chap10 Example 10 55 5: the unit-ratio Milnor line has zero residual projective
class after subtracting the free rank-one class. -/
theorem equalEndpointLineSubmodule_one_residualClass_eq_zero :
    projectiveGrothendieckGroupOf R (equalEndpointLineSubmodule_oneProjectiveModule k) -
      equalEndpointProjectiveFreeClass k = 0 := by
  -- The base Milnor line is the free module, so the residual line-boundary class vanishes.
  rw [equalEndpointLineSubmodule_one_class_eq_freeClass, sub_self]


end

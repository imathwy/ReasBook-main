import stacks_proof.stacks_project.Chap10.Example_10_55_5.ProjectiveClutching.VectorClutchingBasics

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the polynomial column transvection used to compare
vector-clutching modules after right multiplication of the clutching matrix. -/
def equalEndpointVectorClutchingTransvectionRightVector {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    n → equalEndpointPolynomialMulModule k :=
  fun i =>
    if i = t.i then
      let p : Polynomial k := Polynomial.C t.c * (Polynomial.X - Polynomial.C (1 : k))
      ((equalEndpointPolynomialMulModule.toPolynomial k (x i) +
          p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j) : Polynomial k) :
        equalEndpointPolynomialMulModule k)
    else x i

/-- Helper for Chap10 Example 10 55 5: the right transvection path is the identity at endpoint
`1`. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_eval_one
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) (i : n) :
    Polynomial.eval 1
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionRightVector k t x i)) =
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x i)) := by
  -- At `X = 1`, the coefficient `c (X - 1)` vanishes, so every coordinate is unchanged.
  by_cases h : i = t.i
  · subst i
    simp [equalEndpointVectorClutchingTransvectionRightVector,
      equalEndpointPolynomialMulModule.toPolynomial]
  · simp [equalEndpointVectorClutchingTransvectionRightVector,
      equalEndpointPolynomialMulModule.toPolynomial, h]

/-- Helper for Chap10 Example 10 55 5: at endpoint `0`, the right transvection path applies the
inverse elementary column operation in the transvection target coordinate. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_eval_zero_same
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    Polynomial.eval 0
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionRightVector k t x t.i)) =
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x t.i)) +
        (-t.c) * Polynomial.eval 0
          (equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) := by
  -- At `X = 0`, the coefficient `c (X - 1)` evaluates to `-c`.
  simp [equalEndpointVectorClutchingTransvectionRightVector,
    equalEndpointPolynomialMulModule.toPolynomial]

/-- Helper for Chap10 Example 10 55 5: the right transvection path fixes every coordinate other
than the transvection target coordinate at endpoint `0`. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_eval_zero_of_ne
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) {i : n} (hi : i ≠ t.i) :
    Polynomial.eval 0
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionRightVector k t x i)) =
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x i)) := by
  -- Away from the target coordinate, the polynomial transvection vector is definitionally the
  -- original vector.
  simp [equalEndpointVectorClutchingTransvectionRightVector,
    equalEndpointPolynomialMulModule.toPolynomial, hi]

/-- Helper for Chap10 Example 10 55 5: a vector whose endpoint-`0` values are transformed by the
inverse of a transvection pairs with `g * t` exactly as the original vector pairs with `g`. -/
theorem equalEndpointVectorClutchingTransvectionRight_endpoint_sum
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k) (v y : n → k)
    (hy_i : y t.i = v t.i + (-t.c) * v t.j)
    (hy_ne : ∀ {b : n}, b ≠ t.i → y b = v b) (a : n) :
    ∑ b : n, (g * t.toMatrix) a b * y b = ∑ b : n, g a b * v b := by
  -- Split the row sum first at the changed column of `g * t`, then at the changed coordinate of
  -- the endpoint vector; the two correction terms cancel.
  have hy_j : y t.j = v t.j := hy_ne t.hij.symm
  have hi_mem : t.i ∈ Finset.univ.erase t.j := by
    simp [t.hij]
  have htarget :
      ∑ b : n, g a b * v b =
        g a t.j * v t.j +
          (g a t.i * v t.i +
            (((Finset.univ.erase t.j).erase t.i).sum (fun b => g a b * v b))) := by
    rw [← Finset.add_sum_erase Finset.univ (fun b => g a b * v b)
      (Finset.mem_univ t.j)]
    rw [← Finset.add_sum_erase (Finset.univ.erase t.j) (fun b => g a b * v b)
      hi_mem]
  calc
    ∑ b : n, (g * t.toMatrix) a b * y b =
        (g * t.toMatrix) a t.j * y t.j +
          (Finset.univ.erase t.j).sum (fun b => (g * t.toMatrix) a b * y b) := by
          rw [← Finset.add_sum_erase Finset.univ
            (fun b => (g * t.toMatrix) a b * y b) (Finset.mem_univ t.j)]
    _ = (g a t.j + t.c * g a t.i) * v t.j +
          (Finset.univ.erase t.j).sum (fun b => g a b * y b) := by
          rw [Matrix.TransvectionStruct.toMatrix, Matrix.mul_transvection_apply_same, hy_j]
          congr 1
          apply Finset.sum_congr rfl
          intro b hb
          have hbne : b ≠ t.j := (Finset.mem_erase.mp hb).1
          rw [Matrix.mul_transvection_apply_of_ne (i := t.i) (j := t.j) a b hbne t.c g]
    _ = (g a t.j + t.c * g a t.i) * v t.j +
          (g a t.i * (v t.i + (-t.c) * v t.j) +
            (((Finset.univ.erase t.j).erase t.i).sum (fun b => g a b * v b))) := by
          rw [← Finset.add_sum_erase (Finset.univ.erase t.j)
            (fun b => g a b * y b) hi_mem]
          rw [hy_i]
          congr 2
          apply Finset.sum_congr rfl
          intro b hb
          have hbne : b ≠ t.i := (Finset.mem_erase.mp hb).1
          rw [hy_ne hbne]
    _ = g a t.j * v t.j +
          (g a t.i * v t.i +
            (((Finset.univ.erase t.j).erase t.i).sum (fun b => g a b * v b))) := by
          ring
    _ = ∑ b : n, g a b * v b := htarget.symm

/-- Helper for Chap10 Example 10 55 5: the polynomial right-transvection path sends
`g`-clutching vectors to `(g * t)`-clutching vectors. -/
theorem equalEndpointVectorClutchingCondition_transvection_right
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    {x : n → equalEndpointPolynomialMulModule k}
    (hx : equalEndpointVectorClutchingCondition (k := k) g x) :
    equalEndpointVectorClutchingCondition (k := k) (g * t.toMatrix)
      (equalEndpointVectorClutchingTransvectionRightVector k t x) := by
  -- Endpoint `1` is unchanged, while endpoint `0` is acted on by the inverse elementary column
  -- operation, so the row sum for `g * t` collapses to the original `g`-clutching equation.
  intro a
  have hone :
      Polynomial.eval 1
          (equalEndpointPolynomialMulModule.toPolynomial k
            (equalEndpointVectorClutchingTransvectionRightVector k t x a)) =
        Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x a)) :=
    equalEndpointVectorClutchingTransvectionRightVector_eval_one (k := k) t x a
  have hzero_i :
      Polynomial.eval 0
          (equalEndpointPolynomialMulModule.toPolynomial k
            (equalEndpointVectorClutchingTransvectionRightVector k t x t.i)) =
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x t.i)) +
          (-t.c) * Polynomial.eval 0
            (equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) :=
    equalEndpointVectorClutchingTransvectionRightVector_eval_zero_same (k := k) t x
  have hzero_ne :
      ∀ {b : n}, b ≠ t.i →
        Polynomial.eval 0
            (equalEndpointPolynomialMulModule.toPolynomial k
              (equalEndpointVectorClutchingTransvectionRightVector k t x b)) =
          Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x b)) := by
    intro b hb
    exact equalEndpointVectorClutchingTransvectionRightVector_eval_zero_of_ne (k := k) t x hb
  calc
    Polynomial.eval 1
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionRightVector k t x a)) =
        Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x a)) := hone
    _ = ∑ b : n,
          g a b * Polynomial.eval 0
            (equalEndpointPolynomialMulModule.toPolynomial k (x b)) := by
          simpa [equalEndpointPolynomialMulModule.toPolynomial] using hx a
    _ = ∑ b : n, (g * t.toMatrix) a b *
          Polynomial.eval 0
            (equalEndpointPolynomialMulModule.toPolynomial k
              (equalEndpointVectorClutchingTransvectionRightVector k t x b)) := by
          exact (equalEndpointVectorClutchingTransvectionRight_endpoint_sum (k := k)
            g t
            (fun b => Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x b)))
            (fun b => Polynomial.eval 0
              (equalEndpointPolynomialMulModule.toPolynomial k
                (equalEndpointVectorClutchingTransvectionRightVector k t x b)))
            hzero_i hzero_ne a).symm

/-- Helper for Chap10 Example 10 55 5: the left transvection vector map preserves addition. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_add
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x y : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionLeftVector k t (x + y) =
      equalEndpointVectorClutchingTransvectionLeftVector k t x +
        equalEndpointVectorClutchingTransvectionLeftVector k t y := by
  -- Away from the changed row the map is the identity; on the changed row it is distributivity.
  funext i
  by_cases hi : i = t.i
  · subst i
    let p : Polynomial k := Polynomial.C t.c * Polynomial.X
    have hpoly :
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            equalEndpointPolynomialMulModule.toPolynomial k (y t.i) +
            p * (equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
              equalEndpointPolynomialMulModule.toPolynomial k (y t.j)) =
          equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
            (equalEndpointPolynomialMulModule.toPolynomial k (y t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (y t.j)) := by
      rw [mul_add]
      abel
    simpa only [equalEndpointVectorClutchingTransvectionLeftVector, Pi.add_apply,
      if_pos rfl, equalEndpointPolynomialMulModule.toPolynomial, p] using hpoly
  · simp only [equalEndpointVectorClutchingTransvectionLeftVector, Pi.add_apply, if_neg hi]

/-- Helper for Chap10 Example 10 55 5: the left transvection vector map is `R`-linear on
scalars. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_smul
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (r : R) (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionLeftVector k t (r • x) =
      r • equalEndpointVectorClutchingTransvectionLeftVector k t x := by
  -- The changed row is ordinary polynomial multiplication by the scalar, so commutativity moves
  -- the scalar through the elementary correction term.
  funext i
  by_cases hi : i = t.i
  · subst i
    let p : Polynomial k := Polynomial.C t.c * Polynomial.X
    have hpoly :
        (r : Polynomial k) * equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            p * ((r : Polynomial k) * equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) =
          (r : Polynomial k) *
            (equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) := by
      ring
    simpa only [equalEndpointVectorClutchingTransvectionLeftVector, Pi.smul_apply,
      if_pos rfl, equalEndpointPolynomialMulModule.toPolynomial,
      equalEndpointPolynomialMulModule_smul_eq_mul, p] using hpoly
  · simp only [equalEndpointVectorClutchingTransvectionLeftVector, Pi.smul_apply, if_neg hi]

/-- Helper for Chap10 Example 10 55 5: applying the inverse left transvection vector map after
the left transvection vector map is the identity. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_inv_apply
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionLeftVector k t.inv
        (equalEndpointVectorClutchingTransvectionLeftVector k t x) = x := by
  -- The inverse has the same source and target rows and coefficient `-c`, so the two correction
  -- terms cancel in the only changed coordinate.
  funext i
  by_cases hi : i = t.i
  · subst i
    have hpoly :
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            (Polynomial.C t.c * Polynomial.X) *
              equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
          Polynomial.X * equalEndpointPolynomialMulModule.toPolynomial k (x t.j) *
            Polynomial.C (-t.c) =
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) := by
      rw [Polynomial.C_neg]
      ring
    simpa [equalEndpointVectorClutchingTransvectionLeftVector,
      Matrix.TransvectionStruct.inv_i, Matrix.TransvectionStruct.inv_j,
      Matrix.TransvectionStruct.inv_c, t.hij.symm,
      equalEndpointPolynomialMulModule.toPolynomial] using hpoly
  · have hi_inv : i ≠ t.inv.i := by
      simpa only [Matrix.TransvectionStruct.inv_i] using hi
    simpa [equalEndpointVectorClutchingTransvectionLeftVector,
      Matrix.TransvectionStruct.inv_i, hi, hi_inv]

/-- Helper for Chap10 Example 10 55 5: applying the left transvection vector map after its
inverse vector map is the identity. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_apply_inv
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionLeftVector k t
        (equalEndpointVectorClutchingTransvectionLeftVector k t.inv x) = x := by
  -- This is the previous cancellation identity applied to the inverse transvection.
  simpa [Matrix.TransvectionStruct.inv, equalEndpointVectorClutchingTransvectionLeftVector,
    equalEndpointPolynomialMulModule.toPolynomial] using
    (equalEndpointVectorClutchingTransvectionLeftVector_inv_apply (k := k) t.inv x)

/-- Helper for Chap10 Example 10 55 5: left multiplication of a vector-clutching matrix by a
transvection gives an `R`-linearly equivalent clutching module. -/
theorem equalEndpointVectorClutchingModule_transvection_left_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k) :
    Nonempty
      (equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k) (t.toMatrix * g)) := by
  -- Package the condition-level row-operation bridge into a linear equivalence of submodules.
  refine ⟨
    { toFun := fun x =>
        ⟨equalEndpointVectorClutchingTransvectionLeftVector k t x.1,
          equalEndpointVectorClutchingCondition_transvection_left (k := k) g t x.2⟩
      invFun := fun y =>
        ⟨equalEndpointVectorClutchingTransvectionLeftVector k t.inv y.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro x y
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionLeftVector_add (k := k) t x.1 y.1
  · intro r x
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionLeftVector_smul (k := k) t r x.1
  · -- The inverse row operation carries `(t * g)`-clutching vectors back to `g`-clutching
    -- vectors because `t⁻¹ * t = 1`.
    have hy :=
      equalEndpointVectorClutchingCondition_transvection_left (k := k)
        (t.toMatrix * g) t.inv y.2
    simpa [mem_equalEndpointVectorClutchingModule, ← Matrix.mul_assoc,
      Matrix.TransvectionStruct.inv_mul] using hy
  · intro x
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionLeftVector_inv_apply (k := k) t x.1
  · intro y
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionLeftVector_apply_inv (k := k) t y.1

/-- Helper for Chap10 Example 10 55 5: the right transvection vector map preserves addition. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_add
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x y : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionRightVector k t (x + y) =
      equalEndpointVectorClutchingTransvectionRightVector k t x +
        equalEndpointVectorClutchingTransvectionRightVector k t y := by
  -- Away from the changed column coordinate the map is the identity; at that coordinate it is
  -- distributivity of polynomial multiplication over addition.
  funext i
  by_cases hi : i = t.i
  · subst i
    let p : Polynomial k := Polynomial.C t.c * (Polynomial.X - Polynomial.C (1 : k))
    have hpoly :
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            equalEndpointPolynomialMulModule.toPolynomial k (y t.i) +
            p * (equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
              equalEndpointPolynomialMulModule.toPolynomial k (y t.j)) =
          equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
            (equalEndpointPolynomialMulModule.toPolynomial k (y t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (y t.j)) := by
      rw [mul_add]
      abel
    simpa only [equalEndpointVectorClutchingTransvectionRightVector, Pi.add_apply,
      if_pos rfl, equalEndpointPolynomialMulModule.toPolynomial, p] using hpoly
  · simp only [equalEndpointVectorClutchingTransvectionRightVector, Pi.add_apply, if_neg hi]

/-- Helper for Chap10 Example 10 55 5: the right transvection vector map is `R`-linear on
scalars. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_smul
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (r : R) (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionRightVector k t (r • x) =
      r • equalEndpointVectorClutchingTransvectionRightVector k t x := by
  -- Scalar multiplication is ambient polynomial multiplication, so it commutes with the
  -- right-transvection correction polynomial.
  funext i
  by_cases hi : i = t.i
  · subst i
    let p : Polynomial k := Polynomial.C t.c * (Polynomial.X - Polynomial.C (1 : k))
    have hpoly :
        (r : Polynomial k) * equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            p * ((r : Polynomial k) * equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) =
          (r : Polynomial k) *
            (equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
              p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) := by
      ring
    simpa only [equalEndpointVectorClutchingTransvectionRightVector, Pi.smul_apply,
      if_pos rfl, equalEndpointPolynomialMulModule.toPolynomial,
      equalEndpointPolynomialMulModule_smul_eq_mul, p] using hpoly
  · simp only [equalEndpointVectorClutchingTransvectionRightVector, Pi.smul_apply, if_neg hi]

/-- Helper for Chap10 Example 10 55 5: applying the inverse right transvection vector map after
the right transvection vector map is the identity. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_inv_apply
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionRightVector k t.inv
        (equalEndpointVectorClutchingTransvectionRightVector k t x) = x := by
  -- The inverse right operation uses the same endpoint path with coefficient `-c`, so the
  -- correction terms cancel in the changed coordinate.
  funext i
  by_cases hi : i = t.i
  · subst i
    have hpoly :
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) +
            (Polynomial.C t.c * (Polynomial.X - Polynomial.C (1 : k))) *
              equalEndpointPolynomialMulModule.toPolynomial k (x t.j) +
          (Polynomial.X - Polynomial.C (1 : k)) *
              equalEndpointPolynomialMulModule.toPolynomial k (x t.j) * Polynomial.C (-t.c) =
        equalEndpointPolynomialMulModule.toPolynomial k (x t.i) := by
      rw [Polynomial.C_neg]
      ring
    simpa [equalEndpointVectorClutchingTransvectionRightVector,
      Matrix.TransvectionStruct.inv_i, Matrix.TransvectionStruct.inv_j,
      Matrix.TransvectionStruct.inv_c, t.hij.symm,
      equalEndpointPolynomialMulModule.toPolynomial] using hpoly
  · have hi_inv : i ≠ t.inv.i := by
      simpa only [Matrix.TransvectionStruct.inv_i] using hi
    simpa [equalEndpointVectorClutchingTransvectionRightVector,
      Matrix.TransvectionStruct.inv_i, hi, hi_inv]

/-- Helper for Chap10 Example 10 55 5: applying the right transvection vector map after its
inverse vector map is the identity. -/
theorem equalEndpointVectorClutchingTransvectionRightVector_apply_inv
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingTransvectionRightVector k t
        (equalEndpointVectorClutchingTransvectionRightVector k t.inv x) = x := by
  -- This is the inverse-cancellation identity with `t` replaced by `t⁻¹`.
  simpa [Matrix.TransvectionStruct.inv, equalEndpointVectorClutchingTransvectionRightVector,
    equalEndpointPolynomialMulModule.toPolynomial] using
    (equalEndpointVectorClutchingTransvectionRightVector_inv_apply (k := k) t.inv x)

/-- Helper for Chap10 Example 10 55 5: right multiplication of a vector-clutching matrix by a
transvection gives an `R`-linearly equivalent clutching module. -/
theorem equalEndpointVectorClutchingModule_transvection_right_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k) :
    Nonempty
      (equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k) (g * t.toMatrix)) := by
  -- Package the condition-level column-operation bridge into a linear equivalence of submodules.
  refine ⟨
    { toFun := fun x =>
        ⟨equalEndpointVectorClutchingTransvectionRightVector k t x.1,
          equalEndpointVectorClutchingCondition_transvection_right (k := k) g t x.2⟩
      invFun := fun y =>
        ⟨equalEndpointVectorClutchingTransvectionRightVector k t.inv y.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro x y
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionRightVector_add (k := k) t x.1 y.1
  · intro r x
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionRightVector_smul (k := k) t r x.1
  · -- The inverse column operation carries `(g * t)`-clutching vectors back to `g`-clutching
    -- vectors because `t * t⁻¹ = 1`.
    have hy :=
      equalEndpointVectorClutchingCondition_transvection_right (k := k)
        (g * t.toMatrix) t.inv y.2
    simpa [mem_equalEndpointVectorClutchingModule, Matrix.mul_assoc,
      Matrix.TransvectionStruct.mul_inv] using hy
  · intro x
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionRightVector_inv_apply (k := k) t x.1
  · intro y
    apply Subtype.ext
    exact equalEndpointVectorClutchingTransvectionRightVector_apply_inv (k := k) t y.1

/-- Helper for Chap10 Example 10 55 5: identity vector clutching is coordinatewise membership
in the equal-endpoint ring. -/
theorem equalEndpointVectorClutchingCondition_one_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingCondition (k := k) (1 : Matrix n n k) x ↔
      ∀ i : n, equalEndpointPolynomialMulModule.toPolynomial k (x i) ∈ R := by
  -- The identity matrix makes the row equation compare the two endpoint values of each
  -- coordinate separately.
  constructor
  · intro hx i
    rw [mem_equal_endpoint_poly_subring_iff]
    have hi := hx i
    simpa [equalEndpointVectorClutchingCondition, Matrix.one_apply,
      equalEndpointPolynomialMulModule.toPolynomial, Polynomial.coeff_zero_eq_eval_zero, eq_comm]
      using hi
  · intro hx i
    have hi : Polynomial.eval 0 (x i : Polynomial k) =
        Polynomial.eval 1 (x i : Polynomial k) := by
      have hmem := (mem_equal_endpoint_poly_subring_iff (k := k)
        (equalEndpointPolynomialMulModule.toPolynomial k (x i))).mp (hx i)
      simpa [equalEndpointPolynomialMulModule.toPolynomial, Polynomial.coeff_zero_eq_eval_zero]
        using hmem
    simpa [equalEndpointVectorClutchingCondition, Matrix.one_apply,
      Polynomial.coeff_zero_eq_eval_zero, hi.symm]

/-- Helper for Chap10 Example 10 55 5: membership in the identity vector clutching module is
coordinatewise membership in the equal-endpoint ring. -/
theorem mem_equalEndpointVectorClutchingModule_one_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : n → equalEndpointPolynomialMulModule k) :
    x ∈ equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k) ↔
      ∀ i : n, equalEndpointPolynomialMulModule.toPolynomial k (x i) ∈ R := by
  -- This packages the identity endpoint computation in the submodule membership form that
  -- future linear-equivalence and projectivity lemmas can rewrite with directly.
  rw [mem_equalEndpointVectorClutchingModule,
    equalEndpointVectorClutchingCondition_one_iff]

/-- Helper for Chap10 Example 10 55 5: send a free vector over the equal-endpoint ring to
the identity vector-clutching module by forgetting each coordinate to the polynomial owner. -/
def equalEndpointVectorClutchingModule_oneToModule
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : n → R) :
    equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k) :=
  ⟨fun i => ((x i : Polynomial k) : equalEndpointPolynomialMulModule k),
    (mem_equalEndpointVectorClutchingModule_one_iff (k := k)
      (fun i => ((x i : Polynomial k) : equalEndpointPolynomialMulModule k))).mpr
      (fun i => (x i).2)⟩

/-- Helper for Chap10 Example 10 55 5: recover an equal-endpoint vector from the identity
vector-clutching module coordinatewise. -/
def equalEndpointVectorClutchingModule_oneToSubringVector
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k)) :
    n → R :=
  fun i =>
    ⟨equalEndpointPolynomialMulModule.toPolynomial k (x.1 i),
      ((mem_equalEndpointVectorClutchingModule_one_iff (k := k) x.1).mp x.2) i⟩

/-- Helper for Chap10 Example 10 55 5: the identity-clutching forward map preserves
addition. -/
theorem equalEndpointVectorClutchingModule_oneToModule_add
    {n : Type u} [Fintype n] [DecidableEq n]
    (x y : n → R) :
    equalEndpointVectorClutchingModule_oneToModule k (x + y) =
      equalEndpointVectorClutchingModule_oneToModule k x +
        equalEndpointVectorClutchingModule_oneToModule k y := by
  -- Addition is checked on each underlying polynomial coordinate.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: the identity-clutching forward map preserves
scalar multiplication. -/
theorem equalEndpointVectorClutchingModule_oneToModule_smul
    {n : Type u} [Fintype n] [DecidableEq n]
    (r : R) (x : n → R) :
    equalEndpointVectorClutchingModule_oneToModule k (r • x) =
      r • equalEndpointVectorClutchingModule_oneToModule k x := by
  -- The scalar action on both sides is ambient multiplication by the same equal-endpoint
  -- polynomial, coordinate by coordinate.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: going from free vectors to identity clutching and
back is the identity. -/
theorem equalEndpointVectorClutchingModule_oneToSubringVector_toModule
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : n → R) :
    equalEndpointVectorClutchingModule_oneToSubringVector k
      (equalEndpointVectorClutchingModule_oneToModule k x) = x := by
  -- Each recovered coordinate has the same underlying equal-endpoint polynomial.
  funext i
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: going from identity clutching to free vectors and
back is the identity. -/
theorem equalEndpointVectorClutchingModule_oneToModule_toSubringVector
    {n : Type u} [Fintype n] [DecidableEq n]
    (x : equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k)) :
    equalEndpointVectorClutchingModule_oneToModule k
      (equalEndpointVectorClutchingModule_oneToSubringVector k x) = x := by
  -- The submodule element is determined by its underlying polynomial vector.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: identity vector clutching is the free vector module
over the equal-endpoint ring. -/
noncomputable def equalEndpointVectorClutchingModule_one_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n] :
    (n → R) ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k) :=
  { toFun := equalEndpointVectorClutchingModule_oneToModule k
    invFun := equalEndpointVectorClutchingModule_oneToSubringVector k
    map_add' := equalEndpointVectorClutchingModule_oneToModule_add k
    map_smul' := equalEndpointVectorClutchingModule_oneToModule_smul k
    left_inv := equalEndpointVectorClutchingModule_oneToSubringVector_toModule k
    right_inv := equalEndpointVectorClutchingModule_oneToModule_toSubringVector k }

/-- Helper for Chap10 Example 10 55 5: identity vector clutching is projective over the
equal-endpoint ring. -/
theorem equalEndpointVectorClutchingModule_one_projective
    {n : Type u} [Fintype n] [DecidableEq n] :
    Module.Projective R (equalEndpointVectorClutchingModule (k := k) (1 : Matrix n n k)) := by
  -- Transport projectivity from the finite product of free rank-one modules.
  exact Module.Projective.of_equiv' (equalEndpointVectorClutchingModule_one_linearEquiv k)

/-- Helper for Chap10 Example 10 55 5: every vector clutching module is finitely generated over
the equal-endpoint ring. -/
theorem equalEndpointVectorClutchingModule_finite {n : Type u} [Fintype n]
    (g : Matrix n n k) :
    Module.Finite R (equalEndpointVectorClutchingModule (k := k) g) := by
  -- The vector clutching module is a submodule of a finite ambient polynomial-vector module
  -- over the Noetherian equal-endpoint ring.
  let _ : IsNoetherianRing R := equal_endpoint_poly_subring_isNoetherian k
  let _ : Module.Finite R (equalEndpointPolynomialMulModule k) := by
    simpa [equalEndpointPolynomialMulModule] using equal_endpoint_polynomial_finite (k := k)
  let _ : Module.Finite R (n → equalEndpointPolynomialMulModule k) := inferInstance
  apply Module.Finite.of_fg
  have htop : (⊤ : Submodule R (n → equalEndpointPolynomialMulModule k)).FG :=
    Module.Finite.fg_top
  exact Submodule.FG.of_le htop le_top

/-- Helper for Chap10 Example 10 55 5: every vector clutching module satisfies the finitely
generated object property. -/
theorem equalEndpointVectorClutchingModule_isFG {n : Type u} [Fintype n]
    (g : Matrix n n k) :
    ModuleCat.isFG R (ModuleCat.of R (equalEndpointVectorClutchingModule (k := k) g)) := by
  -- Translate finite generation into the object property used by `FGModuleCat`.
  rw [ModuleCat.isFG_iff]
  exact equalEndpointVectorClutchingModule_finite (k := k) g

/-- Helper for Chap10 Example 10 55 5: package a vector clutching module as a finitely generated
module. -/
abbrev equalEndpointVectorClutchingFGModule {n : Type u} [Fintype n]
    (g : Matrix n n k) : FGModuleCat R :=
  ⟨ModuleCat.of R (equalEndpointVectorClutchingModule (k := k) g),
    equalEndpointVectorClutchingModule_isFG k g⟩

/-- Helper for Chap10 Example 10 55 5: package a projective vector-clutching module as a
finite projective object using an explicit projectivity proof. -/
abbrev equalEndpointVectorClutchingProjectiveModule
    {n : Type u} [Fintype n] (g : Matrix n n k)
    (hprojective :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R (equalEndpointVectorClutchingModule (k := k) g),
    ⟨equalEndpointVectorClutchingModule_finite k g, hprojective⟩⟩

/-- Helper for Chap10 Example 10 55 5: a linear equivalence between vector-clutching modules
transports their projective `K₀` classes. -/
theorem equalEndpointVectorClutchingClass_eq_of_linearEquiv
    {n : Type u} [Fintype n]
    {g h : Matrix n n k}
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g))
    (hh :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) h))
    (e :
      equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k) h) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k h hh) := by
  -- K₀ is invariant under isomorphism in the finite-projective subcategory; the linear
  -- equivalence supplies exactly that isomorphism.
  have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
    exact ⟨inferInstance, inferInstance⟩
  let eIso :
      equalEndpointVectorClutchingProjectiveModule k g hg ≅
        equalEndpointVectorClutchingProjectiveModule k h hh :=
    CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R) e.toModuleIso
  exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
    (equalEndpointVectorClutchingProjectiveModule k g hg)
    (equalEndpointVectorClutchingProjectiveModule k h hh)
    eIso)

/-- Helper for Chap10 Example 10 55 5: equal vector-clutching matrices give linearly equivalent
vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_congr
    {n : Type u} [Fintype n]
    {g h : Matrix n n k} (hgh : g = h) :
    Nonempty
      (equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k) h) := by
  -- Replace the target matrix by the source matrix, then use the identity equivalence.
  subst h
  refine ⟨?_⟩
  exact LinearEquiv.refl R (equalEndpointVectorClutchingModule (k := k) g)

/-- Helper for Chap10 Example 10 55 5: equal vector-clutching matrices have the same projective
`K₀` class for any chosen projectivity proofs. -/
theorem equalEndpointVectorClutchingClass_eq_of_matrix_eq
    {n : Type u} [Fintype n]
    {g h : Matrix n n k} (hgh : g = h)
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g))
    (hh :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) h)) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k h hh) := by
  -- Turn matrix equality into a linear equivalence, then reuse the general K₀ transport lemma.
  rcases equalEndpointVectorClutchingModule_congr (k := k) hgh with ⟨e⟩
  exact equalEndpointVectorClutchingClass_eq_of_linearEquiv (k := k) hg hh e

/-- Helper for Chap10 Example 10 55 5: left multiplication by a transvection preserves
projectivity of vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_transvection_left_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k) (t.toMatrix * g)) := by
  -- Transport projectivity along the transvection linear equivalence.
  rcases equalEndpointVectorClutchingModule_transvection_left_linearEquiv
      (k := k) g t with ⟨e⟩
  let _ :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g) := hg
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: right multiplication by a transvection preserves
projectivity of vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_transvection_right_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k) (g * t.toMatrix)) := by
  -- Transport projectivity along the transvection linear equivalence.
  rcases equalEndpointVectorClutchingModule_transvection_right_linearEquiv
      (k := k) g t with ⟨e⟩
  let _ :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g) := hg
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: left multiplication by a transvection preserves the
projective `K₀` class of a vector-clutching module. -/
theorem equalEndpointVectorClutchingClass_transvection_left
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k (t.toMatrix * g)
          (equalEndpointVectorClutchingModule_transvection_left_projective k g t hg)) := by
  -- First take the transvection linear equivalence, then apply the general K₀ transport lemma.
  rcases equalEndpointVectorClutchingModule_transvection_left_linearEquiv
      (k := k) g t with ⟨e⟩
  exact equalEndpointVectorClutchingClass_eq_of_linearEquiv (k := k) hg
    (equalEndpointVectorClutchingModule_transvection_left_projective k g t hg) e

/-- Helper for Chap10 Example 10 55 5: right multiplication by a transvection preserves the
projective `K₀` class of a vector-clutching module. -/
theorem equalEndpointVectorClutchingClass_transvection_right
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k (g * t.toMatrix)
          (equalEndpointVectorClutchingModule_transvection_right_projective k g t hg)) := by
  -- First take the transvection linear equivalence, then apply the general K₀ transport lemma.
  rcases equalEndpointVectorClutchingModule_transvection_right_linearEquiv
      (k := k) g t with ⟨e⟩
  exact equalEndpointVectorClutchingClass_eq_of_linearEquiv (k := k) hg
    (equalEndpointVectorClutchingModule_transvection_right_projective k g t hg) e

/-- Helper for Chap10 Example 10 55 5: a right-associated fold of left transvections is the
corresponding product of transvection matrices acting on the left. -/
theorem equalEndpointTransvectionList_foldr_normalForm
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k)) :
    L.foldr (fun t A => t.toMatrix * A) g =
      (L.map Matrix.TransvectionStruct.toMatrix).prod * g := by
  -- Induct through the list so every fold step becomes one associative matrix multiplication.
  induction L with
  | nil =>
      simp
  | cons t L ih =>
      simpa [ih, mul_assoc]

/-- Helper for Chap10 Example 10 55 5: a left-associated fold of right transvections is the
corresponding product of transvection matrices acting on the right. -/
theorem equalEndpointTransvectionList_foldl_normalForm
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k)) :
    L.foldl (fun A t => A * t.toMatrix) g =
      g * (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  -- Generalize the starting matrix so the induction hypothesis rewrites the accumulated product.
  induction L generalizing g with
  | nil =>
      simp
  | cons t L ih =>
      simpa [ih, mul_assoc]

/-- Helper for Chap10 Example 10 55 5: a list of left transvections gives an `R`-linear
equivalence of vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_leftTransvectionList_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k)) :
    Nonempty
      (equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k)
          (L.foldr (fun t A => t.toMatrix * A) g)) := by
  -- Compose the one-step left transvection equivalences along the list.
  induction L with
  | nil =>
      refine ⟨?_⟩
      exact LinearEquiv.refl R (equalEndpointVectorClutchingModule (k := k) g)
  | cons t L ih =>
      rcases ih with ⟨eL⟩
      rcases equalEndpointVectorClutchingModule_transvection_left_linearEquiv
          (k := k) (L.foldr (fun t A => t.toMatrix * A) g) t with ⟨eT⟩
      refine ⟨?_⟩
      exact eL.trans eT

/-- Helper for Chap10 Example 10 55 5: a list of right transvections gives an `R`-linear
equivalence of vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_rightTransvectionList_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k)) :
    Nonempty
      (equalEndpointVectorClutchingModule (k := k) g ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k)
          (L.foldl (fun A t => A * t.toMatrix) g)) := by
  -- First perform the head right transvection, then continue with the tail list on the new
  -- right-multiplied matrix.
  induction L generalizing g with
  | nil =>
      refine ⟨?_⟩
      exact LinearEquiv.refl R (equalEndpointVectorClutchingModule (k := k) g)
  | cons t L ih =>
      rcases equalEndpointVectorClutchingModule_transvection_right_linearEquiv
          (k := k) g t with ⟨eT⟩
      rcases ih (g * t.toMatrix) with ⟨eL⟩
      refine ⟨?_⟩
      exact eT.trans eL

/-- Helper for Chap10 Example 10 55 5: a list of left transvections preserves projectivity of
vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_leftTransvectionList_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k)
        (L.foldr (fun t A => t.toMatrix * A) g)) := by
  -- Transport projectivity along the accumulated left-transvection equivalence.
  rcases equalEndpointVectorClutchingModule_leftTransvectionList_linearEquiv
      (k := k) g L with ⟨e⟩
  let _ :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g) := hg
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: a list of right transvections preserves projectivity of
vector-clutching modules. -/
theorem equalEndpointVectorClutchingModule_rightTransvectionList_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k)
        (L.foldl (fun A t => A * t.toMatrix) g)) := by
  -- Transport projectivity along the accumulated right-transvection equivalence.
  rcases equalEndpointVectorClutchingModule_rightTransvectionList_linearEquiv
      (k := k) g L with ⟨e⟩
  let _ :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g) := hg
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: a product of left transvection matrices preserves
projectivity of a vector-clutching module. -/
theorem equalEndpointVectorClutchingModule_leftTransvectionList_prod_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k)
        ((L.map Matrix.TransvectionStruct.toMatrix).prod * g)) := by
  -- First transport along the list-fold equivalence, then rewrite the fold to the product matrix.
  have hfold :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (L.foldr (fun t A => t.toMatrix * A) g)) :=
    equalEndpointVectorClutchingModule_leftTransvectionList_projective (k := k) g L hg
  rcases equalEndpointVectorClutchingModule_congr (k := k)
      (equalEndpointTransvectionList_foldr_normalForm (k := k) g L) with ⟨e⟩
  let _ :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (L.foldr (fun t A => t.toMatrix * A) g)) := hfold
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: a product of right transvection matrices preserves
projectivity of a vector-clutching module. -/
theorem equalEndpointVectorClutchingModule_rightTransvectionList_prod_projective
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g)) :
    Module.Projective R
      (equalEndpointVectorClutchingModule (k := k)
        (g * (L.map Matrix.TransvectionStruct.toMatrix).prod)) := by
  -- First transport along the list-fold equivalence, then rewrite the fold to the product matrix.
  have hfold :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (L.foldl (fun A t => A * t.toMatrix) g)) :=
    equalEndpointVectorClutchingModule_rightTransvectionList_projective (k := k) g L hg
  rcases equalEndpointVectorClutchingModule_congr (k := k)
      (equalEndpointTransvectionList_foldl_normalForm (k := k) g L) with ⟨e⟩
  let _ :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (L.foldl (fun A t => A * t.toMatrix) g)) := hfold
  exact Module.Projective.of_equiv' e

/-- Helper for Chap10 Example 10 55 5: multiplying a clutching matrix on the left by a product of
transvection matrices does not change its projective `K₀` class. -/
theorem equalEndpointVectorClutchingClass_leftTransvectionList_prod
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g))
    (hprod :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          ((L.map Matrix.TransvectionStruct.toMatrix).prod * g))) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k
          ((L.map Matrix.TransvectionStruct.toMatrix).prod * g) hprod) := by
  -- Compose the fold-level equivalence with the product normal-form congruence.
  rcases equalEndpointVectorClutchingModule_leftTransvectionList_linearEquiv
      (k := k) g L with ⟨efold⟩
  rcases equalEndpointVectorClutchingModule_congr (k := k)
      (equalEndpointTransvectionList_foldr_normalForm (k := k) g L) with ⟨eprod⟩
  exact equalEndpointVectorClutchingClass_eq_of_linearEquiv (k := k) hg hprod
    (efold.trans eprod)

/-- Helper for Chap10 Example 10 55 5: multiplying a clutching matrix on the right by a product of
transvection matrices does not change its projective `K₀` class. -/
theorem equalEndpointVectorClutchingClass_rightTransvectionList_prod
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (L : List (Matrix.TransvectionStruct n k))
    (hg :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) g))
    (hprod :
      Module.Projective R
        (equalEndpointVectorClutchingModule (k := k)
          (g * (L.map Matrix.TransvectionStruct.toMatrix).prod))) :
    projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k g hg) =
      projectiveGrothendieckGroupOf R
        (equalEndpointVectorClutchingProjectiveModule k
          (g * (L.map Matrix.TransvectionStruct.toMatrix).prod) hprod) := by
  -- Compose the fold-level equivalence with the product normal-form congruence.
  rcases equalEndpointVectorClutchingModule_rightTransvectionList_linearEquiv
      (k := k) g L with ⟨efold⟩
  rcases equalEndpointVectorClutchingModule_congr (k := k)
      (equalEndpointTransvectionList_foldl_normalForm (k := k) g L) with ⟨eprod⟩
  exact equalEndpointVectorClutchingClass_eq_of_linearEquiv (k := k) hg hprod
    (efold.trans eprod)


end

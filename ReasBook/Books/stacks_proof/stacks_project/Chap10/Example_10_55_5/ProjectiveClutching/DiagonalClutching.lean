import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.VectorTransvections

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: an element of the vector clutching module satisfies its
row-wise endpoint equation. -/
theorem equalEndpointVectorClutchingModule_endpoint {n : Type u} [Fintype n]
    (g : Matrix n n k) (x : equalEndpointVectorClutchingModule (k := k) g) (i : n) :
    Polynomial.eval 1 (x.1 i : Polynomial k) =
      ∑ j : n, g i j * Polynomial.eval 0 (x.1 j : Polynomial k) := by
  -- Project the stored membership proof to the requested row of the clutching equation.
  exact x.2 i

/-- Helper for Chap10 Example 10 55 5: the one-coordinate vector clutching condition is exactly
the existing Milnor line endpoint-ratio condition. -/
theorem equalEndpointVectorClutchingCondition_punit_iff
    (u : kˣ) (x : PUnit → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingCondition (k := k) (fun _ _ : PUnit => (u : k)) x ↔
      equalEndpointLineCondition k u (x PUnit.unit : Polynomial k) := by
  -- In one coordinate, the matrix row sum has just the single endpoint-ratio term.
  constructor
  · intro hx
    unfold equalEndpointVectorClutchingCondition at hx
    unfold equalEndpointLineCondition
    simpa using hx PUnit.unit
  · intro hx i
    cases i
    unfold equalEndpointLineCondition at hx
    simpa [equalEndpointVectorClutchingCondition] using hx

/-- Helper for Chap10 Example 10 55 5: diagonal vector clutching conditions decouple into the
coordinatewise endpoint-ratio equations. -/
theorem equalEndpointVectorClutchingCondition_diagonal_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → k) (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingCondition (k := k) (Matrix.diagonal D) x ↔
      ∀ i : n, Polynomial.eval 1 (x i : Polynomial k) =
        D i * Polynomial.eval 0 (x i : Polynomial k) := by
  -- The diagonal matrix kills every off-diagonal summand in the endpoint row equation.
  constructor
  · intro hx i
    have h := hx i
    simpa [equalEndpointVectorClutchingCondition, Matrix.diagonal] using h
  · intro hx i
    have h := hx i
    simpa [equalEndpointVectorClutchingCondition, Matrix.diagonal] using h

/-- Helper for Chap10 Example 10 55 5: diagonal clutching by units is exactly the
coordinatewise Milnor line endpoint-ratio condition. -/
theorem equalEndpointVectorClutchingCondition_diagonal_units_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (x : n → equalEndpointPolynomialMulModule k) :
    equalEndpointVectorClutchingCondition (k := k)
        (Matrix.diagonal fun i : n => (D i : k)) x ↔
      ∀ i : n, equalEndpointLineCondition k (D i) (x i : Polynomial k) := by
  -- Reduce the diagonal vector equation to one row at a time, then unfold the rank-one line
  -- condition on each coordinate.
  simpa [equalEndpointLineCondition] using
    (equalEndpointVectorClutchingCondition_diagonal_iff (k := k)
      (D := fun i : n => (D i : k)) x)

/-- Helper for Chap10 Example 10 55 5: an element of a unit-diagonal vector clutching module
has each coordinate in the corresponding Milnor line. -/
theorem equalEndpointVectorClutchingModule_diagonal_lineCondition
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ)
    (x : equalEndpointVectorClutchingModule (k := k)
      (Matrix.diagonal fun i : n => (D i : k)))
    (i : n) :
    equalEndpointLineCondition k (D i) (x.1 i : Polynomial k) := by
  -- Read the stored submodule membership through the diagonal-unit bridge.
  exact
    (equalEndpointVectorClutchingCondition_diagonal_units_iff (k := k) D x.1).mp x.2 i

/-- Helper for Chap10 Example 10 55 5: every diagonal entry of a diagonal matrix with nonzero
determinant is nonzero. -/
theorem equalEndpointVectorClutching_diagonalEntry_ne_zero
    {n : Type u} [Fintype n] [DecidableEq n]
    {D : n → k} (hdet : (Matrix.diagonal D).det ≠ 0) (i : n) :
    D i ≠ 0 := by
  -- The determinant of a diagonal matrix is the product of its entries, so product nonvanishing
  -- gives each entry nonvanishing.
  have hprod : (∏ i, D i) ≠ 0 := by
    simpa [Matrix.det_diagonal] using hdet
  exact (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)

/-- Helper for Chap10 Example 10 55 5: a diagonal matrix with unit entries has nonzero
determinant. -/
theorem equalEndpointVectorClutching_diagonalUnits_det_ne_zero
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) :
    (Matrix.diagonal fun i : n => (D i : k)).det ≠ 0 := by
  -- The diagonal determinant is a product of units, hence cannot vanish.
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => (D i).ne_zero

/-- Helper for Chap10 Example 10 55 5: monomial conductor multiples lie in the two-generator
conductor span. -/
theorem equalEndpointConductorMul_X_pow_mem_span_pair (n : ℕ) :
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X ^ n : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈
      Submodule.span R
        ({(((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
            equalEndpointPolynomialMulModule k),
          ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k)} :
          Set (equalEndpointPolynomialMulModule k)) := by
  let E : Polynomial k := Polynomial.X ^ 2 - Polynomial.X
  let S : Submodule R (equalEndpointPolynomialMulModule k) :=
    Submodule.span R
      ({((E : Polynomial k) : equalEndpointPolynomialMulModule k),
        ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
        Set (equalEndpointPolynomialMulModule k))
  change ((E * Polynomial.X ^ n : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [E] using
        (Submodule.subset_span
          (Set.mem_insert ((E : Polynomial k) : equalEndpointPolynomialMulModule k)
            ({((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
              Set (equalEndpointPolynomialMulModule k))) :
          ((E : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S)
  | one =>
      simpa [E, pow_one] using
        (Submodule.subset_span
          (Set.mem_insert_of_mem ((E : Polynomial k) : equalEndpointPolynomialMulModule k)
            (Set.mem_singleton
              ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k))) :
          ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S)
  | more n hn hn1 =>
      let rE : R := ⟨E, by
        rw [mem_equal_endpoint_poly_subring_iff]
        simp [E]⟩
      have hmul :
          ((E * (E * Polynomial.X ^ n) : Polynomial k) :
            equalEndpointPolynomialMulModule k) ∈ S := by
        have h := S.smul_mem rE hn
        simpa [rE, equalEndpointPolynomialMulModule_smul_eq_mul,
          equalEndpointPolynomialMulModule.toPolynomial, mul_assoc] using h
      have hsum :
          (((E * Polynomial.X ^ (n + 1) : Polynomial k) :
              equalEndpointPolynomialMulModule k) +
            ((E * (E * Polynomial.X ^ n) : Polynomial k) :
              equalEndpointPolynomialMulModule k)) ∈ S :=
        S.add_mem hn1 hmul
      have hrec :
          ((E * Polynomial.X ^ (n + 2) : Polynomial k) :
              equalEndpointPolynomialMulModule k) =
            ((E * Polynomial.X ^ (n + 1) : Polynomial k) :
                equalEndpointPolynomialMulModule k) +
              ((E * (E * Polynomial.X ^ n) : Polynomial k) :
                equalEndpointPolynomialMulModule k) := by
        change E * Polynomial.X ^ (n + 2) =
          E * Polynomial.X ^ (n + 1) + E * (E * Polynomial.X ^ n)
        dsimp [E]
        ring_nf
      simpa [hrec] using hsum

/-- Helper for Chap10 Example 10 55 5: every conductor multiple lies in the two-generator
conductor span. -/
theorem equalEndpointConductorMul_mem_span_pair (q : Polynomial k) :
    (((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q : Polynomial k) :
      equalEndpointPolynomialMulModule k) ∈
      Submodule.span R
        ({(((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) : Polynomial k) :
            equalEndpointPolynomialMulModule k),
          ((((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * Polynomial.X : Polynomial k)) :
            equalEndpointPolynomialMulModule k)} :
          Set (equalEndpointPolynomialMulModule k)) := by
  let E : Polynomial k := Polynomial.X ^ 2 - Polynomial.X
  let S : Submodule R (equalEndpointPolynomialMulModule k) :=
    Submodule.span R
      ({((E : Polynomial k) : equalEndpointPolynomialMulModule k),
        ((E * Polynomial.X : Polynomial k) : equalEndpointPolynomialMulModule k)} :
        Set (equalEndpointPolynomialMulModule k))
  change ((E * q : Polynomial k) : equalEndpointPolynomialMulModule k) ∈ S
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa [mul_add] using S.add_mem hp hq
  | monomial n a =>
      have hpow :
          ((E * Polynomial.X ^ n : Polynomial k) :
            equalEndpointPolynomialMulModule k) ∈ S := by
        simpa [E] using equalEndpointConductorMul_X_pow_mem_span_pair (k := k) n
      let rC : R := ⟨Polynomial.C a, by
        rw [mem_equal_endpoint_poly_subring_iff]
        simp⟩
      have hscaled :
          ((Polynomial.C a * (E * Polynomial.X ^ n) : Polynomial k) :
            equalEndpointPolynomialMulModule k) ∈ S := by
        have h := S.smul_mem rC hpow
        simpa [rC, equalEndpointPolynomialMulModule_smul_eq_mul,
          equalEndpointPolynomialMulModule.toPolynomial, mul_assoc] using h
      convert hscaled using 1
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      ring

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio condition is preserved by the
multiplication-owner `R`-action. -/
theorem equalEndpointLineCondition_mulModule_smul
    (u : kˣ) (r : R) {f : equalEndpointPolynomialMulModule k}
    (hf :
      equalEndpointLineCondition k u
        (equalEndpointPolynomialMulModule.toPolynomial k f)) :
    equalEndpointLineCondition k u
      (equalEndpointPolynomialMulModule.toPolynomial k (r • f)) := by
  -- Rewrite the owner action to ambient multiplication, where endpoint preservation was already
  -- proved.
  rw [equalEndpointPolynomialMulModule_smul_eq_mul]
  exact equalEndpointLineCondition_mul (k := k) u r hf

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio carrier is closed under scalar
multiplication on the dedicated polynomial multiplication owner. -/
theorem equalEndpointLineSubmodule_smul_mem
    (u : kˣ) (r : R) {f : equalEndpointPolynomialMulModule k}
    (hf :
      f ∈ {f : equalEndpointPolynomialMulModule k |
        equalEndpointLineCondition k u
          (equalEndpointPolynomialMulModule.toPolynomial k f)}) :
    r • f ∈ {f : equalEndpointPolynomialMulModule k |
      equalEndpointLineCondition k u
        (equalEndpointPolynomialMulModule.toPolynomial k f)} :=
  equalEndpointLineCondition_mulModule_smul (k := k) u r hf

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio line
`I_u = {f : k[X] | f(1) = u f(0)}` as an `R`-submodule of the multiplication owner. -/
def equalEndpointLineSubmodule (u : kˣ) :
    Submodule R (equalEndpointPolynomialMulModule k) :=
  { carrier := {f : equalEndpointPolynomialMulModule k |
      equalEndpointLineCondition k u
        (equalEndpointPolynomialMulModule.toPolynomial k f)}
    zero_mem' := equalEndpointLineCondition_zero (k := k) u
    add_mem' := fun hx hy => equalEndpointLineCondition_add (k := k) u hx hy
    smul_mem' := fun r _ hf => equalEndpointLineSubmodule_smul_mem (k := k) u r hf }

/-- Helper for Chap10 Example 10 55 5: membership in the endpoint-ratio line is exactly the
endpoint-ratio equation on the underlying polynomial. -/
theorem mem_equalEndpointLineSubmodule
    (u : kˣ) (f : equalEndpointPolynomialMulModule k) :
    f ∈ equalEndpointLineSubmodule k u ↔
      equalEndpointLineCondition k u
        (equalEndpointPolynomialMulModule.toPolynomial k f) := by
  -- The line submodule was defined with this carrier predicate.
  rfl

/-- Helper for Chap10 Example 10 55 5: membership in a unit-diagonal vector clutching module is
equivalent to coordinatewise membership in the corresponding Milnor lines. -/
theorem mem_equalEndpointVectorClutchingModule_diagonal_units_iff
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (x : n → equalEndpointPolynomialMulModule k) :
    x ∈ equalEndpointVectorClutchingModule (k := k)
        (Matrix.diagonal fun i : n => (D i : k)) ↔
      ∀ i : n, x i ∈ equalEndpointLineSubmodule k (D i) := by
  -- First expose vector-clutching membership as the endpoint equation, then use the diagonal
  -- unit bridge to read each coordinate as a rank-one Milnor line condition.
  rw [mem_equalEndpointVectorClutchingModule]
  constructor
  · intro hx i
    rw [mem_equalEndpointLineSubmodule]
    have hi :=
      (equalEndpointVectorClutchingCondition_diagonal_units_iff (k := k) D x).mp hx i
    simpa [equalEndpointPolynomialMulModule.toPolynomial] using hi
  · intro hx
    rw [equalEndpointVectorClutchingCondition_diagonal_units_iff (k := k) D x]
    intro i
    have hi := (mem_equalEndpointLineSubmodule (k := k) (D i) (x i)).mp (hx i)
    simpa [equalEndpointPolynomialMulModule.toPolynomial] using hi

/-- Helper for Chap10 Example 10 55 5: send a product of Milnor lines to the corresponding
unit-diagonal vector-clutching module. -/
def equalEndpointVectorClutchingModule_diagonalToModule
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (x : (i : n) → equalEndpointLineSubmodule k (D i)) :
    equalEndpointVectorClutchingModule (k := k)
      (Matrix.diagonal fun i : n => (D i : k)) :=
  ⟨fun i => (x i : equalEndpointPolynomialMulModule k),
    (mem_equalEndpointVectorClutchingModule_diagonal_units_iff (k := k) D
      (fun i => (x i : equalEndpointPolynomialMulModule k))).mpr
      (fun i => (x i).2)⟩

/-- Helper for Chap10 Example 10 55 5: recover the coordinate Milnor lines from a
unit-diagonal vector-clutching module. -/
def equalEndpointVectorClutchingModule_diagonalToLines
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ)
    (x : equalEndpointVectorClutchingModule (k := k)
      (Matrix.diagonal fun i : n => (D i : k))) :
    (i : n) → equalEndpointLineSubmodule k (D i) :=
  fun i =>
    ⟨x.1 i,
      ((mem_equalEndpointVectorClutchingModule_diagonal_units_iff (k := k) D x.1).mp
        x.2) i⟩

/-- Helper for Chap10 Example 10 55 5: the diagonal-clutching forward map preserves
addition. -/
theorem equalEndpointVectorClutchingModule_diagonalToModule_add
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (x y : (i : n) → equalEndpointLineSubmodule k (D i)) :
    equalEndpointVectorClutchingModule_diagonalToModule k D (x + y) =
      equalEndpointVectorClutchingModule_diagonalToModule k D x +
        equalEndpointVectorClutchingModule_diagonalToModule k D y := by
  -- Addition is coordinatewise in the product of line submodules and in the vector clutching
  -- submodule.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: the diagonal-clutching forward map preserves
scalar multiplication. -/
theorem equalEndpointVectorClutchingModule_diagonalToModule_smul
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (r : R) (x : (i : n) → equalEndpointLineSubmodule k (D i)) :
    equalEndpointVectorClutchingModule_diagonalToModule k D (r • x) =
      r • equalEndpointVectorClutchingModule_diagonalToModule k D x := by
  -- Scalar multiplication is also coordinatewise and uses the same ambient polynomial action.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: going from a product of Milnor lines to diagonal
vector clutching and back is the identity. -/
theorem equalEndpointVectorClutchingModule_diagonalToLines_toModule
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ) (x : (i : n) → equalEndpointLineSubmodule k (D i)) :
    equalEndpointVectorClutchingModule_diagonalToLines k D
      (equalEndpointVectorClutchingModule_diagonalToModule k D x) = x := by
  -- Each coordinate is recovered with the same underlying line element.
  funext i
  apply Subtype.ext
  rfl

/-- Helper for Chap10 Example 10 55 5: going from diagonal vector clutching to the product of
Milnor lines and back is the identity. -/
theorem equalEndpointVectorClutchingModule_diagonalToModule_toLines
    {n : Type u} [Fintype n] [DecidableEq n]
    (D : n → kˣ)
    (x : equalEndpointVectorClutchingModule (k := k)
      (Matrix.diagonal fun i : n => (D i : k))) :
    equalEndpointVectorClutchingModule_diagonalToModule k D
      (equalEndpointVectorClutchingModule_diagonalToLines k D x) = x := by
  -- The vector-clutching element is determined by its underlying polynomial vector.
  apply Subtype.ext
  funext i
  rfl

/-- Helper for Chap10 Example 10 55 5: unit-diagonal vector clutching is the product of the
corresponding Milnor line modules. -/
noncomputable def equalEndpointVectorClutchingModule_diagonal_linearEquiv
    {n : Type u} [Fintype n] [DecidableEq n] (D : n → kˣ) :
    ((i : n) → equalEndpointLineSubmodule k (D i)) ≃ₗ[R]
      equalEndpointVectorClutchingModule (k := k)
        (Matrix.diagonal fun i : n => (D i : k)) :=
  { toFun := equalEndpointVectorClutchingModule_diagonalToModule k D
    invFun := equalEndpointVectorClutchingModule_diagonalToLines k D
    map_add' := equalEndpointVectorClutchingModule_diagonalToModule_add k D
    map_smul' := equalEndpointVectorClutchingModule_diagonalToModule_smul k D
    left_inv := equalEndpointVectorClutchingModule_diagonalToLines_toModule k D
    right_inv := equalEndpointVectorClutchingModule_diagonalToModule_toLines k D }

end

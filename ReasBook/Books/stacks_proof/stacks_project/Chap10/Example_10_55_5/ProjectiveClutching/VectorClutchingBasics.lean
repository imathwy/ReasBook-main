import stacks_proof.stacks_project.Chap10.Example_10_55_5.ProjectiveClutching.RankProduct

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio condition defining the Milnor line
submodule attached to a unit `u`. -/
def equalEndpointLineCondition (u : kˣ) (f : Polynomial k) : Prop :=
  f.eval 1 = (u : k) * f.eval 0

/-- Helper for Chap10 Example 10 55 5: the zero polynomial satisfies every endpoint-ratio
condition. -/
theorem equalEndpointLineCondition_zero (u : kˣ) :
    equalEndpointLineCondition k u 0 := by
  -- Both endpoint evaluations of zero vanish, so the line condition is immediate.
  simp [equalEndpointLineCondition]

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio condition is closed under addition. -/
theorem equalEndpointLineCondition_add
    (u : kˣ) {f g : Polynomial k}
    (hf : equalEndpointLineCondition k u f)
    (hg : equalEndpointLineCondition k u g) :
    equalEndpointLineCondition k u (f + g) := by
  -- Evaluate the sum at both endpoints and use distributivity after substituting the two
  -- endpoint-ratio hypotheses.
  simp only [equalEndpointLineCondition, Polynomial.eval_add] at hf hg ⊢
  rw [hf, hg, mul_add]

/-- Helper for Chap10 Example 10 55 5: the endpoint-ratio condition is preserved by ambient
polynomial multiplication by an equal-endpoint polynomial. -/
theorem equalEndpointLineCondition_mul
    (u : kˣ) (r : R) {f : Polynomial k}
    (hf : equalEndpointLineCondition k u f) :
    equalEndpointLineCondition k u ((r : Polynomial k) * f) := by
  -- The scalar owner needed for the Milnor line is ambient multiplication in `k[X]`; this lemma
  -- records the endpoint calculation independently of Lean's competing default module actions.
  have hr :
      (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 := by
    exact ((mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2).symm
  unfold equalEndpointLineCondition at hf ⊢
  calc
    (((r : Polynomial k) * f) : Polynomial k).eval 1 =
        (r : Polynomial k).eval 1 * f.eval 1 := by
      simp only [Polynomial.eval_mul]
    _ = (r : Polynomial k).eval 0 * ((u : k) * f.eval 0) := by
      rw [hr, hf]
    _ = (u : k) * ((r : Polynomial k).eval 0 * f.eval 0) := by
      ring
    _ = (u : k) * ((((r : Polynomial k) * f) : Polynomial k).eval 0) := by
      simp only [Polynomial.eval_mul]

/-- Helper for Chap10 Example 10 55 5: every conductor multiple satisfies every endpoint-ratio
line condition. -/
theorem equalEndpointLineCondition_conductor_mul
    (u : kˣ) (q : Polynomial k) :
    equalEndpointLineCondition k u ((Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q) := by
  -- The conductor vanishes at both endpoints, so both sides of the ratio equation are zero.
  unfold equalEndpointLineCondition
  simp

/-- Helper for Chap10 Example 10 55 5: products of line elements have product ratio. -/
theorem equalEndpointLineCondition_mul_line
    (u v : kˣ) {f g : Polynomial k}
    (hf : equalEndpointLineCondition k u f)
    (hg : equalEndpointLineCondition k v g) :
    equalEndpointLineCondition k (u * v) (f * g) := by
  unfold equalEndpointLineCondition at hf hg ⊢
  simp only [Polynomial.eval_mul]
  rw [hf, hg]
  simpa [mul_assoc, mul_left_comm]

/-- Helper for Chap10 Example 10 55 5: a line element is a linear generator plus a conductor
multiple. -/
theorem equalEndpointLineCondition_exists_conductor_decomposition
    (u : kˣ) {f : Polynomial k}
    (hf : equalEndpointLineCondition k u f) :
    ∃ q : Polynomial k,
      f = Polynomial.C (f.eval 0) *
            (1 + Polynomial.C ((u : k) - 1) * Polynomial.X) +
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q := by
  let line : Polynomial k :=
    Polynomial.C (f.eval 0) * (1 + Polynomial.C ((u : k) - 1) * Polynomial.X)
  let g : Polynomial k := f - line
  have hg0 : g.eval 0 = 0 := by
    simp [g, line]
  have hg1 : g.eval 1 = 0 := by
    unfold equalEndpointLineCondition at hf
    simp [g, line, hf]
    ring
  have hg : g.eval 0 = g.eval 1 := by
    rw [hg0, hg1]
  rcases equal_endpoint_sub_constant_conductor_multiple (k := k) g hg with ⟨q, hq⟩
  have hgE : g = (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q := by
    simpa [hg0] using hq
  refine ⟨q, ?_⟩
  calc
    f = line + g := by
      simp [g]
    _ = line + (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q := by
      rw [hgE]
    _ = Polynomial.C (f.eval 0) *
            (1 + Polynomial.C ((u : k) - 1) * Polynomial.X) +
          (Polynomial.X ^ 2 - Polynomial.X : Polynomial k) * q := rfl

/-- Helper for Chap10 Example 10 55 5: a copy of `k[X]` whose `R`-module structure is
restriction of scalars along the inclusion `R → k[X]`. -/
def equalEndpointPolynomialMulModule : Type u :=
  Polynomial k

/-- Helper for Chap10 Example 10 55 5: the multiplication owner has the additive group of
polynomials. -/
instance equalEndpointPolynomialMulModule.instAddCommMonoid :
    AddCommMonoid (equalEndpointPolynomialMulModule k) :=
  inferInstanceAs (AddCommMonoid (Polynomial k))

/-- Helper for Chap10 Example 10 55 5: the multiplication owner has additive inverses inherited
from polynomials. -/
instance equalEndpointPolynomialMulModule.instAddCommGroup :
    AddCommGroup (equalEndpointPolynomialMulModule k) :=
  inferInstanceAs (AddCommGroup (Polynomial k))

/-- Helper for Chap10 Example 10 55 5: the multiplication owner has the polynomial
commutative-ring structure. -/
instance equalEndpointPolynomialMulModule.instCommRing :
    CommRing (equalEndpointPolynomialMulModule k) :=
  inferInstanceAs (CommRing (Polynomial k))

/-- Helper for Chap10 Example 10 55 5: the multiplication owner is an `R`-module by ambient
polynomial multiplication, not coefficientwise endpoint action. -/
noncomputable instance equalEndpointPolynomialMulModule.instModule :
    Module R (equalEndpointPolynomialMulModule k) :=
  letI : Module R (Polynomial k) := Algebra.toModule
  inferInstanceAs (Module R (Polynomial k))

/-- Helper for Chap10 Example 10 55 5: the multiplication owner is an `R`-algebra through
the ambient inclusion into `k[X]`. -/
noncomputable instance equalEndpointPolynomialMulModule.instAlgebra :
    Algebra R (equalEndpointPolynomialMulModule k) :=
  inferInstanceAs (Algebra R (Polynomial k))

/-- Helper for Chap10 Example 10 55 5: the algebra map from the equal-endpoint ring into the
polynomial multiplication owner is injective. -/
theorem equalEndpointPolynomialMulModule_algebraMap_injective :
    Function.Injective (algebraMap R (equalEndpointPolynomialMulModule k)) := by
  -- The multiplication owner is just `k[X]`, and the algebra map is the subring inclusion.
  intro r s h
  apply Subtype.ext
  change (r : Polynomial k) = (s : Polynomial k)
  exact h

/-- Helper for Chap10 Example 10 55 5: the polynomial multiplication owner is faithful over the
equal-endpoint ring. -/
theorem equalEndpointPolynomialMulModule_faithfulSMul :
    FaithfulSMul R (equalEndpointPolynomialMulModule k) := by
  -- Faithfulness is exactly injectivity of the algebra map for this inclusion owner.
  exact (faithfulSMul_iff_algebraMap_injective R (equalEndpointPolynomialMulModule k)).mpr
    (equalEndpointPolynomialMulModule_algebraMap_injective k)

/-- Helper for Chap10 Example 10 55 5: forget the multiplication owner back to the underlying
polynomial. -/
def equalEndpointPolynomialMulModule.toPolynomial
    (f : equalEndpointPolynomialMulModule k) : Polynomial k :=
  f

/-- Helper for Chap10 Example 10 55 5: on the multiplication owner, scalar multiplication is
ordinary multiplication by the underlying equal-endpoint polynomial. -/
theorem equalEndpointPolynomialMulModule_smul_eq_mul
    (r : R) (f : equalEndpointPolynomialMulModule k) :
    equalEndpointPolynomialMulModule.toPolynomial k (r • f) =
      (r : Polynomial k) * equalEndpointPolynomialMulModule.toPolynomial k f := by
  -- This type owner installs the restricted-scalars module, so the scalar action is literal
  -- ambient polynomial multiplication.
  rfl

/-- Helper for Chap10 Example 10 55 5: a polynomial vector satisfies the endpoint clutching
condition for the matrix `g` when its value at `1` is obtained from its value at `0` by `g`. -/
def equalEndpointVectorClutchingCondition {n : Type u} [Fintype n]
    (g : Matrix n n k) (x : n → equalEndpointPolynomialMulModule k) : Prop :=
  ∀ i : n,
    Polynomial.eval 1 (x i : Polynomial k) =
      ∑ j : n, g i j * Polynomial.eval 0 (x j : Polynomial k)

/-- Helper for Chap10 Example 10 55 5: the zero vector satisfies every endpoint clutching
condition. -/
theorem equalEndpointVectorClutchingCondition_zero {n : Type u} [Fintype n]
    (g : Matrix n n k) :
    equalEndpointVectorClutchingCondition (k := k) g 0 := by
  -- Both endpoint vectors are zero, so every matrix row sum is zero.
  intro i
  change Polynomial.eval 1 (0 : Polynomial k) =
    ∑ j : n, g i j * Polynomial.eval 0 (0 : Polynomial k)
  simp

/-- Helper for Chap10 Example 10 55 5: endpoint clutching conditions are closed under vector
addition. -/
theorem equalEndpointVectorClutchingCondition_add {n : Type u} [Fintype n]
    (g : Matrix n n k) {x y : n → equalEndpointPolynomialMulModule k}
    (hx : equalEndpointVectorClutchingCondition (k := k) g x)
    (hy : equalEndpointVectorClutchingCondition (k := k) g y) :
    equalEndpointVectorClutchingCondition (k := k) g (x + y) := by
  -- Endpoint evaluation is additive, and the matrix row action distributes over the finite sum.
  intro i
  calc
    Polynomial.eval 1 ((x + y) i : Polynomial k) =
        Polynomial.eval 1 (x i : Polynomial k) + Polynomial.eval 1 (y i : Polynomial k) := by
      exact Polynomial.eval_add
    _ = (∑ j : n, g i j * Polynomial.eval 0 (x j : Polynomial k)) +
          (∑ j : n, g i j * Polynomial.eval 0 (y j : Polynomial k)) := by
      rw [hx i, hy i]
    _ = ∑ j : n,
          (g i j * Polynomial.eval 0 (x j : Polynomial k) +
            g i j * Polynomial.eval 0 (y j : Polynomial k)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ j : n,
          g i j * Polynomial.eval 0 ((x + y) j : Polynomial k) := by
      apply Finset.sum_congr rfl
      intro j _
      have hEval : Polynomial.eval 0 ((x + y) j : Polynomial k) =
          Polynomial.eval 0 (x j : Polynomial k) + Polynomial.eval 0 (y j : Polynomial k) := by
        exact Polynomial.eval_add
      rw [hEval]
      ring

/-- Helper for Chap10 Example 10 55 5: endpoint clutching conditions are closed under the
equal-endpoint scalar action. -/
theorem equalEndpointVectorClutchingCondition_smul {n : Type u} [Fintype n]
    (g : Matrix n n k) (r : R) {x : n → equalEndpointPolynomialMulModule k}
    (hx : equalEndpointVectorClutchingCondition (k := k) g x) :
    equalEndpointVectorClutchingCondition (k := k) g (r • x) := by
  -- The scalar has the same endpoint value at `0` and `1`, so it factors through both sides of
  -- the clutching equation.
  intro i
  have hr : (r : Polynomial k).eval 1 = (r : Polynomial k).eval 0 := by
    exact ((mem_equal_endpoint_poly_subring_iff (k := k) (r : Polynomial k)).mp r.2).symm
  calc
    Polynomial.eval 1 ((r • x) i : Polynomial k) =
        (r : Polynomial k).eval 1 * Polynomial.eval 1 (x i : Polynomial k) := by
      rw [Pi.smul_apply]
      exact Polynomial.eval_mul
    _ = (r : Polynomial k).eval 0 *
          (∑ j : n, g i j * Polynomial.eval 0 (x j : Polynomial k)) := by
      rw [hr, hx i]
    _ = ∑ j : n,
          (r : Polynomial k).eval 0 *
            (g i j * Polynomial.eval 0 (x j : Polynomial k)) := by
      rw [Finset.mul_sum]
    _ = ∑ j : n,
          g i j * ((r : Polynomial k).eval 0 * Polynomial.eval 0 (x j : Polynomial k)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : n,
          g i j * Polynomial.eval 0 ((r • x) j : Polynomial k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Pi.smul_apply]
      have hEval : Polynomial.eval 0 ((r • x j : equalEndpointPolynomialMulModule k) :
            Polynomial k) =
          (r : Polynomial k).eval 0 * Polynomial.eval 0 (x j : Polynomial k) := by
        exact Polynomial.eval_mul
      rw [hEval]

/-- Helper for Chap10 Example 10 55 5: the vector clutching module attached to an endpoint
matrix `g`. -/
def equalEndpointVectorClutchingModule {n : Type u} [Fintype n]
    (g : Matrix n n k) : Submodule R (n → equalEndpointPolynomialMulModule k) :=
  { carrier := {x | equalEndpointVectorClutchingCondition (k := k) g x}
    zero_mem' := equalEndpointVectorClutchingCondition_zero (k := k) g
    add_mem' := fun hx hy => equalEndpointVectorClutchingCondition_add (k := k) g hx hy
    smul_mem' := fun r _ hx => equalEndpointVectorClutchingCondition_smul (k := k) g r hx }

/-- Helper for Chap10 Example 10 55 5: membership in a vector clutching module is exactly the
matrix endpoint clutching equation. -/
theorem mem_equalEndpointVectorClutchingModule {n : Type u} [Fintype n]
    (g : Matrix n n k) (x : n → equalEndpointPolynomialMulModule k) :
    x ∈ equalEndpointVectorClutchingModule (k := k) g ↔
      equalEndpointVectorClutchingCondition (k := k) g x := by
  -- The module was defined by this carrier predicate.
  rfl

/-- Helper for Chap10 Example 10 55 5: the polynomial row transvection used to compare
vector-clutching modules after left multiplication of the clutching matrix. -/
def equalEndpointVectorClutchingTransvectionLeftVector {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    n → equalEndpointPolynomialMulModule k :=
  fun i =>
    if i = t.i then
      let p : Polynomial k := Polynomial.C t.c * Polynomial.X
      ((equalEndpointPolynomialMulModule.toPolynomial k (x i) +
          p * equalEndpointPolynomialMulModule.toPolynomial k (x t.j) : Polynomial k) :
        equalEndpointPolynomialMulModule k)
    else x i

/-- Helper for Chap10 Example 10 55 5: the left transvection path is the identity at endpoint
`0`. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_eval_zero
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) (i : n) :
    Polynomial.eval 0
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionLeftVector k t x i)) =
      Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x i)) := by
  -- At `X = 0`, the transvection coefficient `cX` vanishes, so every coordinate is unchanged.
  by_cases h : i = t.i
  · simp [equalEndpointVectorClutchingTransvectionLeftVector,
      equalEndpointPolynomialMulModule.toPolynomial, h]
  · simp [equalEndpointVectorClutchingTransvectionLeftVector,
      equalEndpointPolynomialMulModule.toPolynomial, h]

/-- Helper for Chap10 Example 10 55 5: at endpoint `1`, the transvection path performs the
specified elementary row operation. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_eval_one_same
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) :
    Polynomial.eval 1
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionLeftVector k t x t.i)) =
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x t.i)) +
        t.c * Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) := by
  -- At `X = 1`, the coefficient `cX` evaluates to `c`.
  simp [equalEndpointVectorClutchingTransvectionLeftVector,
    equalEndpointPolynomialMulModule.toPolynomial]

/-- Helper for Chap10 Example 10 55 5: the left transvection path fixes every row other than
the transvection target row. -/
theorem equalEndpointVectorClutchingTransvectionLeftVector_eval_one_of_ne
    {n : Type u} [DecidableEq n]
    (t : Matrix.TransvectionStruct n k)
    (x : n → equalEndpointPolynomialMulModule k) {i : n} (hi : i ≠ t.i) :
    Polynomial.eval 1
        (equalEndpointPolynomialMulModule.toPolynomial k
          (equalEndpointVectorClutchingTransvectionLeftVector k t x i)) =
      Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x i)) := by
  -- Away from the target row, the polynomial transvection vector is definitionally the original
  -- vector.
  simp [equalEndpointVectorClutchingTransvectionLeftVector,
    equalEndpointPolynomialMulModule.toPolynomial, hi]

/-- Helper for Chap10 Example 10 55 5: the polynomial left-transvection path sends
`g`-clutching vectors to `(t * g)`-clutching vectors. -/
theorem equalEndpointVectorClutchingCondition_transvection_left
    {n : Type u} [Fintype n] [DecidableEq n]
    (g : Matrix n n k) (t : Matrix.TransvectionStruct n k)
    {x : n → equalEndpointPolynomialMulModule k}
    (hx : equalEndpointVectorClutchingCondition (k := k) g x) :
    equalEndpointVectorClutchingCondition (k := k) (t.toMatrix * g)
      (equalEndpointVectorClutchingTransvectionLeftVector k t x) := by
  -- Endpoint `0` is unchanged, so the right side of the new clutching equation only changes
  -- through the row operation on the matrix.
  intro a
  have hzero (b : n) :
      Polynomial.eval 0
          (equalEndpointPolynomialMulModule.toPolynomial k
            (equalEndpointVectorClutchingTransvectionLeftVector k t x b)) =
        Polynomial.eval 0 (equalEndpointPolynomialMulModule.toPolynomial k (x b)) :=
    equalEndpointVectorClutchingTransvectionLeftVector_eval_zero (k := k) t x b
  by_cases ha : a = t.i
  · subst a
    -- In the target row, endpoint `1` adds `c` times the source row equation.
    calc
      Polynomial.eval 1
          (equalEndpointPolynomialMulModule.toPolynomial k
            (equalEndpointVectorClutchingTransvectionLeftVector k t x t.i)) =
          Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x t.i)) +
            t.c * Polynomial.eval 1
              (equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) := by
            exact equalEndpointVectorClutchingTransvectionLeftVector_eval_one_same (k := k) t x
      _ = (∑ b : n,
            g t.i b * Polynomial.eval 0
              (equalEndpointPolynomialMulModule.toPolynomial k (x b))) +
            t.c * (∑ b : n,
              g t.j b * Polynomial.eval 0
                (equalEndpointPolynomialMulModule.toPolynomial k (x b))) := by
            have hi :
                Polynomial.eval 1
                    (equalEndpointPolynomialMulModule.toPolynomial k (x t.i)) =
                  ∑ b : n,
                    g t.i b * Polynomial.eval 0
                      (equalEndpointPolynomialMulModule.toPolynomial k (x b)) := by
              simpa [equalEndpointPolynomialMulModule.toPolynomial] using hx t.i
            have hj :
                Polynomial.eval 1
                    (equalEndpointPolynomialMulModule.toPolynomial k (x t.j)) =
                  ∑ b : n,
                    g t.j b * Polynomial.eval 0
                      (equalEndpointPolynomialMulModule.toPolynomial k (x b)) := by
              simpa [equalEndpointPolynomialMulModule.toPolynomial] using hx t.j
            rw [hi, hj]
      _ = ∑ b : n, (t.toMatrix * g) t.i b *
            Polynomial.eval 0
              (equalEndpointPolynomialMulModule.toPolynomial k
                (equalEndpointVectorClutchingTransvectionLeftVector k t x b)) := by
            simp only [Matrix.TransvectionStruct.toMatrix,
              Matrix.transvection_mul_apply_same, hzero]
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro b _
            ring
  · -- In every other row, the transvection path and the matrix row are both unchanged.
    calc
      Polynomial.eval 1
          (equalEndpointPolynomialMulModule.toPolynomial k
            (equalEndpointVectorClutchingTransvectionLeftVector k t x a)) =
          Polynomial.eval 1 (equalEndpointPolynomialMulModule.toPolynomial k (x a)) := by
            exact equalEndpointVectorClutchingTransvectionLeftVector_eval_one_of_ne
              (k := k) t x ha
      _ = ∑ b : n,
            g a b * Polynomial.eval 0
              (equalEndpointPolynomialMulModule.toPolynomial k (x b)) := by
            simpa [equalEndpointPolynomialMulModule.toPolynomial] using hx a
      _ = ∑ b : n, (t.toMatrix * g) a b *
            Polynomial.eval 0
              (equalEndpointPolynomialMulModule.toPolynomial k
                (equalEndpointVectorClutchingTransvectionLeftVector k t x b)) := by
            simp [Matrix.TransvectionStruct.toMatrix,
              Matrix.transvection_mul_apply_of_ne, hzero, ha]


end

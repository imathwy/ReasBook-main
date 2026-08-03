import Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1
import Integer.Chapters.Chap01.section_1_7.ch1_sec1_7_exercise_1_9
import Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_theorem_3_34
import Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: rational `H`-presentations of polyhedra, their extreme points, and their
--   extreme rays
-- * sampled owners in this domain: Chapter 1.3.1 `rational_encoding_size` /
--   `rational_vector_encoding_size`, Chapter 4.1 `rational_matrix_polyhedron`, mathlib's canonical
--   `Set.extremePoints ℝ`, and Section 3.11 `IsExtremeRayOfPolyhedron`
-- * owner abstraction: the geometric inputs are already canonically expressed as extreme points of
--   a set and extreme rays of a polyhedron
-- * primitive data: a rational inequality presentation `A x ≤ b` with coefficient-size bound `L`
-- * derived API: bounded rational coordinates for extreme points and bounded positive rational
--   rescalings for extreme rays

section Theorem338

/-- Helper for Theorem 3.38: a square rational subsystem with linearly independent real rows has
at most one real solution. -/
private lemma selected_square_subsystem_solution_unique
    {n : ℕ}
    (A0 : Matrix (Fin n) (Fin n) ℚ)
    (b0 : Fin n → ℚ)
    (hrows : LinearIndependent ℝ (fun i : Fin n ↦ (A0.map (Rat.castHom ℝ)) i))
    {x y : Fin n → ℝ}
    (hx : (A0.map (Rat.castHom ℝ)) *ᵥ x = fun i ↦ (b0 i : ℝ))
    (hy : (A0.map (Rat.castHom ℝ)) *ᵥ y = fun i ↦ (b0 i : ℝ)) :
    x = y := by
  -- Subtract the two solutions to reduce uniqueness to the homogeneous system.
  have hsub : (A0.map (Rat.castHom ℝ)) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hx, hy, sub_self]
  have hann : ∀ i : Fin n, ((A0.map (Rat.castHom ℝ)) i) ⬝ᵥ (x - y) = 0 := by
    intro i
    -- Reading off the `i`th row turns the homogeneous matrix equality into the required dot
    -- product vanishing.
    exact congrFun hsub i
  have hzero :
      x - y = 0 :=
    eq_zero_of_linearIndependent_rows_annihilate hrows hann
  exact sub_eq_zero.mp hzero

/-- Helper for Theorem 3.38: the encoding size of any square rational subsystem with coefficient
bound `L` is controlled by the cubic majorant `X^3 + X^2` evaluated at `n + L`. -/
private lemma square_rational_system_encoding_bound
    {n : ℕ}
    (A0 : Matrix (Fin n) (Fin n) ℚ)
    (b0 : Fin n → ℚ)
    (L : ℕ)
    (hA0 : ∀ i j, rational_encoding_size (A0 i j) ≤ L)
    (hb0 : ∀ i : Fin n, rational_encoding_size (b0 i) ≤ L) :
    rational_linear_system_encoding_size A0 b0 ≤
      (Polynomial.X ^ 3 + Polynomial.X ^ 2).eval (n + L) := by
  have hmatrix :
      rational_matrix_encoding_size A0 ≤ n * (n * L) := by
    -- Bound each selected row by summing the coordinatewise encoding bound `L`.
    calc
      rational_matrix_encoding_size A0
          = ∑ i : Fin n, rational_vector_encoding_size (A0 i) := rfl
      _ ≤ ∑ i : Fin n, n * L := by
            refine Finset.sum_le_sum ?_
            intro i hi
            calc
              rational_vector_encoding_size (A0 i)
                  = ∑ j : Fin n, rational_encoding_size (A0 i j) := rfl
              _ ≤ ∑ j : Fin n, L := by
                    refine Finset.sum_le_sum ?_
                    intro j hj
                    exact hA0 i j
              _ = n * L := by simp
      _ = n * (n * L) := by simp [Nat.mul_assoc]
  have hvector :
      rational_vector_encoding_size b0 ≤ n * L := by
    -- The right-hand side contributes one more length-`n` block with the same coordinate bound.
    calc
      rational_vector_encoding_size b0
          = ∑ i : Fin n, rational_encoding_size (b0 i) := rfl
      _ ≤ ∑ i : Fin n, L := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact hb0 i
      _ = n * L := by simp
  have hsystem :
      rational_linear_system_encoding_size A0 b0 ≤ n * (n * L) + n * L := by
    -- Add the matrix and right-hand side estimates.
    exact add_le_add hmatrix hvector
  let N : ℕ := n + L
  have hn : n ≤ N := Nat.le_add_right n L
  have hL : L ≤ N := Nat.le_add_left L n
  have hcube : n * (n * L) ≤ N * (N * N) := by
    exact Nat.mul_le_mul hn (Nat.mul_le_mul hn hL)
  have hsquare : n * L ≤ N * N := by
    exact Nat.mul_le_mul hn hL
  -- Replace the concrete size estimate by a universal polynomial in `n + L`.
  have hmajor :
      N * (N * N) + N * N ≤
        (Polynomial.X ^ 3 + Polynomial.X ^ 2).eval (n + L) := by
    simpa [N, pow_succ, Nat.mul_assoc] using
      (le_rfl : N * (N * N) + N * N ≤ N * (N * N) + N * N)
  exact hsystem.trans ((add_le_add hcube hsquare).trans hmajor)

/-- Helper for Theorem 3.38: evaluation of a natural-coefficient polynomial is monotone on `ℕ`. -/
private lemma polynomial_eval_nat_mono (p : Polynomial ℕ) :
    Monotone p.eval := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq x y hxy
    -- Monotonicity is preserved under addition.
    simpa [Polynomial.eval_add] using add_le_add (hp hxy) (hq hxy)
  · intro n a x y hxy
    -- A single monomial is monotone because both multiplication and powers are monotone on `ℕ`.
    simp [Polynomial.eval_monomial]
    gcongr

/-- Theorem 3.38 (1). There is a uniform polynomial bound, depending only on the dimension and the
encoding bound for the rational `H`-presentation, such that every extreme point of the polyhedron
`P = {x ∈ ℝ^n | A x ≤ b}` is itself a rational point whose coordinate encoding size is at most
that value. -/
theorem rational_vertices_have_polynomially_bounded_encoding_size
    : ∃ π : Polynomial ℕ,
        ∀ {m n : ℕ}
          (A : Matrix (Fin m) (Fin n) ℚ)
          (b : Fin m → ℚ)
          (L : ℕ)
          (hA : ∀ i j, rational_encoding_size (A i j) ≤ L)
          (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
          (x : Fin n → ℝ)
          (hx : x ∈ (rational_matrix_polyhedron A b).extremePoints ℝ),
          ∃ v : Fin n → ℚ,
            x = (fun k ↦ (v k : ℝ)) ∧
            rational_vector_encoding_size v ≤ π.eval (n + L) := by
  obtain ⟨p, hp⟩ := rational_linear_system_has_small_rational_solution
  let σ : Polynomial ℕ := Polynomial.X ^ 3 + Polynomial.X ^ 2
  refine ⟨p.comp σ, ?_⟩
  intro m n A b L hA hb x hx
  have hx_mem : x ∈ rational_matrix_polyhedron A b := by
    -- An extreme point is, in particular, a feasible point of the ambient polyhedron.
    exact extremePoints_subset hx
  obtain ⟨I, hactive, hlin⟩ :=
    (mem_extremePoints_iff_exists_active_linearlyIndependent_rows
      (A.map (Rat.castHom ℝ))
      (fun i ↦ (b i : ℝ))
      hx_mem).mp hx
  let A0 : Matrix (Fin n) (Fin n) ℚ := A.submatrix I id
  let b0 : Fin n → ℚ := b ∘ I
  have hx_system :
      (A0.map (Rat.castHom ℝ)) *ᵥ x = fun i ↦ (b0 i : ℝ) := by
    -- The active rows selected by Theorem 3.34 form the square subsystem solved by the vertex.
    ext i
    simpa [A0, b0] using hactive i
  have hA0_linear :
      LinearIndependent ℝ (fun i : Fin n ↦ (A0.map (Rat.castHom ℝ)) i) := by
    -- Repackage the selected active rows as the rows of the square subsystem matrix.
    simpa [A0] using hlin
  have hA0 : ∀ i j, rational_encoding_size (A0 i j) ≤ L := by
    intro i j
    exact hA (I i) j
  have hb0 : ∀ i : Fin n, rational_encoding_size (b0 i) ≤ L := by
    intro i
    exact hb (I i)
  rcases hp n n A0 b0 ⟨x, hx_system⟩ with ⟨v, hv_system, hv_bound⟩
  have hv_system_real :
      (A0.map (Rat.castHom ℝ)) *ᵥ (fun k ↦ (v k : ℝ)) = fun i ↦ (b0 i : ℝ) := by
    -- Coercing the rational solution from Chapter 1 gives a real solution of the same subsystem.
    ext i
    have hi : ((A0 *ᵥ v) i : ℝ) = (b0 i : ℝ) := by
      exact_mod_cast congrArg (fun w : Fin n → ℚ ↦ w i) hv_system
    simpa [Matrix.mulVec, dotProduct] using hi
  have hx_eq_v :
      x = fun k ↦ (v k : ℝ) :=
    selected_square_subsystem_solution_unique A0 b0 hA0_linear hx_system hv_system_real
  have hσ :
      rational_linear_system_encoding_size A0 b0 ≤ σ.eval (n + L) :=
    square_rational_system_encoding_bound A0 b0 L hA0 hb0
  have hbound :
      rational_vector_encoding_size v ≤ (p.comp σ).eval (n + L) := by
    -- Compose the Chapter 1 polynomial with the subsystem-size majorant.
    exact
      (le_trans hv_bound ((polynomial_eval_nat_mono p) hσ)).trans_eq
        (by simp [σ, Polynomial.eval_comp])
  exact ⟨v, hx_eq_v, hbound⟩

/-- Theorem 3.38 (2). There is a uniform polynomial bound, depending only on the dimension and the
encoding bound for the rational `H`-presentation, such that every extreme ray of the polyhedron
`P = {x ∈ ℝ^n | A x ≤ b}` admits a positive rational rescaling whose coordinate encoding size is
bounded by that value. -/
theorem rational_extreme_rays_have_polynomially_bounded_rescaled_encoding_size
    : ∃ π : Polynomial ℕ,
        ∀ {m n : ℕ}
          (A : Matrix (Fin m) (Fin n) ℚ)
          (b : Fin m → ℚ)
          (L : ℕ)
          (hA : ∀ i j, rational_encoding_size (A i j) ≤ L)
          (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
          (r : Fin n → ℝ)
          (hr : IsExtremeRayOfPolyhedron (rational_matrix_polyhedron A b) r),
          ∃ μ : ℚ, 0 < μ ∧
            ∃ r' : Fin n → ℚ,
              (fun k ↦ (r' k : ℝ)) = (μ : ℝ) • r ∧
              rational_vector_encoding_size r' ≤ π.eval (n + L) := by
  -- TODO: follow the source-faithful ray proof route from Theorem 3.35 after deriving the two
  -- missing bridges from `hr`: first that `rational_matrix_polyhedron A b` is nonempty so its
  -- recession cone rewrites to the homogeneous system `A *ᵥ r ≤ 0`, and then that this
  -- homogeneous cone is pointed so Theorem 3.35 yields the `n - 1` active independent rows.
  sorry

end Theorem338

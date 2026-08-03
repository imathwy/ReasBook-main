import Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1
import Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

open IsLocalization
open scoped Matrix

section Theorem910

variable {m n : ℕ}

/-- The encoding size of a rational number is always positive. -/
theorem rational_encoding_size_pos (q : ℚ) :
    0 < rational_encoding_size q := by
  dsimp [rational_encoding_size]
  have hleft : 0 < Nat.log2 (q.num.natAbs + 1) + 1 := Nat.succ_pos _
  have hright : 0 < Nat.log2 (q.den + 1) + 1 := Nat.succ_pos _
  exact lt_trans hleft (lt_add_of_pos_right _ hright)

/-- The bounded truncation `P' = {x ∈ P | -R ≤ x ≤ R}` of the rational polyhedron
`P = rational_matrix_polyhedron A b`. -/
def bounded_rational_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (R : ℤ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | x ∈ rational_matrix_polyhedron A b ∧
      ∀ i : Fin n, -(R : ℝ) ≤ x i ∧ x i ≤ (R : ℝ)}

/-- Membership in `bounded_rational_polyhedron A b R` means satisfying `A x ≤ b` together with
the coordinate box bounds `-R ≤ x_i ≤ R`. -/
theorem mem_bounded_rational_polyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (R : ℤ)
    (x : Fin n → ℝ) :
    x ∈ bounded_rational_polyhedron A b R ↔
      x ∈ rational_matrix_polyhedron A b ∧
        ∀ i : Fin n, -(R : ℝ) ≤ x i ∧ x i ≤ (R : ℝ) :=
  Iff.rfl

/-- An integral vector is primitive if it is nonzero and the gcd of the absolute values of its
coordinates is `1`. -/
def is_primitive_integer_vector (v : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (v i)) = 1

/-- `is_primitive_integer_vector v` means that `v` is nonzero and its coordinates are relatively
prime. -/
theorem is_primitive_integer_vector_iff
    (v : Fin n → ℤ) :
    is_primitive_integer_vector v ↔
      v ≠ 0 ∧ Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (v i)) = 1 :=
  Iff.rfl

/-- The affine hyperplane cut out by the integral equation `v^T x = rhs`, viewed through the
Chapter 3 owner `linear_hyperplane`. -/
abbrev integer_hyperplane
    (v : Fin n → ℤ)
    (rhs : ℚ) : Set (Fin n → ℝ) :=
  linear_hyperplane (Int.cast ∘ v) (rhs : ℝ)

/-- A polynomially bounded box-reduction datum for integer feasibility in rational polyhedra. -/
structure PolynomiallyBoundedBoxReduction
    (pi : Polynomial ℕ)
    (f : ℕ → ℕ → ℤ) : Prop where
  /-- The radius function takes nonnegative values. -/
  nonneg : ∀ n L : ℕ, 0 ≤ f n L
  /-- The encoding size of the radius function is polynomially bounded. -/
  encoding_bound : ∀ n L : ℕ,
    (Nat.log2 ((f n L).natAbs + 1) + 1) ≤ pi.eval (n + L)
  /-- Integer feasibility is preserved after truncating by the radius function. -/
  feasibility_iff {m n : ℕ}
      (A : Matrix (Fin m) (Fin n) ℚ)
      (b : Fin m → ℚ)
      (L : ℕ)
      (hA : ∀ i : Fin m, ∀ j : Fin n, rational_encoding_size (A i j) ≤ L)
      (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L) :
      contains_integral_point (rational_matrix_polyhedron A b) ↔
        contains_integral_point (bounded_rational_polyhedron A b (f n L))

/-- Theorem 9.10 (1). There exists an integer-valued radius function `f(n, L)` whose encoding size
is polynomially bounded in `n + L` such that, for every rational system `A x ≤ b` in `n`
variables whose coefficients have encoding size at most `L`, the rational polyhedron
`P = {x ∈ ℝ^n | A x ≤ b}` contains an integral point if and only if its truncation
`P' = {x ∈ P | -f(n, L) ≤ x ≤ f(n, L)}` contains an integral point. -/
theorem exists_polynomially_bounded_box_reduction_for_integer_feasibility :
    ∃ pi : Polynomial ℕ,
      ∃ f : ℕ → ℕ → ℤ,
        PolynomiallyBoundedBoxReduction pi f := sorry

/-- Theorem 9.10 (2). If the rational polyhedron `P = {x ∈ ℝ^n | A x ≤ b}` is not
full-dimensional, then `P` is contained in a rational hyperplane `v^T x = rhs` whose normal
vector `v ∈ ℤ^n` is primitive. For the empty polyhedron this conclusion is vacuous, so the
nonemptiness hypothesis from the source statement is omitted from the reusable API. -/
theorem non_full_dimensional_rational_polyhedron_subset_integer_hyperplane
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (h_not_full : affineSpan ℝ (rational_matrix_polyhedron A b) ≠ ⊤) :
    ∃ v : Fin n → ℤ,
      ∃ rhs : ℚ,
        is_primitive_integer_vector v ∧
          rational_matrix_polyhedron A b ⊆ integer_hyperplane v rhs := sorry

/-- Theorem 9.10 (3). If the rational polyhedron `P = {x ∈ ℝ^n | A x ≤ b}` is contained in an
integral hyperplane `v^T x = rhs` with nonintegral right-hand side `rhs`, then `P` has no
integral point. -/
theorem rational_polyhedron_has_no_integral_point_of_subset_integer_hyperplane_of_nonintegral_rhs
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (v : Fin n → ℤ)
    (rhs : ℚ)
    (h_subset : rational_matrix_polyhedron A b ⊆ integer_hyperplane v rhs)
    (h_rhs : ¬ IsInteger ℤ rhs) :
    ¬ contains_integral_point (rational_matrix_polyhedron A b) := sorry

end Theorem910

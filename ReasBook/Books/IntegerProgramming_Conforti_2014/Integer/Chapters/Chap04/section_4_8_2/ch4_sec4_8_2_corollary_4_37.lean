import Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_theorem_4_36

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: encoding-size bounds for feasible integer points of rational systems
-- * sampled owner results: Chapter 4.8.2 Theorem 4.36 and Lemma 4.35, plus Chapter 4.1
--   `rational_matrix_polyhedron`
-- * owner abstraction: the uniform polynomial-bound theorem of Theorem 4.36
-- * primitive data: a rational system `A x ≤ b`, an entrywise encoding bound `L`, and an
--   integral feasible point
-- * derived API: a uniformly polynomially bounded integral feasible witness

section Corollary437

/-- Corollary 4.37. Given `A ∈ ℚ^(m × n)` and `b ∈ ℚ^m`, let `L` be the maximum encoding size of
the coefficients of `(A, b)`. If the system `A x ≤ b` has an integral solution, then it has an
integral solution `xbar` whose encoding size is polynomially bounded by `n` and `L`. -/
theorem rational_linear_inequality_system_has_small_integral_solution :
    ∃ π : Polynomial ℕ,
      ∀ {m n : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, rational_encoding_size (A i j) ≤ L)
        (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
        (hfeas : ∃ x : Fin n → ℤ, Int.cast ∘ x ∈ rational_matrix_polyhedron A b),
        ∃ xbar : Fin n → ℤ,
          Int.cast ∘ xbar ∈ rational_matrix_polyhedron A b ∧
            integer_vector_encoding_size xbar ≤ π.eval (n + L) := sorry

end Corollary437

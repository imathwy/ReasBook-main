import Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35

-- Domain-style sampling for this refine pass:
-- * primary domain: mixed-integer feasibility and certificate-size bounds
--   for rational mixed systems
-- * sampled declarations: `mixed_integer_points`, `mem_mixed_integer_points_iff`,
--   `nonnegative_rational_mixed_integer_points`, and the downstream hull surface in Lemma 4.38
-- * owner abstraction: the source-facing feasible-set owner
--   `nonnegative_rational_mixed_integer_points A G b`
-- * primitive data: rational system data `A`, `G`, `b`
--   with an entrywise encoding bound `L`
-- * derived API: a feasible mixed-integer witness with polynomially bounded encoding size

section Theorem436

/-- Theorem 4.36. The MILP feasibility problem is in NP: for every feasible nonnegative rational
mixed-integer system whose coefficients have encoding size at most `L`, there is a certificate
point with integral `x`-block and rational `y`-block whose total encoding size is uniformly
bounded by a polynomial in `n + p + L`. -/
theorem mixed_integer_linear_feasibility_has_polynomially_bounded_certificate :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, rational_encoding_size (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, rational_encoding_size (G i j) ≤ L)
        (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
        (hfeasible : Set.Nonempty (nonnegative_rational_mixed_integer_points A G b)),
        ∃ x : Fin n → ℤ,
          ∃ y : Fin p → ℚ,
            ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) ∈
                nonnegative_rational_mixed_integer_points A G b ∧
              integer_vector_encoding_size x + rational_vector_encoding_size y ≤
                π.eval (n + p + L) := sorry

end Theorem436

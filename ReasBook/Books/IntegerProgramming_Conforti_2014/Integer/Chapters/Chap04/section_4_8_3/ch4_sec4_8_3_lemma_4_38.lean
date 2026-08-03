import Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import Integer.Chapters.Chap04.section_4_8_2.ch4_sec4_8_2_lemma_4_35

section Lemma438

variable {m n p : ℕ}

/-- Lemma 4.38. Given `A ∈ ℚ^(m × n)`, `G ∈ ℚ^(m × p)`, and `b ∈ ℚ^m`, let
`S := {(x, y) ∈ ℤ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}`. If the encoding size of every
coefficient of `(A, G, b)` is at most `L`, then every facet `F` of `conv(S)` is defined on
`conv(S)` by a rational inequality `c · x + d · y ≤ δ` whose coefficient vector and right-hand
side have encoding size uniformly polynomially bounded by `n + p` and `L`. -/
theorem mixed_integer_hull_facets_have_polynomially_bounded_rational_defining_inequalities :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, rational_encoding_size (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, rational_encoding_size (G i j) ≤ L)
        (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
        (F : Set (MixedRealPoint n p))
        (hF : IsFacetOf (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)) F),
        ∃ c : Fin n → ℚ,
          ∃ d : Fin p → ℚ,
            ∃ δ : ℚ,
              (c ≠ 0 ∨ d ≠ 0) ∧
                (∀ xy : MixedRealPoint n p,
                  xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) →
                    mixed_linear_objective
                        (fun i ↦ (c i : ℝ))
                        (fun j ↦ (d j : ℝ))
                        xy ≤
                      (δ : ℝ)) ∧
                F =
                  {xy | xy ∈ convexHull ℝ (nonnegative_rational_mixed_integer_points A G b) ∧
                    mixed_linear_objective
                        (fun i ↦ (c i : ℝ))
                        (fun j ↦ (d j : ℝ))
                        xy =
                      (δ : ℝ)} ∧
                rational_vector_encoding_size c + rational_vector_encoding_size d +
                  rational_encoding_size δ ≤ π.eval (n + p + L) := sorry

end Lemma438

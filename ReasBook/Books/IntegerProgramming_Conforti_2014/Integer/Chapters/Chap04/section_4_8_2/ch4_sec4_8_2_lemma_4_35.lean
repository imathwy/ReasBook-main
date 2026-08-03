import Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1
import Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_3

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tools such as
-- `lean_leansearch`, so the statement below follows the local Chapter 1 encoding conventions and
-- the Chapter 4 product-coordinate model for mixed-integer feasible sets.

section Lemma435

variable {m n p : ℕ}

/-- The nonnegative mixed polyhedron
`{(x, y) ∈ ℝ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}` attached to rational data `A`, `G`, and
`b`, expressed as a source-facing nonnegativity specialization of the Chapter 4.1 mixed-polyhedron
owner. -/
def nonnegative_rational_mixed_polyhedron
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Set (MixedRealPoint n p) :=
  {xy | xy ∈ rational_mixed_polyhedron A G b ∧ 0 ≤ xy.1 ∧ 0 ≤ xy.2}

/-- The mixed-integer feasible set
`{(x, y) ∈ ℤ^n × ℝ^p | A x + G y ≤ b, x ≥ 0, y ≥ 0}` inside `ℝ^n × ℝ^p`, obtained from the
canonical mixed-integer-points owner applied to the nonnegative mixed polyhedron. -/
def nonnegative_rational_mixed_integer_points
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Set (MixedRealPoint n p) :=
  mixed_integer_points (nonnegative_rational_mixed_polyhedron A G b)

/-- Lemma 4.35. There is a uniform polynomial bound such that, for every rational mixed system
`A x + G y ≤ b` with nonnegativity constraints and entrywise encoding bound `L`, every vertex of
the mixed-integer hull `conv(S)` admits an integral `x`-block and a rational `y`-block whose
total encoding size is bounded by that polynomial evaluated at `n + p + L`. -/
theorem mixed_integer_hull_extreme_points_have_polynomially_bounded_encoding_size :
    ∃ π : Polynomial ℕ,
      ∀ {m n p : ℕ}
        (A : Matrix (Fin m) (Fin n) ℚ)
        (G : Matrix (Fin m) (Fin p) ℚ)
        (b : Fin m → ℚ)
        (L : ℕ)
        (hA : ∀ i : Fin m, ∀ j : Fin n, rational_encoding_size (A i j) ≤ L)
        (hG : ∀ i : Fin m, ∀ j : Fin p, rational_encoding_size (G i j) ≤ L)
        (hb : ∀ i : Fin m, rational_encoding_size (b i) ≤ L)
        (xy : MixedRealPoint n p)
        (hxy :
          xy ∈ (convexHull ℝ (nonnegative_rational_mixed_integer_points A G b)).extremePoints ℝ),
        ∃ x : Fin n → ℤ,
          ∃ y : Fin p → ℚ,
            xy = ((fun i ↦ (x i : ℝ)), fun j ↦ (y j : ℝ)) ∧
              integer_vector_encoding_size x + rational_vector_encoding_size y ≤
                π.eval (n + p + L) := sorry

end Lemma435

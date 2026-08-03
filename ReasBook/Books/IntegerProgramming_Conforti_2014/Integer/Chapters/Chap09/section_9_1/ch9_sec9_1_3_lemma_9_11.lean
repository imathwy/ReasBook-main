import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_3_theorem_9_10

open scoped Matrix

-- Domain style sampling:
-- * primary domain: integral points of rational polyhedra cut out by integer hyperplanes
-- * source-facing layer: the coprime-row elimination lemma matching Lemma 9.11
-- * core/canonical owners reused here: `rational_matrix_polyhedron`,
--   `integer_hyperplane`, and `is_primitive_integer_vector`
-- * primitive data: `A`, `b`, `α`, `β`, and the coprime-row hypothesis
-- * derived API: the reduced system witness `(D, b')` and the induced integral-point equivalence

section Lemma911

variable {m n : ℕ}

/-- The source hypothesis that the entries of `α` are relatively prime upgrades the row to the
canonical Chapter 9 owner `is_primitive_integer_vector α`. -/
theorem is_primitive_integer_vector_of_span_eq_top
    (α : Fin n → ℤ)
    (hcoprime : (Ideal.span (Set.range α) : Ideal ℤ) = ⊤) :
    is_primitive_integer_vector α := by
  sorry

/-- Lemma 9.11 in the chapter's canonical primitive-row formulation. -/
theorem exists_hyperplane_elimination_system_of_primitive_integer_row
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (α : Fin n → ℤ)
    (β : ℤ)
    (hprimitive : is_primitive_integer_vector α) :
    ∃ D : Matrix (Fin n) (Fin (n - 1)) ℤ, ∃ b' : Fin m → ℚ,
      contains_integral_point
          (rational_matrix_polyhedron A b ∩ integer_hyperplane α (β : ℚ)) ↔
        contains_integral_point
          (rational_matrix_polyhedron (A * D.map (Int.castRingHom ℚ)) b') := by
  sorry

/-- Lemma 9.11. Let `A ∈ ℚ^(m × n)`, `b ∈ ℚ^m`, `α ∈ ℤ^n`, and `β ∈ ℤ`, and assume that the
entries of `α` are relatively prime. Then there exist an integer matrix
`D ∈ ℤ^(n × (n - 1))` and a rational vector `b' ∈ ℚ^m` such that the system
`A x ≤ b, α x = β` has an integral solution if and only if the reduced system
`A D y ≤ b'` has an integral solution. This source-facing form is a thin bridge to the
canonical owner `is_primitive_integer_vector`. -/
theorem exists_hyperplane_elimination_system_of_coprime_integer_row
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ)
    (α : Fin n → ℤ)
    (β : ℤ)
    (hcoprime : (Ideal.span (Set.range α) : Ideal ℤ) = ⊤) :
    ∃ D : Matrix (Fin n) (Fin (n - 1)) ℤ, ∃ b' : Fin m → ℚ,
      contains_integral_point
          (rational_matrix_polyhedron A b ∩ integer_hyperplane α (β : ℚ)) ↔
        contains_integral_point
          (rational_matrix_polyhedron (A * D.map (Int.castRingHom ℚ)) b') := by
  simpa using
    exists_hyperplane_elimination_system_of_primitive_integer_row
      A b α β (is_primitive_integer_vector_of_span_eq_top α hcoprime)

end Lemma911

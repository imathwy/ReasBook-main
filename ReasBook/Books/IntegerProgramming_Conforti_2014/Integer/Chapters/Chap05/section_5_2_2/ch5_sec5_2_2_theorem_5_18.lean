import Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

section Theorem518

variable {n : ℕ}

/-- Theorem 5.18. Let `P` be a rational polyhedron. Then there exists a positive integer `t`
such that `P^(t) = P_I`, represented here by
`(pure_integer_chvatal_closure^[t]) P = pure_integer_hull P`. -/
theorem exists_positive_iterate_chvatalClosure_eq_pure_integer_hull
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ t : ℕ, 0 < t ∧ (pure_integer_chvatal_closure^[t]) P = pure_integer_hull P := sorry

/-- Companion canonical form of Theorem 5.18. A rational polyhedron has a minimal iterate index
at which the pure-integer Chvátal closure reaches `P_I`; the Chapter 5 owner for that minimal
attainment is `is_iterate_rank_of_polyhedron`. -/
theorem exists_chvatal_rank_of_rational_polyhedron
    (P : Set (Fin n → ℝ))
    (hP_rational : is_rational_polyhedron P) :
    ∃ t : ℕ, is_iterate_rank_of_polyhedron pure_integer_chvatal_closure P t := sorry

end Theorem518

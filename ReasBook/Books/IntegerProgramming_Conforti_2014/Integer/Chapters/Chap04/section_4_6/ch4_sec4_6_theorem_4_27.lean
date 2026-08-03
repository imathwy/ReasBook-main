import Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: totally dual integral descriptions of rational polyhedra
-- * sampled owner declarations: Chapter 4.1 `rational_matrix_polyhedron` and `is_integral`,
--   Chapter 4.6 `totally_dual_integral`, and Theorem 4.26
-- * owner abstraction: the Chapter 4.6 owner `totally_dual_integral A b` on the Chapter 4.1
--   rational-system owner `rational_matrix_polyhedron A b`
-- * source/core/bridge triage: Theorem 4.27 is source-facing existential content stated directly
--   in terms of the Chapter 4 owners, so no extra wrapper around "integral TDI presentations" is
--   introduced
-- * primitive data: a finite row index `m : ℕ`, an integral matrix presentation, and, in part
--   `(2)`, an integral right-hand side witness
-- * derived API: equality with the target polyhedron and the TDI property of that presentation

section Theorem427

variable {n : ℕ} (P : Set (Fin n → ℝ)) (hP : is_rational_polyhedron P)

/-- Theorem 4.27 (1). Every rational polyhedron admits a totally dual integral description
`A x ≤ b` in which the coefficient matrix `A` is integral. -/
theorem rational_polyhedron_has_tdi_system_with_integral_matrix
    :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℚ,
      P = rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) b ∧
        totally_dual_integral (A.map (Int.castRingHom ℚ)) b := sorry

/-- Theorem 4.27 (2). If a rational polyhedron is integral, then it admits a totally dual
integral description `A x ≤ b` in which both `A` and `b` are integral. -/
theorem integral_rational_polyhedron_has_tdi_system_with_integral_rhs
    (hPi : is_integral P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℤ, ∃ b : Fin m → ℤ,
      P = rational_matrix_polyhedron (A.map (Int.castRingHom ℚ)) (Int.cast ∘ b) ∧
        totally_dual_integral (A.map (Int.castRingHom ℚ)) (Int.cast ∘ b) := sorry

end Theorem427

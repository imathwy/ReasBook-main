import Integer.Chapters.Chap04.section_4_6.ch4_sec4_6_definition_4_6_extra_1

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: totally dual integral descriptions of rational polyhedra
-- * sampled owner declarations: Chapter 4.1 `rational_matrix_polyhedron`, `is_integral`, and
--   `ℤ^m`, plus Chapter 4.6 `totally_dual_integral`
-- * owner abstraction: the Chapter 4.6 owner `totally_dual_integral A b` on the Chapter 4.1
--   rational-system owner `rational_matrix_polyhedron A b`
-- * source/core/bridge triage: Theorem 4.26 is source-facing and should use the primitive
--   integral right-hand side data `b : Fin m → ℤ`; the cast `Int.cast ∘ b` is the canonical
--   bridge into the Chapter 4.6 owner, while membership in `ℤ^m` is derived API from
--   `mem_integerVectors_iff`
-- * primitive data: a rational matrix presentation and an integral right-hand side
-- * derived API: the induced rational polyhedron and its integrality

section Theorem426

variable {m n : ℕ}

/-- Theorem 4.26. Let `A x ≤ b` be a totally dual integral system and let `b` be an integral
vector. Then `P := {x : A x ≤ b}` is an integral polyhedron. -/
theorem totally_dual_integral_rational_matrix_polyhedron_is_integral
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℤ)
    (hTDI : totally_dual_integral A (Int.cast ∘ b)) :
    is_integral (rational_matrix_polyhedron A (Int.cast ∘ b)) := sorry

end Theorem426

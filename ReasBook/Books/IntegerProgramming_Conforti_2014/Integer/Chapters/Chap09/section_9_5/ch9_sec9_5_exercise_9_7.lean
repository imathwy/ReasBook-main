import Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectionalWidthNotation

section Exercise97

variable {n : ℕ}

/-- Exercise 9.7. For a convex body `K ⊆ ℝ^n` in positive dimension, the infimum defining
the widths `w_d(K)` over nonzero integral directions is attained by some nonzero integral
direction. -/
theorem exists_nonzero_integral_direction_realizing_lattice_width
    (hn : 0 < n)
    (K : ConvexBody (Fin n → ℝ)) :
    ∃ d : {d : Fin n → ℤ // d ≠ 0},
      lattice_width K = w_{d}((K : Set (Fin n → ℝ))) := sorry

/-- Companion form of Exercise 9.7: the minimizing direction can be exposed as an ordinary
integral vector together with its nonzeroness proof. -/
theorem exists_integral_direction_ne_zero_realizing_lattice_width
    (hn : 0 < n)
    (K : ConvexBody (Fin n → ℝ)) :
    ∃ d : Fin n → ℤ,
      d ≠ 0 ∧ lattice_width K = w_{d}((K : Set (Fin n → ℝ))) := by
  obtain ⟨d, hd⟩ := exists_nonzero_integral_direction_realizing_lattice_width hn K
  exact ⟨d, d.2, hd⟩

end Exercise97

import Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise717

variable {n : ℕ}

/-- Exercise 7.17. Every flow cover inequality `(7.14)` for the single-node flow set can be
realized as a Gomory mixed integer inequality after encoding `(x,y)` as a mixed-integer vector in
which the `x`-coordinates are the integer variables. -/
theorem exercise_7_17_flow_cover_inequality_is_gomory_mixed_integer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j) (hb_nonneg : 0 ≤ b)
    (hC : IsFlowCover a b C) :
    ∃ α : Fin (n + n) → ℝ, ∃ β : ℝ, ∃ hβ : 0 < Int.fract β,
      ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C p ≤ b ↔
          Fin.append p.1 p.2 ∈
            gomory_mixed_integer_inequality (Finset.univ.image (Fin.castAdd n)) α β hβ := sorry

end Exercise717

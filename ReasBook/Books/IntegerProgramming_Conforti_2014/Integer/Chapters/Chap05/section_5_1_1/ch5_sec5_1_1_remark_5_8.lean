import Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_corollary_5_7
import Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_theorem_5_5

open scoped Matrix SplitHullNotation
open scoped SplitBasisNotation

section Remark58

variable {m n : ℕ}

/-- Remark 5.8. Let `(π, π₀)` be a split. For a row set `B`, assume `B ∈ 𝓑[A, π]` and that `ū` is
the supported row multiplier for `B`, so uniqueness is supplied by `𝓑[A, π]`. If
`P_B^(π, π₀) ≠ P_B`, then `P_B^(π, π₀)` is exactly `P_B` intersected with the split-cut halfspace
defined by `ū`. -/
theorem split_P_B_eq_inter_split_cut
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (ubar : Fin m → ℝ)
    (hubar : IsSupportedSplitRowMultiplier A π B ubar)
    (hB : B ∈ 𝓑[A, π])
    (hproper : (P_B A b B)^(π, π0) ≠ P_B A b B) :
    (P_B A b B)^(π, π0) =
      P_B A b B ∩
        (split_cut_value A b ubar π0) ⁻¹' Set.Ici (1 : ℝ) := sorry

/-- A point lies in `P_B^(π, π₀)` exactly when it lies in `P_B` and satisfies the split-cut
inequality defined by the supported row multiplier `ū`. -/
theorem mem_split_P_B_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (π : Fin n → ℤ)
    (π0 : ℤ)
    (ubar : Fin m → ℝ)
    (hubar : IsSupportedSplitRowMultiplier A π B ubar)
    (hB : B ∈ 𝓑[A, π])
    (hproper : (P_B A b B)^(π, π0) ≠ P_B A b B)
    (x : Fin n → ℝ) :
    x ∈ (P_B A b B)^(π, π0) ↔
      x ∈ P_B A b B ∧ 1 ≤ split_cut_value A b ubar π0 x := by
  rw [split_P_B_eq_inter_split_cut A b B π π0 ubar hubar hB hproper]
  simp

end Remark58

import Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import Integer.Chapters.Chap05.section_5_2_4.ch5_sec5_2_4_definition_5_2_4_extra_1

open scoped BigOperators

/-
Domain-style sampling for this refine pass:
* primary domain: one-row Gomory mixed-integer inequalities and their pure-integer specialization
* core/canonical owner: `gomory_mixed_integer_inequality` from `section_5_1_4`
* comparison owner: `gomory_fractional_cut` from `section_5_2_4`
* bridge/view layer here: the tableau-row support presentation via `Finset.piecewise`
-/

noncomputable section Remark520

variable {n : ℕ}

/-- The tableau-row coefficient vector for the pure-integer case `C = ∅`, viewed in `ℝ`. -/
def pureIntegerTableauCoefficients
    (tableauCoeff : Fin n → ℚ) : Fin n → ℝ :=
  fun j ↦ (tableauCoeff j : ℝ)

/-- The pure-integer specialization of the mixed Gomory coefficient from Remark 5.20. -/
def pureIntegerGomoryMixedCutCoefficient
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (j : Fin n) : ℝ :=
  gomory_mixed_integer_inequality_coefficient Finset.univ
    (pureIntegerTableauCoefficients tableauCoeff)
    (tableauRhs : ℝ)
    (by exact_mod_cast h_rhs)
    j

/-- The pure-integer specialization of `gomory_mixed_integer_inequality` from Remark 5.20. -/
def pureIntegerGomoryMixedCut
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_inequality Finset.univ
    (pureIntegerTableauCoefficients tableauCoeff)
    (tableauRhs : ℝ)
    (by exact_mod_cast h_rhs)

/-- Membership in the pure-integer specialization of `gomory_mixed_integer_inequality` is
exactly the normalized pure-integer cut inequality from Remark 5.20. -/
@[simp] theorem mem_pureIntegerGomoryMixedCut_iff
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (x : Fin n → ℝ) :
    x ∈ pureIntegerGomoryMixedCut tableauCoeff tableauRhs h_rhs ↔
      1 ≤
        ∑ j : Fin n,
          pureIntegerGomoryMixedCutCoefficient tableauCoeff tableauRhs h_rhs j * x j := by
  rw [pureIntegerGomoryMixedCut, mem_gomory_mixed_integer_inequality_iff]
  rfl

/-- The tableau-row coefficient vector restricted to the support `N`, viewed in `ℝ`. -/
def tableauSupportCoefficients
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ) : Fin n → ℝ :=
  N.piecewise (fun j ↦ (tableauCoeff j : ℝ)) 0

/-- The tableau-support specialization of the mixed Gomory coefficient from Remark 5.20. -/
def tableauSupportGomoryMixedIntegerCoefficient
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (j : Fin n) : ℝ :=
  gomory_mixed_integer_inequality_coefficient N
    (tableauSupportCoefficients N tableauCoeff)
    (tableauRhs : ℝ)
    (by exact_mod_cast h_rhs)
    j

/-- The mixed Gomory inequality attached to a tableau row after restricting its coefficients to the
support `N`. -/
def tableauSupportGomoryMixedIntegerInequality
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_inequality N
    (tableauSupportCoefficients N tableauCoeff)
    (tableauRhs : ℝ)
    (by exact_mod_cast h_rhs)

/-- The tableau-support specialization used in Remark 5.20 has zero mixed-cut coefficient off the
support `N`. -/
@[simp] theorem gomory_mixed_integer_inequality_coefficient_tableau_support_eq_zero_of_not_mem
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (j : Fin n)
    (hj : j ∉ N) :
    tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j = 0 := by
  rw [tableauSupportGomoryMixedIntegerCoefficient,
    gomory_mixed_integer_inequality_coefficient_eq N (tableauSupportCoefficients N tableauCoeff)
      (tableauRhs : ℝ) (by exact_mod_cast h_rhs) j, if_neg hj]
  simp [tableauSupportCoefficients, Finset.piecewise, hj]

/-- Membership in the tableau-row specialization of `gomory_mixed_integer_inequality` is exactly
the normalized pure-integer Gomory mixed cut inequality supported on `N`. -/
@[simp]
theorem mem_gomory_mixed_integer_inequality_tableau_support_iff
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (x : Fin n → ℝ) :
    x ∈ tableauSupportGomoryMixedIntegerInequality N tableauCoeff tableauRhs h_rhs ↔
      1 ≤
        Finset.sum N fun j ↦
          tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j * x j := by
  rw [tableauSupportGomoryMixedIntegerInequality, mem_gomory_mixed_integer_inequality_iff]
  change 1 ≤
      ∑ j : Fin n,
          tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j * x j ↔
    1 ≤ Finset.sum N fun j ↦
      tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j * x j
  have hsum :
      ∑ j : Fin n,
          tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j * x j =
        Finset.sum N fun j ↦
          tableauSupportGomoryMixedIntegerCoefficient N tableauCoeff tableauRhs h_rhs j * x j := by
    classical
    symm
    refine Finset.sum_subset (Finset.subset_univ N) ?_
    intro j _ hjN
    simp [gomory_mixed_integer_inequality_coefficient_tableau_support_eq_zero_of_not_mem, hjN]
  rw [hsum]

/-- On the branch `f₀ < f_j` from Remark 5.20, the pure-integer specialization of
`gomory_mixed_integer_inequality_coefficient` is exactly `(1 - f_j) / (1 - f₀)`. -/
theorem pure_integer_gomory_mixed_cut_coefficient_eq_of_rhs_lt
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (j : Fin n)
    (hj : Int.fract tableauRhs < Int.fract (tableauCoeff j)) :
    pureIntegerGomoryMixedCutCoefficient tableauCoeff tableauRhs h_rhs j =
      (1 - Int.fract (tableauCoeff j) : ℝ) / (1 - Int.fract tableauRhs : ℝ) := by
  rw [pureIntegerGomoryMixedCutCoefficient,
    gomory_mixed_integer_inequality_coefficient_eq Finset.univ
      (pureIntegerTableauCoefficients tableauCoeff) (tableauRhs : ℝ) (by exact_mod_cast h_rhs) j,
    if_pos (by simp)]
  have hj_cast : Int.fract (tableauRhs : ℝ) < Int.fract (tableauCoeff j : ℝ) := by
    exact_mod_cast hj
  have hj' :
      ¬ Int.fract (pureIntegerTableauCoefficients tableauCoeff j) ≤ Int.fract (tableauRhs : ℝ) := by
    simpa [pureIntegerTableauCoefficients] using not_le_of_gt hj_cast
  rw [if_neg hj']
  simp [pureIntegerTableauCoefficients]

/-- On indices with `f_j > f₀`, the pure-integer specialization of
`gomory_mixed_integer_inequality_coefficient` uses the smaller coefficient
`(1 - f_j) / (1 - f₀)` instead of the normalized fractional-cut coefficient `f_j / f₀`. -/
theorem pure_integer_gomory_mixed_cut_coefficient_lt_normalized_fractional_coefficient
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (j : Fin n)
    (h_rhs : 0 < Int.fract tableauRhs)
    (hj : Int.fract tableauRhs < Int.fract (tableauCoeff j)) :
    pureIntegerGomoryMixedCutCoefficient tableauCoeff tableauRhs h_rhs j <
      (Int.fract (tableauCoeff j) : ℝ) / (Int.fract tableauRhs : ℝ) := sorry

/-- Remark 5.20. For pure integer sets (`C = ∅`), the Gomory mixed integer cut `(5.31)`
dominates the Gomory fractional cut `(5.25)`: every point whose coordinates on the tableau
support `N` are nonnegative and which satisfies the pure-integer specialization of
`gomory_mixed_integer_inequality` also satisfies the Gomory fractional cut. -/
theorem pure_integer_gomory_mixed_cut_dominates_fractional_cut
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (x : Fin n → ℝ)
    (h_rhs : 0 < Int.fract tableauRhs)
    (hx_nonneg : ∀ j ∈ N, 0 ≤ x j)
    (hx_mixed :
      x ∈ tableauSupportGomoryMixedIntegerInequality N tableauCoeff tableauRhs h_rhs) :
    x ∈ gomory_fractional_cut N tableauCoeff tableauRhs := sorry

end Remark520

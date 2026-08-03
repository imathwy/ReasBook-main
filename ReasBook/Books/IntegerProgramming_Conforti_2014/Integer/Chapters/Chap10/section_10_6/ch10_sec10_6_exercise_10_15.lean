import Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_14
import Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped LovaszSchrijverNotation

-- This exercise reuses the Chapter 7 graph-support owners together with the source-facing
-- `fractional_stable_set_cone G` and `lovasz_schrijver_n_frac_relaxation G` owners from
-- Exercise 10.14. The source-facing `Option V` witness surface is kept here for arbitrary finite
-- vertex types, and the `Fin n` specialization is bridged below to the canonical Section 10.3
-- owner `N₊(FRAC(G))`.

section Exercise_10_15

variable {V : Type}

noncomputable local instance : DecidableEq V := Classical.decEq V

section SourceOwner

variable [Fintype V]
variable (G : SimpleGraph V)

/-- The positive-semidefinite Lovasz-Schrijver relaxation `N₊(FRAC(G))`, stated directly on the
ambient vertex type `V` through an `Option V`-indexed lifted matrix witness whose columns and
residual columns lie in `fractional_stable_set_cone G`. -/
def lovasz_schrijver_nplus_frac_relaxation : Set (V → ℝ) :=
  {x | ∃ Y : Matrix (Option V) (Option V) ℝ,
      Y.PosSemidef ∧
      Y none none = 1 ∧
      (∀ i : Option V, Y i none = Y i i) ∧
      (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      (∀ v : V,
        (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      ∀ v : V, x v = Y (some v) none}

end SourceOwner

variable (G : SimpleGraph V)

/-- Membership in `lovasz_schrijver_nplus_frac_relaxation G` is exactly the existence of the
standard positive-semidefinite lifted witness for `N₊(FRAC(G))`. -/
theorem mem_lovasz_schrijver_nplus_frac_relaxation_iff
    {x : V → ℝ} :
    x ∈ lovasz_schrijver_nplus_frac_relaxation G ↔
      ∃ Y : Matrix (Option V) (Option V) ℝ,
        Y.PosSemidef ∧
        Y none none = 1 ∧
        (∀ i : Option V, Y i none = Y i i) ∧
        (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        (∀ v : V,
          (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        ∀ v : V, x v = Y (some v) none :=
  Iff.rfl

/-- For graphs already presented on `Fin n`, the source-facing `Option`-indexed definition of
`N₊(FRAC(G))` agrees with the canonical Section 10.3 Lovász-Schrijver owner. -/
theorem lovasz_schrijver_nplus_frac_relaxation_eq_lovasz_schrijver_N_plus
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    lovasz_schrijver_nplus_frac_relaxation G = N₊(FRAC(G)) := by
  sorry

/-- For graphs on `Fin n`, membership in the local source-facing `Option`-indexed owner is exactly
membership in the canonical Section 10.3 relaxation `N₊(FRAC(G))`. -/
theorem mem_lovasz_schrijver_nplus_frac_relaxation_iff_mem_lovasz_schrijver_N_plus
    {n : ℕ} (G : SimpleGraph (Fin n)) {x : Fin n → ℝ} :
    x ∈ lovasz_schrijver_nplus_frac_relaxation G ↔ x ∈ N₊(FRAC(G)) := by
  rw [lovasz_schrijver_nplus_frac_relaxation_eq_lovasz_schrijver_N_plus G]

/-- The positive-semidefinite relaxation `N₊(FRAC(G))` is contained in the corresponding linear
Lovasz-Schrijver relaxation `N(FRAC(G))`. -/
theorem lovasz_schrijver_nplus_frac_relaxation_subset_n_frac_relaxation :
    lovasz_schrijver_nplus_frac_relaxation G ⊆ lovasz_schrijver_n_frac_relaxation G := by
  intro x hx
  rcases hx with ⟨Y, hYpsd, hY00, hdiag, hcols, hres, hxY⟩
  exact ⟨Y, by simpa using hYpsd.isHermitian, hY00, hdiag, hcols, hres, hxY⟩

/-- Exercise 10.15. For every odd antihole support `H` contained in `G`, the odd antihole
inequality on `H.vertexFinset` is valid for `N₊(FRAC(G))`. -/
theorem exercise_10_15_odd_antihole_inequality_valid_on_nplus_frac_relaxation
    [Fintype V]
    (H : AntiholeSupport V)
    (hH : H.IsContainedIn G)
    (hodd : Odd H.length) :
    is_valid_inequality
      (lovasz_schrijver_nplus_frac_relaxation G)
      (stableSetIndicator H.vertexFinset)
      2 := sorry

end Exercise_10_15

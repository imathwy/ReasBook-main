module

public import Topology_Munkres_2000.Book.Theorem_4_1

public section

/-- Helper for Exercise 4.4: removing the absent upper endpoint shrinks a positive-integer
interval by one. -/
lemma subset_Icc_of_succ_not_mem (n : ℕ+) (s : Set ℕ+)
    (hsub : s ⊆ Set.Icc 1 (n + 1)) (htop : n + 1 ∉ s) : s ⊆ Set.Icc 1 n := by
  -- Preserve the lower bound and turn exclusion of the endpoint into a strict upper bound.
  intro x hx
  have hxBounds := hsub hx
  have hxNe : x ≠ n + 1 := by
    intro hEq
    exact htop (hEq ▸ hx)
  have hxLt : x < n + 1 := lt_of_le_of_ne hxBounds.2 hxNe
  exact ⟨hxBounds.1, PNat.lt_add_one_iff.mp hxLt⟩

/-- Exercise 4.4 (1): Every nonempty subset of the positive-integer interval from `1` to `n`
has a greatest element. -/
theorem positiveInterval_hasGreatest (n : ℕ+) (s : Set ℕ+) (hs : s.Nonempty)
    (hsub : s ⊆ Set.Icc 1 n) : ∃ m, IsGreatest s m := by
  -- Induct on the positive upper endpoint, splitting on whether the new endpoint occurs.
  induction n using PNat.recOn with
  | one =>
      obtain ⟨x, hx⟩ := hs
      refine ⟨x, hx, ?_⟩
      intro y hy
      exact (hsub hy).2.trans (hsub hx).1
  | succ n ih =>
      classical
      by_cases htop : n + 1 ∈ s
      · refine ⟨n + 1, htop, ?_⟩
        intro x hx
        exact (hsub hx).2
      · exact ih (subset_Icc_of_succ_not_mem n s hsub htop)

/-- Exercise 4.4 (2), pointwise form: No positive integer is greatest among all positive
integers. -/
theorem positiveNaturals_not_isGreatest (m : ℕ+) :
    ¬ IsGreatest (Set.univ : Set ℕ+) m := by
  -- The successor belongs to the universal set but is strictly larger than the alleged greatest.
  intro hm
  have hUpper : m + 1 ≤ m := hm.2 (Set.mem_univ (m + 1))
  exact (not_lt_of_ge hUpper) (PNat.lt_succ_self m)

/-- Exercise 4.4 (2): The set of all positive integers has no greatest element. -/
theorem positiveNaturals_noGreatest : ¬ ∃ m, IsGreatest (Set.univ : Set ℕ+) m := by
  simpa only [not_exists] using positiveNaturals_not_isGreatest

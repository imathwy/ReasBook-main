module

public import Topology_Munkres_2000.Book.Theorem_7_2.Enumeration

public section

/-- Theorem 7.2. For an infinite set `C` of positive natural numbers, there is a
unique function that selects at each index the least element of `C` not selected
at an earlier index. -/
theorem existsUnique_leastUnused (C : Set ℕ+) (hC : C.Infinite) :
    ∃! h : ℕ+ → C, ∀ i : ℕ+, IsLeast (Set.univ \ h '' Set.Iio i) (h i) := by
  -- Choose the canonical least-unused enumeration and reuse its specification.
  refine ⟨C.leastUnused hC, C.leastUnused_isLeast hC, ?_⟩
  -- Any other enumeration with the same least-unused property is canonical.
  intro h hh
  exact C.leastUnused_unique hC h hh

module

public import Topology_Munkres_2000.Book.Theorem_7_2.Enumeration
public import Topology_Munkres_2000.Book.Theorem_8_1.LeastUnused
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Finite.Basic

public section

/-- Theorem 8.1. For an infinite set `C` of positive natural numbers, there is a
unique function that selects at each index the least element of `C` not selected
at an earlier index. -/
theorem existsUnique_recursiveLeastUnused (C : Set ℕ+) (hC : C.Infinite) :
    ∃! h : ℕ+ → C, h.IsLeastUnused := by
  -- Choose the canonical increasing enumeration and package its pointwise specification.
  refine ⟨C.leastUnused hC, Function.IsLeastUnused.of_forall (C.leastUnused_isLeast hC), ?_⟩
  -- The least-unused specification uniquely identifies the canonical enumeration.
  intro h hh
  exact C.leastUnused_unique hC h fun i ↦ hh.at i

module

import Topology_Munkres_2000.Book.Theorem_7_7
public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.PNat.Basic

public section

open Equiv

/- Example 7.5 (1): The type of infinite binary sequences is uncountable. -/
#check binarySequences_uncountable

/-- Example 7.5 (2): The powerset of the positive integers is uncountable. -/
instance positiveIntegerPowerSet_uncountable : Uncountable (Set ℕ+) := by
  constructor
  intro h
  obtain ⟨f, hf⟩ := h.exists_injective_nat'
  have hpnat : Function.Injective pnatEquivNat.symm := pnatEquivNat.symm.injective
  exact Function.cantor_injective (pnatEquivNat.symm ∘ f)
    (hpnat.comp hf)

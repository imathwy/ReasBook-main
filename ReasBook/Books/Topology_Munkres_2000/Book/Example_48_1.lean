module

public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Irrational
public import Mathlib.Topology.Instances.Real.Lemmas
public section

open Set

/-- Example 48.1 (1): The rational numbers have empty interior as a subset of `ℝ`. -/
theorem interior_ratCastRange_eq_empty :
    interior (range (fun q : ℚ ↦ (q : ℝ))) = ∅ := by
  -- The complement of the rational range is the dense set of irrational reals.
  rw [interior_eq_empty_iff_dense_compl]
  have rationalRangeCompl :
      (range (fun q : ℚ ↦ (q : ℝ)))ᶜ = {x : ℝ | Irrational x} := by
    ext x
    simp only [Irrational, mem_compl_iff, mem_range, mem_setOf_eq]
  rw [rationalRangeCompl]
  exact dense_irrational

/-- Example 48.1 (2): The interval `[0, 1]` has nonempty interior in `ℝ`. -/
theorem interior_Icc_zero_one_nonempty :
    (interior (Icc (0 : ℝ) 1)).Nonempty := by
  -- Rewrite the interior as an open interval and use its midpoint.
  rw [interior_Icc]
  refine ⟨1 / 2, ?_⟩
  norm_num

/-- Example 48.1 (3): The set `[0, 1] × {0}` has empty interior in `ℝ × ℝ`. -/
theorem interior_Icc_zero_one_prod_singleton_eq_empty :
    interior (Icc (0 : ℝ) 1 ×ˢ ({0} : Set ℝ)) = ∅ := by
  -- The singleton factor has empty interior, forcing the product interior to vanish.
  rw [interior_prod_eq, interior_singleton]
  simp only [prod_empty]

/-- Example 48.1 (4): The set `ℚ × ℝ` has empty interior in `ℝ × ℝ`. -/
theorem interior_ratCastRange_prod_univ_eq_empty :
    interior (range (fun q : ℚ ↦ (q : ℝ)) ×ˢ (univ : Set ℝ)) = ∅ := by
  -- Compute the product interior factorwise and reuse the rational-range result.
  rw [interior_prod_eq, interior_ratCastRange_eq_empty]
  simp only [empty_prod]

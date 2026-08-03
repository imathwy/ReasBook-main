module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine

public section

namespace SorgenfreyLine

/-- Helper for Example 18.3: the carrier preimage of a nonempty half-open real interval
is open in the Sorgenfrey line. -/
private lemma isOpen_preimage_Ico_toReal (a b : ℝ) (hab : a < b) :
    IsOpen (toReal ⁻¹' Set.Ico a b) := by
  -- The preimage is the same carrier set, hence is itself a lower-limit basis element.
  apply isTopologicalBasis_lowerLimitBasis.isOpen
  exact ⟨a, b, hab, rfl⟩

/-- Example 18.3 (1). The carrier identity from the usual real line to the
Sorgenfrey line is not continuous. -/
theorem not_continuous_toReal_symm : ¬ Continuous toReal.symm := by
  -- Continuity would make the ordinary preimage of the Sorgenfrey-open `[0, 1)` open.
  intro hContinuous
  have hOpenSorgenfrey : IsOpen (toReal ⁻¹' Set.Ico (0 : ℝ) 1) :=
    isOpen_preimage_Ico_toReal 0 1 zero_lt_one
  have hOpenReal : IsOpen (toReal.symm ⁻¹' (toReal ⁻¹' Set.Ico (0 : ℝ) 1)) :=
    hContinuous.isOpen_preimage _ hOpenSorgenfrey
  have hPreimage :
      toReal.symm ⁻¹' (toReal ⁻¹' Set.Ico (0 : ℝ) 1) = Set.Ico (0 : ℝ) 1 := by
    ext x
    rfl
  have hOpenIco : IsOpen (Set.Ico (0 : ℝ) 1) := by
    rw [hPreimage] at hOpenReal
    exact hOpenReal
  -- But the left endpoint would then belong to the interior `Ioo 0 1`.
  have hZeroInterior : (0 : ℝ) ∈ Set.Ioo 0 1 := by
    rw [← interior_Ico, hOpenIco.interior_eq]
    exact ⟨le_rfl, zero_lt_one⟩
  exact (lt_irrefl (0 : ℝ)) hZeroInterior.1

/-- Example 18.3 (2). The carrier identity from the Sorgenfrey line to the
usual real line is continuous. -/
theorem continuous_toReal : Continuous toReal := by
  -- Refine each ordinary open neighborhood to an open interval, whose preimage is open.
  refine continuous_def.mpr ?_
  intro U hU
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hx
  obtain ⟨a, b, hxIoo, hIooU⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
  refine ⟨Set.Ico (toReal x) b, ?_, Set.left_mem_Ico.mpr hxIoo.2, ?_⟩
  · exact ⟨toReal x, b, hxIoo.2, rfl⟩
  · intro y hy
    exact hIooU ⟨hxIoo.1.trans_le hy.1, hy.2⟩

end SorgenfreyLine

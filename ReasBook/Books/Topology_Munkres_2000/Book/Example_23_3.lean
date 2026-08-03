module

import Topology_Munkres_2000.Book.Example_17_8
public import Topology_Munkres_2000.Book.Definition_23_1.Separation
public import Mathlib.Topology.DerivedSet
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue

public section

open Set
open scoped Set.Notation

/-- Helper for Example 23.3: The induced subsets `[-1, 0]` and `(0, 1]` of the
subspace `[-1, 1]` are disjoint. -/
theorem realIcc_negOne_one_induced_inter_eq_empty :
    (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0) ∩
      (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1) = ∅ := by
  -- Reduce membership in the intersection to the incompatible inequalities `x ≤ 0` and `0 < x`.
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Icc, mem_Ioc, mem_empty_iff_false]
  constructor
  · rintro ⟨hleft, hright⟩
    exact (not_lt_of_ge hleft.2) hright.1
  · intro hfalse
    exact hfalse.elim

/-- Helper for Example 23.3: The induced subset `[-1, 0]` of the subspace `[-1, 1]`
is nonempty. -/
theorem realIcc_negOne_one_induced_left_nonempty :
    (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0).Nonempty := by
  -- The midpoint `0` satisfies both the subtype bounds and the left-interval bounds.
  refine ⟨⟨0, ?_⟩, ?_⟩
  · norm_num
  · norm_num

/-- Helper for Example 23.3: The induced subset `(0, 1]` of the subspace `[-1, 1]`
is nonempty. -/
theorem realIcc_negOne_one_induced_right_nonempty :
    (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1).Nonempty := by
  -- The endpoint `1` belongs to the subtype and to the half-open right interval.
  refine ⟨⟨1, ?_⟩, ?_⟩
  · norm_num
  · norm_num

/-- Helper for Example 23.3: The induced subsets `[-1, 0]` and `(0, 1]` cover the
subspace `[-1, 1]`. -/
theorem realIcc_negOne_one_induced_union_eq_univ :
    (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0) ∪
      (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1) = Set.univ := by
  -- Split each point of the subtype according to which side of zero it lies on.
  ext x
  simp only [mem_union, mem_preimage, mem_Icc, mem_Ioc, mem_univ, iff_true]
  rcases le_or_gt (x : ℝ) 0 with hx | hx
  · exact Or.inl ⟨x.property.1, hx⟩
  · exact Or.inr ⟨hx, x.property.2⟩

/-- Helper for Example 23.3: the induced subset `(0, 1]` is open in the
subspace `[-1, 1]`. -/
lemma realIcc_negOne_one_induced_right_isOpen :
    IsOpen (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1) := by
  -- Remove the redundant upper bound, identifying the set with the pullback of `Ioi 0`.
  have hright :
      Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1 = Icc (-1 : ℝ) 1 ↓∩ Ioi (0 : ℝ) := by
    ext x
    simp only [mem_preimage, mem_Ioc, mem_Ioi]
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, x.property.2⟩
  rw [hright]
  exact isOpen_Ioi.preimage_val

/-- Helper for Example 23.3: The induced subset `[-1, 0]` is not open in the
subspace `[-1, 1]`. -/
theorem realIcc_negOne_one_induced_left_not_isOpen :
    ¬ IsOpen (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0) := by
  -- If the left side were open, the two induced sets would form a separation.
  intro hleftOpen
  have hdisjoint :
      Disjoint (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0)
        (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1) :=
    Set.disjoint_iff_inter_eq_empty.mpr realIcc_negOne_one_induced_inter_eq_empty
  have hseparation :
      (Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0).IsSeparation
        (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1) :=
    ⟨hleftOpen, realIcc_negOne_one_induced_right_isOpen, hdisjoint,
      realIcc_negOne_one_induced_left_nonempty,
      realIcc_negOne_one_induced_right_nonempty,
      realIcc_negOne_one_induced_union_eq_univ⟩
  -- Preconnectedness of the closed interval rules out that separation.
  have hpreconnected : PreconnectedSpace (Icc (-1 : ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hnoSeparation :
      ¬ ∃ U V : Set (Icc (-1 : ℝ) 1), U.IsSeparation V :=
    (preconnectedSpace_iff_no_separation (Icc (-1 : ℝ) 1)).mp hpreconnected
  apply hnoSeparation
  exact ⟨_, _, hseparation⟩

/-- Helper for Example 23.3: The induced subsets `[-1, 0]` and `(0, 1]` of the
subspace `[-1, 1]` do not form a separation. -/
theorem realIcc_negOne_one_not_separation :
    ¬ ((Icc (-1 : ℝ) 1 ↓∩ Icc (-1 : ℝ) 0).IsSeparation
      (Icc (-1 : ℝ) 1 ↓∩ Ioc (0 : ℝ) 1)) := by
  -- Any proposed separation supplies precisely the impossible openness of its left member.
  intro hseparation
  exact realIcc_negOne_one_induced_left_not_isOpen hseparation.isOpen_left

/-- Helper for Example 23.3: Zero is a limit point of `(0, 1]`. -/
theorem zero_mem_derivedSet_Ioc_zero_one :
    (0 : ℝ) ∈ derivedSet (Ioc 0 1) := by
  rw [derivedSet_Ioc_zero_one]
  exact left_mem_Icc.mpr zero_le_one

/-- Example 23.3: The subspace `[-1, 1]` admits no separation. -/
theorem realIcc_negOne_one_no_separation :
    ¬ ∃ U V : Set (Icc (-1 : ℝ) 1), U.IsSeparation V := by
  rw [← preconnectedSpace_iff_no_separation]
  exact isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc

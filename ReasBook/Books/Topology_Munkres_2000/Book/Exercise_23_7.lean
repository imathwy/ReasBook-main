module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Topology.Connected.Basic

public section

namespace SorgenfreyLine

/-- Helper for Exercise 23.7: points with real coordinate below `b` form an open
set in the Sorgenfrey line. -/
private lemma isOpen_toReal_lt (b : ℝ) : IsOpen {x : SorgenfreyLine | toReal x < b} := by
  -- Use the basis interval from the point up to the boundary `b`.
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hxb
  exact ⟨Set.Ico (toReal x) b, ⟨toReal x, b, hxb, rfl⟩,
    Set.left_mem_Ico.mpr hxb, Set.Ico_subset_Iio_self⟩

/-- Helper for Exercise 23.7: points with real coordinate at least `b` form an
open set in the Sorgenfrey line. -/
private lemma isOpen_toReal_ge (b : ℝ) : IsOpen {x : SorgenfreyLine | b ≤ toReal x} := by
  -- A short basis interval beginning at the point stays above `b`.
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hbx
  refine ⟨Set.Ico (toReal x) (toReal x + 1),
    ⟨toReal x, toReal x + 1, lt_add_one (toReal x), rfl⟩,
    Set.left_mem_Ico.mpr (lt_add_one (toReal x)), ?_⟩
  exact Set.Ico_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hbx)

/-- Helper for Exercise 23.7: complementary strict-lower and weak-upper
coordinate rays have empty intersection. -/
private lemma toReal_lt_inter_ge (b : ℝ) :
    {x : SorgenfreyLine | toReal x < b} ∩ {x : SorgenfreyLine | b ≤ toReal x} = ∅ := by
  -- Membership in both rays would give incompatible inequalities.
  ext x
  constructor
  · intro hx
    change toReal x < b ∧ b ≤ toReal x at hx
    exact ((not_le_of_gt hx.1) hx.2).elim
  · intro hx
    exact hx.elim

/-- Exercise 23.7: The Sorgenfrey line `SorgenfreyLine`, namely `ℝ` with the
lower-limit topology, is not connected. -/
theorem notConnected : ¬ ConnectedSpace SorgenfreyLine := by
  -- Connectedness would force the two complementary open rays to intersect.
  intro hconnected
  have hintersection := hconnected.toPreconnectedSpace.isPreconnected_univ
    {x : SorgenfreyLine | toReal x < 0} {x : SorgenfreyLine | 0 ≤ toReal x}
    (isOpen_toReal_lt 0) (isOpen_toReal_ge 0)
  have hcover :
      (Set.univ : Set SorgenfreyLine) ⊆
        {x : SorgenfreyLine | toReal x < 0} ∪ {x : SorgenfreyLine | 0 ≤ toReal x} := by
    -- Linear order trichotomy places every coordinate in one of the rays.
    intro x hx
    rcases lt_or_ge (toReal x) 0 with hxneg | hxnonneg
    · exact Set.mem_union_left _ hxneg
    · exact Set.mem_union_right _ hxnonneg
  have hlower :
      ((Set.univ : Set SorgenfreyLine) ∩ {x : SorgenfreyLine | toReal x < 0}).Nonempty := by
    -- The carrier point corresponding to `-1 : ℝ` lies in the strict lower ray.
    refine ⟨toReal.symm (-1), ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_univ, Set.mem_setOf_eq, true_and,
      Equiv.apply_symm_apply]
    norm_num
  have hupper :
      ((Set.univ : Set SorgenfreyLine) ∩ {x : SorgenfreyLine | 0 ≤ toReal x}).Nonempty := by
    -- The carrier point corresponding to `0 : ℝ` lies in the weak upper ray.
    refine ⟨toReal.symm 0, ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_univ, Set.mem_setOf_eq, true_and,
      Equiv.apply_symm_apply, le_refl]
  have himpossible := hintersection hcover hlower hupper
  -- The intersection supplied by preconnectedness is actually empty.
  rw [Set.univ_inter, toReal_lt_inter_ge 0] at himpossible
  exact Set.not_nonempty_empty himpossible

end SorgenfreyLine

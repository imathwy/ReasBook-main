module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Baire.Lemmas

public section

namespace SorgenfreyLine

/-- Helper for Exercise 48.11: every open neighborhood in the Sorgenfrey line contains a
half-open interval based at the chosen point. -/
private lemma exists_Ico_subset_of_mem_open {U : Set SorgenfreyLine} {x : SorgenfreyLine}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ b : ℝ, toReal x < b ∧ toReal ⁻¹' Set.Ico (toReal x) b ⊆ U := by
  -- Refine the neighborhood to a basis interval and raise its left endpoint to `x`.
  obtain ⟨v, ⟨a, b, hab, rfl⟩, hxv, hvU⟩ :=
    isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open hxU hU
  refine ⟨b, hxv.2, ?_⟩
  intro y hy
  exact hvU ⟨hxv.1.trans hy.1, hy.2⟩

/-- Helper for Exercise 48.11: a dense open Sorgenfrey set contains a dense ordinary-open
core after identifying its carrier with `ℝ`. -/
private lemma dense_interior_preimage_toReal_symm {U : Set SorgenfreyLine}
    (hU : IsOpen U) (hDense : Dense U) :
    Dense (interior (toReal.symm ⁻¹' U) : Set ℝ) := by
  -- It suffices to put a point of the ordinary-open core in every nonempty ordinary open set.
  refine dense_iff_inter_open.mpr ?_
  intro V hV hVNonempty
  obtain ⟨a, b, hab, hIooV⟩ := hV.exists_Ioo_subset hVNonempty
  have hBasis : toReal ⁻¹' Set.Ico a b ∈ RealTopology.lowerLimitBasis :=
    ⟨a, b, hab, rfl⟩
  have hBasisNonempty : (toReal ⁻¹' Set.Ico a b).Nonempty := by
    refine ⟨toReal.symm a, ?_⟩
    simp only [Set.mem_preimage, Equiv.apply_symm_apply, Set.mem_Ico]
    exact ⟨le_rfl, hab⟩
  obtain ⟨x, hxInterval, hxU⟩ :=
    (isTopologicalBasis_lowerLimitBasis.dense_iff.mp hDense)
      (toReal ⁻¹' Set.Ico a b) hBasis hBasisNonempty
  obtain ⟨c, hxc, hIntervalU⟩ := exists_Ico_subset_of_mem_open hU hxU
  have hxUpper : toReal x < min c b := lt_min hxc hxInterval.2
  obtain ⟨z, hxz, hzUpper⟩ := exists_between hxUpper
  have hOrdinaryIntervalSubset :
      Set.Ioo (toReal x) (min c b) ⊆ toReal.symm ⁻¹' U := by
    intro y hy
    apply hIntervalU
    simp only [Set.mem_preimage, Set.mem_Ico]
    exact ⟨hy.1.le, hy.2.trans_le (min_le_left c b)⟩
  have hzInterior : z ∈ interior (toReal.symm ⁻¹' U) :=
    interior_maximal hOrdinaryIntervalSubset isOpen_Ioo ⟨hxz, hzUpper⟩
  -- The chosen point also lies in the original ordinary open set.
  refine ⟨z, hIooV ?_, hzInterior⟩
  exact ⟨hxInterval.1.trans_lt hxz, hzUpper.trans_le (min_le_right c b)⟩

/-- Helper for Exercise 48.11: ordinary density on the real carrier implies density in the
Sorgenfrey topology. -/
private lemma dense_of_dense_preimage_toReal_symm {s : Set SorgenfreyLine}
    (hDense : Dense (toReal.symm ⁻¹' s : Set ℝ)) : Dense s := by
  -- Meet each lower-limit basis interval inside its nonempty ordinary interior.
  refine isTopologicalBasis_lowerLimitBasis.dense_iff.mpr ?_
  intro o ho hoNonempty
  obtain ⟨a, b, hab, rfl⟩ := ho
  obtain ⟨r, hrInterval, hrs⟩ :=
    hDense.inter_open_nonempty (Set.Ioo a b) isOpen_Ioo (Set.nonempty_Ioo.mpr hab)
  refine ⟨toReal.symm r, ?_, hrs⟩
  exact ⟨hrInterval.1.le, hrInterval.2⟩

/-- Exercise 48.11. The Sorgenfrey line is a Baire space. -/
instance instBaireSpace : BaireSpace SorgenfreyLine := by
  constructor
  intro f hOpen hDense
  -- Apply the ordinary Baire theorem to the dense open cores of the given family.
  have hRealDense :
      Dense (⋂ n : ℕ, interior (toReal.symm ⁻¹' f n) : Set ℝ) := by
    exact dense_iInter_of_isOpen_nat (fun _ ↦ isOpen_interior)
      (fun n ↦ dense_interior_preimage_toReal_symm (hOpen n) (hDense n))
  have hCoreSubset :
      (⋂ n : ℕ, interior (toReal.symm ⁻¹' f n) : Set ℝ) ⊆
        toReal.symm ⁻¹' (⋂ n, f n) := by
    intro x hx
    exact Set.mem_iInter.mpr fun n ↦ interior_subset (Set.mem_iInter.mp hx n)
  have hPreimageDense : Dense (toReal.symm ⁻¹' (⋂ n, f n) : Set ℝ) :=
    hRealDense.mono hCoreSubset
  -- Transfer the enlarged ordinary-dense intersection back to the Sorgenfrey topology.
  exact dense_of_dense_preimage_toReal_symm hPreimageDense

end SorgenfreyLine

module

public import Topology_Munkres_2000.Book.Exercise_13_7.RealLine
import Topology_Munkres_2000.Book.Lemma_13_4
public import Mathlib.Order.Comparable
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.LowerUpperTopology

public section

namespace RealTopology

/-- Helper for Exercise 13.7: ordinary open intervals are open in the upper-limit topology. -/
lemma isOpen_Ioo_upperLimit (a b : ℝ) :
    @IsOpen ℝ upperLimit (Set.Ioo a b) := by
  -- Refine each point by the upper-limit basis interval ending at that point.
  rw [(@TopologicalSpace.IsTopologicalBasis.isOpen_iff ℝ upperLimit
    (Set.Ioo a b) upperLimitBasis upperLimitBasis_isTopologicalBasis)]
  intro x hx
  have hBasis : Set.Ioc a x ∈ upperLimitBasis := by
    exact (mem_upperLimitBasis_iff _).mpr ⟨a, x, hx.1, rfl⟩
  refine ⟨Set.Ioc a x, hBasis, ⟨hx.1, le_rfl⟩, ?_⟩
  intro y hy
  exact ⟨hy.1, hy.2.trans_lt hx.2⟩

/-- Helper for Exercise 13.7: `positiveReciprocals` is closed in the upper-limit topology. -/
lemma positiveReciprocals_isClosed_upperLimit :
    @IsClosed ℝ upperLimit positiveReciprocals := by
  -- Around each point outside the reciprocal set, choose a basis interval avoiding it.
  apply (@isOpen_compl_iff ℝ positiveReciprocals upperLimit).mp
  rw [(@TopologicalSpace.IsTopologicalBasis.isOpen_iff ℝ upperLimit
    positiveReciprocalsᶜ upperLimitBasis upperLimitBasis_isTopologicalBasis)]
  intro x hx
  by_cases hxPos : 0 < x
  · classical
    let p : ℕ → Prop := fun n ↦ 0 < n ∧ (n : ℝ)⁻¹ < x
    have hp : ∃ n, p n := Real.exists_nat_pos_inv_lt hxPos
    let m := Nat.find hp
    have hm : p m := Nat.find_spec hp
    have hBasis : Set.Ioc (m : ℝ)⁻¹ x ∈ upperLimitBasis := by
      exact (mem_upperLimitBasis_iff _).mpr ⟨(m : ℝ)⁻¹, x, hm.2, rfl⟩
    refine ⟨Set.Ioc (m : ℝ)⁻¹ x, hBasis, ⟨hm.2, le_rfl⟩, ?_⟩
    intro y hy hyReciprocal
    obtain ⟨n, hnPos, rfl⟩ := (mem_positiveReciprocals y).mp hyReciprocal
    by_cases hnm : n < m
    · have hnNot : ¬p n := Nat.find_min hp hnm
      have hxLe : x ≤ (n : ℝ)⁻¹ := not_lt.mp fun hnInv ↦ hnNot ⟨hnPos, hnInv⟩
      have hxNe : x ≠ (n : ℝ)⁻¹ := fun hEq ↦ hx (hEq ▸
        (mem_positiveReciprocals _).mpr ⟨n, hnPos, rfl⟩)
      exact (not_le_of_gt (lt_of_le_of_ne hxLe hxNe)) hy.2
    · have hmLe : m ≤ n := Nat.le_of_not_gt hnm
      have hmPos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm.1
      have hInvLe : (n : ℝ)⁻¹ ≤ (m : ℝ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hmPos (Nat.cast_le.mpr hmLe)
      exact (not_lt_of_ge hInvLe) hy.1
  · have hLeft : x - 1 < x := by linarith
    have hBasis : Set.Ioc (x - 1) x ∈ upperLimitBasis := by
      exact (mem_upperLimitBasis_iff _).mpr ⟨x - 1, x, hLeft, rfl⟩
    refine ⟨Set.Ioc (x - 1) x, hBasis, ⟨hLeft, le_rfl⟩, ?_⟩
    intro y hy hyReciprocal
    have hyPos := positiveReciprocals_pos hyReciprocal
    exact (not_lt_of_ge (not_lt.mp hxPos)) (hyPos.trans_le hy.2)

/-- Helper for Exercise 13.7: every `K`-basis generator is upper-limit open. -/
lemma isOpen_upperLimit_of_mem_kBasis {u : Set ℝ} (hu : u ∈ kBasis) :
    @IsOpen ℝ upperLimit u := by
  -- Split a generator into an ordinary interval or a deleted interval.
  obtain ⟨a, b, hab, rfl | rfl⟩ := (mem_kBasis_iff u).mp hu
  · exact isOpen_Ioo_upperLimit a b
  · have hCompl : @IsOpen ℝ upperLimit positiveReciprocalsᶜ :=
      (@isOpen_compl_iff ℝ positiveReciprocals upperLimit).mpr
        positiveReciprocals_isClosed_upperLimit
    exact @IsOpen.inter ℝ upperLimit _ _ (isOpen_Ioo_upperLimit a b) hCompl

/-- Helper for Exercise 13.7: at a reciprocal point, every `K`-open neighborhood
contains an ordinary open interval around that point. -/
lemma exists_Ioo_subset_of_kOpen_of_mem_positiveReciprocals {u : Set ℝ} {x : ℝ}
    (hu : @IsOpen ℝ k u) (hxu : x ∈ u) (hxReciprocal : x ∈ positiveReciprocals) :
    ∃ a b : ℝ, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ u := by
  -- Induct through generated opens; a deleted generator cannot contain the center.
  rw [k_eq_generateFrom] at hu
  induction hu generalizing x with
  | basic s hs =>
      obtain ⟨a, b, hab, rfl | rfl⟩ := (mem_kBasis_iff s).mp hs
      · exact ⟨a, b, hxu, Set.Subset.rfl⟩
      · exact False.elim (hxu.2 hxReciprocal)
  | univ =>
      exact ⟨x - 1, x + 1, ⟨by linarith, by linarith⟩, Set.subset_univ _⟩
  | inter s t _ _ hs ht =>
      obtain ⟨a, b, hxab, hab⟩ := hs hxu.1 hxReciprocal
      obtain ⟨c, d, hxcd, hcd⟩ := ht hxu.2 hxReciprocal
      refine ⟨max a c, min b d, ⟨max_lt hxab.1 hxcd.1, lt_min hxab.2 hxcd.2⟩, ?_⟩
      intro y hy
      exact ⟨hab ⟨(le_max_left _ _).trans_lt hy.1, hy.2.trans_le (min_le_left _ _)⟩,
        hcd ⟨(le_max_right _ _).trans_lt hy.1, hy.2.trans_le (min_le_right _ _)⟩⟩
  | sUnion S _ hS =>
      obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp hxu
      obtain ⟨a, b, hxab, hab⟩ := hS s hsS hxs hxReciprocal
      exact ⟨a, b, hxab, hab.trans (Set.subset_sUnion_of_mem hsS)⟩

/-- Helper for Exercise 13.7: every open set of the lower topology is a lower set. -/
lemma isLowerSet_of_isOpen_lower {u : Set ℝ}
    (hu : @IsOpen ℝ (Topology.lower ℝ) u) : IsLowerSet u := by
  -- The generating rays are lower sets, and this property is preserved by open-set operations.
  induction hu with
  | basic s hs =>
      obtain ⟨a, rfl⟩ := hs
      simpa only [Set.compl_Ici] using isLowerSet_Iio a
  | univ =>
      exact isLowerSet_univ
  | inter s t _ _ hs ht =>
      exact hs.inter ht
  | sUnion S _ hS =>
      exact isLowerSet_sUnion hS

/-- The first comparison for Exercise 13.7. In Lean's reversed order on topologies,
`upperLimit < k` says that the upper-limit topology
strictly contains the `K`-topology. -/
theorem upperLimit_lt_k : upperLimit < k := by
  -- All `K`-generators are upper-limit open; `(0,1]` witnesses strictness.
  apply lt_of_le_not_ge
  · rw [k_eq_generateFrom]
    apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    intro u hu
    exact isOpen_upperLimit_of_mem_kBasis hu
  · intro hKUpper
    have hUpperOpen : @IsOpen ℝ upperLimit (Set.Ioc 0 1) := by
      have hBasis : Set.Ioc (0 : ℝ) 1 ∈ upperLimitBasis := by
        exact (mem_upperLimitBasis_iff _).mpr ⟨0, 1, zero_lt_one, rfl⟩
      rw [upperLimit_eq_generateFrom]
      exact TopologicalSpace.isOpen_generateFrom_of_mem hBasis
    have hKOpen : @IsOpen ℝ k (Set.Ioc 0 1) := hKUpper _ hUpperOpen
    have hOneReciprocal : (1 : ℝ) ∈ positiveReciprocals :=
      (mem_positiveReciprocals 1).mpr ⟨1, Nat.zero_lt_succ 0, by norm_num⟩
    obtain ⟨a, b, hOne, hab⟩ :=
      exists_Ioo_subset_of_kOpen_of_mem_positiveReciprocals hKOpen
        ⟨zero_lt_one, le_rfl⟩ hOneReciprocal
    have hMid : (1 + b) / 2 ∈ Set.Ioo a b := by
      constructor <;> linarith [hOne.1, hOne.2]
    exact (not_lt_of_ge (hab hMid).2) (by linarith [hOne.2])

/- Exercise 13.7 (2). In Lean's reversed order on topologies,
`k < (inferInstance : TopologicalSpace ℝ)` says that the `K`-topology
strictly contains the standard topology. -/
#check k_lt_standard

/-- The third comparison for Exercise 13.7. In Lean's reversed order on topologies,
this says that the standard topology strictly contains the finite-complement topology. -/
theorem standard_lt_cofinite :
    (inferInstance : TopologicalSpace ℝ) < TopologicalSpace.cofinite := by
  -- Cofinite opens are standard-open; `(0,1)` has infinite complement.
  apply lt_of_le_not_ge
  · intro u hu
    by_cases huEmpty : u = ∅
    · simpa only [huEmpty] using (isOpen_empty : IsOpen (∅ : Set ℝ))
    · rw [← compl_compl u]
      exact (hu (Set.nonempty_iff_ne_empty.mpr huEmpty)).isClosed.isOpen_compl
  · intro hCofiniteStandard
    have hCofiniteOpen : @IsOpen ℝ TopologicalSpace.cofinite (Set.Ioo 0 1) :=
      hCofiniteStandard _ isOpen_Ioo
    have hFinite : (Set.Ioo (0 : ℝ) 1)ᶜ.Finite :=
      hCofiniteOpen ⟨1 / 2, by norm_num⟩
    have hIicSubset : Set.Iic (0 : ℝ) ⊆ (Set.Ioo 0 1)ᶜ := by
      intro x hx hxInterval
      exact (not_lt_of_ge hx) hxInterval.1
    exact Set.Iic_infinite (0 : ℝ) (hFinite.subset hIicSubset)

/-- The fourth comparison for Exercise 13.7. In Lean's reversed order on topologies,
this says that the standard topology strictly contains the topology generated by the rays
`(-∞, a)`. -/
theorem standard_lt_lower :
    (inferInstance : TopologicalSpace ℝ) < Topology.lower ℝ := by
  -- Standard intervals are lower-topology open; `(0,1)` is not downward closed.
  apply lt_of_le_not_ge
  · unfold Topology.lower
    apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    intro s hs
    obtain ⟨a, rfl⟩ := hs
    have hOpen : @IsOpen ℝ (inferInstance : TopologicalSpace ℝ) (Set.Iio a) := isOpen_Iio
    change @IsOpen ℝ (inferInstance : TopologicalSpace ℝ) (Set.Ici a)ᶜ
    simpa only [Set.compl_Ici] using hOpen
  · intro hLowerStandard
    have hLowerOpen : @IsOpen ℝ (Topology.lower ℝ) (Set.Ioo 0 1) :=
      hLowerStandard _ isOpen_Ioo
    have hLower := isLowerSet_of_isOpen_lower hLowerOpen
    have hHalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
    have hZeroLeHalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
    exact (lt_irrefl 0) (hLower hZeroLeHalf hHalf).1

/-- The fifth comparison for Exercise 13.7. The finite-complement topology and the topology
generated by the rays `(-∞, a)` contain neither one another. -/
theorem cofinite_lower_incomparable :
    IncompRel (· ≤ ·) TopologicalSpace.cofinite (Topology.lower ℝ) := by
  -- An initial ray and a punctured line witness the two failed comparisons.
  constructor
  · intro hCofiniteLower
    have hLowerOpen : @IsOpen ℝ (Topology.lower ℝ) (Set.Iio 0) := by
      rw [Topology.lower]
      exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨0, by simp only [Set.compl_Ici]⟩
    have hCofiniteOpen : @IsOpen ℝ TopologicalSpace.cofinite (Set.Iio 0) :=
      hCofiniteLower _ hLowerOpen
    have hFinite : (Set.Iio (0 : ℝ))ᶜ.Finite := hCofiniteOpen ⟨-1, by norm_num⟩
    have hIciSubset : Set.Ici (0 : ℝ) ⊆ (Set.Iio 0)ᶜ := by
      intro x hx hxInterval
      change x < 0 at hxInterval
      exact (not_lt_of_ge hx) hxInterval
    exact Set.Ici_infinite (0 : ℝ) (hFinite.subset hIciSubset)
  · intro hLowerCofinite
    have hCofiniteOpen : @IsOpen ℝ TopologicalSpace.cofinite ({0}ᶜ : Set ℝ) := by
      intro _
      rw [compl_compl]
      exact Set.finite_singleton (0 : ℝ)
    have hLowerOpen : @IsOpen ℝ (Topology.lower ℝ) ({0}ᶜ : Set ℝ) :=
      hLowerCofinite _ hCofiniteOpen
    have hLower := isLowerSet_of_isOpen_lower hLowerOpen
    have hOne : (1 : ℝ) ∈ ({0}ᶜ : Set ℝ) := by norm_num
    exact (hLower (by norm_num : (0 : ℝ) ≤ 1) hOne) rfl

/-- Exercise 13.7. Summary of the strict containments and incomparability relations among the
upper-limit, `K`, standard, finite-complement, and lower topologies on `ℝ`. -/
theorem exercise13_7_topologyComparisons :
    upperLimit < k ∧
      k < (inferInstance : TopologicalSpace ℝ) ∧
      (inferInstance : TopologicalSpace ℝ) < TopologicalSpace.cofinite ∧
      (inferInstance : TopologicalSpace ℝ) < Topology.lower ℝ ∧
      IncompRel (· ≤ ·) TopologicalSpace.cofinite (Topology.lower ℝ) := by
  -- Package the five comparison facts that determine every requested containment.
  exact ⟨upperLimit_lt_k, k_lt_standard, standard_lt_cofinite, standard_lt_lower,
    cofinite_lower_incomparable⟩

end RealTopology

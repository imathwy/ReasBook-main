module

public import Topology_Munkres_2000.Book.Definition_25_1.ComponentIn
public import Topology_Munkres_2000.Book.Definition_4_5.LinearContinuum
public import Topology_Munkres_2000.Book.Exercise_3_13
public import Topology_Munkres_2000.Book.Theorem_24_1
public import Topology_Munkres_2000.Book.Theorem_27_1
public import Mathlib.Topology.Order.T5
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.Compact

public section

universe u

open Filter Set Topology

/- Exercise 32.8 (1): Every linear continuum with its order topology is normal. In fact,
every linear order with its order topology has the stronger canonical `T5Space` instance. -/
#check OrderTopology.t5Space

namespace Set

/-- An open interval lies between `A` and `B` when its two endpoints lie one in each set. -/
def IsOpenIntervalBetween {X : Type u} [LinearOrder X] (A B U : Set X) : Prop :=
  (∃ a ∈ A, ∃ b ∈ B, U = Ioo a b) ∨ ∃ b ∈ B, ∃ a ∈ A, U = Ioo b a

/-- A complementary component is a crossing component of `A` and `B` when it is an open
interval with one endpoint in each set. -/
def IsCrossingComponent {X : Type u} [TopologicalSpace X] [LinearOrder X]
    (A B W : Set X) : Prop :=
  IsConnectedComponentIn (A ∪ B)ᶜ W ∧ IsOpenIntervalBetween A B W

/-- A crossing component is a connected component of `(A ∪ B)ᶜ`. -/
theorem IsCrossingComponent.isConnectedComponentIn {X : Type u} [TopologicalSpace X]
    [LinearOrder X] {A B W : Set X} (hW : IsCrossingComponent A B W) :
    IsConnectedComponentIn (A ∪ B)ᶜ W :=
  hW.1

/-- A crossing component is an open interval between `A` and `B`. -/
theorem IsCrossingComponent.isOpenIntervalBetween {X : Type u} [TopologicalSpace X]
    [LinearOrder X] {A B W : Set X} (hW : IsCrossingComponent A B W) :
    IsOpenIntervalBetween A B W :=
  hW.2

/-- The type of complementary components that are open intervals between `A` and `B`. -/
abbrev CrossingComponent {X : Type u} [TopologicalSpace X] [LinearOrder X]
    (A B : Set X) :=
  {W : Set X // IsCrossingComponent A B W}

/-- The points selected from the crossing components of `A` and `B`. -/
def crossingComponentPoints {X : Type u} [TopologicalSpace X] [LinearOrder X]
    (A B : Set X) (choose : (W : CrossingComponent A B) → (W : Set X)) : Set X :=
  range fun W ↦ (choose W : X)

/-- Membership in `crossingComponentPoints A B choose` means being the point selected from
some crossing component of `A` and `B`. -/
theorem mem_crossingComponentPoints {X : Type u} [TopologicalSpace X] [LinearOrder X]
    {A B : Set X} {choose : (W : CrossingComponent A B) → (W : Set X)} {x : X} :
    x ∈ crossingComponentPoints A B choose ↔
      ∃ W, (choose W : X) = x := by
  rfl

/-- Part (a) of Exercise 32.8: A component of the complement of a nonempty closed set in a
linear continuum is a bounded open interval with endpoints in the set, or an open ray
with endpoint in the set. -/
theorem component_compl_closed_eq_interval {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LinearContinuum X] {C U : Set X}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hU : IsConnectedComponentIn Cᶜ U) :
    (∃ c ∈ C, ∃ c' ∈ C, U = Ioo c c') ∨
      (∃ c ∈ C, U = Ioi c) ∨ ∃ c ∈ C, U = Iio c := by
  obtain ⟨x, hxU⟩ := hU.nonempty
  have hxC : x ∉ C := hU.subset hxU
  have hU_ord : U.OrdConnected := hU.isConnected.isPreconnected.ordConnected
  let lowerCut := C ∩ Iio x
  let upperCut := C ∩ Ioi x
  by_cases hLower : lowerCut.Nonempty
  · obtain ⟨c, hc⟩ := LinearContinuum.leastUpperBoundProperty.exists_isLUB lowerCut hLower
      ⟨x, fun y hy ↦ hy.2.le⟩
    have hcC : c ∈ C := by
      -- Closedness returns the supremum of the lower cut to `C`.
      rw [← hC_closed.closure_eq]
      exact closure_mono inter_subset_left (hc.mem_closure hLower)
    have hcx : c < x := by
      have hcle : c ≤ x := hc.2 (fun _ hy ↦ hy.2.le)
      exact hcle.lt_of_ne fun h ↦ hxC (h ▸ hcC)
    by_cases hUpper : upperCut.Nonempty
    · obtain ⟨c', hc'⟩ :=
        (leastUpperBoundProperty_implies_greatestLowerBoundProperty X
          LinearContinuum.leastUpperBoundProperty).exists_isGLB upperCut hUpper
          ⟨x, fun y hy ↦ hy.2.le⟩
      have hc'C : c' ∈ C := by
        -- Closedness likewise returns the infimum of the upper cut to `C`.
        rw [← hC_closed.closure_eq]
        exact closure_mono inter_subset_left (hc'.mem_closure hUpper)
      have hxc' : x < c' := by
        have hlec' : x ≤ c' := hc'.2 (fun _ hy ↦ hy.2.le)
        exact hlec'.lt_of_ne fun h ↦ hxC (h.symm ▸ hc'C)
      left
      refine ⟨c, hcC, c', hc'C, ?_⟩
      apply Subset.antisymm
      · intro y hyU
        have hcy : c < y := by
          apply lt_of_not_ge
          intro hyc
          rcases eq_or_lt_of_le hyc with rfl | hyc'
          · exact (hU.subset hyU) hcC
          · obtain ⟨z, hz, hyz, -⟩ := hc.exists_between hyc'
            exact (hU.subset (hU_ord.out hyU hxU ⟨hyz.le, hz.2.le⟩)) hz.1
        have hyc' : y < c' := by
          apply lt_of_not_ge
          intro hc'y
          rcases eq_or_lt_of_le hc'y with rfl | hc'y'
          · exact (hU.subset hyU) hc'C
          · obtain ⟨z, hz, -, hzy⟩ := hc'.exists_between hc'y'
            exact (hU.subset (hU_ord.out hxU hyU ⟨hz.2.le, hzy.le⟩)) hz.1
        exact ⟨hcy, hyc'⟩
      · intro y hy
        have hIntervalSubset : Ioo c c' ⊆ Cᶜ := by
          intro z hz hzC
          rcases le_total z x with hzx | hxz
          · rcases hzx.eq_or_lt with rfl | hzx'
            · exact hxC hzC
            · exact (not_le_of_gt hz.1) (hc.1 ⟨hzC, hzx'⟩)
          · rcases hxz.eq_or_lt with rfl | hxz'
            · exact hxC hzC
            · exact (not_le_of_gt hz.2) (hc'.1 ⟨hzC, hxz'⟩)
        have hIntervalPreconnected : IsPreconnected (Ioo c c') :=
          (LinearContinuum.isConnected_of_ordConnected ordConnected_Ioo
            ⟨x, hcx, hxc'⟩).isPreconnected
        rw [hU.eq_connectedComponentIn hxU]
        exact hIntervalPreconnected.subset_connectedComponentIn ⟨hcx, hxc'⟩
          hIntervalSubset hy
    · right
      left
      refine ⟨c, hcC, ?_⟩
      apply Subset.antisymm
      · intro y hyU
        apply lt_of_not_ge
        intro hyc
        rcases eq_or_lt_of_le hyc with rfl | hyc'
        · exact (hU.subset hyU) hcC
        · obtain ⟨z, hz, hyz, -⟩ := hc.exists_between hyc'
          exact (hU.subset (hU_ord.out hyU hxU ⟨hyz.le, hz.2.le⟩)) hz.1
      · intro y hcy
        have hRaySubset : Ioi c ⊆ Cᶜ := by
          intro z hcz hzC
          rcases le_total z x with hzx | hxz
          · rcases hzx.eq_or_lt with rfl | hzx'
            · exact hxC hzC
            · exact (not_le_of_gt hcz) (hc.1 ⟨hzC, hzx'⟩)
          · rcases hxz.eq_or_lt with rfl | hxz'
            · exact hxC hzC
            · exact hUpper ⟨z, hzC, hxz'⟩
        have hRayPreconnected : IsPreconnected (Ioi c) :=
          (LinearContinuum.isConnected_of_ordConnected ordConnected_Ioi ⟨x, hcx⟩).isPreconnected
        rw [hU.eq_connectedComponentIn hxU]
        exact hRayPreconnected.subset_connectedComponentIn hcx hRaySubset hcy
  · have hUpper : upperCut.Nonempty := by
      rcases hC_nonempty with ⟨c, hcC⟩
      rcases lt_trichotomy c x with hcx | hcx | hxc
      · exact False.elim (hLower ⟨c, hcC, hcx⟩)
      · exact False.elim (hxC (hcx ▸ hcC))
      · exact ⟨c, hcC, hxc⟩
    obtain ⟨c, hc⟩ :=
      (leastUpperBoundProperty_implies_greatestLowerBoundProperty X
        LinearContinuum.leastUpperBoundProperty).exists_isGLB upperCut hUpper
        ⟨x, fun y hy ↦ hy.2.le⟩
    have hcC : c ∈ C := by
      -- The upper cut has a least point in the closure of `C`.
      rw [← hC_closed.closure_eq]
      exact closure_mono inter_subset_left (hc.mem_closure hUpper)
    have hxc : x < c := by
      have hlec : x ≤ c := hc.2 (fun _ hy ↦ hy.2.le)
      exact hlec.lt_of_ne fun h ↦ hxC (h.symm ▸ hcC)
    right
    right
    refine ⟨c, hcC, ?_⟩
    apply Subset.antisymm
    · intro y hyU
      apply lt_of_not_ge
      intro hcy
      rcases eq_or_lt_of_le hcy with rfl | hcy'
      · exact (hU.subset hyU) hcC
      · obtain ⟨z, hz, -, hzy⟩ := hc.exists_between hcy'
        exact (hU.subset (hU_ord.out hxU hyU ⟨hz.2.le, hzy.le⟩)) hz.1
    · intro y hyc
      have hRaySubset : Iio c ⊆ Cᶜ := by
        intro z hzc hzC
        rcases le_total z x with hzx | hxz
        · rcases hzx.eq_or_lt with rfl | hzx'
          · exact hxC hzC
          · exact hLower ⟨z, hzC, hzx'⟩
        · rcases hxz.eq_or_lt with rfl | hxz'
          · exact hxC hzC
          · exact (not_le_of_gt hzc) (hc.1 ⟨hzC, hxz'⟩)
      have hRayPreconnected : IsPreconnected (Iio c) :=
        (LinearContinuum.isConnected_of_ordConnected ordConnected_Iio ⟨x, hxc⟩).isPreconnected
      rw [hU.eq_connectedComponentIn hxU]
      exact hRayPreconnected.subset_connectedComponentIn hxc hRaySubset hyc

/-- Helper for Exercise 32.8: every selected crossing point lies in the canonical
order-separating set. -/
lemma crossingComponentPoints_subset_ordSeparatingSet {X : Type u} [LinearOrder X]
    [TopologicalSpace X] {A B : Set X}
    (hAB : Disjoint A B) (choose : (W : CrossingComponent A B) → (W : Set X)) :
    crossingComponentPoints A B choose ⊆ ordSeparatingSet A B := by
  intro x hx
  obtain ⟨W, rfl⟩ := mem_crossingComponentPoints.mp hx
  have hxW : (choose W : X) ∈ (W : Set X) := (choose W).property
  rcases W.property.isOpenIntervalBetween with hW | hW
  · obtain ⟨a, haA, b, hbB, hW⟩ := hW
    have hxInterval : (choose W : X) ∈ Ioo a b := hW.le hxW
    have haB : a ∉ B := fun haB ↦ Set.disjoint_left.mp hAB haA haB
    have hbA : b ∉ A := fun hbA ↦ Set.disjoint_left.mp hAB hbA hbB
    constructor
    · refine mem_iUnion₂.mpr ⟨a, haA, ?_⟩
      rw [mem_ordConnectedComponent, uIcc_of_le hxInterval.1.le]
      intro z hz
      rcases hz.1.eq_or_lt with rfl | haz
      · exact haB
      · intro hzB
        have hzW : z ∈ (W : Set X) := hW.symm ▸ ⟨haz, hz.2.trans_lt hxInterval.2⟩
        exact W.property.isConnectedComponentIn.subset hzW (Or.inr hzB)
    · refine mem_iUnion₂.mpr ⟨b, hbB, ?_⟩
      rw [mem_ordConnectedComponent, uIcc_of_ge hxInterval.2.le]
      intro z hz
      rcases hz.2.eq_or_lt with rfl | hzb
      · exact hbA
      · intro hzA
        have hzW : z ∈ (W : Set X) := hW.symm ▸ ⟨hxInterval.1.trans_le hz.1, hzb⟩
        exact W.property.isConnectedComponentIn.subset hzW (Or.inl hzA)
  · obtain ⟨b, hbB, a, haA, hW⟩ := hW
    have hxInterval : (choose W : X) ∈ Ioo b a := hW.le hxW
    have haB : a ∉ B := fun haB ↦ Set.disjoint_left.mp hAB haA haB
    have hbA : b ∉ A := fun hbA ↦ Set.disjoint_left.mp hAB hbA hbB
    constructor
    · refine mem_iUnion₂.mpr ⟨a, haA, ?_⟩
      rw [mem_ordConnectedComponent, uIcc_of_ge hxInterval.2.le]
      intro z hz
      rcases hz.2.eq_or_lt with rfl | hza
      · exact haB
      · intro hzB
        have hzW : z ∈ (W : Set X) := hW.symm ▸ ⟨hxInterval.1.trans_le hz.1, hza⟩
        exact W.property.isConnectedComponentIn.subset hzW (Or.inr hzB)
    · refine mem_iUnion₂.mpr ⟨b, hbB, ?_⟩
      rw [mem_ordConnectedComponent, uIcc_of_le hxInterval.1.le]
      intro z hz
      rcases hz.1.eq_or_lt with rfl | hbz
      · exact hbA
      · intro hzA
        have hzW : z ∈ (W : Set X) := hW.symm ▸ ⟨hbz, hz.2.trans_lt hxInterval.2⟩
        exact W.property.isConnectedComponentIn.subset hzW (Or.inl hzA)
/-- Helper for Exercise 32.8: two selected crossing points joined inside the
order-separating set are equal. -/
lemma eq_of_mem_crossingComponentPoints_of_uIcc_subset {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LinearContinuum X] {A B : Set X}
    (choose : (W : CrossingComponent A B) → (W : Set X)) {x y : X}
    (hx : x ∈ crossingComponentPoints A B choose)
    (hy : y ∈ crossingComponentPoints A B choose)
    (hxy : uIcc x y ⊆ ordSeparatingSet A B) : x = y := by
  classical
  obtain ⟨W, hWx⟩ := mem_crossingComponentPoints.mp hx
  obtain ⟨W', hW'y⟩ := mem_crossingComponentPoints.mp hy
  have hSep : ordSeparatingSet A B ⊆ (A ∪ B)ᶜ := by
    intro z hz hzAB
    rcases hzAB with hzA | hzB
    · exact Set.disjoint_left.mp disjoint_left_ordSeparatingSet hzA hz
    · exact Set.disjoint_left.mp disjoint_right_ordSeparatingSet hzB hz
  have hPreconnected : IsPreconnected (uIcc x y) :=
    (LinearContinuum.isConnected_of_ordConnected ordConnected_uIcc
      ⟨x, left_mem_uIcc⟩).isPreconnected
  have hyW : y ∈ (W : Set X) := by
    rw [W.property.isConnectedComponentIn.eq_connectedComponentIn
      (hWx ▸ (choose W).property)]
    exact hPreconnected.subset_connectedComponentIn left_mem_uIcc
      (hxy.trans hSep) right_mem_uIcc
  have hWW' : W = W' := by
    apply Subtype.ext
    calc
      (W : Set X) = connectedComponentIn (A ∪ B)ᶜ y :=
        W.property.isConnectedComponentIn.eq_connectedComponentIn hyW
      _ = (W' : Set X) :=
        (W'.property.isConnectedComponentIn.eq_connectedComponentIn
          (hW'y ▸ (choose W').property)).symm
  subst W'
  exact hWx.symm.trans hW'y

/-- Helper for Exercise 32.8: the complement of a one-point section of an
order-separating set is a right neighborhood of every point of the first set. -/
lemma compl_mem_nhdsGE_of_subset_ordSeparatingSet_of_uIcc_unique
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    {A B S : Set X} {a : X} (hAB : Disjoint A (closure B)) (ha : a ∈ A)
    (hS : S ⊆ ordSeparatingSet A B)
    (hUnique : ∀ {x y}, x ∈ S → y ∈ S →
      uIcc x y ⊆ ordSeparatingSet A B → x = y) :
    Sᶜ ∈ 𝓝[≥] a := by
  -- First choose a right interval at `a` that avoids the second set.
  have hmem : Bᶜ ∈ 𝓝[≥] a := by
    refine mem_nhdsWithin_of_mem_nhds ?_
    rw [← mem_interior_iff_mem_nhds, interior_compl]
    exact disjoint_left.mp hAB ha
  rcases exists_Icc_mem_subset_of_mem_nhdsGE hmem with ⟨b, hab, hmem', hsub⟩
  by_cases hDisjoint : Disjoint (Icc a b) S
  · exact mem_of_superset hmem' (disjoint_left.mp hDisjoint)
  · simp only [Set.disjoint_left, not_forall, Classical.not_not] at hDisjoint
    rcases hDisjoint with ⟨c, ⟨hac, hcb⟩, hcS⟩
    have hComponent : Icc a b ⊆ ordConnectedComponent Bᶜ a :=
      subset_ordConnectedComponent (left_mem_Icc.mpr hab) hsub
    have hAS : Disjoint A S :=
      disjoint_left_ordSeparatingSet.mono_right hS
    have hac' : a < c :=
      hac.lt_of_ne (Ne.symm (ne_of_mem_of_not_mem hcS (disjoint_left.mp hAS ha)))
    -- The half-open interval below `c` contains no second selected point.
    filter_upwards [Ico_mem_nhdsGE hac'] with x hx hxS
    refine hx.2.ne (hUnique hxS hcS ?_)
    refine subset_inter (subset_iUnion₂_of_subset a ha ?_) ?_
    · exact OrdConnected.uIcc_subset inferInstance
        (hComponent ⟨hx.1, hx.2.le.trans hcb⟩)
        (hComponent ⟨hac'.le, hcb⟩)
    · rcases mem_iUnion₂.mp (hS hxS).2 with ⟨y, hyB, hxy⟩
      refine subset_iUnion₂_of_subset y hyB (OrdConnected.uIcc_subset inferInstance hxy ?_)
      refine subset_ordConnectedComponent left_mem_uIcc hxy ?_
      suffices c < y by
        rw [uIcc_of_ge (hx.2.trans this).le]
        exact ⟨hx.2.le, this.le⟩
      refine lt_of_not_ge fun hyc ↦ ?_
      have hya : y < a := not_le.mp fun hay ↦ hsub ⟨hay, hyc.trans hcb⟩ hyB
      exact hxy (Icc_subset_uIcc ⟨hya.le, hx.1⟩) ha

/-- Helper for Exercise 32.8: the complement of a one-point section of an
order-separating set is a neighborhood of every point of the first set. -/
lemma compl_mem_nhds_of_subset_ordSeparatingSet_of_uIcc_unique
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    {A B S : Set X} {a : X} (hAB : Disjoint A (closure B)) (ha : a ∈ A)
    (hS : S ⊆ ordSeparatingSet A B)
    (hUnique : ∀ {x y}, x ∈ S → y ∈ S →
      uIcc x y ⊆ ordSeparatingSet A B → x = y) :
    Sᶜ ∈ 𝓝 a := by
  -- Obtain the left neighborhood by applying the right-neighborhood result in the dual order.
  have hLeft : Sᶜ ∈ 𝓝[≤] a := by
    have hAB' : Disjoint (OrderDual.ofDual ⁻¹' A)
        (closure (OrderDual.ofDual ⁻¹' B)) := hAB
    have ha' : OrderDual.toDual a ∈ OrderDual.ofDual ⁻¹' A := ha
    have hS' : OrderDual.ofDual ⁻¹' S ⊆
        ordSeparatingSet (OrderDual.ofDual ⁻¹' A) (OrderDual.ofDual ⁻¹' B) := by
      simpa only [dual_ordSeparatingSet] using! hS
    have hUnique' : ∀ {x y : Xᵒᵈ}, x ∈ OrderDual.ofDual ⁻¹' S →
        y ∈ OrderDual.ofDual ⁻¹' S →
        uIcc x y ⊆ ordSeparatingSet (OrderDual.ofDual ⁻¹' A) (OrderDual.ofDual ⁻¹' B) →
        x = y := by
      intro x y hx hy hxy
      apply hUnique (x := OrderDual.ofDual x) (y := OrderDual.ofDual y) hx hy
      intro z hz
      have hzDual : OrderDual.toDual z ∈ uIcc x y := by
        simpa [mem_uIcc, min_comm, max_comm] using hz
      simpa only [dual_ordSeparatingSet] using! hxy hzDual
    simpa only using!
      (compl_mem_nhdsGE_of_subset_ordSeparatingSet_of_uIcc_unique
        hAB' ha' hS' hUnique')
  -- The two one-sided neighborhoods generate the ordinary neighborhood filter.
  rw [← nhdsLE_sup_nhdsGE, mem_sup]
  exact ⟨hLeft,
    compl_mem_nhdsGE_of_subset_ordSeparatingSet_of_uIcc_unique hAB ha hS hUnique⟩

/-- Helper for Exercise 32.8: a complementary component contains at most one
selected crossing point. -/
lemma eq_of_mem_crossingComponentPoints_of_mem_component
    {X : Type u} [TopologicalSpace X] [LinearOrder X] {A B U : Set X}
    {choose : (W : CrossingComponent A B) → (W : Set X)} {x y : X}
    (hU : IsConnectedComponentIn (A ∪ B)ᶜ U)
    (hx : x ∈ crossingComponentPoints A B choose)
    (hy : y ∈ crossingComponentPoints A B choose) (hxU : x ∈ U) (hyU : y ∈ U) :
    x = y := by
  -- Both crossing components equal the canonical component through the common ambient component.
  classical
  obtain ⟨W, hWx⟩ := mem_crossingComponentPoints.mp hx
  obtain ⟨W', hW'y⟩ := mem_crossingComponentPoints.mp hy
  have hUW : U = (W : Set X) := by
    calc
      U = connectedComponentIn (A ∪ B)ᶜ x := hU.eq_connectedComponentIn hxU
      _ = (W : Set X) :=
        (W.property.isConnectedComponentIn.eq_connectedComponentIn
          (hWx ▸ (choose W).property)).symm
  have hUW' : U = (W' : Set X) := by
    calc
      U = connectedComponentIn (A ∪ B)ᶜ y := hU.eq_connectedComponentIn hyU
      _ = (W' : Set X) :=
        (W'.property.isConnectedComponentIn.eq_connectedComponentIn
          (hW'y ▸ (choose W').property)).symm
  have hWW' : W = W' := Subtype.ext (hUW.symm.trans hUW')
  subst W'
  exact hWx.symm.trans hW'y

/-- Part (b) of Exercise 32.8: Choosing a point in every complementary component that is an open
interval between two closed disjoint sets produces a closed set of selected points. -/
theorem crossingComponentPoints_isClosed {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LinearContinuum X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (choose : (W : CrossingComponent A B) → (W : Set X)) :
    IsClosed (crossingComponentPoints A B choose) := by
  -- It suffices to give every point outside the selected set an open neighborhood
  -- contained in its complement.
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxAB : x ∈ A ∪ B
  · rcases hxAB with hxA | hxB
    · exact compl_mem_nhds_of_subset_ordSeparatingSet_of_uIcc_unique
        (hB.closure_eq.symm ▸ hAB) hxA
        (crossingComponentPoints_subset_ordSeparatingSet hAB choose)
        (eq_of_mem_crossingComponentPoints_of_uIcc_subset choose)
    · have hBA : Disjoint B (closure A) := hA.closure_eq.symm ▸ hAB.symm
      have hSubset : crossingComponentPoints A B choose ⊆ ordSeparatingSet B A := by
        rw [ordSeparatingSet_comm]
        exact crossingComponentPoints_subset_ordSeparatingSet hAB choose
      have hUnique : ∀ {y z}, y ∈ crossingComponentPoints A B choose →
          z ∈ crossingComponentPoints A B choose →
          uIcc y z ⊆ ordSeparatingSet B A → y = z := by
        intro y z hy hz hyz
        apply eq_of_mem_crossingComponentPoints_of_uIcc_subset choose hy hz
        rwa [ordSeparatingSet_comm] at hyz
      exact compl_mem_nhds_of_subset_ordSeparatingSet_of_uIcc_unique
        hBA hxB hSubset hUnique
  · have hxCompl : x ∈ (A ∪ B)ᶜ := hxAB
    let U := connectedComponentIn (A ∪ B)ᶜ x
    have hU : IsConnectedComponentIn (A ∪ B)ᶜ U :=
      IsConnectedComponentIn.of_mem hxCompl
    have hxU : x ∈ U := mem_connectedComponentIn hxCompl
    by_cases hUnionNonempty : (A ∪ B).Nonempty
    · have hUOpen : IsOpen U := by
        rcases component_compl_closed_eq_interval hUnionNonempty (hA.union hB) hU with
          hBounded | hRay
        · obtain ⟨a, -, b, -, hUeq⟩ := hBounded
          rw [hUeq]
          exact isOpen_Ioo
        · rcases hRay with hRight | hLeft
          · obtain ⟨a, -, hUeq⟩ := hRight
            rw [hUeq]
            exact isOpen_Ioi
          · obtain ⟨a, -, hUeq⟩ := hLeft
            rw [hUeq]
            exact isOpen_Iio
      by_cases hSelected : (U ∩ crossingComponentPoints A B choose).Nonempty
      · obtain ⟨c, hcU, hcSelected⟩ := hSelected
        have hOpen : IsOpen (U \ {c}) := hUOpen.sdiff isClosed_singleton
        refine mem_of_superset (hOpen.mem_nhds ⟨hxU, ?_⟩) ?_
        · intro hxc
          exact hx (hxc ▸ hcSelected)
        · intro y hy hySelected
          have hyU : y ∈ U := hy.1
          have hyc := eq_of_mem_crossingComponentPoints_of_mem_component
            hU hySelected hcSelected hyU hcU
          exact hy.2 (hyc ▸ mem_singleton c)
      · refine mem_of_superset (hUOpen.mem_nhds hxU) ?_
        intro y hyU hySelected
        exact hSelected ⟨y, hyU, hySelected⟩
    · have hSelectedEmpty : crossingComponentPoints A B choose = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨W, -⟩ := mem_crossingComponentPoints.mp hy
        apply hUnionNonempty
        rcases W.property.isOpenIntervalBetween with hW | hW
        · obtain ⟨a, ha, -, -, -⟩ := hW
          exact ⟨a, Or.inl ha⟩
        · obtain ⟨b, hb, -, -, -⟩ := hW
          exact ⟨b, Or.inr hb⟩
      rw [hSelectedEmpty, compl_empty]
      exact univ_mem

/-- Helper for Exercise 32.8: crossing-component status is symmetric in the two
endpoint sets. -/
lemma isCrossingComponent_comm {X : Type u} [TopologicalSpace X] [LinearOrder X]
    {A B W : Set X} : IsCrossingComponent A B W ↔ IsCrossingComponent B A W := by
  -- The complementary set is unchanged, and the two interval alternatives exchange places.
  constructor
  · rintro ⟨hComponent, hInterval⟩
    refine ⟨?_, ?_⟩
    · rwa [union_comm]
    · exact hInterval.elim Or.inr Or.inl
  · rintro ⟨hComponent, hInterval⟩
    refine ⟨?_, ?_⟩
    · rwa [union_comm]
    · exact hInterval.elim Or.inr Or.inl

/-- Helper for Exercise 32.8: an open gap with endpoints in the two closed sets and
no intervening endpoint-set points is a crossing component. -/
lemma isCrossingComponent_Ioo_of_subset_compl
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LinearContinuum X] {A B : Set X} {α β : X}
    (hαA : α ∈ A) (hβB : β ∈ B) (hαβ : α < β)
    (hGap : Ioo α β ⊆ (A ∪ B)ᶜ) : IsCrossingComponent A B (Ioo α β) := by
  -- Choose an interior point and compare the gap with its canonical complementary component.
  obtain ⟨x, hαx, hxβ⟩ := exists_between hαβ
  have hxGap : x ∈ Ioo α β := ⟨hαx, hxβ⟩
  have hPreconnected : IsPreconnected (Ioo α β) :=
    (LinearContinuum.isConnected_of_ordConnected ordConnected_Ioo ⟨x, hxGap⟩).isPreconnected
  have hxCompl : x ∈ (A ∪ B)ᶜ := hGap hxGap
  have hComponentEq : connectedComponentIn (A ∪ B)ᶜ x = Ioo α β := by
    apply Subset.antisymm
    · intro y hy
      have hyCompl := connectedComponentIn_subset (A ∪ B)ᶜ x hy
      have hOrd : (connectedComponentIn (A ∪ B)ᶜ x).OrdConnected :=
        isPreconnected_connectedComponentIn.ordConnected
      have hyx : Icc y x ⊆ connectedComponentIn (A ∪ B)ᶜ x :=
        hOrd.out hy (mem_connectedComponentIn hxCompl)
      have hαy : α < y := by
        refine lt_of_not_ge fun hyα ↦ ?_
        have hαInterval : α ∈ Icc y x := ⟨hyα, hαx.le⟩
        exact (connectedComponentIn_subset (A ∪ B)ᶜ x (hyx hαInterval)) (Or.inl hαA)
      have hyβ : y < β := by
        refine lt_of_not_ge fun hβy ↦ ?_
        have hβInterval : β ∈ Icc x y := ⟨hxβ.le, hβy⟩
        have hxy : Icc x y ⊆ connectedComponentIn (A ∪ B)ᶜ x :=
          hOrd.out (mem_connectedComponentIn hxCompl) hy
        exact (connectedComponentIn_subset (A ∪ B)ᶜ x (hxy hβInterval)) (Or.inr hβB)
      exact ⟨hαy, hyβ⟩
    · exact hPreconnected.subset_connectedComponentIn hxGap hGap
  refine ⟨?_, ?_⟩
  · exact hComponentEq ▸ IsConnectedComponentIn.of_mem hxCompl
  · exact Or.inl ⟨α, hαA, β, hβB, rfl⟩

/-- Helper for Exercise 32.8: when an `A`-point lies left of a `B`-point, a crossing
component is contained in the closed interval joining them. -/
lemma exists_crossingComponent_subset_Icc_of_lt
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LinearContinuum X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {a b : X} (haA : a ∈ A) (hbB : b ∈ B) (hab : a < b) :
    ∃ W : CrossingComponent A B, (W : Set X) ⊆ Icc a b := by
  -- Take the last `A`-point, then the first `B`-point after it.
  letI : LeastUpperBoundProperty X := LinearContinuum.leastUpperBoundProperty
  have hACompact : IsCompact (A ∩ Icc a b) := IsCompact.inter_left isCompact_Icc hA
  have hANonempty : (A ∩ Icc a b).Nonempty := ⟨a, haA, left_mem_Icc.mpr hab.le⟩
  obtain ⟨α, hαGreatest⟩ := hACompact.exists_isGreatest hANonempty
  have hαA : α ∈ A := hαGreatest.1.1
  have hαBounds : α ∈ Icc a b := hαGreatest.1.2
  have hBCompact : IsCompact (B ∩ Icc α b) := IsCompact.inter_left isCompact_Icc hB
  have hBNonempty : (B ∩ Icc α b).Nonempty :=
    ⟨b, hbB, right_mem_Icc.mpr hαBounds.2⟩
  obtain ⟨β, hβLeast⟩ := hBCompact.exists_isLeast hBNonempty
  have hβB : β ∈ B := hβLeast.1.1
  have hβBounds : β ∈ Icc α b := hβLeast.1.2
  have hαβ : α < β := by
    refine hβBounds.1.lt_of_ne ?_
    intro hαβEq
    exact Set.disjoint_left.mp hAB hαA (hαβEq ▸ hβB)
  -- Extremality removes both endpoint sets from the open gap.
  have hGap : Ioo α β ⊆ (A ∪ B)ᶜ := by
    intro z hz hzAB
    rcases hzAB with hzA | hzB
    · have hzBounds : z ∈ Icc a b :=
        ⟨hαBounds.1.trans hz.1.le, hz.2.le.trans hβBounds.2⟩
      exact (not_le_of_gt hz.1) (hαGreatest.2 ⟨hzA, hzBounds⟩)
    · have hzBounds : z ∈ Icc α b := ⟨hz.1.le, hz.2.le.trans hβBounds.2⟩
      exact (not_le_of_gt hz.2) (hβLeast.2 ⟨hzB, hzBounds⟩)
  have hCross : IsCrossingComponent A B (Ioo α β) :=
    isCrossingComponent_Ioo_of_subset_compl hαA hβB hαβ hGap
  let W : CrossingComponent A B := ⟨Ioo α β, hCross⟩
  refine ⟨W, ?_⟩
  intro z hz
  exact ⟨hαBounds.1.trans hz.1.le, hz.2.le.trans hβBounds.2⟩

/-- Helper for Exercise 32.8: any interval joining an `A`-point to a `B`-point
contains a crossing component. -/
lemma exists_crossingComponent_subset_uIcc
    {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LinearContinuum X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) {a b : X} (haA : a ∈ A) (hbB : b ∈ B) :
    ∃ W : CrossingComponent A B, (W : Set X) ⊆ uIcc a b := by
  -- Orient the endpoints; in the reverse case, construct for `B,A` and transport by symmetry.
  have habNe : a ≠ b := by
    intro hab
    exact Set.disjoint_left.mp hAB haA (hab.symm ▸ hbB)
  rcases lt_or_gt_of_ne habNe with hab | hba
  · obtain ⟨W, hW⟩ :=
      exists_crossingComponent_subset_Icc_of_lt hA hB hAB haA hbB hab
    refine ⟨W, ?_⟩
    rwa [uIcc_of_le hab.le]
  · obtain ⟨W, hW⟩ :=
      exists_crossingComponent_subset_Icc_of_lt hB hA hAB.symm hbB haA hba
    have hCross : IsCrossingComponent A B (W : Set X) :=
      isCrossingComponent_comm.mpr W.property
    let W' : CrossingComponent A B := ⟨(W : Set X), hCross⟩
    refine ⟨W', ?_⟩
    rwa [uIcc_of_ge hba.le]

/-- Exercise 32.8 (c): A component of the complement of the selected crossing points
is disjoint from at least one of the two original closed sets. -/
theorem component_compl_crossingPoints_disjoint {X : Type u} [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [LinearContinuum X] {A B V : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (choose : (W : CrossingComponent A B) → (W : Set X))
    (hV : IsConnectedComponentIn (crossingComponentPoints A B choose)ᶜ V) :
    Disjoint V A ∨ Disjoint V B := by
  -- If both intersections were nonempty, order-convexity would trap a selected point in `V`.
  by_cases hVA : Disjoint V A
  · exact Or.inl hVA
  · right
    by_contra hVB
    obtain ⟨a, haV, haA⟩ := not_disjoint_iff.mp hVA
    obtain ⟨b, hbV, hbB⟩ := not_disjoint_iff.mp hVB
    obtain ⟨W, hWSubset⟩ :=
      exists_crossingComponent_subset_uIcc hA hB hAB haA hbB
    have hIntervalSubset : uIcc a b ⊆ V :=
      hV.isConnected.isPreconnected.ordConnected.uIcc_subset haV hbV
    have hChosenInterval : (choose W : X) ∈ uIcc a b :=
      hWSubset (choose W).property
    have hChosenV : (choose W : X) ∈ V := hIntervalSubset hChosenInterval
    have hChosenSelected : (choose W : X) ∈ crossingComponentPoints A B choose :=
      mem_crossingComponentPoints.mpr ⟨W, rfl⟩
    exact hV.subset hChosenV hChosenSelected

end Set

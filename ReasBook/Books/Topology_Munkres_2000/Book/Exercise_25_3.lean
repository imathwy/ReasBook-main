module

public import Topology_Munkres_2000.Book.Example_24_6
public import Topology_Munkres_2000.Book.Definition_25_4.Neighborhoods
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Bases

public section

namespace OrderedSquare

/-- Helper for Exercise 25.3: the canonical parametrization of a vertical fiber. -/
def verticalMap (x : unitInterval) : unitInterval → OrderedSquare :=
  fun y ↦ toLex (x, y)

/-- Helper for Exercise 25.3: `1 / 2` lies in the real unit interval. -/
lemma unitIntervalMidpoint_mem : (1 / 2 : ℝ) ∈ Set.Icc 0 1 := by
  norm_num

/-- Helper for Exercise 25.3: the midpoint of the unit interval. -/
noncomputable def unitIntervalMidpoint : unitInterval :=
  ⟨1 / 2, unitIntervalMidpoint_mem⟩

/-- Helper for Exercise 25.3: the unit-interval midpoint is positive. -/
lemma unitIntervalMidpoint_pos : (⊥ : unitInterval) < unitIntervalMidpoint := by
  apply Subtype.mk_lt_mk.mpr
  norm_num [unitIntervalMidpoint]

/-- Helper for Exercise 25.3: the unit-interval midpoint is less than one. -/
lemma unitIntervalMidpoint_lt_top : unitIntervalMidpoint < (⊤ : unitInterval) := by
  apply Subtype.mk_lt_mk.mpr
  norm_num [unitIntervalMidpoint]

/-- Helper for Exercise 25.3: a vertical fiber is a closed interval in the lexicographic order. -/
lemma verticalFiber_eq_Icc (x : unitInterval) :
    {q : OrderedSquare | q.1 = x} =
      @Set.Icc OrderedSquare instLinearOrder.toPreorder (x, ⊥) (x, ⊤) := by
  -- Compare both endpoints lexicographically; only the first coordinate can be fixed both ways.
  ext q
  constructor
  · intro hq
    subst x
    constructor
    · change ((toLex (q.1, ⊥) : LexUnitSquare) ≤ q)
      exact Prod.Lex.le_iff.mpr (Or.inr ⟨rfl, bot_le⟩)
    · change (q ≤ (toLex (q.1, ⊤) : LexUnitSquare))
      exact Prod.Lex.le_iff.mpr (Or.inr ⟨rfl, le_top⟩)
  · rintro ⟨hq_lower, hq_upper⟩
    change ((toLex (x, ⊥) : LexUnitSquare) ≤ q) at hq_lower
    change (q ≤ (toLex (x, ⊤) : LexUnitSquare)) at hq_upper
    have hq_lower' := Prod.Lex.le_iff.mp hq_lower
    have hq_upper' := Prod.Lex.le_iff.mp hq_upper
    rcases hq_lower' with hq_lower | ⟨hq, _⟩
    · rcases hq_upper' with hq_upper | ⟨hq, _⟩
      · exact (hq_lower.trans hq_upper).false.elim
      · exact hq
    · exact hq.symm

/-- Helper for Exercise 25.3: the open vertical fiber is a lexicographic open interval. -/
lemma verticalFiberInterior_eq_Ioo (x : unitInterval) :
    {q : OrderedSquare | q.1 = x ∧ q.2 ∈ Set.Ioo (⊥ : unitInterval) ⊤} =
      @Set.Ioo OrderedSquare instLinearOrder.toPreorder
        (verticalMap x ⊥) (verticalMap x ⊤) := by
  -- Strict lexicographic comparison fixes the first coordinate and bounds the second.
  ext q
  constructor
  · rintro ⟨hq_first, hq_second⟩
    subst x
    constructor
    · change (toLex (q.1, ⊥) : LexUnitSquare) < q
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hq_second.1⟩)
    · change q < (toLex (q.1, ⊤) : LexUnitSquare)
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hq_second.2⟩)
  · rintro ⟨hq_lower, hq_upper⟩
    change (toLex (x, ⊥) : LexUnitSquare) < q at hq_lower
    change q < (toLex (x, ⊤) : LexUnitSquare) at hq_upper
    have hq_lower' := Prod.Lex.lt_iff.mp hq_lower
    have hq_upper' := Prod.Lex.lt_iff.mp hq_upper
    rcases hq_lower' with hq_lower | ⟨hq_first, hq_second_lower⟩
    · rcases hq_upper' with hq_upper | ⟨hq_first, hq_second_upper⟩
      · exact (hq_lower.trans hq_upper).false.elim
      · exact (hq_lower.trans_eq hq_first).false.elim
    · rcases hq_upper' with hq_upper | ⟨_, hq_second_upper⟩
      · exact (hq_first.trans_lt hq_upper).false.elim
      · exact ⟨hq_first.symm, hq_second_lower, hq_second_upper⟩

/-- Helper for Exercise 25.3: the vertical-coordinate map has exactly the chosen fiber as range. -/
lemma range_verticalMap (x : unitInterval) :
    Set.range (verticalMap x) =
      {q : OrderedSquare | q.1 = x} := by
  -- A point is in the range precisely when its first coordinate is `x`.
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hq
    exact ⟨q.2, Prod.ext hq.symm rfl⟩

/-- Helper for Exercise 25.3: every vertical fiber of the ordered square is path connected. -/
lemma verticalFiber_isPathConnected (x : unitInterval) :
    IsPathConnected {q : OrderedSquare | q.1 = x} := by
  -- Embed the ordinary unit interval as the vertical lexicographic interval.
  have hstrict : StrictMono (verticalMap x) := by
    intro y z hyz
    unfold verticalMap
    exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, hyz⟩)
  have hrange : @Set.OrdConnected OrderedSquare instLinearOrder.toPreorder
      (Set.range (verticalMap x)) := by
    rw [range_verticalMap, verticalFiber_eq_Icc]
    exact @Set.ordConnected_Icc OrderedSquare instLinearOrder.toPreorder _ _
  have hcontinuous : Continuous (verticalMap x) :=
    (hstrict.isEmbedding_of_ordConnected hrange).continuous
  have hunit : IsPathConnected (Set.univ : Set unitInterval) := by
    have hreal : IsPathConnected (Set.Icc (0 : ℝ) 1) :=
      Convex.isPathConnected (convex_Icc (0 : ℝ) 1) ⟨0, ⟨le_rfl, zero_le_one⟩⟩
    letI : PathConnectedSpace unitInterval := isPathConnected_iff_pathConnectedSpace.mp hreal
    exact isPathConnected_univ
  -- Continuous images preserve path connectedness, and the image is the fiber.
  simpa only [Set.image_univ, range_verticalMap] using hunit.image hcontinuous

/-- Helper for Exercise 25.3: joined points cannot have strictly increasing first coordinates. -/
lemma not_joined_of_first_lt {p q : OrderedSquare} (hpq : p.1 < q.1) : ¬Joined p q := by
  -- A joining path would meet every intermediate vertical fiber.
  intro hpq_joined
  classical
  let γ : Path p q := hpq_joined.somePath
  let xUnit (x : Set.Ioo (p.1 : ℝ) q.1) : unitInterval :=
    ⟨x, ⟨p.1.property.1.trans x.property.1.le, x.property.2.le.trans q.1.property.2⟩⟩
  let slice (x : Set.Ioo (p.1 : ℝ) q.1) : Set unitInterval :=
    γ ⁻¹' @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤)
  have hslice_open (x : Set.Ioo (p.1 : ℝ) q.1) : IsOpen (slice x) := by
    exact γ.continuous.isOpen_preimage _ isOpen_Ioo
  have hslice_nonempty (x : Set.Ioo (p.1 : ℝ) q.1) : (slice x).Nonempty := by
    have hp_range : p ∈ Set.range γ := ⟨0, γ.source⟩
    have hq_range : q ∈ Set.range γ := ⟨1, γ.target⟩
    have hmid_lower : p ≤ verticalMap (xUnit x) unitIntervalMidpoint := by
      change p ≤ (toLex (xUnit x, unitIntervalMidpoint) : LexUnitSquare)
      exact Prod.Lex.le_iff.mpr (Or.inl x.property.1)
    have hmid_upper : verticalMap (xUnit x) unitIntervalMidpoint ≤ q := by
      change (toLex (xUnit x, unitIntervalMidpoint) : LexUnitSquare) ≤ q
      exact Prod.Lex.le_iff.mpr (Or.inl x.property.2)
    have hmid_range : verticalMap (xUnit x) unitIntervalMidpoint ∈ Set.range γ :=
      (isPreconnected_range γ.continuous).Icc_subset hp_range hq_range ⟨hmid_lower, hmid_upper⟩
    obtain ⟨t, ht⟩ := hmid_range
    refine ⟨t, ?_⟩
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤)
    rw [ht]
    constructor
    · unfold verticalMap
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, unitIntervalMidpoint_pos⟩)
    · unfold verticalMap
      exact Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, unitIntervalMidpoint_lt_top⟩)
  have hslice_disjoint : Pairwise (Function.onFun Disjoint slice) := by
    intro x y hxy
    unfold Function.onFun
    rw [Set.disjoint_left]
    intro t htx hty
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit x) ⊥) (verticalMap (xUnit x) ⊤) at htx
    change γ t ∈ @Set.Ioo OrderedSquare instLinearOrder.toPreorder
      (verticalMap (xUnit y) ⊥) (verticalMap (xUnit y) ⊤) at hty
    rw [← verticalFiberInterior_eq_Ioo] at htx hty
    apply hxy
    exact @Subtype.ext ℝ (fun z ↦ z ∈ Set.Ioo (p.1 : ℝ) q.1) x y
      (congrArg (fun z : unitInterval ↦ (z : ℝ)) (htx.1.symm.trans hty.1))
  have hcountable : Countable (Set.Ioo (p.1 : ℝ) q.1) :=
    hslice_disjoint.countable_of_isOpen_disjoint hslice_open hslice_nonempty
  have hreal_countable : (Set.Ioo (p.1 : ℝ) q.1).Countable :=
    Set.countable_coe_iff.mp hcountable
  exact (not_le_of_gt hpq) ((Cardinal.Real.Ioo_countable_iff).mp hreal_countable)

/-- Helper for Exercise 25.3: joined points have equal first coordinates. -/
lemma Joined.first_eq {p q : OrderedSquare} (hpq : Joined p q) : p.1 = q.1 := by
  -- Either strict orientation contradicts the disjoint-open-slice argument.
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq_first | hqp_first
  · exact not_joined_of_first_lt hpq_first hpq
  · exact not_joined_of_first_lt hqp_first hpq.symm

/-- For Exercise 25.3, the ordered square is locally connected. -/
instance instLocallyConnectedSpace : LocallyConnectedSpace OrderedSquare :=
  locallyConnectedSpace_iff_connected_subsets.2 fun p U hU ↦ by
    -- Closed order intervals form connected neighborhoods in a linear continuum.
    obtain ⟨a, b, hp, hab_nhds, habU⟩ := exists_Icc_mem_subset_of_mem_nhds hU
    exact ⟨Set.Icc a b, hab_nhds,
      LinearContinuum.isConnected_of_ordConnected Set.ordConnected_Icc ⟨p, hp⟩ |>.isPreconnected,
      habU⟩

/-- For Exercise 25.3, the ordered square is not locally path connected. -/
theorem notLocallyPathConnected : ¬LocallyPathConnectedSpace OrderedSquare := by
  -- Connectedness plus local path connectedness would make the whole ordered square path connected.
  intro h
  letI : LocallyPathConnectedSpace OrderedSquare := h
  letI : PathConnectedSpace OrderedSquare := PathConnectedSpace.of_locallyPathConnectedSpace
  exact OrderedSquare.notPathPreconnected inferInstance

/-- Exercise 25.3 (3): The path component of a point in the ordered square is the
vertical fiber through that point. -/
theorem pathComponent_eq_fiber (p : OrderedSquare) :
    pathComponent p = {q : OrderedSquare | q.1 = p.1} := by
  -- Joined points stay in one fiber, while each fiber is itself path connected.
  ext q
  constructor
  · intro hq
    exact (Joined.first_eq ((_root_.mem_pathComponent_iff).mp hq)).symm
  · intro hq
    exact (verticalFiber_isPathConnected p.1).subset_pathComponent rfl hq

/-- Two points of the ordered square lie in the same path component exactly when
they have the same first coordinate. -/
theorem mem_pathComponent_iff (p q : OrderedSquare) :
    q ∈ pathComponent p ↔ q.1 = p.1 := by
  rw [pathComponent_eq_fiber]
  rfl

end OrderedSquare

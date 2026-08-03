module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty
public import Topology_Munkres_2000.Book.Example_3_11
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Tactic.Linarith

public section

open Prod.Lex

universe u v

/-- Helper for Exercise 3.15: an inhabited order-connected subtype of a
conditionally complete linear order has the least upper bound property. -/
lemma ordConnectedSubtype_leastUpperBoundProperty {α : Type u}
    [ConditionallyCompleteLinearOrder α] {s : Set α} [Set.OrdConnected s]
    [Inhabited s] : LeastUpperBoundProperty s := by
  -- The order-connected subtype already carries the required conditional completion.
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro t ht hb
  exact ⟨sSup t, isLUB_csSup ht hb⟩

/-- Helper for Exercise 3.15: a lexicographic product inherits the least upper
bound property when its second factor is bounded. -/
lemma Prod.Lex.leastUpperBoundProperty_of_boundedSecond
    {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    [BoundedOrder β] (hα : LeastUpperBoundProperty α)
    (hβ : LeastUpperBoundProperty β) : LeastUpperBoundProperty (α ×ₗ β) := by
  -- First take the least upper bound of the first-coordinate projection.
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro s hs hb
  classical
  let firstCoordinates : Set α := (fun p : α ×ₗ β ↦ (ofLex p).1) '' s
  have hFirstNonempty : firstCoordinates.Nonempty := hs.image _
  obtain ⟨upper, hUpper⟩ := hb
  have hFirstBounded : BddAbove firstCoordinates := by
    refine ⟨(ofLex upper).1, ?_⟩
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact monotone_fst p upper (hUpper hp)
  obtain ⟨a, ha⟩ := hα.exists_isLUB firstCoordinates hFirstNonempty hFirstBounded
  by_cases hAttained : ∃ p ∈ s, (ofLex p).1 = a
  · -- If the first-coordinate supremum is attained, take the supremum of that fiber.
    let fiber : Set β :=
      {b | ∃ q ∈ s, (ofLex q).1 = a ∧ (ofLex q).2 = b}
    obtain ⟨p, hp, hpFirst⟩ := hAttained
    have hpFiber : (ofLex p).2 ∈ fiber := by
      exact ⟨p, hp, hpFirst, rfl⟩
    have hFiberNonempty : fiber.Nonempty := ⟨(ofLex p).2, hpFiber⟩
    have hFiberBounded : BddAbove fiber := ⟨⊤, fun _ _ ↦ le_top⟩
    obtain ⟨b, hbFiber⟩ := hβ.exists_isLUB fiber hFiberNonempty hFiberBounded
    refine ⟨toLex (a, b), ?_⟩
    constructor
    · intro q hq
      have hqFirst : (ofLex q).1 ≤ a := ha.1 ⟨q, hq, rfl⟩
      rcases hqFirst.eq_or_lt with hEq | hLt
      · apply le_iff.mpr
        right
        refine ⟨hEq, ?_⟩
        have hqFiber : (ofLex q).2 ∈ fiber := by
          exact ⟨q, hq, hEq, rfl⟩
        exact hbFiber.1 hqFiber
      · exact le_iff.mpr (Or.inl hLt)
    · intro c hc
      have hp_le_c : p ≤ c := hc hp
      have ha_le_cFirst : a ≤ (ofLex c).1 := by
        simpa [hpFirst] using monotone_fst p c hp_le_c
      rcases ha_le_cFirst.eq_or_lt with hEq | hLt
      · apply le_iff.mpr
        right
        refine ⟨hEq, ?_⟩
        apply hbFiber.2
        intro d hd
        obtain ⟨q, hq, hqFirst, hqSecond⟩ := hd
        have hqc : q ≤ c := hc hq
        have hNotFirstLt : ¬ (ofLex q).1 < (ofLex c).1 := by
          rw [hqFirst, ← hEq]
          exact lt_irrefl a
        have hSecond : (ofLex q).2 ≤ (ofLex c).2 :=
          (le_iff.mp hqc).resolve_left hNotFirstLt |>.2
        simpa [hqSecond] using hSecond
      · exact le_iff.mpr (Or.inl hLt)
  · -- Otherwise `(a, ⊥)` is the least upper bound because equality is never attained.
    refine ⟨toLex (a, ⊥), ?_⟩
    constructor
    · intro p hp
      have hpFirst : (ofLex p).1 ≤ a := ha.1 ⟨p, hp, rfl⟩
      have hpFirstNe : (ofLex p).1 ≠ a := fun h ↦ hAttained ⟨p, hp, h⟩
      exact le_iff.mpr (Or.inl (lt_of_le_of_ne hpFirst hpFirstNe))
    · intro c hc
      have hcFirstUpper : (ofLex c).1 ∈ upperBounds firstCoordinates := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := hx
        exact monotone_fst p c (hc hp)
      have ha_le_cFirst : a ≤ (ofLex c).1 := ha.2 hcFirstUpper
      exact le_iff'.mpr ⟨ha_le_cFirst, fun _ ↦ bot_le⟩

/-- Helper for Exercise 3.15: every point of `[0, 1)` has a strictly larger
point in the same interval. -/
lemma halfOpenUnitInterval_exists_gt (y : Set.Ico (0 : ℝ) 1) :
    ∃ z : Set.Ico (0 : ℝ) 1, y < z := by
  -- The midpoint of `y` and the omitted endpoint lies strictly between them.
  have hmem : (y.1 + 1) / 2 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · linarith [y.property.1]
    · linarith [y.property.2]
  let z : Set.Ico (0 : ℝ) 1 := ⟨(y.1 + 1) / 2, hmem⟩
  refine ⟨z, ?_⟩
  have hy_lt_z : y.1 < (y.1 + 1) / 2 := by
    linarith [y.property.2]
  exact Subtype.mk_lt_mk.mpr hy_lt_z

/-- Helper for Exercise 3.15: the vertical fiber over zero in
`[0, 1] ×ₗ [0, 1)` has no least upper bound. -/
lemma verticalHalfOpenFiber_no_isLUB :
    ¬ ∃ a : Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1,
      IsLUB {p | (ofLex p).1.1 = 0} a := by
  -- Increase a candidate over zero vertically; lower a positive candidate horizontally.
  rintro ⟨a, ha⟩
  have hzeroClosed : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hzeroHalfOpen : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
  let zeroClosed : Set.Icc (0 : ℝ) 1 := ⟨0, hzeroClosed⟩
  let zeroHalfOpen : Set.Ico (0 : ℝ) 1 := ⟨0, hzeroHalfOpen⟩
  by_cases hFirstZero : (ofLex a).1.1 = 0
  · obtain ⟨z, hz⟩ := halfOpenUnitInterval_exists_gt (ofLex a).2
    let p : Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1 := toLex (zeroClosed, z)
    have hpMem : p ∈ {q | (ofLex q).1.1 = 0} := by
      exact rfl
    have ha_lt_p : a < p := by
      apply lt_iff.mpr
      right
      exact ⟨Subtype.ext hFirstZero, hz⟩
    exact (not_le_of_gt ha_lt_p) (ha.1 hpMem)
  · have hFirstPositive : 0 < (ofLex a).1.1 := by
      exact lt_of_le_of_ne (ofLex a).1.property.1 (Ne.symm hFirstZero)
    have hhalfClosed : (ofLex a).1.1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [(ofLex a).1.property.2]
    let halfFirst : Set.Icc (0 : ℝ) 1 := ⟨(ofLex a).1.1 / 2, hhalfClosed⟩
    let c : Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1 :=
      toLex (halfFirst, zeroHalfOpen)
    have hcUpper : c ∈ upperBounds {q | (ofLex q).1.1 = 0} := by
      intro q hq
      apply le_iff.mpr
      left
      have hqFirst : (ofLex q).1.1 = 0 := hq
      have hq_lt_half : (ofLex q).1.1 < (ofLex a).1.1 / 2 := by
        rw [hqFirst]
        exact half_pos hFirstPositive
      exact Subtype.mk_lt_mk.mpr hq_lt_half
    have hc_lt_a : c < a := by
      apply lt_iff.mpr
      left
      have hhalf_lt : (ofLex a).1.1 / 2 < (ofLex a).1.1 := by
        linarith
      exact Subtype.mk_lt_mk.mpr hhalf_lt
    exact (not_le_of_gt hc_lt_a) (ha.2 hcUpper)

/-- Part (1) of Exercise 3.15: The closed interval `[0, 1]` has the least upper bound
property. -/
theorem closedUnitInterval_leastUpperBoundProperty :
    LeastUpperBoundProperty (Set.Icc (0 : ℝ) 1) := by
  -- The closed interval is inhabited and order-connected.
  have hzero_le_one : (0 : ℝ) ≤ 1 := by norm_num
  let zeroClosed : Set.Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, hzero_le_one⟩⟩
  letI : Inhabited (Set.Icc (0 : ℝ) 1) := ⟨zeroClosed⟩
  exact ordConnectedSubtype_leastUpperBoundProperty
    (s := Set.Icc (0 : ℝ) 1)

/-- Part (2) of Exercise 3.15: The half-open interval `[0, 1)` has the least upper bound
property. -/
theorem halfOpenUnitInterval_leastUpperBoundProperty :
    LeastUpperBoundProperty (Set.Ico (0 : ℝ) 1) := by
  -- The half-open interval is inhabited and order-connected.
  have hzero_lt_one : (0 : ℝ) < 1 := by norm_num
  let zeroHalfOpen : Set.Ico (0 : ℝ) 1 := ⟨0, ⟨le_rfl, hzero_lt_one⟩⟩
  letI : Inhabited (Set.Ico (0 : ℝ) 1) := ⟨zeroHalfOpen⟩
  exact ordConnectedSubtype_leastUpperBoundProperty
    (s := Set.Ico (0 : ℝ) 1)

/-- Part (3) of Exercise 3.15: The dictionary-ordered product `[0, 1] ×ₗ [0, 1]` has the
least upper bound property. -/
theorem lexClosedClosed_leastUpperBoundProperty :
    LeastUpperBoundProperty
      (Set.Icc (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1) := by
  -- Apply the general lexicographic theorem with the bounded closed interval second.
  have hzero_le_one : (0 : ℝ) ≤ 1 := by norm_num
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨hzero_le_one⟩
  exact Prod.Lex.leastUpperBoundProperty_of_boundedSecond
    closedUnitInterval_leastUpperBoundProperty
    closedUnitInterval_leastUpperBoundProperty

/-- Part (4) of Exercise 3.15: The dictionary-ordered product `[0, 1] ×ₗ [0, 1)` does
not have the least upper bound property. -/
theorem lexClosedHalfOpen_not_leastUpperBoundProperty :
    ¬ LeastUpperBoundProperty
      (Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1) := by
  -- The bounded nonempty vertical fiber would have a least upper bound, contradicting the helper.
  intro h
  have hzeroClosed : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have honeClosed : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hzeroHalfOpen : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
  let zeroClosed : Set.Icc (0 : ℝ) 1 := ⟨0, hzeroClosed⟩
  let oneClosed : Set.Icc (0 : ℝ) 1 := ⟨1, honeClosed⟩
  let zeroHalfOpen : Set.Ico (0 : ℝ) 1 := ⟨0, hzeroHalfOpen⟩
  let p : Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1 :=
    toLex (zeroClosed, zeroHalfOpen)
  let upper : Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1 :=
    toLex (oneClosed, zeroHalfOpen)
  have hpMem : p ∈ {q | (ofLex q).1.1 = 0} := by exact rfl
  have hNonempty : ({q | (ofLex q).1.1 = 0} :
      Set (Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1)).Nonempty := ⟨p, hpMem⟩
  have hBounded : BddAbove ({q | (ofLex q).1.1 = 0} :
      Set (Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1)) := by
    refine ⟨upper, ?_⟩
    intro q hq
    apply le_iff.mpr
    left
    have hqFirst : (ofLex q).1.1 = 0 := hq
    have hq_lt_one : (ofLex q).1.1 < 1 := by
      rw [hqFirst]
      norm_num
    exact Subtype.mk_lt_mk.mpr hq_lt_one
  obtain ⟨a, ha⟩ := h.exists_isLUB _ hNonempty hBounded
  exact verticalHalfOpenFiber_no_isLUB ⟨a, ha⟩

/-- Part (5) of Exercise 3.15: The dictionary-ordered product `[0, 1) ×ₗ [0, 1]` has the
least upper bound property. -/
theorem lexHalfOpenClosed_leastUpperBoundProperty :
    LeastUpperBoundProperty
      (Set.Ico (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1) := by
  -- Only the second coordinate needs bounded endpoints in the general theorem.
  have hzero_le_one : (0 : ℝ) ≤ 1 := by norm_num
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨hzero_le_one⟩
  exact Prod.Lex.leastUpperBoundProperty_of_boundedSecond
    halfOpenUnitInterval_leastUpperBoundProperty
    closedUnitInterval_leastUpperBoundProperty

/-- Exercise 3.15: The least-upper-bound classifications of the
two unit intervals and their three dictionary-ordered products. -/
theorem «Exercise 3.15 theorem suite» :
    LeastUpperBoundProperty (Set.Icc (0 : ℝ) 1) ∧
      LeastUpperBoundProperty (Set.Ico (0 : ℝ) 1) ∧
      LeastUpperBoundProperty
        (Set.Icc (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1) ∧
      ¬ LeastUpperBoundProperty
        (Set.Icc (0 : ℝ) 1 ×ₗ Set.Ico (0 : ℝ) 1) ∧
      LeastUpperBoundProperty
        (Set.Ico (0 : ℝ) 1 ×ₗ Set.Icc (0 : ℝ) 1) := by
  -- Package the interval and dictionary-order classifications proved above.
  exact ⟨closedUnitInterval_leastUpperBoundProperty,
    halfOpenUnitInterval_leastUpperBoundProperty,
    lexClosedClosed_leastUpperBoundProperty,
    lexClosedHalfOpen_not_leastUpperBoundProperty,
    lexHalfOpenClosed_leastUpperBoundProperty⟩

module

public import Topology_Munkres_2000.Book.Definition_10_4.MinimalOrder
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.Interval.Set.InitialSeg
public import Mathlib.Order.SuccPred.InitialSeg

public section

open scoped Ordinal

universe u

namespace OpenOmegaOne

/-- Helper for Exercise 10.6: every closed initial interval in `OpenOmegaOne` is countable. -/
lemma countableIic (α : OpenOmegaOne.{u}) : (Set.Iic α).Countable := by
  -- Add the endpoint to the countable strict initial interval.
  rw [← Set.Iio_insert]
  exact (inferInstance : Countable (Set.Iio α)).to_set.insert α

/-- Part (1) of Exercise 10.6: The minimal uncountable well-ordered set `S_Ω`
has no largest element. -/
instance instNoMaxOrder : NoMaxOrder (OpenOmegaOne.{u}) := by
  refine ⟨fun α ↦ ?_⟩
  -- A largest point would make the whole carrier a countable initial interval.
  by_contra hGreater
  have hUniv : (Set.univ : Set OpenOmegaOne).Countable :=
    (countableIic α).mono fun x _ ↦ le_of_not_gt fun hαx ↦ hGreater ⟨x, hαx⟩
  exact Set.not_countable_univ hUniv

/-- Part (2) of Exercise 10.6: For every `α ∈ S_Ω`, the strict upper tail
`{x | α < x}` is uncountable. -/
instance instUncountableIoi (α : OpenOmegaOne.{u}) : Uncountable (Set.Ioi α) := by
  apply not_countable_iff.mp
  intro hTail
  -- The lower closed interval and upper open interval cover the carrier.
  have hUniv := (countableIic α).union hTail.to_set
  rw [Set.Iic_union_Ioi] at hUniv
  exact Set.not_countable_univ hUniv

/-- Helper for Exercise 10.6: every countable set of countable ordinals is bounded above. -/
lemma countableSet_bddAbove {s : Set OpenOmegaOne.{u}} (hs : s.Countable) : BddAbove s := by
  classical
  -- The empty set is bounded; otherwise enumerate the subtype by natural numbers.
  by_cases hsNonempty : s.Nonempty
  · obtain ⟨x, hx⟩ := hsNonempty
    letI : Countable s := hs
    letI : Nonempty s := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := exists_surjective_nat s
    let g : ℕ → Ordinal := fun n ↦ f n
    have hSupMem : (⨆ n, g n) < (ω₁ : Ordinal) := by
      apply Ordinal.iSup_lt_omega_one
      intro n
      exact (f n).1.property
    let β : OpenOmegaOne := ⟨⨆ n, g n, hSupMem⟩
    refine ⟨β, ?_⟩
    intro y hy
    obtain ⟨n, hn⟩ := hf ⟨y, hy⟩
    have hle : g n ≤ ⨆ m, g m := Ordinal.le_iSup g n
    change (y : Ordinal) ≤ ⨆ m, g m
    simpa [g, hn] using hle
  · rw [Set.not_nonempty_iff_eq_empty.mp hsNonempty]
    exact bddAbove_empty

/-- Helper for Exercise 10.6: successor-prelimit points are cofinal in `OpenOmegaOne`. -/
lemma exists_gt_isSuccPrelimit (α : OpenOmegaOne.{u}) :
    ∃ β : OpenOmegaOne.{u}, α < β ∧ Order.IsSuccPrelimit β := by
  -- The ordinal `α + ω` is still countable.
  have hαCard : (α : Ordinal).card ≤ Cardinal.aleph0 :=
    (CountableOrdinal.mem_iff_card_le_aleph0 (α : Ordinal)).mp α.property
  have hSumCard : ((α : Ordinal) + ω).card ≤ Cardinal.aleph0 := by
    rw [Ordinal.card_add, Cardinal.add_le_aleph0, Ordinal.card_omega0]
    exact ⟨hαCard, le_rfl⟩
  have hSumMem : (α : Ordinal) + ω < (ω₁ : Ordinal) :=
    (CountableOrdinal.mem_iff_card_le_aleph0 ((α : Ordinal) + ω)).mpr hSumCard
  let β : OpenOmegaOne := ⟨(α : Ordinal) + ω, hSumMem⟩
  have hαβ : α < β := by
    change (α : Ordinal) < (α : Ordinal) + ω
    exact lt_add_of_pos_right (α : Ordinal) Ordinal.omega0_pos
  -- The principal-segment embedding reflects the successor-prelimit property.
  have hOrdinalPrelimit : Order.IsSuccPrelimit ((α : Ordinal) + ω) :=
    (Ordinal.isSuccLimit_add (α : Ordinal) Ordinal.isSuccLimit_omega0).isSuccPrelimit
  have hImagePrelimit :
      Order.IsSuccPrelimit ((Set.principalSegIio (ω₁ : Ordinal)) β) := by
    simpa [β] using hOrdinalPrelimit
  have hβPrelimit : Order.IsSuccPrelimit β :=
    (Set.principalSegIio (ω₁ : Ordinal)).isSuccPrelimit_apply_iff.mp hImagePrelimit
  exact ⟨β, hαβ, hβPrelimit⟩

/-- Exercise 10.6 (3): The subset of `S_Ω` consisting of elements with no
immediate predecessor is uncountable. -/
instance instSuccPrelimitsUncountable :
    Uncountable {x : OpenOmegaOne.{u} // Order.IsSuccPrelimit x} := by
  apply not_countable_iff.mp
  intro hCountable
  -- A countable family of prelimit points has an upper bound.
  have hBound : BddAbove {x : OpenOmegaOne | Order.IsSuccPrelimit x} :=
    countableSet_bddAbove hCountable.to_set
  obtain ⟨α, hα⟩ := hBound
  -- Cofinality supplies a prelimit point strictly above that bound.
  obtain ⟨β, hαβ, hβ⟩ := exists_gt_isSuccPrelimit α
  exact (not_lt_of_ge (hα hβ)) hαβ

end OpenOmegaOne

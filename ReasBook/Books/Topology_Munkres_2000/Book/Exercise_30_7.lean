module

import Topology_Munkres_2000.Book.Exercise_10_6
import Mathlib.Topology.Order.SuccPred

public import Topology_Munkres_2000.Book.Exercise_29_7.Compactification
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.Lindelof

public section

open scoped Ordinal

/-- Helper for Exercise 30.7: a successor-ordered space with countable strict
initial sections is first-countable. -/
private lemma firstCountableTopology_of_countable_Iio
    {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [SuccOrder α] [NoMaxOrder α] (hCountable : ∀ a : α, (Set.Iio a).Countable) :
    FirstCountableTopology α := by
  refine ⟨fun a ↦ ?_⟩
  -- At a minimum the neighborhood filter is principal; otherwise use lower endpoints below `a`.
  by_cases ha : IsMin a
  · rw [SuccOrder.nhds_of_isMin ha]
    exact Filter.isCountablyGenerated_pure a
  · have hLower : ∃ b, b < a := not_isMin_iff.mp ha
    exact Filter.HasCountableBasis.isCountablyGenerated
      ⟨SuccOrder.hasBasis_nhds_Ioc_of_exists_lt hLower, hCountable a⟩

/-- Helper for Exercise 30.7: no countable subset of `OpenOmegaOne` is dense. -/
private lemma OpenOmegaOne.noCountableDenseSet {s : Set OpenOmegaOne}
    (hs : s.Countable) : ¬ Dense s := by
  intro hDense
  -- Bound the countable set, then test density against the nonempty open tail above the bound.
  obtain ⟨a, ha⟩ := OpenOmegaOne.countableSet_bddAbove hs
  obtain ⟨b, hab⟩ := exists_gt a
  obtain ⟨x, hax, hxs⟩ :=
    hDense.inter_open_nonempty (Set.Ioi a) isOpen_Ioi ⟨b, hab⟩
  exact (not_lt_of_ge (ha hxs)) hax

/-- Helper for Exercise 30.7: every sequence strictly below
`ClosedOmegaOne.omega` has a common strict upper bound below the endpoint. -/
private lemma ClosedOmegaOne.exists_lt_omega_above_nat
    (b : ℕ → ClosedOmegaOne) (hb : ∀ n, b n < ClosedOmegaOne.omega) :
    ∃ x, (∀ n, b n < x) ∧ x < ClosedOmegaOne.omega := by
  -- Regard the sequence as countable ordinals and bound its range in `OpenOmegaOne`.
  have hBelow (n : ℕ) : (b n : Ordinal) < (ω₁ : Ordinal) := by
    have hOrdinal : (b n : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := hb n
    rwa [ClosedOmegaOne.coe_omega] at hOrdinal
  let c : ℕ → OpenOmegaOne := fun n ↦ ⟨b n, hBelow n⟩
  obtain ⟨a, ha⟩ :=
    OpenOmegaOne.countableSet_bddAbove (Set.countable_range c)
  obtain ⟨d, had⟩ := exists_gt a
  refine ⟨OpenOmegaOne.toClosed d, ?_, ?_⟩
  · intro n
    have hcnd : c n < d := lt_of_le_of_lt (ha (Set.mem_range_self n)) had
    have hcOrdinal : (c n : Ordinal) < (d : Ordinal) := hcnd
    have hOrdinal : (b n : Ordinal) < (d : Ordinal) := by
      simpa only [c] using hcOrdinal
    have hTarget :
        (b n : Ordinal) < (OpenOmegaOne.toClosed d : Ordinal) := by
      rwa [OpenOmegaOne.coe_toClosed]
    exact hTarget
  · have hOrdinal : (d : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rw [ClosedOmegaOne.coe_omega]
      exact d.property
    have hTarget :
        (OpenOmegaOne.toClosed d : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rwa [OpenOmegaOne.coe_toClosed]
    exact hTarget

/-- Helper for Exercise 30.7: every open neighborhood of
`ClosedOmegaOne.omega` contains a terminal interval. -/
private lemma ClosedOmegaOne.exists_Ioc_omega_subset_of_isOpen
    {U : Set ClosedOmegaOne} (hU : IsOpen U) (hOmega : ClosedOmegaOne.omega ∈ U) :
    ∃ b, b < ClosedOmegaOne.omega ∧ Set.Ioc b ClosedOmegaOne.omega ⊆ U := by
  -- Lift the subtype neighborhood to `Ordinal` and choose an interval there.
  obtain ⟨V, hV, hVSubset⟩ :=
    (mem_nhds_subtype (Set.Iic (ω₁ : Ordinal)) ClosedOmegaOne.omega U).mp
      (hU.mem_nhds hOmega)
  have hZeroOmega : (0 : Ordinal) < ω₁ := Ordinal.omega_pos 1
  obtain ⟨a, haOmega, haV⟩ :=
    exists_Ioc_subset_of_mem_nhds hV ⟨0, hZeroOmega⟩
  have haLeOmega : a ≤ (ω₁ : Ordinal) := le_of_lt haOmega
  let b : ClosedOmegaOne := ⟨a, haLeOmega⟩
  have hbOmega : b < ClosedOmegaOne.omega := by
    have hOrdinal : (b : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rw [ClosedOmegaOne.coe_omega]
      exact haOmega
    exact hOrdinal
  -- Pull the ordinal interval back through the subtype coercion.
  refine ⟨b, hbOmega, fun x hx ↦ hVSubset ?_⟩
  apply haV
  constructor
  · exact hx.1
  · have hxOrdinal : (x : Ordinal) ≤ (ClosedOmegaOne.omega : Ordinal) := hx.2
    rwa [ClosedOmegaOne.coe_omega] at hxOrdinal

/-- Helper for Exercise 30.7: the canonical inclusion of `OpenOmegaOne` into
`ClosedOmegaOne` is an open embedding. -/
lemma OpenOmegaOne.isOpenEmbedding_toClosed :
    Topology.IsOpenEmbedding (OpenOmegaOne.toClosed : OpenOmegaOne → ClosedOmegaOne) := by
  refine ⟨OpenOmegaOne.isEmbedding_toClosed, ?_⟩
  -- Its range is precisely the open complement of the added endpoint.
  rw [OpenOmegaOne.range_toClosed]
  exact isClosed_singleton.isOpen_compl

/-- Part (1) of Exercise 30.7: The open first-uncountable ordinal `S_Ω` is
first-countable. -/
instance OpenOmegaOne.instFirstCountableTopology :
    FirstCountableTopology OpenOmegaOne := by
  -- Apply the generic interval-basis criterion to the countable ordinal initial sections.
  exact firstCountableTopology_of_countable_Iio fun a ↦
    (inferInstance : Countable (Set.Iio a)).to_set

/-- Part (2) of Exercise 30.7: The open first-uncountable ordinal `S_Ω` is not
second-countable. -/
theorem OpenOmegaOne.notSecondCountable :
    ¬ SecondCountableTopology OpenOmegaOne := by
  intro hSecondCountable
  letI : SecondCountableTopology OpenOmegaOne := hSecondCountable
  -- A countable basis supplies a countable dense set, contradicting boundedness.
  obtain ⟨s, hs, hDense⟩ := TopologicalSpace.exists_countable_dense OpenOmegaOne
  exact OpenOmegaOne.noCountableDenseSet hs hDense

/-- Part (3) of Exercise 30.7: The open first-uncountable ordinal `S_Ω` has no
countable dense subset. -/
theorem OpenOmegaOne.notSeparable :
    ¬ TopologicalSpace.SeparableSpace OpenOmegaOne := by
  intro hSeparable
  letI : TopologicalSpace.SeparableSpace OpenOmegaOne := hSeparable
  -- Unpack separability and use the same bounded-countable-set obstruction.
  obtain ⟨s, hs, hDense⟩ := TopologicalSpace.exists_countable_dense OpenOmegaOne
  exact OpenOmegaOne.noCountableDenseSet hs hDense

/-- The open first-uncountable ordinal `S_Ω` has the canonical
non-Lindelöf typeclass instance. -/
instance OpenOmegaOne.instNonLindelofSpace :
    NonLindelofSpace OpenOmegaOne := by
  refine ⟨fun hLindelof ↦ ?_⟩
  -- The open initial intervals cover the space because it has no greatest point.
  have hCover : (Set.univ : Set OpenOmegaOne) ⊆ ⋃ a, Set.Iio a := by
    intro x _
    obtain ⟨a, hxa⟩ := exists_gt x
    exact Set.mem_iUnion.mpr ⟨a, hxa⟩
  obtain ⟨s, hs, hsCover⟩ :=
    hLindelof.elim_countable_subcover (fun a : OpenOmegaOne ↦ Set.Iio a)
      (fun _ ↦ isOpen_Iio) hCover
  -- A common upper bound of the chosen indices is omitted by every chosen interval.
  obtain ⟨b, hb⟩ := OpenOmegaOne.countableSet_bddAbove hs
  have hbCovered := hsCover (Set.mem_univ b)
  simp only [Set.mem_iUnion, Set.mem_Iio] at hbCovered
  obtain ⟨a, ha, hba⟩ := hbCovered
  exact (not_lt_of_ge (hb ha)) hba

/-- Part (4) of Exercise 30.7: The open first-uncountable ordinal `S_Ω` is not
Lindelöf. -/
theorem OpenOmegaOne.notLindelof : ¬ LindelofSpace OpenOmegaOne :=
  not_LindelofSpace_iff.mpr inferInstance

/-- Part (5) of Exercise 30.7: The closed first-uncountable ordinal `S̄_Ω` is not
first-countable. -/
theorem ClosedOmegaOne.notFirstCountable :
    ¬ FirstCountableTopology ClosedOmegaOne := by
  classical
  intro hFirstCountable
  letI : FirstCountableTopology ClosedOmegaOne := hFirstCountable
  -- Extract a countable open basis and a terminal interval inside each basis set.
  obtain ⟨U, hU, hBasis⟩ :=
    (nhds_basis_opens ClosedOmegaOne.omega).exists_antitone_subbasis
  choose b hb hSub using fun n ↦
    ClosedOmegaOne.exists_Ioc_omega_subset_of_isOpen (hU n).2 (hU n).1
  obtain ⟨x, hbx, hxOmega⟩ :=
    ClosedOmegaOne.exists_lt_omega_above_nat b hb
  -- Some basis set avoids `x`, but its chosen terminal interval contains `x`.
  have hOmegaMem : ClosedOmegaOne.omega ∈ ({x} : Set ClosedOmegaOne)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hxOmega
  have hComplNhd : ({x} : Set ClosedOmegaOne)ᶜ ∈ nhds ClosedOmegaOne.omega :=
    isClosed_singleton.isOpen_compl.mem_nhds hOmegaMem
  obtain ⟨n, hn⟩ := hBasis.mem_iff.mp hComplNhd
  have hxInterval : x ∈ Set.Ioc (b n) ClosedOmegaOne.omega :=
    ⟨hbx n, le_of_lt hxOmega⟩
  have hxx := hn (hSub n hxInterval)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hxx
  exact hxx trivial

/-- Part (6) of Exercise 30.7: The closed first-uncountable ordinal `S̄_Ω` is not
second-countable. -/
theorem ClosedOmegaOne.notSecondCountable :
    ¬ SecondCountableTopology ClosedOmegaOne := by
  intro hSecondCountable
  letI : SecondCountableTopology ClosedOmegaOne := hSecondCountable
  -- Second countability implies first countability, already ruled out at the endpoint.
  exact ClosedOmegaOne.notFirstCountable inferInstance

/-- Part (7) of Exercise 30.7: The closed first-uncountable ordinal `S̄_Ω` has no
countable dense subset. -/
theorem ClosedOmegaOne.notSeparable :
    ¬ TopologicalSpace.SeparableSpace ClosedOmegaOne := by
  intro hSeparable
  letI : TopologicalSpace.SeparableSpace ClosedOmegaOne := hSeparable
  -- Separability restricts along the open embedding to `OpenOmegaOne`.
  have hOpenSeparable : TopologicalSpace.SeparableSpace OpenOmegaOne :=
    OpenOmegaOne.isOpenEmbedding_toClosed.separableSpace
  exact OpenOmegaOne.notSeparable hOpenSeparable

/- Part (8) of Exercise 30.7: The closed first-uncountable ordinal `S̄_Ω` is
Lindelöf. -/
#check (inferInstance : LindelofSpace ClosedOmegaOne)

/-- Exercise 30.7: `S_Ω` is first-countable but is neither second-countable,
separable, nor Lindelöf, while `S̄_Ω` is Lindelöf but is neither first-countable,
second-countable, nor separable. -/
theorem «Exercise 30.7 countability classification declarations» :
    FirstCountableTopology OpenOmegaOne ∧
      ¬ SecondCountableTopology OpenOmegaOne ∧
      ¬ TopologicalSpace.SeparableSpace OpenOmegaOne ∧
      ¬ LindelofSpace OpenOmegaOne ∧
      ¬ FirstCountableTopology ClosedOmegaOne ∧
      ¬ SecondCountableTopology ClosedOmegaOne ∧
      ¬ TopologicalSpace.SeparableSpace ClosedOmegaOne ∧
      LindelofSpace ClosedOmegaOne := by
  -- Package the eight established classifications under the planner's declaration name.
  exact ⟨inferInstance, OpenOmegaOne.notSecondCountable,
    OpenOmegaOne.notSeparable, OpenOmegaOne.notLindelof,
    ClosedOmegaOne.notFirstCountable, ClosedOmegaOne.notSecondCountable,
    ClosedOmegaOne.notSeparable, inferInstance⟩

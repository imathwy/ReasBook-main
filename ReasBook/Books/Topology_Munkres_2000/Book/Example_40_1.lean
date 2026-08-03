module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Topology.Separation.GDelta

public section

open Set
open scoped Ordinal

/- Example 40.1 (1): Every open subset of a topological space is a `Gδ` set. -/
#check IsOpen.isGδ

/- Example 40.1 (2): In a first-countable Hausdorff space, every singleton is a
`Gδ` set. -/
#check fun {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [T2Space X] (x : X) ↦
  IsGδ.singleton x

/-- Helper for Example 40.1: every open neighborhood of `Ω` contains a terminal interval. -/
private lemma ClosedOmegaOne.exists_Ioc_omega_subset_of_isOpen {U : Set ClosedOmegaOne}
    (hU : IsOpen U) (hOmega : ClosedOmegaOne.omega ∈ U) :
    ∃ b, b < ClosedOmegaOne.omega ∧ Set.Ioc b ClosedOmegaOne.omega ⊆ U := by
  -- Lift the subtype neighborhood to an ordinal neighborhood of `ω₁`.
  obtain ⟨V, hV, hVSubset⟩ :=
    (mem_nhds_subtype (Set.Iic (ω₁ : Ordinal)) ClosedOmegaOne.omega U).mp
      (hU.mem_nhds hOmega)
  have hZeroOmega : (0 : Ordinal) < ω₁ := Ordinal.omega_pos 1
  obtain ⟨a, haOmega, haV⟩ := exists_Ioc_subset_of_mem_nhds hV ⟨0, hZeroOmega⟩
  have haLeOmega : a ≤ (ω₁ : Ordinal) := le_of_lt haOmega
  let b : ClosedOmegaOne := ⟨a, haLeOmega⟩
  have hbOmega : b < ClosedOmegaOne.omega := by
    have hOrdinal : (b : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rw [ClosedOmegaOne.coe_omega]
      exact haOmega
    exact hOrdinal
  -- Pull the ordinal interval back along the subtype coercion.
  refine ⟨b, hbOmega, fun x hx ↦ hVSubset ?_⟩
  apply haV
  constructor
  · exact hx.1
  · have hxOrdinal : (x : Ordinal) ≤ (ClosedOmegaOne.omega : Ordinal) := hx.2
    rwa [ClosedOmegaOne.coe_omega] at hxOrdinal

/-- Helper for Example 40.1: a sequence of points below `Ω` has a strict upper bound below `Ω`. -/
private lemma ClosedOmegaOne.exists_lt_omega_above_nat (b : ℕ → ClosedOmegaOne)
    (hb : ∀ n, b n < ClosedOmegaOne.omega) :
    ∃ x : ClosedOmegaOne, (∀ n, b n < x) ∧ x < ClosedOmegaOne.omega := by
  -- The ordinal supremum of the countable family remains countable.
  let γ : Ordinal := ⨆ n, (b n : Ordinal)
  have hγOmega : γ < (ω₁ : Ordinal) := by
    apply Ordinal.iSup_lt_omega_one
    intro n
    have hOrdinal : (b n : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := hb n
    rwa [ClosedOmegaOne.coe_omega] at hOrdinal
  have hγCard : γ.card ≤ Cardinal.aleph0 :=
    (CountableOrdinal.mem_iff_card_le_aleph0 γ).mp hγOmega
  -- Passing to the successor makes the upper bound strict while preserving countability.
  have hSuccCard : (γ + 1).card ≤ Cardinal.aleph0 := by
    rw [Ordinal.card_add_one, Cardinal.add_le_aleph0]
    exact ⟨hγCard, Cardinal.natCast_le_aleph0⟩
  have hSuccOmega : γ + 1 < (ω₁ : Ordinal) :=
    (CountableOrdinal.mem_iff_card_le_aleph0 (γ + 1)).mpr hSuccCard
  let y : OpenOmegaOne := ⟨γ + 1, hSuccOmega⟩
  let x : ClosedOmegaOne := OpenOmegaOne.toClosed y
  have hAbove : ∀ n, b n < x := by
    intro n
    change (b n : Ordinal) < γ + 1
    exact (Ordinal.le_iSup (fun m ↦ (b m : Ordinal)) n).trans_lt (lt_add_one γ)
  have hxOmega : x < ClosedOmegaOne.omega := by
    have hOrdinal : (x : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rw [ClosedOmegaOne.coe_omega]
      exact hSuccOmega
    exact hOrdinal
  exact ⟨x, hAbove, hxOmega⟩

/-- Helper for Example 40.1: a countable intersection of open neighborhoods of `Ω`
contains a point distinct from `Ω`. -/
private lemma ClosedOmegaOne.exists_mem_iInter_open_ne_omega (U : ℕ → Set ClosedOmegaOne)
    (hU : ∀ n, IsOpen (U n)) (hOmega : ∀ n, ClosedOmegaOne.omega ∈ U n) :
    ∃ x, x ∈ ⋂ n, U n ∧ x ≠ ClosedOmegaOne.omega := by
  classical
  -- Choose one terminal interval inside each open neighborhood.
  choose b hb hSubset using fun n ↦
    ClosedOmegaOne.exists_Ioc_omega_subset_of_isOpen (hU n) (hOmega n)
  -- A single point strictly above all lower endpoints lies in every chosen interval.
  obtain ⟨x, hAbove, hxOmega⟩ := ClosedOmegaOne.exists_lt_omega_above_nat b hb
  have hxU : ∀ n, x ∈ U n := by
    intro n
    exact hSubset n ⟨hAbove n, le_of_lt hxOmega⟩
  have hxInter : x ∈ ⋂ n, U n := Set.mem_iInter.mpr hxU
  have hxNe : x ≠ ClosedOmegaOne.omega := ne_of_lt hxOmega
  exact ⟨x, hxInter, hxNe⟩

/-- Example 40.1 (3): The singleton containing `Ω` in the closed first-uncountable
ordinal `S̄_Ω` is not a `Gδ` set. -/
theorem ClosedOmegaOne.singleton_omega_not_isGδ :
    ¬IsGδ ({ClosedOmegaOne.omega} : Set ClosedOmegaOne) := by
  intro hGδ
  -- Present the alleged `Gδ` singleton as a countable intersection of open sets.
  obtain ⟨U, hU, hEq⟩ := hGδ.eq_iInter_nat
  have hOmega : ∀ n, ClosedOmegaOne.omega ∈ U n := by
    intro n
    have hSingleton : ClosedOmegaOne.omega ∈ ({ClosedOmegaOne.omega} : Set ClosedOmegaOne) :=
      Set.mem_singleton ClosedOmegaOne.omega
    rw [hEq] at hSingleton
    exact Set.mem_iInter.mp hSingleton n
  -- The helper supplies another point in the intersection, contradicting singleton equality.
  obtain ⟨x, hxInter, hxNe⟩ :=
    ClosedOmegaOne.exists_mem_iInter_open_ne_omega U hU hOmega
  have hxSingleton : x ∈ ({ClosedOmegaOne.omega} : Set ClosedOmegaOne) := by
    rw [hEq]
    exact hxInter
  exact hxNe (Set.mem_singleton_iff.mp hxSingleton)

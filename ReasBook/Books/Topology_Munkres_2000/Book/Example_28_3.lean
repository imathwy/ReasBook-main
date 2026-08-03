module

import Topology_Munkres_2000.Book.Example_28_2.Instances
public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace
import Topology_Munkres_2000.Book.Theorem_10_3
import Topology_Munkres_2000.Book.Theorem_28_2
public import Mathlib.Topology.Sequences

public section

namespace ClosedOmegaOne

/-- Helper for Example 28.3: The point `ClosedOmegaOne.omega` is an accumulation point of
the included open first-uncountable ordinal. -/
theorem omega_accPt_openOmegaOne :
    AccPt ClosedOmegaOne.omega
      (Filter.principal (Set.range OpenOmegaOne.toClosed)) := by
  -- The interval is nontrivial because its endpoint lies strictly above zero.
  let zero : ClosedOmegaOne := ⟨0, bot_le⟩
  have hzeroNeOmega : zero ≠ ClosedOmegaOne.omega := by
    intro hzero
    have hOrdinal := congrArg (fun x : ClosedOmegaOne ↦ (x : Ordinal)) hzero
    dsimp [zero] at hOrdinal
    exact (ne_of_lt (Ordinal.omega_pos 1)) hOrdinal
  have hNontrivial : Nontrivial ClosedOmegaOne :=
    ⟨⟨zero, ClosedOmegaOne.omega, hzeroNeOmega⟩⟩
  letI : Nontrivial ClosedOmegaOne := hNontrivial
  -- Equip the closed interval with its evident greatest element, the adjoined endpoint.
  letI : OrderTop ClosedOmegaOne :=
    { top := ClosedOmegaOne.omega
      le_top := fun a ↦ a.property }
  have hOrderTopologyIic :
      OrderTopology (Set.Iic (Ordinal.omega 1)) := inferInstance
  have hOrderTopology : OrderTopology ClosedOmegaOne := hOrderTopologyIic
  letI : OrderTopology ClosedOmegaOne := hOrderTopology
  have homega : ClosedOmegaOne.omega = (⊤ : ClosedOmegaOne) := by
    apply Subtype.ext
    exact ClosedOmegaOne.coe_omega.trans ClosedOmegaOne.coe_omega.symm
  rw [homega, accPt_iff_frequently, nhds_top_basis.frequently_iff]
  intro a ha
  -- Regard a point below the endpoint as an open countable ordinal and go above it.
  have haOrdinal : (a : Ordinal) < Ordinal.omega 1 := by
    have haOmega : a < ClosedOmegaOne.omega := by
      rwa [homega]
    have haUnderlying :
        (a : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := haOmega
    rwa [ClosedOmegaOne.coe_omega] at haUnderlying
  let aOpen : OpenOmegaOne := ⟨a, haOrdinal⟩
  obtain ⟨b, hab⟩ := OpenOmegaOne.exists_gt aOpen
  have habClosed : a < OpenOmegaOne.toClosed b := hab
  have hbTop : OpenOmegaOne.toClosed b < (⊤ : ClosedOmegaOne) := by
    exact b.property
  -- The included point `b` lies in the required punctured tail neighborhood.
  exact ⟨OpenOmegaOne.toClosed b, habClosed, ne_of_lt hbTop, ⟨b, rfl⟩⟩

end ClosedOmegaOne

namespace OpenOmegaOne

/-- Helper for Example 28.3: The range of every sequence in `OpenOmegaOne` is bounded above. -/
theorem bddAbove_range (sequence : ℕ → OpenOmegaOne) :
    BddAbove (Set.range sequence) := by
  -- A sequence has countable range, so Theorem 10.3 supplies an upper bound.
  exact OpenOmegaOne.bddAbove_of_countable _ (Set.countable_range sequence)

/-- Helper for Example 28.3: No sequence from `OpenOmegaOne`, included into `ClosedOmegaOne`,
converges to `ClosedOmegaOne.omega`. -/
theorem no_tendsto_toClosed_omega (sequence : ℕ → OpenOmegaOne) :
    ¬ Filter.Tendsto (OpenOmegaOne.toClosed ∘ sequence) Filter.atTop
      (nhds ClosedOmegaOne.omega) := by
  intro hTendsto
  -- Bound the entire sequence below one countable ordinal `b`.
  obtain ⟨b, hb⟩ := OpenOmegaOne.bddAbove_range sequence
  have hSequenceLe (n : ℕ) : sequence n ≤ b :=
    hb (Set.mem_range_self n)
  have hbOmega : OpenOmegaOne.toClosed b < ClosedOmegaOne.omega := by
    have hOrdinal :
        (OpenOmegaOne.toClosed b : Ordinal) < (ClosedOmegaOne.omega : Ordinal) := by
      rw [OpenOmegaOne.coe_toClosed, ClosedOmegaOne.coe_omega]
      exact b.property
    exact hOrdinal
  -- Convergence to the endpoint would eventually put the sequence above `b`.
  have hEventuallyAbove :
      Filter.Eventually
        (fun n ↦ OpenOmegaOne.toClosed b < (OpenOmegaOne.toClosed ∘ sequence) n)
        Filter.atTop :=
    hTendsto.eventually (Ioi_mem_nhds hbOmega)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hEventuallyAbove
  have hContradiction : b < sequence n := by
    have hClosed := hn n le_rfl
    have hOrdinal :
        (OpenOmegaOne.toClosed b : Ordinal) <
          (OpenOmegaOne.toClosed (sequence n) : Ordinal) := hClosed
    rwa [OpenOmegaOne.coe_toClosed, OpenOmegaOne.coe_toClosed] at hOrdinal
  exact (not_lt_of_ge (hSequenceLe n)) hContradiction

end OpenOmegaOne

namespace ClosedOmegaOne

/-- Example 28.3: The closed first-uncountable ordinal is not metrizable. -/
theorem notMetrizable : ¬ TopologicalSpace.MetrizableSpace ClosedOmegaOne := by
  intro hMetrizable
  letI : TopologicalSpace.MetrizableSpace ClosedOmegaOne := hMetrizable
  -- The endpoint accumulation point belongs to the closure of the included open ordinal.
  have homegaClosure :
      ClosedOmegaOne.omega ∈ closure (Set.range OpenOmegaOne.toClosed) :=
    omega_accPt_openOmegaOne.clusterPt.mem_closure
  -- Metrizability turns closure membership into a convergent sequence in that range.
  obtain ⟨sequence, hsequenceRange, hsequenceTendsto⟩ :=
    mem_closure_iff_seq_limit.mp homegaClosure
  choose openSequence hopenSequence using hsequenceRange
  have hsequenceEq : OpenOmegaOne.toClosed ∘ openSequence = sequence := by
    funext n
    exact hopenSequence n
  -- Its chosen open-ordinal preimages contradict the sequence obstruction above.
  apply OpenOmegaOne.no_tendsto_toClosed_omega openSequence
  rwa [hsequenceEq]

end ClosedOmegaOne

namespace OpenOmegaOne

/-- Helper for Example 28.3: The open first-uncountable ordinal satisfies the sequence lemma. -/
instance instFrechetUrysohnSpace : FrechetUrysohnSpace OpenOmegaOne := by
  -- Countable initial segments give a countable neighborhood basis at every point.
  letI : NoMaxOrder OpenOmegaOne := ⟨OpenOmegaOne.exists_gt⟩
  have hFirstCountable : FirstCountableTopology OpenOmegaOne := by
    refine ⟨fun a ↦ ?_⟩
    by_cases ha : IsMin a
    · rw [SuccOrder.nhds_of_isMin ha]
      exact Filter.isCountablyGenerated_pure a
    · have hLower : ∃ b, b < a := not_isMin_iff.mp ha
      exact Filter.HasCountableBasis.isCountablyGenerated
        ⟨SuccOrder.hasBasis_nhds_Ioc_of_exists_lt hLower,
          OpenOmegaOne.countable_Iio a⟩
  letI : FirstCountableTopology OpenOmegaOne := hFirstCountable
  exact FirstCountableTopology.frechetUrysohnSpace

/-- Helper for Example 28.3: The open first-uncountable ordinal is not metrizable. -/
theorem notMetrizable : ¬ TopologicalSpace.MetrizableSpace OpenOmegaOne := by
  intro hMetrizable
  letI : TopologicalSpace.MetrizableSpace OpenOmegaOne := hMetrizable
  -- In a metrizable space, the existing limit-point compactness forces compactness.
  have hCompact : CompactSpace OpenOmegaOne :=
    (compactSpace_iff_limitPointCompactSpace OpenOmegaOne).mpr inferInstance
  -- This contradicts the previously established noncompactness instance.
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace OpenOmegaOne)) hCompact

end OpenOmegaOne

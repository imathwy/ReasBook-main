module

public import Topology_Munkres_2000.Book.Example_28_2.Instances
public import Mathlib.Topology.Sequences

public section

namespace OpenOmegaOne

/-- The open first-uncountable ordinal satisfies the sequence lemma: every point in the
closure of a set is the limit of a sequence in that set. -/
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

end OpenOmegaOne

end

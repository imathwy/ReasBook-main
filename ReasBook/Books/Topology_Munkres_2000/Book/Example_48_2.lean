module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Rat

import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.PNat

public section

namespace Rat

/-- Example 48.2 (1): The space `ℚ` of rational numbers is not a Baire space. -/
theorem not_baireSpace : ¬ BaireSpace ℚ := by
  intro hB
  letI : BaireSpace ℚ := hB
  -- The closed singleton cover forces one rational singleton to have nonempty interior.
  obtain ⟨q, hq⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun r : ℚ ↦ ({r} : Set ℚ)) (fun _ ↦ isClosed_singleton) (Set.iUnion_of_singleton ℚ)
  -- Rational singletons have empty interior, contradicting that conclusion.
  rw [interior_singleton] at hq
  exact Set.not_nonempty_empty hq

end Rat

/- Example 48.2 (2): The positive integers `ℕ+`, with their discrete topology,
form a Baire space. -/
#synth DiscreteTopology ℕ+
#check (inferInstance : BaireSpace ℕ+)

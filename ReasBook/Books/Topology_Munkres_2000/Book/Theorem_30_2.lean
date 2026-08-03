module

import Mathlib.Topology.Bases

universe u v

/- Theorem 30.2 (1): A subspace of a first-countable space is first-countable. -/
#check fun (X : Type u) [TopologicalSpace X] [FirstCountableTopology X] (s : Set X) ↦
  (inferInstance : FirstCountableTopology s)

/- Theorem 30.2 (2): A countable product of first-countable spaces is first-countable. -/
#check fun (ι : Type u) (X : ι → Type v) [Countable ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)] ↦
  (inferInstance : FirstCountableTopology (∀ i, X i))

/- Theorem 30.2 (3): A subspace of a second-countable space is second-countable. -/
#check fun (X : Type u) [TopologicalSpace X] [SecondCountableTopology X] (s : Set X) ↦
  (inferInstance : SecondCountableTopology s)

/- Theorem 30.2 (4): A countable product of second-countable spaces is second-countable. -/
#check fun (ι : Type u) (X : ι → Type v) [Countable ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, SecondCountableTopology (X i)] ↦
  (inferInstance : SecondCountableTopology (∀ i, X i))

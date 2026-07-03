import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap15.Definition_15_110_1
import StacksProject_2024.Chap15.Lemma_15_110_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing TopologicalSpace

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

/- Domain-style sampling for Ratliff's equivalence:
- primary domain: Noetherian local commutative rings, formal catenarity, and universal
  catenarity;
- sampled owner declarations:
  `IsFormallyCatenaryRing`,
  `UniversallyCatenaryRing`,
  `instUniversallyCatenaryRingOfIsFormallyCatenaryRing`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner and
  `UniversallyCatenaryRing` is the canonical core owner; this proposition is the source-facing
  equivalence between those two owners, while the forward bridge back to
  `UniversallyCatenaryRing` is already owned upstream by `15.110.4`;
- primitive data: only the ambient local ring `A`;
- derived API: the right-to-left implication should reuse the existing owner instance rather than
  re-proving a parallel bridge.

Source/core/bridge triage:
- `source-facing`: Ratliff's equivalence on a local ring `A`;
- `core/canonical`: `UniversallyCatenaryRing` and `IsFormallyCatenaryRing`;
- `bridge/view`: the existing instance
  `instUniversallyCatenaryRingOfIsFormallyCatenaryRing`.
-/

-- Proof sketch: apply the existing bridge instance from Lemma `15.110.4` for the reverse
-- implication. For the forward implication, argue by contraposition from the failure of formal
-- catenarity.
/-- Proposition 15.110.5 (Ratliff): a Noetherian local ring is universally catenary if and only if
it is formally catenary. -/
theorem universallyCatenaryRing_iff_isFormallyCatenaryRing :
    UniversallyCatenaryRing A ↔ IsFormallyCatenaryRing A := by
  constructor
  · intro hUC
    sorry
  · intro hFC
    letI : IsFormallyCatenaryRing A := hFC
    exact inferInstance

end

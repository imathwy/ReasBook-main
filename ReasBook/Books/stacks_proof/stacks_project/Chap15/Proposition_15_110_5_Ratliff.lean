import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_105_3
import stacks_proof.stacks_project.Chap15.Definition_15_110_1
import stacks_proof.stacks_project.Chap15.Lemma_15_110_2

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
/-- Helper for Proposition 15.110.5 (Ratliff): formally catenary Noetherian local rings are
universally catenary. -/
theorem universallyCatenaryRing_of_isFormallyCatenaryRing [IsFormallyCatenaryRing A] :
    UniversallyCatenaryRing A := by
  sorry

/-- Proposition 15.110.5 (Ratliff): a Noetherian local ring is universally catenary if and only if
it is formally catenary. -/
@[stacks 0AW6]
theorem universallyCatenaryRing_iff_isFormallyCatenaryRing :
    UniversallyCatenaryRing A ↔ IsFormallyCatenaryRing A := by
  constructor
  · intro hUC
    -- Contrapose Lemma `15.110.2`: universal catenarity cannot coexist with failure of formal
    -- catenarity.
    classical
    by_contra hFC
    exact
      (not_universallyCatenaryRing_of_not_isFormallyCatenaryRing (A := A) hFC) hUC
  · intro hFC
    -- Reuse the canonical instance from Lemma `15.110.4` for the reverse implication.
    letI : IsFormallyCatenaryRing A := hFC
    exact universallyCatenaryRing_of_isFormallyCatenaryRing (A := A)

end

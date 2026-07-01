import Mathlib
import stacks_project.Chap15.Proposition_15_110_5_Ratliff

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

/- Domain-style sampling for the formal-catenary failure criterion:
- primary domain: local commutative algebra of formally catenary and universally catenary rings;
- sampled owner declarations:
  `IsFormallyCatenaryRing`,
  `UniversallyCatenaryRing`,
  `universallyCatenaryRing_iff_isFormallyCatenaryRing`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner and
  `UniversallyCatenaryRing` is the canonical core owner; this lemma is only the negated
  bridge/view obtained from the Ratliff equivalence;
- primitive data: the local-ring ambient structure and the source-facing failure
  `¬ IsFormallyCatenaryRing A`;
- derived API: the Ratliff equivalence already absorbs the Noetherian hypothesis, so no separate
  public Noetherian binder or proof-only local instance should remain here.

Source/core/bridge triage:
- `source-facing`: failure of formal catenarity;
- `core/canonical`: `UniversallyCatenaryRing`;
- `bridge/view`: the implication `UniversallyCatenaryRing A → IsFormallyCatenaryRing A` from
  `universallyCatenaryRing_iff_isFormallyCatenaryRing`.
-/
-- Proof sketch: Proposition `15.110.5` upgrades universal catenarity directly to formal
-- catenarity, contradicting the hypothesis.
/-- Lemma 15.110.2: if a Noetherian local ring is not formally catenary, then it is not
universally catenary. -/
theorem not_universallyCatenaryRing_of_not_isFormallyCatenaryRing
    (hA : ¬ IsFormallyCatenaryRing A) :
    ¬ UniversallyCatenaryRing A := by
  intro hUC
  exact hA ((universallyCatenaryRing_iff_isFormallyCatenaryRing A).mp hUC)

end

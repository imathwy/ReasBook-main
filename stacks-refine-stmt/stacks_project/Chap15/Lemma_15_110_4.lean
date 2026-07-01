import Mathlib
import stacks_project.Chap10.Definition_10_105_3
import stacks_project.Chap15.Definition_15_110_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling for the formal-catenary to universal-catenary bridge:
- primary domain: Noetherian local commutative rings, formal catenarity, and universal
  catenarity;
- sampled owner declarations:
  `IsFormallyCatenaryRing`,
  `UniversallyCatenaryRing`,
  `universallyCatenaryRing_of_support_eq_univ_of_locallyCohenMacaulay`,
  `universallyCatenaryRing_of_isCompleteLocalRing`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner and
  `UniversallyCatenaryRing` is the canonical core owner; this file supplies only the bridge from
  the former to the latter;
- primitive data: the owner hypothesis `[IsFormallyCatenaryRing A]`;
- derived API: any term-level theorem restating the resulting instance is redundant.

Source/core/bridge triage:
- `source-facing`: the textbook implication that formally catenary Noetherian local rings are
  universally catenary;
- `core/canonical`: `UniversallyCatenaryRing`;
- `bridge/view`: the instance upgrading `[IsFormallyCatenaryRing A]` to
  `[UniversallyCatenaryRing A]`.
-/

-- Proof sketch: combine the formally catenary hypothesis with the equidimensionality of the
-- completed quotients by minimal primes, then apply the local-to-global criterion for universal
-- catenarity through local finite type algebras and the complete local case.
/-- Lemma 15.110.4: a formally catenary Noetherian local ring is universally catenary. -/
instance instUniversallyCatenaryRingOfIsFormallyCatenaryRing [IsFormallyCatenaryRing A] :
    UniversallyCatenaryRing A := sorry

end

import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap15.Lemma_15_107_7
import StacksProject_2024.Chap15.Lemma_15_109_8
import StacksProject_2024.Chap15.Proposition_15_110_5_Ratliff

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing TopologicalSpace

section

variable {A : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling:
- primary domain: Noetherian local commutative algebra of geometrically normal formal fibers,
  henselizations, unibranch local rings, and universal catenarity;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `branchNumber_eq_one_iff_isUnibranch`,
  `branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers`,
  `universallyCatenaryRing_iff_isFormallyCatenaryRing`;
- best owner abstraction: the source-facing formal-fiber hypothesis belongs to
  `LocalFormalFibersHaveProperty`, while the conclusion should be stated directly in the canonical
  owner `UniversallyCatenaryRing`; the branch-number equalities from Chapter 15 are derived API
  used only as the bridge from the formal-fiber hypothesis to formal catenarity;
- primitive data: the local Noetherian ring `A`, a chosen henselization `Ah`, and the shared
  hypothesis `hgeom`;
- derived API: the universal-catenarity instances for `Ah` and, under `[IsUnibranch A]`, for `A`.

Source/core/bridge triage:
- `source-facing`: the two clauses of Lemma `15.110.6`;
- `core/canonical`: `LocalFormalFibersHaveProperty`, `IsUnibranch`, and
  `UniversallyCatenaryRing`;
- `bridge/view`: the branch-number comparison theorems from `15.107.7` and `15.109.8`, together
  with Ratliff's equivalence `universallyCatenaryRing_iff_isFormallyCatenaryRing`.
-/

-- Proof sketch: apply the branch-count comparison from Lemma `15.109.8` and the radical-primality
-- criterion from Lemma `15.109.2` to each minimal prime of `Ah`, obtaining the equidimensional
-- completion quotients required for formal catenarity. Ratliff's equivalence then upgrades formal
-- catenarity of `Ah` to universal catenarity.
/-- Lemma 15.110.6 (1): if the Noetherian local ring `A` has geometrically normal formal fibers,
then any chosen henselization `Ah` of `A` is universally catenary. -/
theorem universallyCatenaryRing_henselization_of_geometricallyNormal_formalFibers
    {Ah : Type u} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    UniversallyCatenaryRing Ah := sorry

-- Proof sketch: under `[IsUnibranch A]`, Lemma `15.107.7` gives `branchNumber A Ah = 1`. Combine
-- this with the branch-count formula from Lemma `15.109.8` to force each completed quotient by a
-- minimal prime of `A` to have a unique minimal prime, hence to be equidimensional. Ratliff's
-- equivalence then yields universal catenarity of `A`.
/-- Lemma 15.110.6 (2): if the Noetherian local ring `A` has geometrically normal formal fibers
and `A` is unibranch, then `A` is universally catenary. In particular this applies to normal local
rings. -/
theorem universallyCatenaryRing_of_unibranch_of_geometricallyNormal_formalFibers
    [IsUnibranch A]
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    UniversallyCatenaryRing A := sorry

end

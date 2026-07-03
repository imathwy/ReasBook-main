import Mathlib
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Noetherian.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_110_1 (from Chap15) -/
universe u

open IsLocalRing TopologicalSpace

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling for formal catenarity of Noetherian local rings:
- primary domain: local commutative algebra of maximal-ideal completions, minimal primes, and
  equidimensional spectra;
- sampled owner declarations:
  `UniversallyCatenaryRing`,
  `IsCatenaryRing`,
  `EquidimensionalSpace`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: `IsFormallyCatenaryRing` is the source-facing owner for this definition;
  the completed quotient `A^∧ / pA^∧` is only an auxiliary canonical construction and should not
  be promoted to a second public owner;
- primitive data: for each minimal prime `p` of `A`, equidimensionality of `Spec (A^∧ / pA^∧)`;
- derived API: the later bridge from formal catenarity to `UniversallyCatenaryRing`.

Source/core/bridge triage:
- `source-facing`: `IsFormallyCatenaryRing`;
- `core/canonical`: `UniversallyCatenaryRing` and `EquidimensionalSpace`;
- `bridge/view`: the quotient `ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p`.
-/

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-- Definition 15.110.1: a Noetherian local ring is formally catenary if for every minimal prime
`p` of `A`, the prime spectrum of the completion quotient `A^∧ / p A^∧` is equidimensional. -/
class IsFormallyCatenaryRing : Prop extends IsLocalRing A, IsNoetherianRing A where
  equidimensional_completion_quotient (p : minimalPrimes A) :
      EquidimensionalSpace
        (PrimeSpectrum (ACompletion ⧸ Ideal.map (algebraMap A ACompletion) p.1))

end

/-! ### Lemma_15_110_2 (from Chap15) -/
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

/-! ### Lemma_15_110_3 (from Chap15) -/
universe u v

open TopologicalSpace

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing B] [Module.Flat A B]
variable [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)]

/- Domain-style sampling for local dimension theory over `PrimeSpectrum`:
- topological owners from Chapter 5: `EquidimensionalSpace`
- topological catenary owner from Chapter 5 / Chapter 10: `CatenarySpace (PrimeSpectrum A)`,
  with ring-level alias `IsCatenaryRing A`
- fiber-ring owner used throughout Chapter 10: `Ideal.Fiber`
- spectrum/fiber bridge: `PrimeSpectrum.preimageHomeomorphFiber`
- faithfully-flat local-map owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`
- Noetherian descent owner: `isNoetherianRing_of_faithfullyFlat`

Layer triage:
- `source-facing`: the equidimensionality conclusions for the quotient spectra `Spec (B / pB)` and
  for `Spec A`
- `core/canonical`: `CatenarySpace (PrimeSpectrum A)`, `EquidimensionalSpace`, and `Ideal.Fiber`
- `bridge/view`: the comparison between the source quotient `B ⧸ p.asIdeal.map (algebraMap A B)`
  and the canonical fiber ring `p.asIdeal.Fiber B`, together with the ring-level alias
  `IsCatenaryRing A`

The source statement of part `(1)` is the quotient-spectrum claim `Spec (B / pB)`, so that
quotient must remain the main public theorem surface. The canonical fiber ring `p.asIdeal.Fiber B`
is still the right comparison owner for any auxiliary bridge, but it should not replace the
source-facing quotient statement. Likewise, the catenary conclusion of part `(2)` should live
first on the canonical owner `CatenarySpace (PrimeSpectrum A)`, with `IsCatenaryRing A` retained
only as the source-facing bridge spelling.
-/

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent from the flat local
-- map `A → B` and `[IsNoetherianRing B]`. For a prime `p` of `A`, choose primes of `B` minimal
-- over `pB`. Going down for the flat map `A → B` and the catenary equidimensional hypotheses on
-- `B` identify the dimensions of the corresponding local rings, showing that all irreducible
-- components of the quotient spectrum `Spec (B ⧸ p.asIdeal.map (algebraMap A B))` have the same
-- dimension.
/-- Lemma 15.110.3 (1): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then for every prime ideal `p` of `A` the quotient
spectrum `Spec (B ⧸ p.asIdeal.map (algebraMap A B))`, equivalently `Spec (B / pB)`, is
equidimensional. -/
theorem primeSpectrum_quotient_equidimensional_of_flat_local_of_catenary_equidimensional
    (p : PrimeSpectrum A) :
    EquidimensionalSpace (PrimeSpectrum (B ⧸ p.asIdeal.map (algebraMap A B))) := sorry

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent. Then apply part `(1)`
-- to every quotient `A / p`, use the flat dimension formula to show that `p ↦ dim(A / p)` is a
-- dimension function, and conclude that the local ring `A` is catenary.
/-- Core canonical owner for Lemma 15.110.3 (2): under the flat local hypotheses, the prime
spectrum `Spec A` is catenary. The ring-level conclusion `IsCatenaryRing A` is the thin alias
bridge to this owner theorem. -/
theorem catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional :
    CatenarySpace (PrimeSpectrum A) := sorry

/-- Lemma 15.110.3 (2): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `A` is catenary. -/
theorem isCatenaryRing_of_flat_local_of_catenary_equidimensional :
    IsCatenaryRing A :=
  catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent. Then compare
-- `dim(A_p)` with `dim(B_q)` for primes `q` minimal over `pB`, deduce that `dim(A) - dim(A / p)`
-- is independent of the choice of a minimal prime of `A`, and conclude that all irreducible
-- components of `Spec A` have the same dimension.
/-- Lemma 15.110.3 (3): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `Spec A` is equidimensional. -/
theorem primeSpectrum_equidimensional_of_flat_local_of_catenary_equidimensional :
    EquidimensionalSpace (PrimeSpectrum A) := sorry

end

/-! ### Lemma_15_110_4 (from Chap15) -/
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

/-! ### Proposition_15_110_5_Ratliff (from Chap15) -/
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

/-! ### Lemma_15_110_6 (from Chap15) -/
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

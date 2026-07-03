import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_51_1 (from Chap15) -/
universe u

section

/- Domain sampling pass:
- primary domain: `P`-rings and formal fibers of completed localizations in Noetherian
  commutative algebra;
- sampled owner declarations:
  `CompletedLocalizationAtPrime`,
  `IsGRing`,
  `isGRing_iff_forall_regular_localization_completion`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: the source-facing owner is the class `IsPRing P R`, extending
  `IsNoetherianRing R`, while the prime-pair condition is only a bridge/view of that owner;
- primitive data: the field-algebra predicate `P` and the fiberwise condition on the completion
  maps `R_p → R̂_[p]`;
 - derived API: the prime-pair reformulation `SatisfiesPPrimePairCondition` and its localization
   bridge `isPRing_localizationAtPrime_iff`.

Layering:
- `source-facing`: `IsPRing P R`;
- `core/canonical`: `CompletedLocalizationAtPrime` and the owner class `IsPRing`;
- `bridge/view`: the prime-pair criterion `SatisfiesPPrimePairCondition`.
-/

/-- A property of commutative algebras over fields, used to formulate the `P`-ring condition in
terms of formal fibers. -/
abbrev FieldAlgebraProperty : Type (u + 1) :=
  ∀ (k A : Type u), [Field k] → [CommRing A] → [Algebra k A] → Prop

variable (P : FieldAlgebraProperty)
variable (R : Type u) [CommRing R]

/-- The source-facing owner: a `P`-ring is a Noetherian ring whose completed localizations have
formal fibers with property `P`. -/
class IsPRing (P : FieldAlgebraProperty) (R : Type u) [CommRing R] : Prop
    extends IsNoetherianRing R where
  /-- Every fiber of `R_𝔭 → (R_𝔭)^∧` has property `P`. -/
  satisfiesPFormalFiberCondition (p : PrimeSpectrum R)
      (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))

/-- The prime-pair reformulation of the bare formal-fiber condition, phrased using the equivalent
`κ(𝔮)`-algebra `R̂_𝔭 ⊗[R] κ(𝔮)` attached to an inclusion `𝔮 ⊆ 𝔭`. -/
abbrev SatisfiesPPrimePairCondition : Prop :=
  ∀ p q : PrimeSpectrum R,
    ∀ _hqp : q.asIdeal ≤ p.asIdeal,
      P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))

variable {P R}

-- Proof sketch: use the order isomorphism between primes of `Localization.AtPrime p.asIdeal` and
-- primes `q` of `R` with `q ≤ p`. Under this identification, the local formal fiber of
-- `Localization.AtPrime p.asIdeal → (R_𝔭)^∧` over a prime above `q` is canonically the same
-- `κ(𝔮)`-algebra as `q.asIdeal.Fiber R̂_[p]`, equivalently
-- `((R ⧸ q.asIdeal)_p)^∧ ⊗[R ⧸ q.asIdeal] κ(𝔮)`.
/-- Rewriting the fibers of the completed localization `R_p → R̂_𝔭` by primes `q ⊆ p` of `R`
gives the prime-pair criterion. -/
private theorem satisfiesPFormalFiberCondition_iff_satisfiesPPrimePairCondition :
    (∀ p : PrimeSpectrum R,
      ∀ q : PrimeSpectrum (Localization.AtPrime p.asIdeal),
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) ↔
      SatisfiesPPrimePairCondition P R := sorry

/-- A `P`-ring satisfies the prime-pair reformulation of the formal-fiber condition. -/
theorem IsPRing.satisfiesPPrimePairCondition (h : IsPRing P R) :
    SatisfiesPPrimePairCondition P R := by
  exact
    satisfiesPFormalFiberCondition_iff_satisfiesPPrimePairCondition.1
      h.satisfiesPFormalFiberCondition

/-- A Noetherian ring whose prime-pair formal fibers have property `P` is a `P`-ring. -/
theorem isPRing_of_satisfiesPPrimePairCondition [IsNoetherianRing R]
    (h : SatisfiesPPrimePairCondition P R) :
    IsPRing P R := by
  exact
    { satisfiesPFormalFiberCondition :=
        satisfiesPFormalFiberCondition_iff_satisfiesPPrimePairCondition.2 h }

/-- Lemma 15.51.1: a Noetherian ring is a `P`-ring if and only if for every
inclusion of primes `𝔮 ⊆ 𝔭`, the equivalent `κ(𝔮)`-algebra
`R̂_𝔭 ⊗[R] κ(𝔮)`, equivalently `((R ⧸ 𝔮)_𝔭)^∧ ⊗[R ⧸ 𝔮] κ(𝔮)`,
has property `P`. -/
theorem isPRing_iff_satisfiesPPrimePairCondition [IsNoetherianRing R] :
    IsPRing P R ↔ SatisfiesPPrimePairCondition P R :=
  ⟨IsPRing.satisfiesPPrimePairCondition, isPRing_of_satisfiesPPrimePairCondition⟩

-- Proof sketch: apply the prime-pair criterion to the local ring `R_p`. Its primes correspond to
-- the primes `q` of `R` with `q ≤ p`, and under that identification the formal fiber of
-- `Localization.AtPrime p.asIdeal` at the prime above `q` is exactly `q.asIdeal.Fiber (R̂_[p])`.
/-- Rephrasing the `P`-ring condition on the local ring `R_p`, one may quantify directly over
primes `q ⊆ p` of `R`. -/
theorem isPRing_localizationAtPrime_iff [IsNoetherianRing R] (p : PrimeSpectrum R) :
    IsPRing P (Localization.AtPrime p.asIdeal) ↔
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := sorry

end

/-! ### Lemma_15_51_2 (from Chap15) -/
universe u

section

variable (P : FieldAlgebraProperty)
variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]

/- Domain sampling pass:
* primary domain: commutative algebra of fiber algebras, prime localizations, and local criteria
  for residue-field algebra properties on Noetherian fibers;
* sampled owner declarations:
  - `FieldAlgebraProperty`, the Chapter 15 owner for properties of residue-field algebras;
  - `FieldAlgebraProperty.HasPropertyB`, the canonical owner for axiom `(B)`;
  - `Ideal.Fiber`, the canonical owner for the fiber algebra `κ(𝔭) ⊗[R] Λ`;
  - `fiberLocalRingAt R Λ q` from `Definition_10_112_5`, the canonical owner for the local ring of
    the fiber at `q`;
  - `fiberLocalRingAtResidueFieldAlgebra`, the Chapter 10 owner-level bridge making
    `fiberLocalRingAt R Λ q` a `κ(q ∩ R)`-algebra;
  - `PrimeSpectrum.preimageHomeomorphFiber`, the canonical identification between primes of a fiber
    algebra and primes of `Λ` lying over a fixed base prime;
  - `isRegularRingMap_local_tfae` from `Lemma_15_41_2_Regular_is_a_local_property`, the same
    source-facing local-to-global TFAE pattern in the nearby chapter development.

Source/core/bridge triage:
* `source-facing`: `fiberProperty_tfae`, the textbook local criterion on fiber
  algebras and their localization at maximal source/target pairs;
* `core/canonical`: `FieldAlgebraProperty.HasPropertyB`, `Ideal.Fiber`, `fiberLocalRingAt`, and
  the owner-level bridge `fiberLocalRingAtResidueFieldAlgebra`;
* `bridge/view`: the identification between primes of the fiber algebra and primes of `Λ` lying
  over a fixed base prime.

Primitive data are the field-algebra property `P k A` together with the Chapter 15 owner axiom
`FieldAlgebraProperty.HasPropertyB`. The theorem below applies that owner directly to the fiber
algebras and their localizations. Following the chapter owner pattern from
`Lemma_15_41_2_Regular_is_a_local_property`, the source-facing theorem is phrased directly on the
three clauses rather than through one-off public wrapper names. In the maximal-ideal clause, the
source tests the single local fiber of `R_(m' ∩ R) → Λ_(m')` at each `m' : MaximalSpectrum Λ`;
the auxiliary source-localization choice is already absorbed by the canonical owner
`fiberLocalRingAt`.
-/

end

namespace Algebra

section

variable {R Λ : Type u} [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing Λ]
variable (P : FieldAlgebraProperty) [P.HasPropertyB]

-- Proof sketch: for each `p : Spec(R)`, the prime spectrum of the fiber algebra
-- `p.asIdeal.Fiber Λ = κ(p) ⊗[R] Λ` is identified with the primes of `Λ` lying over `p` by
-- `PrimeSpectrum.preimageHomeomorphFiber`. Under that identification, clause `(2)` says exactly
-- that every localization of the fiber algebra at a prime has `P`. Clause `(3)` is the same
-- local test specialized to the maximal-local fiber `R_(m' ∩ R) → Λ_(m')`. Apply property `(B)`
-- to each Noetherian fiber algebra; Noetherianity comes from the Noetherian target ring `Λ`, and
-- the maximal-local clause is the corresponding specialization of the prime-local one.
/-- Lemma 15.51.2: let `R → Λ` be a ring map with `Λ` Noetherian, and let `P` be a
field-algebra property satisfying `(B)`. Then the following are equivalent: every fiber algebra
`κ(p) ⊗[R] Λ` has `P` over `κ(p)`; for every prime `q` of `Λ`, the local fiber ring at `q`,
equivalently the fiber of `R_(q ∩ R) → Λ_q`, has `P` over `κ(q ∩ R)`; and it suffices to test
that local condition only for maximal ideals `m'` of `Λ`, using the maximal-local fiber of
`R_(m' ∩ R) → Λ_(m')`. -/
theorem fiberProperty_tfae :
    ([ ∀ p : PrimeSpectrum R, P p.asIdeal.ResidueField (p.asIdeal.Fiber Λ)
      , ∀ q : PrimeSpectrum Λ, P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      , ∀ m' : MaximalSpectrum Λ,
          let q : PrimeSpectrum Λ := m'.toPrimeSpectrum
          P (q.asIdeal.under R).ResidueField (fiberLocalRingAt R Λ q)
      ] : List Prop).TFAE :=
  by
  sorry

end

end Algebra

/-! ### Lemma_15_51_3 (from Chap15) -/
open Algebra
open scoped TensorProduct

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: permanence of formal-fiber conditions for properties of Noetherian algebras over
  fields;
- sampled owner declarations:
  `Algebra.EssFiniteType`,
  `FieldAlgebraProperty`,
  `IsPRing`,
  `SatisfiesPPrimePairCondition`;
- best owner abstraction: `FieldAlgebraProperty`, with the transfer/locality axioms packaged by
  `HasPropertyA` and `HasPropertyB`, and the source-facing ring owner `IsPRing`; clause `(2)`
  should therefore be phrased on the theorem surface using the local `P`-ring owner
  `IsPRing P (Localization.AtPrime p.asIdeal)` rather than duplicating its prime-pair expansion;
- primitive data: the underlying predicate `P k A` together with the base-change and
  prime-localization laws;
- derived API: source-facing specializations and larger chapter packages built from those owner
  axioms.

Sampling note: the nearby local-fiber criterion `Lemma_15_51_2` is also phrased over the chapter
owner `FieldAlgebraProperty.HasPropertyB`. That owner is the right layer here as well, because
`FieldAlgebraProperty` depends on a chosen `k`-algebra structure, not just the underlying
commutative ring.

Source/core/bridge triage:
- `source-facing`: the quasi-finite transfer theorems for formal fibers and the resulting
  `isPRing_of_quasiFinite`;
- `core/canonical`: the owner classes `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`, and the ring owner `IsPRing`;
- `bridge/view`: the geometric-regularity specialization in `Lemma_15_50_3`.
-/

/-- A field-algebra property satisfies `(A)` if it is preserved by base change along finitely
generated extensions of the ground field. -/
class HasPropertyA (P : FieldAlgebraProperty) : Prop where
  /-- Base change of a Noetherian `k`-algebra along a finitely generated field extension preserves
  the property `P`. -/
  baseChange (k A K : Type u) [Field k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
      [Field K] [Algebra k K] [Algebra.EssFiniteType k K] (hA : P k A) :
      P K (K ⊗[k] A)

/-- A field-algebra property satisfies `(B)` if for every ground field `k`, the induced ring
property on Noetherian `k`-algebras can be checked on prime localizations. -/
class HasPropertyB (P : FieldAlgebraProperty) : Prop where
  /-- The prime-local criterion for `P` over the fixed base field `k`. -/
  localizationCriterion (k A : Type u) [Field k] [CommRing A] [Algebra k A]
      [IsNoetherianRing A] :
      P k A ↔ ∀ p : PrimeSpectrum A, P k (Localization.AtPrime p.asIdeal)

end FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyA] [P.HasPropertyB]

section QuasiFiniteAtPrime

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R']

-- Proof sketch: use quasi-finiteness at `p'` to identify `R̂_[p] ⊗[R] R'` with a product whose
-- first factor is `R̂_[p']`. After tensoring with `κ(q')`, the target formal fiber is therefore a
-- direct factor of the base change of the source formal fiber along `κ(q) → κ(q')`. Apply
-- property `(A)` to obtain `P` after base change and property `(B)` to descend `P` from the
-- product ring to the direct factor.
/-- Lemma 15.51.3 (1): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
`q' ⊆ p'` lies over `q`, the map is quasi-finite at `p'`, and the formal fibre
`(R_p)^∧ ⊗[R] κ(q)` has property `P`, then the formal fibre `(R'_(p'))^∧ ⊗[R'] κ(q')` also has
property `P`. -/
theorem completed_localization_formalFiber_hasProperty_of_quasiFiniteAt
    (p q : PrimeSpectrum R) (p' q' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    (hq : PrimeSpectrum.comap (algebraMap R R') q' = q)
    (hqp' : q'.asIdeal ≤ p'.asIdeal)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) :
    P q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p'])) := sorry

-- Proof sketch: view the hypothesis as saying that the local ring `R_p` is a `P`-ring. For a
-- prime `q'` of `R'_(p')`, let `q` be its image in `R_p`, equivalently in `R`. The `P`-ring
-- hypothesis on `R_p` gives `P` on the source formal fiber over `q`, and clause (1) transfers
-- that property to the formal fiber over `q'`.
/-- Lemma 15.51.3 (2): for a finite type map of Noetherian rings `R → R'`, if `p'` lies over `p`,
the map is quasi-finite at `p'`, and every formal fibre of `R_p` has `P`, then every formal fibre
of `R'_(p')` has `P`. -/
theorem completed_localization_formalFibers_haveProperty_of_quasiFiniteAt
    (p : PrimeSpectrum R) (p' : PrimeSpectrum R')
    (hp : PrimeSpectrum.comap (algebraMap R R') p' = p)
    [Algebra.QuasiFiniteAt R p'.asIdeal]
    (hP : IsPRing P (Localization.AtPrime p.asIdeal)) :
    IsPRing P (Localization.AtPrime p'.asIdeal) := sorry

end QuasiFiniteAtPrime

section QuasiFinite

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable [IsNoetherianRing R] [Algebra.FiniteType R R'] [Algebra.QuasiFinite R R']

-- Proof sketch: finite type over the Noetherian ring `R` makes `R'` Noetherian. For each prime
-- `p'` of `R'`, let `p` be its image in `R`. The hypothesis that `R` is a `P`-ring gives that
-- the local ring `R_p` is a `P`-ring, and clause (2) transfers that owner statement to the local
-- ring `R'_(p')`.
/-- Lemma 15.51.3 (3): if `R → R'` is quasi-finite and `R` satisfies the `P`-ring formal-fibre
condition, then `R'` also satisfies the `P`-ring formal-fibre condition. -/
theorem isPRing_of_quasiFinite
    (hP : IsPRing P R) :
    IsPRing P R' := sorry

end QuasiFinite

end

/-! ### Lemma_15_51_4 (from Chap15) -/
open IsLocalRing

universe u

namespace FieldAlgebraProperty

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber permanence axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `IsPRing`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: `FieldAlgebraProperty`, with the reusable axioms `(C)` and `(D)` owned
  as inferable classes, matching the existing owner form for `(A)` and `(B)`;
- primitive data: the field-algebra predicate `P` together with the regular-ascent and faithfully
  flat local-descent laws on fibers, plus the local formal-fiber predicate itself;
- derived API: the maximal-ideal criterion for `IsPRing`.

Source/core/bridge triage:
- `source-facing`: `LocalFormalFibersHaveProperty` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- `core/canonical`: `P.HasPropertyC` and `P.HasPropertyD`;
- `bridge/view`: none needed.
-/

section

/-- A field-algebra property has property `(C)` if it ascends along regular morphisms on fibers of
flat maps of Noetherian rings. -/
class HasPropertyC (P : FieldAlgebraProperty) : Prop where
  /-- Property `(C)` ascends from the fibers of `A → B` to the fibers of `A → C` when `A → B` is
  flat and `B → C` is regular. -/
  regularAscent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [(algebraMap B C).IsRegularRingMap]
      (hB : ∀ q : PrimeSpectrum A, P q.asIdeal.ResidueField (q.asIdeal.Fiber B))
      (q : PrimeSpectrum A) :
      P q.asIdeal.ResidueField (q.asIdeal.Fiber C)

/-- A field-algebra property has property `(D)` if it descends along faithfully flat local
extensions on closed fibers of Noetherian local rings. -/
class HasPropertyD (P : FieldAlgebraProperty) : Prop where
  /-- Property `(D)` descends from the closed fiber over `A → C` to the closed fiber over `A → B`
  along a faithfully flat local extension `B → C`. -/
  closedFiberDescent (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
      [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
      (hBC : RingHom.FaithfullyFlat (algebraMap B C))
      (hC : P (ResidueField A) ((maximalIdeal A).Fiber C)) :
      P (ResidueField A) ((maximalIdeal A).Fiber B)

end

end FieldAlgebraProperty

section

/-- A local ring has formal fibers with property `P` if every fiber of its completion map to the
maximal-ideal adic completion has property `P`. -/
abbrev LocalFormalFibersHaveProperty
    (P : FieldAlgebraProperty) (A : Type u) [CommRing A] [IsLocalRing A] :
    Prop :=
  ∀ q : PrimeSpectrum A,
    P q.asIdeal.ResidueField (q.asIdeal.Fiber (AdicCompletion (maximalIdeal A) A))

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

-- Proof sketch: the forward implication is the specialization of the `P`-ring condition to the
-- maximal prime `m`. For the converse, fix `p : Spec(R)` and choose a maximal ideal `m ⊇ p`.
-- The hypothesis gives `P` on the fibers of `R_m → (R_m)^∧`. After choosing a prime of
-- `(R_m)^∧` over `pR_m` using faithful flatness of completion, apply Proposition `15.50.6` and
-- Lemma `15.41.4` to obtain a regular map from `(R_m)^∧` to the relevant completed localization,
-- then use `(C)` to transfer `P` to those fibers and `(D)` to descend from that faithfully flat
-- local extension to the fibers of `R_p → (R_p)^∧`.
/-- Lemma 15.51.4: let `R` be a Noetherian ring, and assume the field-algebra property `P`
satisfies `(C)` and `(D)`. Then `R` is a `P`-ring if and only if, for every maximal ideal `m` of
`R`, the local ring `R_m` has formal fibers with property `P`. -/
theorem isPRing_iff_localFormalFibersHaveProperty_atMaximal
    (P : FieldAlgebraProperty)
    [P.HasPropertyC] [P.HasPropertyD] :
    IsPRing P R ↔
      ∀ m : MaximalSpectrum R,
        LocalFormalFibersHaveProperty P (Localization.AtPrime m.asIdeal) := sorry

end

/-! ### Proposition_15_51_5 (from Chap15) -/
universe u

section

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 `P`-ring formal-fiber condition under essentially
  finite type algebra maps;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`,
  `isPRing_of_quasiFinite`,
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`;
- best owner abstraction: the source-facing owner is `IsPRing P R`; the theorem should stay on
  that owner and reuse the Chapter 15 permanence axioms as inferable classes, rather than
  expanding the prime-pair condition or carrying redundant Noetherian hypotheses in the public
  interface;
- primitive data: the `R`-algebra `S`, the essentially finite type hypothesis, the four transfer
  axioms `(A)` through `(D)` on `P`, and the owner input `hR : IsPRing P R`;
- derived API: the resulting owner conclusion `IsPRing P S`.

Source/core/bridge triage:
- `source-facing`: `isPRing_of_essFiniteType`;
- `core/canonical`: `IsPRing` together with the owner axioms `P.HasPropertyA`, `P.HasPropertyB`,
  `P.HasPropertyC`, and `P.HasPropertyD`;
- `bridge/view`: `isPRing_of_quasiFinite` and
  `isPRing_iff_localFormalFibersHaveProperty_atMaximal`, which supply the canonical local and
  quasi-finite reductions used by the proof strategy.
-/
variable (P : FieldAlgebraProperty)
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
variable [P.HasPropertyA] [P.HasPropertyB] [P.HasPropertyC] [P.HasPropertyD]

-- Proof sketch: reduce by `isPRing_iff_localFormalFibersHaveProperty_atMaximal` to the local
-- rings `S_m` at maximal ideals of `S`. Present each `S_m` as essentially finite type over the
-- corresponding localization of `R`, use the quasi-finite permanence theorem `isPRing_of_quasiFinite`
-- from Lemma `15.51.3` together with axioms `(A)` and `(B)` to handle the finite-type part, and
-- then apply axioms `(C)` and `(D)` through Lemma `15.51.4` to descend the comparison on formal
-- fibers.
/-- Proposition 15.51.5: if `R` is a `P`-ring and `R → S` is essentially of finite type, where
`P` satisfies `(A)`, `(B)`, `(C)`, and `(D)`, then `S` is again a `P`-ring. -/
theorem isPRing_of_essFiniteType
    (hR : IsPRing P R) :
    IsPRing P S := sorry

end

/-! ### Lemma_15_51_6 (from Chap15) -/
universe u

namespace Algebra

section

variable (P : FieldAlgebraProperty)

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable [P.HasPropertyB] [P.HasPropertyD]

/- Domain sampling pass:
- primary domain: Chapter 15 formal fibers of adic completion maps for `P`-rings in Noetherian
  commutative algebra;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyD`,
  `completed_localization_formalFibers_haveProperty_of_quasiFiniteAt`,
  `LocalFormalFibersHaveProperty`;
- best owner abstraction: the source-facing owner is still `IsPRing P A`; this lemma is not a new
  owner, but a `bridge/view` from the local formal-fiber owner to the concrete fiber algebra of
  the global completion map `A → AdicCompletion I A`;
- primitive data: the owner hypothesis `IsPRing P A` together with the transfer/descent axioms
  `(B)` and `(D)`;
- derived API: the specific fiberwise consequence for `p.asIdeal.Fiber (AdicCompletion I A)`.

Source/core/bridge triage:
- `source-facing`: `completion_fibers_have_property_of_pRing`;
- `core/canonical`: `IsPRing`, `P.HasPropertyB`, and `P.HasPropertyD`;
- `bridge/view`: the comparison between the global completion fiber over `p` and the relevant
  completed local fiber used in the descent argument.

Refinement note: the theorem should not expose `[IsNoetherianRing A]` as primitive public data,
because that structure is already part of the source-facing owner hypothesis `IsPRing P A`.
-/

-- Proof sketch: for each prime `p ⊂ A`, localize the completion map at a prime `p'` of
-- `AdicCompletion I A` above `p`. By property `(B)`, it suffices to treat the corresponding local
-- fiber ring. Compare the maximal-ideal completion of `A_p` with the completion of the localized
-- completed ring using Lemma `15.43.9`, then use faithful flatness of the completion map and
-- property `(D)` to descend `P` from the completed local fiber. Finally invoke the `P`-ring
-- hypothesis on `A`.
/-- Lemma 15.51.6: if `A` is a `P`-ring, where `P` satisfies `(B)` and `(D)`, then for every
prime `p` of `A` the fiber ring of the completion map `A → AdicCompletion I A` over `p` has
property `P` over `κ(p)`. -/
theorem completion_fibers_have_property_of_pRing
    (hA : IsPRing P A)
    (p : PrimeSpectrum A) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber (AdicCompletion I A)) := sorry

end

end Algebra

/-! ### Lemma_15_51_7 (from Chap15) -/
open RingPairCat

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- Pair henselization exists as the right adjoint supplied by Lemma `15.12.1`. -/
local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [P.HasPropertyC] [P.HasPropertyD] [P.HasPropertyE]

-- Proof sketch: by Lemma `15.51.4`, it is enough to check the local formal fibres of the
-- henselization ring at maximal ideals. For a maximal ideal `m^h` of `A^h`, compare the completed
-- local ring of `(A^h)_(m^h)` with the completion of `A_m`, where `m` is the inverse image of
-- `m^h`. The completion comparison from Lemma `15.12.4`, the finite product description of the
-- fibre from Lemma `15.45.12`, property `(B)` for localization, and property `(E)` for separable
-- algebraic residue-field extensions transfer `P` from the formal fibres of `A` to those of
-- `A^h`.
/-- Lemma 15.51.7: if `A` is a `P`-ring and the field-algebra property `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then the canonical pair-henselization ring `A^h` of `(A, I)` is again a
`P`-ring. -/
theorem isPRing_henselizationRing
    (hA : IsPRing P A) :
    IsPRing P (henselizationRing (pairOfIdeal I)) := by
  let _ : IsPRing P A := hA
  let _ : IsNoetherianRing (henselizationRing (pairOfIdeal I)) :=
    henselizationRing_isNoetherian (pairOfIdeal I)
  sorry

end

/-! ### Lemma_15_51_8 (from Chap15) -/
open IsLocalRing

universe u

section

variable (P : FieldAlgebraProperty)
variable [P.HasPropertyB]
variable [FieldAlgebraProperty.HasPropertyC P] [FieldAlgebraProperty.HasPropertyD P]
variable [P.HasPropertyE]

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain sampling pass:
- primary domain: permanence of the Chapter 15 owner `IsPRing P R` under henselization and strict
  henselization of Noetherian local rings;
- sampled owner declarations:
  `IsPRing`,
  `FieldAlgebraProperty.HasPropertyE`,
  `isPRing_henselizationRing`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the source-facing conclusions are owner statements `IsPRing P Rh` and
  `IsPRing P Rsh`; clause `(E)` already has the canonical owner `P.HasPropertyE`, so it should
  not reappear as a duplicate theorem argument;
- primitive data: a Noetherian local `P`-ring `R` together with chosen henselization and strict
  henselization owners;
- derived API: the paired conjunction theorem below, assembled from the two atomic owner-level
  consequences.

Source/core/bridge triage:
- `source-facing`: the permanence statements for henselization and strict henselization;
- `core/canonical`: `IsPRing` and `P.HasPropertyE`;
- `bridge/view`: the canonical pair-henselization theorem `isPRing_henselizationRing` and the
  comparison from a strict henselization over a henselization back to the base ring.
-/

-- Proof sketch: compare an arbitrary henselization `Rh` with the canonical pair-henselization
-- ring from Lemma `15.51.7` and transport the `P`-ring owner statement across that canonical
-- comparison.
/-- Lemma 15.51.8, henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`,
`(D)`, and `(E)`, then any henselization `Rh` of `R` is a `P`-ring. -/
theorem isPRing_henselization
    (hR : IsPRing P R) :
    IsPRing P Rh := by
  let _ : IsPRing P R := hR
  sorry

-- Proof sketch: use Lemma `15.51.4` to reduce to local formal fibers. For a prime `r` of `Rsh`
-- over `p ⊂ R`, Lemma `15.45.13` writes the fiber over `p` as a finite product of residue fields
-- and shows `κ(r) / κ(p)` is separable algebraic. Lemma `15.45.3` and Proposition `15.49.2`
-- identify the completion comparison `R^∧ → (R^sh)^∧` as regular, and then `(C)`, `(B)`, and
-- `(E)` transfer property `P` from the formal fibers of `R` to those of `Rsh`.
/-- Lemma 15.51.8, strict-henselization case: if `R` is a `P`-ring, where `P` satisfies `(B)`,
`(C)`, `(D)`, and `(E)`, then any strict henselization `Rsh` of `R` is a `P`-ring. -/
theorem isPRing_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rsh := by
  let _ : IsPRing P R := hR
  sorry

/-- Lemma 15.51.8: if `R` is a `P`-ring, where `P` satisfies `(B)`, `(C)`, `(D)`, and `(E)`,
then any henselization `Rh` and any strict henselization `Rsh` of `R` are `P`-rings. -/
theorem isPRing_henselization_and_strictHenselization
    (hR : IsPRing P R) :
    IsPRing P Rh ∧ IsPRing P Rsh := by
  exact ⟨isPRing_henselization P hR, isPRing_strictHenselization P hR⟩

end

/-! ### Lemma_15_51_9 (from Chap15) -/
open scoped TensorProduct
open IsLocalRing

namespace Algebra

universe u

/- Domain triage:
- primary domain: geometrically reduced algebras over fields and the Chapter 15 formal-fiber
  axioms for field-algebra properties;
- sampled owner declarations:
  `Algebra.IsGeometricallyReduced`,
  `IsRegularRingMap`,
  `RingHom.FaithfullyFlat`,
  `isReduced_of_faithfullyFlat`,
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertiesABCDE`,
  `isGeometricallyReduced_iff_of_isSeparable`;
- best owner abstraction: the public owner is the Chapter 15 package
  `FieldAlgebraProperty.HasPropertiesABCDE`, specialized directly to the canonical
  field-algebra predicate `fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦
    IsGeometricallyReduced k R`;
- source/core/bridge triage:
  clauses `(1)` through `(5)` are the source-facing companions, while the chapter-level
  `FieldAlgebraProperty.HasPropertiesABCDE` instance is the core/canonical owner interface.

Primitive data are the ambient field/ring maps and the fiber hypotheses. Reducedness after
tensoring, localization stability, regular/faithfully-flat fiber transfer, and separable-base-field
invariance stay in derived owner API rather than being repackaged by a local wrapper.
-/

/-- The canonical `FieldAlgebraProperty` bridge for geometric reducedness. -/
abbrev IsGeometricallyReducedProperty : FieldAlgebraProperty :=
  fun k R ↦ fun [Field k] [CommRing R] [Algebra k R] ↦ IsGeometricallyReduced k R

-- Proof sketch: a finitely generated field extension is built from a purely transcendental
-- extension and a finite algebraic extension. Polynomial extensions and localizations preserve
-- geometric reducedness, and algebraic field extensions preserve reducedness after tensoring with
-- a geometrically reduced algebra.
/-- Lemma 15.51.9 (1): geometric reducedness is preserved after base change along a finitely
generated field extension. -/
theorem isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {R : Type u}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced K (K ⊗[k] R) := sorry

section

variable {k : Type u} {R : Type u} [Field k] [CommRing R] [Algebra k R]

-- Proof sketch: geometric reducedness is defined by reducedness after tensoring with field
-- extensions. Reducedness is a local property of commutative rings, and localizing a
-- geometrically reduced algebra stays geometrically reduced, so the global ring is geometrically
-- reduced exactly when all of its prime localizations are.
/-- Lemma 15.51.9 (2): a Noetherian `k`-algebra is geometrically reduced if and only if all of its
prime localizations are geometrically reduced over `k`. -/
theorem isGeometricallyReduced_iff_forall_localization_atPrime [IsNoetherianRing R] :
    IsGeometricallyReduced k R ↔
      ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal) := sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

-- Proof sketch: fix `p : Spec(A)` and base change the regular map `B → C` along `κ(p)`. The
-- induced map on fibers is regular. Since the fiber of `A → B` over `p` is geometrically reduced,
-- its base change to an algebraic closure of `κ(p)` is reduced; then Lemma `15.42.1` applied to
-- the regular map on base-changed fibers shows the corresponding base change of the fiber of
-- `A → C` is reduced, which is exactly geometric reducedness.
/-- Lemma 15.51.9 (3): if `A → B → C` are maps of commutative rings, `A → B` is flat, every fiber
of `A → B` is geometrically reduced, and `B → C` is a regular ring map, then every fiber of
`A → C` is geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_flat_of_regular [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hAB :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C) := sorry

-- Proof sketch: fix `p : Spec(A)` and base change the faithfully flat map `B → C` along `κ(p)`.
-- This gives a faithfully flat map of fiber rings. If the fiber of `A → C` over `p` is
-- geometrically reduced, then after tensoring with an algebraic closure of `κ(p)` the target
-- fiber is reduced. Lemma `10.164.2` descends reducedness along the faithfully flat map of these
-- base-changed fibers, giving geometric reducedness of the fiber of `A → B` over `p`.
/-- Lemma 15.51.9 (4): if `A → B → C` are maps of commutative rings, every fiber of `A → C` is
geometrically reduced, and `B → C` is faithfully flat, then every fiber of `A → B` is
geometrically reduced. -/
theorem fibers_areGeometricallyReduced_of_comp_of_faithfullyFlat
    (hBC_ff : (algebraMap B C).FaithfullyFlat)
    (hAC :
      ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber C)) :
    ∀ p : PrimeSpectrum A, IsGeometricallyReduced p.asIdeal.ResidueField (p.asIdeal.Fiber B) := sorry

end

section

variable {k : Type u} {k' : Type u} {R : Type u}
variable [Field k] [Field k'] [CommRing R]
variable [Algebra k k'] [Algebra k' R] [Algebra k R] [IsScalarTower k k' R]

-- Proof sketch: this is exactly the separable-base-field invariance of geometric reducedness from
-- Lemma `10.43.9`; apply that result and take the forward implication.
/-- Lemma 15.51.9 (5): if `k' / k` is a separable algebraic field extension and `R` is
geometrically reduced over `k`, then `R` is geometrically reduced over `k'`. -/
theorem isGeometricallyReduced_of_separableAlgebraicExtension [Algebra.IsSeparable k k']
    [IsGeometricallyReduced k R] :
    IsGeometricallyReduced k' R :=
  (isGeometricallyReduced_iff_of_isSeparable : IsGeometricallyReduced k R ↔
    IsGeometricallyReduced k' R).1 inferInstance

-- Proof sketch: this repackages source-facing clause `(5)` as the Chapter 15 axiom `(E)` for the
-- canonical field-algebra property `fun k R ↦ IsGeometricallyReduced k R`.
/-- Lemma 15.51.9 (5), owner-form: geometric reducedness has property `(E)` in the Chapter 15
formal-fiber package. -/
theorem isGeometricallyReduced_hasPropertyE :
    IsGeometricallyReducedProperty.HasPropertyE := by
  refine ⟨?_⟩
  intro k k' R _ _ _ _ _ _ _ _ hR
  exact
    (isGeometricallyReduced_iff_of_isSeparable :
      IsGeometricallyReduced k R ↔ IsGeometricallyReduced k' R).1 hR

end

section

-- Proof sketch: first descend the faithfully flat local map `B → C` to the induced faithfully
-- flat map on closed fibers over the residue field `κ(A)`. Then test geometric reducedness of the
-- source closed fiber by tensoring with arbitrary field extensions of `κ(A)` and descend
-- reducedness along that faithfully flat base change using Lemma `10.164.2`.
/-- Geometric reducedness descends on the closed fiber along a faithfully flat local extension. -/
theorem isGeometricallyReduced_closedFiberDescent
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC : IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber C)) :
    IsGeometricallyReduced (ResidueField A) ((maximalIdeal A).Fiber B) := by
  sorry

-- Proof sketch: the five source-facing clauses above match the five fields of the canonical
-- Chapter 15 owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `fun k R ↦ IsGeometricallyReduced k R`; only property `(B)` needs a symmetry to match the
-- owner's local-to-global orientation.
/-- Lemma 15.51.9 packages geometric reducedness into the canonical Chapter 15 owner for
field-algebra properties satisfying the formal-fiber axioms `(A)` through `(E)`. -/
instance isGeometricallyReduced_hasPropertiesABCDE :
    IsGeometricallyReducedProperty.HasPropertiesABCDE where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    letI : IsGeometricallyReduced k R := hR
    exact isGeometricallyReduced_baseChange_of_finitelyGeneratedFieldExtension
  localizationCriterion := by
    intro k R _ _ _ _
    simpa using
      (isGeometricallyReduced_iff_forall_localization_atPrime :
        IsGeometricallyReduced k R ↔
          ∀ p : PrimeSpectrum R, IsGeometricallyReduced k (Localization.AtPrime p.asIdeal))
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hAB q
    exact fibers_areGeometricallyReduced_of_flat_of_regular hAB q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact isGeometricallyReduced_closedFiberDescent hBC hC
  separableBaseChange := by
    intro k k' R _ _ _ _ _ _ _ _ hR
    exact isGeometricallyReduced_hasPropertyE.separableBaseChange k k' R hR

end

end Algebra

/-! ### Lemma_15_51_10 (from Chap15) -/
open scoped TensorProduct

universe u

namespace FieldAlgebraProperty

section

variable (P : FieldAlgebraProperty)

/-- A field-algebra property has property `(E)` if it is preserved when the ground field is
replaced by a separable algebraic extension. -/
class HasPropertyE : Prop where
  /-- Base change of the ground field along a separable algebraic extension preserves `P`. -/
  separableBaseChange (k k' A : Type u) [Field k] [Field k'] [CommRing A]
      [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
      [Algebra.IsSeparable k k'] (hA : P k A) :
      P k' A

/- Domain sampling pass:
- primary domain: Chapter 15 formal-fiber axioms for `FieldAlgebraProperty`;
- sampled owner declarations:
  `FieldAlgebraProperty.HasPropertyA`,
  `FieldAlgebraProperty.HasPropertyB`,
  `FieldAlgebraProperty.HasPropertyC`,
  `FieldAlgebraProperty.HasPropertyD`;
- best owner abstraction: the chapter package extending `(A)` and `(B)` by the canonical upstream
  `(C)` and `(D)` owners from `Lemma_15_51_4`, together with the named bridge
  `IsGeometricallyNormalProperty`; this file adds only the genuinely new separable-base-field
  clause `(E)`.

Source/core/bridge triage:
- `P.HasPropertyE` is source-facing;
- `P.HasPropertiesABCDE` is the core/canonical owner wrapper;
- `IsGeometricallyNormalProperty` and the instance below are the thin bridge/view from
  `IsGeometricallyNormal` to that owner.
-/

/-- The five formal-fiber axioms `(A)` through `(E)` for a property of Noetherian algebras over
fields. -/
class HasPropertiesABCDE : Prop
    extends P.HasPropertyA, P.HasPropertyB, P.HasPropertyC, P.HasPropertyD, P.HasPropertyE

end

end FieldAlgebraProperty

namespace Algebra

section

/-- The canonical `FieldAlgebraProperty` bridge for geometric normality. -/
abbrev IsGeometricallyNormalProperty : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsGeometricallyNormal.{u, u} k A

section

variable {k k' A : Type u}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]

-- Proof sketch: this is exactly the separable-base-field invariance theorem for geometric
-- normality from Lemma `10.165.6`, repackaged as Chapter 15 property `(E)` for the canonical
-- bridge `IsGeometricallyNormalProperty`.
/-- Lemma 15.51.10 (5), owner-form: geometric normality has property `(E)` in the Chapter 15
formal-fiber package. -/
instance isGeometricallyNormal_hasPropertyE :
    IsGeometricallyNormalProperty.HasPropertyE where
  separableBaseChange k k' A := by
    intro _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

-- Proof sketch: property `(A)` is immediate from the definition of geometric normality under
-- finitely generated base change. Property `(B)` is the local criterion for normality. Property
-- `(C)` is ascent of normality along regular maps on each fiber, using `Lemma 15.42.2`. Property
-- `(D)` is faithfully flat descent of normality on fibers, using `Lemma 10.164.3`. Property `(E)`
-- is invariance of geometric normality under separable algebraic extension of the ground field,
-- using `Lemma 10.165.6`.
/-- Lemma 15.51.10: the field-algebra property `IsGeometricallyNormal` satisfies the formal-fiber
axioms `(A)`, `(B)`, `(C)`, `(D)`, and `(E)`. -/
instance isGeometricallyNormal_hasPropertiesABCDE :
    IsGeometricallyNormalProperty.HasPropertiesABCDE where
  baseChange := by
    sorry
  localizationCriterion := by
    sorry
  regularAscent := by
    sorry
  closedFiberDescent := by
    sorry
  separableBaseChange := by
    intro k k' A _ _ _ _ _ _ _ _ hA
    exact isGeometricallyNormal_iff_of_isSeparable.1 hA

end

end Algebra

/-! ### Lemma_15_51_11 (from Chap15) -/
open scoped TensorProduct
open Algebra
open IsLocalRing

universe u

/-
Domain sampling pass:
* primary domain: permanence properties of LinearRepresentations_Serre_1977's condition `(S_n)` for Noetherian rings under
  finitely generated field extensions and on fibers of ring maps;
* sampled owner declarations:
  - `Algebra.EssFiniteType` from Definition `9.6.6`, the canonical owner for finitely generated
    field extensions;
  - `SerreConditionS` from `Definition_10_157_1`, the canonical owner for the ring-theoretic
    condition `(S_n)`;
  - `cohenMacaulayRing_tensorProduct_of_fieldExtensions_of_finitelyGeneratedFieldExtension` from
    `Lemma_10_167_1`, the tensor-product fiber input behind the base-change step;
  - `serreConditionS_of_flat_of_fiber` from `Lemma_10_163_4`, the canonical ascent theorem along
    flat maps with fiberwise `(S_n)`;
  - `FieldAlgebraProperty.HasPropertiesABCDE` from `Lemma_15_51_10`, the chapter owner for the five
    formal-fiber axioms attached to a field-algebra property.

Source/core/bridge triage:
* `source-facing`: the tensor-product, localization, and fiberwise permanence statements in parts
  `(1)` through `(4)`;
* `core/canonical`: `SerreConditionS` together with `FieldAlgebraProperty.HasPropertiesABCDE`;
* `bridge/view`: the direct Chapter 15 field-algebra specialization `SerreConditionSProperty n`
  of the ring owner `SerreConditionS`, including the separable-ground-field clause `(5)` as
  property `(E)`.

Primitive data are only the owner property `SerreConditionS`; the chapter-level `(A)`--`(E)`
package is derived API and should reuse the existing owner class rather than a bespoke wrapper.
-/

section

variable {n : ℕ}

-- Proof sketch: the ring map `R → k' ⊗[k] R` is flat, and its fibers are Cohen-Macaulay by
-- Lemma `10.167.1` because they are tensor products of field extensions with one side
-- finitely generated over the base. Apply Lemma `10.163.4` to ascend LinearRepresentations_Serre_1977's condition `(S_n)`
-- along this flat base change.
/-- Lemma 15.51.11 (1): if `k → R` is a map from a field to a Noetherian ring, and
`k' / k` is a finitely generated field extension, then `R` having LinearRepresentations_Serre_1977's condition `(S_n)`
implies that `k' ⊗[k] R` also has LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
    {k : Type u} {k' : Type u} {R : Type u}
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [Algebra.EssFiniteType k k'] [SerreConditionS R n] :
    SerreConditionS (k' ⊗[k] R) n := sorry

-- Proof sketch: the forward implication is inherited by localizations of a ring satisfying
-- `(S_n)`. For the converse, a Noetherian ring has `(S_n)` exactly when each localization at a
-- prime does, which is the local formulation built into `SerreConditionS`.
/-- Lemma 15.51.11 (2): if `R` is Noetherian, then `R` has LinearRepresentations_Serre_1977's condition `(S_n)`
if and only if every localization `R_𝔭` has LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem serreConditionS_iff_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    SerreConditionS R n ↔
      ∀ p : PrimeSpectrum R, SerreConditionS (Localization.AtPrime p.asIdeal) n := sorry

-- Proof sketch: for each `p : Spec(A)`, base change the regular map `B → C` along
-- `A → κ(p)` to obtain a regular map on the fibers. Regular fibers are geometrically regular,
-- hence Cohen-Macaulay, so Lemma `10.163.4` ascends `(S_n)` from the fiber of `A → B` to the
-- fiber of `A → C`.
/-- Lemma 15.51.11 (3): if `A → B → C` are maps of commutative rings, `C` is Noetherian, the
fibers of `A → B` satisfy LinearRepresentations_Serre_1977's condition `(S_n)`, and `B → C` is a regular ring map, then the
fibers of `A → C` satisfy LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem fiber_serreConditionS_of_regularRingMap
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing C] [(algebraMap B C).IsRegularRingMap]
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n := sorry

-- Proof sketch: for each `p : Spec(A)`, base change the faithfully flat map `B → C` along
-- `A → κ(p)` to obtain a faithfully flat map on fibers. Then apply Lemma `10.164.5` to descend
-- LinearRepresentations_Serre_1977's condition `(S_n)` from the fiber of `A → C` to the corresponding fiber of `A → B`.
/-- Lemma 15.51.11 (4): if `A → B → C` are maps of commutative rings, the fibers of `A → C`
satisfy LinearRepresentations_Serre_1977's condition `(S_n)`, and `B → C` is faithfully flat, then the fibers of `A → B`
satisfy LinearRepresentations_Serre_1977's condition `(S_n)`. -/
theorem fiber_serreConditionS_of_faithfullyFlat
    {A : Type u} {B : Type u} {C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hff : (algebraMap B C).FaithfullyFlat)
    (hfiber : ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber C) n) :
    ∀ p : PrimeSpectrum A, SerreConditionS (p.asIdeal.Fiber B) n := sorry

end

namespace Algebra

section

variable {n : ℕ}

/-- The canonical `FieldAlgebraProperty` bridge for LinearRepresentations_Serre_1977's condition `(S_n)`. -/
abbrev SerreConditionSProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ SerreConditionS A n

-- Proof sketch: `SerreConditionS A n` depends only on the underlying Noetherian ring `A`, so
-- changing the base field along a separable algebraic extension leaves the same ring property.
/-- Lemma 15.51.11 (5), owner-form: the Chapter 15 field-algebra property
`SerreConditionSProperty n` has property `(E)`, i.e. LinearRepresentations_Serre_1977's condition `(S_n)` is
unchanged under separable algebraic extension of the ground field. -/
theorem serreConditionS_hasPropertyE :
    (SerreConditionSProperty n).HasPropertyE := by
  refine { separableBaseChange := ?_ }
  intro k k' A _ _ _ _ _ _ _ _ hS
  exact hS

-- Proof sketch: the five source-facing parts of Lemma `15.51.11` already match the five fields of
-- the canonical chapter owner `FieldAlgebraProperty.HasPropertiesABCDE` for the property
-- `SerreConditionSProperty n`, so the instance reuses those owner theorems directly and only
-- spells out the closed-fiber faithfully flat descent step.
/-- Lemma 15.51.11 packages LinearRepresentations_Serre_1977's condition `(S_n)` into the canonical Chapter 15 owner for
field-algebra properties satisfying `(A)` through `(E)`. -/
instance serreConditionS_hasPropertiesABCDE :
    (SerreConditionSProperty n).HasPropertiesABCDE where
  baseChange := by
    intro k R K _ _ _ _ _ _ _ hR
    letI : SerreConditionS R n := hR
    exact serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
  localizationCriterion := by
    intro k R _ _ _ _
    exact serreConditionS_iff_localizationAtPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber q
    exact fiber_serreConditionS_of_regularRingMap hfiber q
  closedFiberDescent := by
    intro A B C
    intro _ _ _ _ _ _ _
    intro _ _ _
    intro _ _ _
    intro _ _
    intro hBC hC
    letI : SerreConditionS ((maximalIdeal A).Fiber C) n := hC
    letI : Algebra B ((maximalIdeal A).Fiber B) := Algebra.TensorProduct.rightAlgebra
    let D := ((maximalIdeal A).Fiber B) ⊗[B] C
    letI : CommRing D := inferInstance
    letI : Algebra ((maximalIdeal A).Fiber B) D := Algebra.TensorProduct.leftAlgebra
    letI : Algebra C D := Algebra.TensorProduct.rightAlgebra
    letI : Module.FaithfullyFlat B C := RingHom.faithfullyFlat_algebraMap_iff.mp hBC
    let f : ((maximalIdeal A).Fiber B) →+* D := algebraMap ((maximalIdeal A).Fiber B) D
    have hf : f.FaithfullyFlat := by
      letI : Module.FaithfullyFlat ((maximalIdeal A).Fiber B) D := by infer_instance
      simpa [f] using (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance : f.FaithfullyFlat)
    let e : D ≃+* ((maximalIdeal A).Fiber C) :=
      (Algebra.IsPushout.cancelBaseChangeAlg A ((maximalIdeal A).ResidueField)
        B ((maximalIdeal A).Fiber B) C).toRingEquiv
    let g : D →+* ((maximalIdeal A).Fiber C) := e.toRingHom
    have hg : g.FaithfullyFlat := by
      simpa [g] using (RingHom.FaithfullyFlat.of_bijective e.bijective : g.FaithfullyFlat)
    have hfiber_ff : (g.comp f).FaithfullyFlat := by
      change (RingHom.comp g f).FaithfullyFlat
      exact RingHom.FaithfullyFlat.stableUnderComposition f g hf hg
    letI : Algebra ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C) := RingHom.toAlgebra (g.comp f)
    simpa [f, g] using
      (serreConditionS_of_faithfullyFlat
        (algebraMap ((maximalIdeal A).Fiber B) ((maximalIdeal A).Fiber C)) hfiber_ff :
          SerreConditionS ((maximalIdeal A).Fiber B) n)
  separableBaseChange := serreConditionS_hasPropertyE.separableBaseChange

end

end Algebra

/-! ### Lemma_15_51_12 (from Chap15) -/
namespace Algebra

universe u

open IsLocalRing
open scoped TensorProduct

section

/-
Domain sampling pass:
* primary domain: Chapter 15 formal-fiber axioms for field-algebra properties, specialized to the
  Cohen-Macaulay ring property from Chapter 10;
* sampled owner declarations:
  - `CohenMacaulayRing` from `Definition_10_104_6`, the source-facing ring owner;
  - `cohenMacaulayRing_tensorProduct_of_finitelyGeneratedFieldExtension` from `Lemma_10_167_1`,
    the canonical one-sided tensor-product theorem for finitely generated field extensions;
  - `SerreConditionSProperty` from `Lemma_15_51_11`, the chapter owner for the fiberwise
    `(S_n)` formal-fiber axioms;
  - `FieldAlgebraProperty.HasPropertiesABCDE` from `Lemma_15_51_10`, the chapter owner for the five
    formal-fiber axioms.

Source/core/bridge triage:
* `source-facing`: the ring property `CohenMacaulayRing`;
* `core/canonical`: the Chapter 15 owner `FieldAlgebraProperty.HasPropertiesABCDE`;
* `bridge/view`: the already-packaged chapter owner `SerreConditionSProperty n`, used internally to
  recover the `(C)` and `(D)` clauses for `CohenMacaulayRing` via the characterization by all
  LinearRepresentations_Serre_1977 conditions.

Primitive data are only the canonical owner `CohenMacaulayRing`. The chapter package `(A)` through
`(E)` is derived API, so the owner-form declarations below should use the canonical predicate
directly rather than a one-file alias.
-/
-- Proof sketch: `CohenMacaulayRing A` depends only on the underlying Noetherian ring `A`, so
-- changing the base field along a separable algebraic extension does not alter the property.
/-- Lemma 15.51.12 (5), owner-form: Cohen-Macaulayness has property `(E)` in the Chapter 15
formal-fiber package, i.e. it is unchanged by replacing the ground field with a separable
algebraic extension. -/
theorem cohenMacaulay_hasPropertyE :
    FieldAlgebraProperty.HasPropertyE
      (fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ CohenMacaulayRing A) := by
  refine ⟨?_⟩
  intro k k' A _ _ _ _ _ _ _ _ hCM
  exact hCM

-- Proof sketch: property `(A)` is the canonical tensor-product theorem from Lemma `10.167.1`.
-- Property `(B)` is reconstructed from the owner theorem
-- `serreConditionS_iff_localizationAtPrime`. Properties `(C)` and `(D)` are recovered from the
-- already-packaged Chapter 15 owner `SerreConditionSProperty n` for each `n`, then reassembled by
-- the canonical characterization `CohenMacaulayRing.of_serreConditionS`. Property `(E)` is the
-- base-field independence theorem above.
/-- Lemma 15.51.12 packages Cohen-Macaulayness into the canonical Chapter 15 owner for
field-algebra properties satisfying the formal-fiber axioms `(A)` through `(E)`. -/
instance cohenMacaulay_hasPropertiesABCDE :
    FieldAlgebraProperty.HasPropertiesABCDE
      (fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ CohenMacaulayRing A) where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    letI : CohenMacaulayRing A := hA
    let T := TensorProduct k K A
    let _ : SerreConditionS A 0 := CohenMacaulayRing.serreConditionS A 0
    let _ : SerreConditionS T 0 := serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension
    exact CohenMacaulayRing.of_serreConditionS T fun n ↦
      let _ : SerreConditionS A n := CohenMacaulayRing.serreConditionS A n
      (serreConditionS_tensorProduct_of_finitelyGeneratedFieldExtension : SerreConditionS T n)
  localizationCriterion := by
    intro k A _ _ _ _
    constructor
    · intro hA p
      letI : CohenMacaulayRing A := hA
      let _ :
          Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal) :=
        localizedRing_cohenMacaulay A p
      exact
        { toIsNoetherian := inferInstance
          toLocallyCohenMacaulay := inferInstance }
    · intro hA
      refine CohenMacaulayRing.of_serreConditionS A fun n ↦ ?_
      have hSerre :
          SerreConditionS A n ↔
            ∀ p : PrimeSpectrum A, SerreConditionS (Localization.AtPrime p.asIdeal) n :=
        serreConditionS_iff_localizationAtPrime
      exact hSerre.2 fun p ↦ by
        letI : CohenMacaulayRing (Localization.AtPrime p.asIdeal) := hA p
        exact CohenMacaulayRing.serreConditionS (Localization.AtPrime p.asIdeal) n
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber p
    let T := TensorProduct A C p.asIdeal.ResidueField
    let _ : Algebra.EssFiniteType C T := inferInstance
    let _ : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing C T
    let _ : IsNoetherianRing (p.asIdeal.Fiber C) :=
      isNoetherianRing_of_ringEquiv T
        (Algebra.TensorProduct.comm A p.asIdeal.ResidueField C).toRingEquiv.symm
    refine CohenMacaulayRing.of_serreConditionS (p.asIdeal.Fiber C) fun n ↦ ?_
    have hSerre :
        ∀ q : PrimeSpectrum A, SerreConditionS (q.asIdeal.Fiber C) n :=
      fiber_serreConditionS_of_regularRingMap fun q ↦ by
        letI : CohenMacaulayRing (q.asIdeal.Fiber B) := hfiber q
        exact CohenMacaulayRing.serreConditionS (q.asIdeal.Fiber B) n
    exact hSerre p
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    let T := TensorProduct A B (maximalIdeal A).ResidueField
    let _ : Algebra.EssFiniteType B T := inferInstance
    let _ : IsNoetherianRing T := Algebra.EssFiniteType.isNoetherianRing B T
    let _ : IsNoetherianRing ((maximalIdeal A).Fiber B) :=
      isNoetherianRing_of_ringEquiv T
        (Algebra.TensorProduct.comm A (maximalIdeal A).ResidueField B).toRingEquiv.symm
    refine CohenMacaulayRing.of_serreConditionS ((maximalIdeal A).Fiber B) fun n ↦ ?_
    have hCSerre : SerreConditionS ((maximalIdeal A).Fiber C) n := by
      letI : CohenMacaulayRing ((maximalIdeal A).Fiber C) := hC
      exact CohenMacaulayRing.serreConditionS ((maximalIdeal A).Fiber C) n
    exact
      ((inferInstance : (SerreConditionSProperty n).HasPropertyD).closedFiberDescent
        A B C hBC hCSerre)
  separableBaseChange := by
    simpa using
      cohenMacaulay_hasPropertyE.separableBaseChange

end

end Algebra

/-! ### Lemma_15_51_13 (from Chap15) -/
open Algebra
open IsLocalRing
open scoped TensorProduct

universe u

/- Domain sampling pass:
- primary domain: Chapter 15 field-algebra properties satisfying the formal-fiber axioms,
  specialized to LinearRepresentations_Serre_1977's condition `(R_n)` after finite extensions of the base field;
- sampled owner declarations:
  `SerreConditionR`,
  `serreConditionR_of_flat_of_fiber`,
  `serreConditionR_of_faithfullyFlat`,
  `FieldAlgebraProperty.HasPropertiesABCDE`,
  `FieldAlgebraProperty`;
- best owner abstraction: the source-facing Chapter 15 owner
  `FiniteFieldExtensionSerreConditionRProperty n`, whose primitive data are exactly the
  `SerreConditionR` conditions on the tensor-product base changes `K ⊗[k] A`;
- source/core/bridge triage:
  `FiniteFieldExtensionSerreConditionRProperty n` is `source-facing`,
  `SerreConditionR` on each finite tensor-product base change is `core/canonical`,
  and `FieldAlgebraProperty.HasPropertiesABCDE` is the derived `bridge/view` package of axioms
  `(A)` through `(E)`.

Primitive data are only the predicate saying that every finite field extension `K / k` makes
`K ⊗[k] A` satisfy `SerreConditionR _ n`. The chapter-level `(A)`--`(E)` package is derived API
on top of that source-facing owner, so the file should expose that owner directly instead of
keeping separate one-use closure wrappers.
-/

namespace Algebra

/-- The finite-field-extension form of LinearRepresentations_Serre_1977's condition `(R_n)`, viewed as a Chapter 15
`FieldAlgebraProperty`. -/
abbrev FiniteFieldExtensionSerreConditionRProperty (n : ℕ) : FieldAlgebraProperty :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      SerreConditionR (K ⊗[k] A) n

end Algebra

section

variable {n : ℕ}

-- Proof sketch: fix a finitely generated extension `K / k` and a finite extension `L / K`.
-- Re-express `L ⊗[K] (K ⊗[k] A)` as `L ⊗[k] A`, note that `L / k` is still finite after
-- descending to a finite subextension of the chosen finitely generated extension, and then apply
-- the defining finite-field-extension hypothesis over `k`.
/-- Lemma 15.51.13 (1): the finite-field-extension form of LinearRepresentations_Serre_1977's condition `(R_n)` is preserved
after base change along a finitely generated extension of the ground field. -/
theorem finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension
    {k : Type u} {K : Type u} {A : Type u}
    [Field k] [Field K] [CommRing A] [Algebra k K] [Algebra k A] [Algebra.EssFiniteType k K]
    (hA : FiniteFieldExtensionSerreConditionRProperty n k A) :
    FiniteFieldExtensionSerreConditionRProperty n K (K ⊗[k] A) := sorry

section

variable {k : Type u} {A : Type u} [Field k] [CommRing A] [Algebra k A]

-- Proof sketch: unfold the source-facing property and apply the prime-local criterion for
-- `SerreConditionR` to each finite tensor-product base change `K ⊗[k] A`.
/-- Lemma 15.51.13 (2): for a Noetherian `k`-algebra `A`, the finite-field-extension form of
LinearRepresentations_Serre_1977's condition `(R_n)` can be checked on the localizations `A_𝔭`. -/
theorem finiteFieldExtensionSerreConditionR_iff_localizationAtPrime [IsNoetherianRing A] :
    FiniteFieldExtensionSerreConditionRProperty n k A ↔
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n k (Localization.AtPrime p.asIdeal) := sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]

-- Proof sketch: after any finite residue-field extension of `κ(p)`, apply
-- `serreConditionR_of_flat_of_fiber` to the induced base change of the fiber map. Regularity of
-- the fibers of `B → C` comes from the regular-ring-map hypothesis, so `(R_n)` ascends from the
-- fibers of `A → B` to those of `A → C`.
/-- Lemma 15.51.13 (3): if `A → B → C` are maps of Noetherian rings, `A → B` is flat, every fiber
of `A → B` satisfies the finite-field-extension form of `(R_n)`, and `B → C` is regular, then
every fiber of `A → C` satisfies the same property. -/
theorem fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap [Module.Flat A B]
    [(algebraMap B C).IsRegularRingMap]
    (hfiber :
      ∀ p : PrimeSpectrum A,
        FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber B)) :
    ∀ p : PrimeSpectrum A,
      FiniteFieldExtensionSerreConditionRProperty n p.asIdeal.ResidueField (p.asIdeal.Fiber C) :=
  sorry

end

section

variable {A : Type u} {B : Type u} {C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
variable [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)]

-- Proof sketch: after any finite residue-field extension of `ResidueField A`, the induced map on
-- closed fibers stays faithfully flat. Apply `serreConditionR_of_faithfullyFlat` to descend
-- `(R_n)` from the extended closed fiber over `C` to the corresponding extended closed fiber over
-- `B`.
/-- Lemma 15.51.13 (4): under a faithfully flat local extension on closed fibers, the
finite-field-extension form of LinearRepresentations_Serre_1977's condition `(R_n)` descends from the closed fiber over `C`
to the closed fiber over `B`. -/
theorem closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat
    (hBC : RingHom.FaithfullyFlat (algebraMap B C))
    (hC :
      FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber C)) :
    FiniteFieldExtensionSerreConditionRProperty n (ResidueField A) ((maximalIdeal A).Fiber B) :=
  sorry

end

end

namespace Algebra

section

variable {n : ℕ}

-- Proof sketch: reduce to the finite separable case by descending the chosen finite extension of
-- the larger base field to a finite subextension, then identify the resulting tensor product with
-- a localization of a finite base change over the original field using Lemma `10.43.8`.
/-- Lemma 15.51.13 (5), owner-form: the Chapter 15 field-algebra property
`P(k → R) := ∀ K / k` finite, `SerreConditionR (K ⊗[k] R) n` has property `(E)`. -/
theorem finiteFieldExtensionSerreConditionR_hasPropertyE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertyE := sorry

-- Proof sketch: property `(A)` writes a finitely generated extension `K / k` as in Lemma
-- `10.45.3`, passes to a smooth `k'`-model of the separable part using Lemma `10.158.10`,
-- ascends `(R_n)` along the resulting smooth map by Lemma `10.163.5`, localizes to the fraction
-- field, and then descends back along the faithfully flat map to `K` using Lemma `10.164.6`.
-- Property `(B)` is the prime-local criterion for `(R_n)`. Property `(C)` applies
-- Lemma `10.163.5` fiberwise after finite residue-field extension. Property `(D)` is the
-- closed-fiber faithfully flat descent statement from Lemma `10.164.6`. Property `(E)` is the
-- separable-base-field reduction recorded in `finiteFieldExtensionSerreConditionR_hasPropertyE`.
/-- Lemma 15.51.13 packages the finite-field-extension form of LinearRepresentations_Serre_1977's condition `(R_n)` into the
canonical owner for field-algebra properties satisfying `(A)` through `(E)`. -/
instance finiteFieldExtensionSerreConditionR_hasPropertiesABCDE :
    (FiniteFieldExtensionSerreConditionRProperty n).HasPropertiesABCDE where
  baseChange := by
    intro k A K _ _ _ _ _ _ _ hA
    exact finiteFieldExtensionSerreConditionR_baseChange_of_finitelyGeneratedFieldExtension hA
  localizationCriterion := by
    intro k A _ _ _ _
    exact finiteFieldExtensionSerreConditionR_iff_localizationAtPrime
  regularAscent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hfiber q
    exact fiber_finiteFieldExtensionSerreConditionR_of_regularRingMap hfiber q
  closedFiberDescent := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hBC hC
    exact closedFiber_finiteFieldExtensionSerreConditionR_of_faithfullyFlat hBC hC
  separableBaseChange := by
    simpa using finiteFieldExtensionSerreConditionR_hasPropertyE.separableBaseChange

end

end Algebra

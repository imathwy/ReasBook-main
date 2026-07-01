import stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

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

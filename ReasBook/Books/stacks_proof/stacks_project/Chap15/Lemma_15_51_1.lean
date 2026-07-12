import StacksProject_2024.Chap15.Definition_15_50_1
import StacksProject_2024.Chap15.Lemma_15_10_5
import Mathlib.Tactic.StacksAttribute

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
/-- Helper for Lemma 15.51.1: the formal fiber over a prime of `R_p` is the same `κ(𝔮)`-algebra
as the formal fiber over its contracted prime `𝔮 ⊆ p` in `R`. -/
-- TODO: prove this by the canonical residue-field identification `κ(q') ≃ κ(q)` for primes of
-- `R_p` and the resulting tensor presentation of both fiber rings over the same `κ(q)`.
private theorem formalFiber_over_localizationPrime_iff_contractedPrime
    (p : PrimeSpectrum R) (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    let q0 : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
    P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) ↔
      P q0.asIdeal.ResidueField (q0.asIdeal.Fiber (R̂_[p])) := sorry

/-- Rewriting the fibers of the completed localization `R_p → R̂_𝔭` by primes `q ⊆ p` of `R`
gives the prime-pair criterion. -/
private theorem satisfiesPFormalFiberCondition_iff_satisfiesPPrimePairCondition :
    (∀ p : PrimeSpectrum R,
      ∀ q : PrimeSpectrum (Localization.AtPrime p.asIdeal),
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p]))) ↔
      SatisfiesPPrimePairCondition P R := by
  constructor
  · intro h p q hqp
    -- Reindex the prime of `R` below `p` as the corresponding prime of `R_p`.
    let q' :
        PrimeSpectrum (Localization.AtPrime p.asIdeal) :=
      (IsLocalization.AtPrime.primeSpectrumOrderIso
        (Localization.AtPrime p.asIdeal) p.asIdeal).symm ⟨q, hqp⟩
    have hcomap :
        PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q' = q := by
      simpa [q'] using
        atPrime_primeSpectrumOrderIso_symm_apply_comap p.asIdeal ⟨q, hqp⟩
    let q0 : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q'
    -- Transport from the prime of `R_p` back to its contracted prime in `R`.
    have htransport :
        P q'.asIdeal.ResidueField (q'.asIdeal.Fiber (R̂_[p])) ↔
          P q0.asIdeal.ResidueField (q0.asIdeal.Fiber (R̂_[p])) := by
      simpa [q0] using
        formalFiber_over_localizationPrime_iff_contractedPrime (P := P) (p := p) q'
    have hq0 : q0 = q := by
      simpa [q0] using hcomap
    have hresult :
        P q0.asIdeal.ResidueField (q0.asIdeal.Fiber (R̂_[p])) :=
      htransport.mp (h p q')
    exact hq0 ▸ hresult
  · intro h p q
    -- Contract a prime of `R_p` back to the corresponding prime of `R`.
    let q0 : PrimeSpectrum R :=
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q
    have hq0p : q0.asIdeal ≤ p.asIdeal := by
      -- Every prime of `R_p` contracts to a prime of `R` contained in `p`.
      change Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q.asIdeal ≤ p.asIdeal
      intro x hx
      by_contra hxp
      exact q.2.ne_top <|
        Ideal.eq_top_of_isUnit_mem _ hx <|
          IsLocalization.map_units (Localization.AtPrime p.asIdeal)
            (⟨x, hxp⟩ : p.asIdeal.primeCompl)
    -- Apply the prime-pair hypothesis to the contracted prime.
    exact
      (formalFiber_over_localizationPrime_iff_contractedPrime (P := P) (p := p) q).mpr <|
        h p q0 hq0p

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
@[stacks 0BIS]
theorem isPRing_iff_satisfiesPPrimePairCondition [IsNoetherianRing R] :
    IsPRing P R ↔ SatisfiesPPrimePairCondition P R :=
  ⟨IsPRing.satisfiesPPrimePairCondition, isPRing_of_satisfiesPPrimePairCondition⟩

-- Proof sketch: apply the prime-pair criterion to the local ring `R_p`. Its primes correspond to
-- the primes `q` of `R` with `q ≤ p`, and under that identification the formal fiber of
-- `Localization.AtPrime p.asIdeal` at the prime above `q` is exactly `q.asIdeal.Fiber (R̂_[p])`.
/-- Rephrasing the `P`-ring condition on the local ring `R_p`, one may quantify directly over
primes `q ⊆ p` of `R`. -/
-- TODO: the current left-hand owner statement is stronger than the fixed-top-prime condition on
-- `R_p`; replace it with that corrected local condition and update downstream uses.
theorem isPRing_localizationAtPrime_iff [IsNoetherianRing R] (p : PrimeSpectrum R) :
    IsPRing P (Localization.AtPrime p.asIdeal) ↔
      ∀ q : PrimeSpectrum R, q.asIdeal ≤ p.asIdeal →
        P q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) := sorry

end

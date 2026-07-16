import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)` from `Chap05/Definition_5_11_4`
- ring owner: `IsCatenaryRing R` from `Lemma_10_105_2`
- universal owner: `UniversallyCatenaryRing R` from `Definition_10_105_3`
- localization bridge: `localization_isCatenaryRing` and
  `localization_universallyCatenaryRing` from `Lemma_10_105_4`

Layer triage:
- `source-facing`: Lemma 10.105.6 records the prime-local and maximal-local TFAE criteria
- `core/canonical`: `IsCatenaryRing` and `UniversallyCatenaryRing`
- `bridge/view`: the localization predicates below are derived from the canonical owner instances

Primitive data already belongs to the upstream owner abstractions, so this file should only expose
the TFAE bridge and should not duplicate the catenary owner definitions locally.
-/

/-- Lemma 10.105.6 (1): for a commutative ring `R`, the following are equivalent: `R` is
catenary, every localization `R_𝔭` at a prime ideal is catenary, and every localization `R_𝔪`
at a maximal ideal is catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate because maximal ideals
-- are prime. For `(3) → (1)`, compare chains of prime ideals between `𝔭 ⊆ 𝔮` in `R` with the
-- corresponding chains in a localization `R_𝔪` for a maximal ideal `𝔪` containing `𝔮`.
theorem isCatenaryRing_localization_tfae :
    List.TFAE
      [ IsCatenaryRing R,
        ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := sorry

section

variable [IsNoetherianRing R]

/-- Lemma 10.105.6 (2): for a Noetherian commutative ring `R`, the following are equivalent:
`R` is universally catenary, every localization `R_𝔭` at a prime ideal is universally catenary,
and every localization `R_𝔪` at a maximal ideal is universally catenary. -/
-- Proof sketch: `(1) → (2)` is Lemma `10.105.4`. `(2) → (3)` is immediate. For `(3) → (1)`,
-- let `R → A` be a finite type algebra. Localizing at a prime `𝔮` of `A` above `𝔭 ⊆ R`, choose a
-- maximal ideal `𝔪` of `R` containing `𝔭`; then `R_𝔭` is a localization of `R_𝔪`, so `A_𝔮` is
-- catenary, and the first TFAE gives catenarity of `A`.
theorem universallyCatenaryRing_localization_tfae :
    List.TFAE
      [ UniversallyCatenaryRing R,
        ∀ p : PrimeSpectrum R, UniversallyCatenaryRing (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, UniversallyCatenaryRing (Localization.AtPrime m.asIdeal) ] := sorry

end

end

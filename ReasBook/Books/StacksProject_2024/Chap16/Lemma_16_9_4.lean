import Mathlib
import StacksProject_2024.Chap16.Lemma_16_9_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Algebra

open PrimeSpectrum
open scoped Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]

/- Domain-style sampling:
- primary domain: localized commutative algebra for resolution data at a prime;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `exists_factorization_with_singularIdeal_not_le_of_localResolutionAtMinimalPrime`,
  `Localization.AtPrime`,
  `Algebra.algebraMapSubmonoid`;
- best owner abstraction: the localized hypothesis is the canonical owner
  `ResolvableAtPrime` on the localized rings, exactly as in Lemma `16.9.3`;
- primitive data: the minimal prime itself, now taken canonically as `q : PrimeSpectrum Λ`,
  together with the localized rings `R_𝔭`, `A_𝔭`, `Λ_𝔮` and the prime ideal `𝔮Λ_𝔮`;
- derived API: the local-resolution hypothesis is stated directly via `ResolvableAtPrime` on those
  localized rings, with the prime structure supplied by `q` rather than repeated `let`-bound
  instance reconstruction.

Source/core/bridge triage:
- `source-facing`: Lemma `16.9.4`, which upgrades a local resolution at a minimal prime to a
  global one under the dimension-zero hypothesis;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: the localized rings built from the prime-spectrum point `q`.
-/

section Prime

variable (q : PrimeSpectrum Λ)

local notation "𝔮" => q.asIdeal
local notation "Rₚ" => Localization.AtPrime (q.asIdeal.under R)
local notation "Sₚ" => Algebra.algebraMapSubmonoid A (Ideal.primeCompl (q.asIdeal.under R))
local notation "Aₚ" => Localization Sₚ
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal
local notation "𝔮Λ_𝔮" => Ideal.map (algebraMap Λ Λ_𝔮) q.asIdeal

-- Proof sketch: use Lemma `16.9.3` to replace the assumed local resolution at `q` by a finitely
-- presented factorization `A → C → Λ` with `𝔥_C` not contained in `q`. Because
-- `ringKrullDim (Localization.AtPrime q) = 0`, the local ring `Λ_q` is Artinian local, so some
-- power of `𝔥_A` is killed away from `q`. Adjoin variables and relations as in the textbook proof
-- to build a finitely presented `R`-algebra `B` over `A` whose target singular ideal contains
-- `𝔥_A` and still avoids `q`.
/-- Lemma 16.9.4: in Situation `16.9.1`, let `𝔭 = R ∩ 𝔮`. Assume `R` is Noetherian, `A` is
finitely presented over `R`, `𝔮` is minimal over `𝔥_A`, the localized map
`R_𝔭 → A_𝔭 → Λ_𝔮 ⊃ 𝔮 Λ_𝔮` can be resolved, and `ringKrullDim (Localization.AtPrime 𝔮) = 0`.
Then `R → A → Λ ⊃ 𝔮` can be resolved. -/
theorem resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero
    [IsNoetherianRing R] [FinitePresentation R A]
    (hq : q.asIdeal ∈ (h(A⁄R, Λ)).minimalPrimes)
    (hlocal : ResolvableAtPrime Rₚ Aₚ Λ_𝔮 𝔮Λ_𝔮)
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0) :
    ResolvableAtPrime R A Λ q.asIdeal := by
  sorry

end Prime

end

end Algebra

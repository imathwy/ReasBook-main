import Mathlib
import StacksProject_2024.Chap10.Lemma_10_166_5
import StacksProject_2024.Chap16.Lemma_16_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open PrimeSpectrum
open scoped Algebra

section

variable {k : Type u} {A : Type v} {Λ : Type w}
variable [Field k] [CommRing A] [CommRing Λ]
variable [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]

/-
Domain-style sampling:
- primary domain: source-facing resolution-at-a-prime statements in commutative algebra;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_iff`,
  `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`,
  `resolvableAtPrime_of_minimalPrime_regularLocalRing_and_separable_residueField`;
- best owner abstraction: Chapter 16 uses `ResolvableAtPrime` as the owner for the statement
  that `k → A → Λ ⊃ q` can be resolved; an explicit finitely presented factorization is derived API
  obtained by unfolding that predicate, not a second public owner;
- primitive data: the prime-spectrum point `q : PrimeSpectrum Λ`, its minimal-prime condition over
  `h(A⁄k, Λ)`, and the ambient geometric-regularity hypotheses;
- derived API: explicit factorization data via `resolvableAtPrime_iff`.

Source/core/bridge triage:
- `source-facing`: the statement that `k → A → Λ ⊃ q` can be resolved;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: `resolvableAtPrime_iff`.
-/

-- Proof sketch: the proof constructs a local resolution at `𝔮` by the Artinian approximation and
-- power-adjoining arguments of Lemmas `16.11.2` and `16.11.3`, then applies Lemma `16.9.4`. The
-- geometric regularity of `Λ` over the field `k` provides the approximation step, and minimality
-- of `𝔮` over `𝔥_A` supplies the singular-ideal control needed to conclude.
/-- Lemma 16.11.4: let `k → A → Λ ⊃ 𝔮` be as in Situation `16.9.1`, with `k` a field of
characteristic `p > 0`, `A` finitely presented over `k`, `Λ` geometrically regular over `k`
(hence Noetherian), and `𝔮` minimal over `𝔥_A`. Then `k → A → Λ ⊃ 𝔮` can be resolved. -/
theorem resolvableAtPrime_at_minimalPrime_of_geometricallyRegular
    {p : ℕ} [Fact p.Prime] [CharP k p] [FinitePresentation k A]
    [IsGeometricallyRegular k Λ] (q : PrimeSpectrum Λ)
    (hq : q.asIdeal ∈ (h(A⁄k, Λ)).minimalPrimes) :
    ResolvableAtPrime k A Λ q.asIdeal := sorry

end

end Algebra

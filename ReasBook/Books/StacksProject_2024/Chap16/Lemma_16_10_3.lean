import Mathlib
import StacksProject_2024.Chap10.Lemma_10_140_5
import StacksProject_2024.Chap16.Lemma_16_9_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

open PrimeSpectrum
open scoped Algebra

section

variable {k : Type u} {A : Type v} {Λ : Type w}
variable [Field k] [CommRing A] [CommRing Λ]
variable [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
variable [FinitePresentation k A] [Algebra.FiniteType k Λ]

/-
Domain-style sampling:
- primary domain: primewise resolution statements for finitely presented algebras over a field,
  organized around the Chapter 16 owner predicate `ResolvableAtPrime`;
- sampled owner declarations:
  `ResolvableAtPrime`,
  `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`,
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`,
  `Algebra.FiniteType.isNoetherianRing`;
- best owner abstraction: the public statement should stay source-facing on
  `ResolvableAtPrime k A Λ 𝔮`; the regular-local-ring and separable-residue-field hypotheses are
  primitive source data, and the finite-type hypothesis on `Λ` is primitive bridge-side data
  needed to reuse the chapter's canonical smoothness criterion and to recover the Noetherian
  hypothesis on `Λ` canonically via `Algebra.FiniteType.isNoetherianRing`; primewise smoothness is
  derived API coming from `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField`;
- primitive data: a minimal prime `𝔮` of `h(A⁄k, Λ)`, regularity of `Λ_𝔮`, separability of
  `κ(𝔮) / k` in the Stacks Project sense, and finite type of `Λ` over `k`;
- derived API: the local smoothness input used to build the local resolution and the final passage
  from a local resolution at `𝔮` to `ResolvableAtPrime k A Λ 𝔮`.

Source/core/bridge triage:
- `source-facing`: the theorem that `k → A → Λ ⊃ 𝔮` is resolvable;
- `core/canonical`: `ResolvableAtPrime`;
- `bridge/view`: the primewise smoothness criterion
  `isSmoothAt_iff_isRegularLocalRing_of_separable_residueField` together with the local-to-global
  resolution owner `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-/

section Prime

variable (q : PrimeSpectrum Λ)

local notation "𝔮" => q.asIdeal
local notation "Λ_𝔮" => Localization.AtPrime q.asIdeal

-- Proof sketch: choose parameters in `Λ` as in Lemma `16.10.2`, use Lemma `16.9.2` to construct
-- a local resolution after quotienting by the corresponding eighth powers, and then apply the
-- local-to-global owner theorem `resolvableAtPrime_of_localResolvableAtMinimalPrime_of_ringKrullDim_eq_zero`.
-- The finite-type and separable-residue-field hypotheses identify regularity of `Λ_𝔮` with
-- smoothness at `𝔮` via Lemma `10.140.5`, which supplies the smoothness input needed in the local
-- construction; the finite-type hypothesis also supplies the Noetherianity of `Λ` canonically via
-- `Algebra.FiniteType.isNoetherianRing`.
/-- Lemma 16.10.3: in Situation `16.9.1`, if `k` is a field, `A` is finitely presented over `k`,
`Λ` is a finite type `k`-algebra, `q` is a minimal prime of `𝔥_A`, the local ring
`Λ_q` is regular, and the residue field extension `κ(q) / k` is separable, then
`k → A → Λ ⊃ q` is resolvable. -/
theorem resolvableAtPrime_of_minimalPrime_regularLocalRing_and_separable_residueField
    (hq : 𝔮 ∈ (h(A⁄k, Λ)).minimalPrimes)
    [IsRegularLocalRing Λ_𝔮]
    [IsSeparableOver k q.asIdeal.ResidueField] :
    ResolvableAtPrime k A Λ 𝔮 := sorry

end Prime

end

end Algebra

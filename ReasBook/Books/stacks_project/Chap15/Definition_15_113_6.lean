import Mathlib
import stacks_project.Chap15.Lemma_15_113_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/- Domain-style sampling for Definition 15.113.6:
- primary domain: wild and tame inertia attached to a maximal ideal in a finite Galois extension
  of fraction fields of discrete valuation rings;
- sampled owner declarations:
  `Ideal.inertia`,
  `wildInertiaSubgroup`,
  `tameInertiaQuotient`,
  `tameInertiaQuotientMulEquiv`;
- best owner abstraction: the source-facing owners introduced in `Lemma_15_113_5`, built from the
  canonical inertia subgroup `m.inertia Gal(L / K)` and its wild inertia subgroup;
- primitive data: the inertia subgroup `m.inertia Gal(L / K)` and the wild inertia subgroup
  `wildInertiaSubgroup K m`;
- derived API: the tame inertia quotient, the canonical quotient equivalence with
  `μ_e(κ(m))`, and the induced tame inertia character.

Layer triage:
- `source-facing`: `wildInertiaSubgroup`, `tameInertiaQuotient`,
  `tameInertiaQuotientMulEquiv`, and `tameInertiaCharacter`;
- `core/canonical`: `Ideal.inertia`, subgroup inclusions, and quotient-group constructions;
- `bridge/view`: the passage from the quotient equivalence `I_t ≃ μ_e(κ(m))` to the induced
  character `I → μ_e(κ(m))`.

This file should therefore remain a pure recall layer, reusing the Chapter 15 owners directly and
introducing no parallel local wrappers. -/

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type v} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [IsGalois K L]

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

/- Definition 15.113.6 (1): with the notation of Lemma 15.113.5, the wild inertia group of `m`
is the canonical subgroup `wildInertiaSubgroup K m` of `Gal(L / K)`, lying inside the
decomposition group and hence inside the inertia group by the companion inclusion theorems. -/
set_option linter.hashCommand false in
#check (wildInertiaSubgroup K m)

/- Definition 15.113.6 (2): with the notation of Lemma 15.113.5, the tame inertia group of `m`
is the canonical quotient
`tameInertiaQuotient K m = (m.inertia Gal(L / K)) ⧸
  (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L / K))`. -/
set_option linter.hashCommand false in
#check (tameInertiaQuotient K m)

/- Definition 15.113.6 (3): with the notation of Lemma 15.113.5, the canonical quotient
equivalence `I_t ≃ μ_e(κ(m))` is `tameInertiaQuotientMulEquiv K m`, and the induced tame inertia
character `I → μ_e(κ(m))` is `tameInertiaCharacter K m`. -/
set_option linter.hashCommand false in
#check (tameInertiaQuotientMulEquiv K m)
set_option linter.hashCommand false in
#check (tameInertiaCharacter K m)

end

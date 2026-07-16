import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_113_5

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

local notation "B" => integralClosure A L
local notation "p" => maximalIdeal A
local notation "e" => Ideal.ramificationIdxIn p B

-- Reuse the owner file's canonical action so `m.inertia` and the imported tame inertia API
-- elaborate against the same instance constant.
attribute [local instance] integralClosureMulSemiringAction

variable (m : Ideal (integralClosure A L)) [m.IsMaximal]

/-- Definition 15.113.6: with the notation of Lemma 15.113.5, the wild inertia group of `m` is
the canonical subgroup `wildInertiaSubgroup K m` of `Gal(L / K)`. -/
abbrev wildInertiaGroup : Subgroup (Gal(L/K)) :=
  wildInertiaSubgroup K m

/-- Definition 15.113.6: with the notation of Lemma 15.113.5, the tame inertia group of `m` is
the canonical quotient
`tameInertiaQuotient K m = (m.inertia Gal(L / K)) ⧸
  (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L / K))`. -/
abbrev tameInertiaGroup :=
  tameInertiaQuotient K m

/-- Definition 15.113.6: with the notation of Lemma 15.113.5, the induced tame inertia character
`θ : I → μ_e(κ(m))` is the canonical map `tameInertiaCharacter K m`. -/
noncomputable abbrev tameInertiaMap :
    m.inertia Gal(L/K) →* rootsOfUnity e m.ResidueField :=
  tameInertiaCharacter K m

/-- Helper for Definition 15.113.6: the canonical quotient equivalence is induced by the tame
inertia character on quotient classes. -/
theorem tame_inertia_quotient_mk_eq_character
    (σ : m.inertia Gal(L/K)) :
    tameInertiaQuotientMulEquiv K m (QuotientGroup.mk σ) = tameInertiaCharacter K m σ := by
  -- The imported quotient compatibility is exactly the source statement that the quotient
  -- equivalence is induced by the tame inertia character.
  exact tameInertiaQuotientMulEquiv_mk K m σ

/-- Helper for Definition 15.113.6: the tame inertia character has kernel equal to the wild
inertia subgroup inside the inertia group. -/
theorem tame_inertia_character_ker
    : (tameInertiaCharacter K m).ker =
        (wildInertiaSubgroup K m).subgroupOf (m.inertia Gal(L/K)) := by
  -- The source-facing kernel identification is already proved in Lemma `15.113.5`.
  exact tameInertiaCharacter_ker K m

/-- Helper for Definition 15.113.6: the tame inertia character is surjective onto
`μ_e(κ(m))`. -/
theorem tame_inertia_character_surjective
    : Function.Surjective (tameInertiaCharacter K m) := by
  -- The source-facing surjectivity statement is reused verbatim from Lemma `15.113.5`.
  exact tameInertiaCharacter_surjective K m

end

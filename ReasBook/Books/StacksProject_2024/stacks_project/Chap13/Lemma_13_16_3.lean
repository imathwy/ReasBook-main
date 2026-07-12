import Mathlib
import StacksProject_2024.Chap13.Definition_13_16_2

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.16.3:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, together with the degree-zero comparison
  `F ⟶ (A ↦ H^0(RF(A[0])))`;
- sampled owner declarations:
  `Functor.boundedBelowRightDerived`,
  `Functor.toBoundedBelowRightDerivedZero`,
  `Functor.rightDerived`,
  `Functor.toRightDerivedZero`,
  `Functor.IsRightDerivedFunctor`;
- best owner abstraction:
  `source-facing`: the three bounded-below consequences for a chosen right derived functor model
    and the two stronger injective-resolution companions;
  `core/canonical`: the owner declarations above;
  `bridge/view`: none beyond the canonical degree-zero comparison morphisms already owned by
    `Functor`.
- primitive data: a chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(𝒝)` with
  comparison `α`, and under stronger assumptions the canonical unbounded owner `F.rightDerived 0`.
- derived API: negative-degree vanishing, left exactness of `RF.boundedBelowRightDerived 0`, the
  characterization of `F.toBoundedBelowRightDerivedZero RF α`, and the injective-resolution
  companions for `F.rightDerived 0` and `F.toRightDerivedZero`.

This file keeps only the public source-facing theorem statements used downstream. The broken
private proof-engineering layer is intentionally omitted here; those details are implementation
scaffolding rather than part of the Chapter 13 API surface. -/

section BoundedBelow

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

/-- Lemma 13.16.3 (1): the `i`-th bounded-below right derived functor vanishes for `i < 0`. -/
theorem boundedBelowRightDerived_isZero_of_neg
    (i : ℤ) (hi : i < 0) :
    IsZero (RF.boundedBelowRightDerived i) := by
  sorry

/-- Lemma 13.16.3 (2): the degree-zero bounded-below right derived functor is left exact. -/
theorem boundedBelowRightDerivedZero_preservesFiniteLimits :
    PreservesFiniteLimits (RF.boundedBelowRightDerived 0) := by
  sorry

/-- Lemma 13.16.3 (3): the canonical comparison
`F ⟶ (A ↦ H^0(RF(A[0])))`, formalized as `F.toBoundedBelowRightDerivedZero RF α`, is an
isomorphism exactly when `F` is left exact. -/
theorem isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits :
    IsIso (F.toBoundedBelowRightDerivedZero RF α) ↔ PreservesFiniteLimits F := by
  sorry

end BoundedBelow

section RightDerived

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]
  [HasInjectiveResolutions 𝒜]

/-- Stronger-assumption companion to Lemma 13.16.3 (2): `R^0F` is left exact. -/
theorem rightDerivedZero_preservesFiniteLimits :
    PreservesFiniteLimits (F.rightDerived 0) := by
  sorry

/-- Stronger-assumption companion to Lemma 13.16.3 (3): `F.toRightDerivedZero` is an isomorphism
exactly when `F` is left exact. -/
theorem isIso_toRightDerivedZero_iff_preservesFiniteLimits :
    IsIso F.toRightDerivedZero ↔ PreservesFiniteLimits F := by
  sorry

end RightDerived

end CategoryTheory

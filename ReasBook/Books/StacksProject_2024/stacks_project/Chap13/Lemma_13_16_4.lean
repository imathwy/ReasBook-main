import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_15_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_3

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.16.4:
- primary domain: right acyclicity for additive functors, expressed through a chosen
  bounded-below right derived functor and its degree-zero comparison;
- sampled owner declarations:
  `Functor.boundedBelowRightDerived`,
  `Functor.toBoundedBelowRightDerivedZero`,
  `Functor.rightDerived`,
  `Functor.toRightDerivedZero`,
  `Functor.IsRightDerivedFunctor`;
- best owner abstraction:
  `source-facing`: the bounded-below and unbounded acyclicity criteria below;
  `core/canonical`: the owner declarations above;
  `bridge/view`: the two vanishing predicates
    `RF.boundedBelowHigherRightDerivedVanishes A` and `F.higherRightDerivedVanishes A`.
- primitive data: a chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` with
  comparison `α`, and under stronger assumptions the unbounded right derived functor of `F`.
- derived API: the bounded-below and unbounded acyclicity characterizations, together with the
  derived-category isomorphism criterion used downstream.

This file keeps only the public statement layer used by downstream chapters. The former helper
proof infrastructure is intentionally omitted from this dependency-closure repair. -/

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]

local notation "H" => DerivedCategory.homologyFunctor ℬ

/-- A morphism in `D(\mathcal B)` is an isomorphism exactly when all of its cohomology maps are
isomorphisms. -/
lemma derivedCategory_isIso_iff_homology_map_isIso
    {X Y : DerivedCategory ℬ} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i : ℤ, IsIso ((H i).map f) := by
  sorry

end

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization QisPlus]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α QisPlus]

namespace Functor

/-- The proposition that all positive bounded-below right derived functors determined by `RF`
vanish on `A`. -/
abbrev boundedBelowHigherRightDerivedVanishes (RF : D⁺(𝒜) ⥤ D⁺(ℬ)) (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((RF.boundedBelowRightDerived (n + 1)).obj A)

end Functor

/-- Lemma 13.16.4: bounded-below right acyclicity is equivalent to invertibility of the
degree-zero comparison together with vanishing of the positive bounded-below right derived
functors. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_isIso_toBoundedBelowRightDerivedZero_app_and_boundedBelowHigherRightDerivedVanishes
    (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      IsIso ((F.toBoundedBelowRightDerivedZero RF α).app A) ∧
        RF.boundedBelowHigherRightDerivedVanishes A := by
  sorry

/-- For a left exact additive functor, bounded-below right acyclicity is equivalent to vanishing
of the positive bounded-below right derived functors. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
    [PreservesFiniteLimits F] (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      RF.boundedBelowHigherRightDerivedVanishes A := by
  sorry

end BoundedBelow

section Unbounded

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [HasInjectiveResolutions 𝒜]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

namespace Functor

/-- The proposition that all positive unbounded right derived functors of `F` vanish on `A`. -/
abbrev higherRightDerivedVanishes (F : 𝒜 ⥤ ℬ) [F.Additive] (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj A)

end Functor

/-- On the degree-zero object `A[0]`, the unbounded and bounded-below right-acyclicity predicates
agree. -/
lemma isRightAcyclicForAdditiveFunctor_iff_isBoundedBelowRightAcyclic
    (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      IsBoundedBelowRightAcyclicForAdditiveFunctor F A := by
  sorry

/-- Under injective resolutions, right acyclicity is equivalent to invertibility of the
degree-zero comparison together with vanishing of the higher right derived functors. -/
theorem isRightAcyclicForAdditiveFunctor_iff_isIso_toRightDerivedZero_app_and_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      IsIso (F.toRightDerivedZero.app A) ∧
        F.higherRightDerivedVanishes A := by
  sorry

/-- For a left exact additive functor, unbounded right acyclicity is equivalent to vanishing of
the higher right derived functors. -/
theorem isRightAcyclicForAdditiveFunctor_iff_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] [PreservesFiniteLimits F] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      F.higherRightDerivedVanishes A := by
  sorry

end Unbounded

end CategoryTheory

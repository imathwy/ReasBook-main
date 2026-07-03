import Mathlib
import StacksProject_2024.Chap13.Lemma_13_16_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-
Domain-style sampling for Lemma 13.16.4:
- primary domain: right acyclicity for additive functors, stated source-faithfully through a
  chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- sampled owner declarations:
  `IsBoundedBelowRightAcyclicForAdditiveFunctor`,
  `Functor.IsRightDerivedFunctor`,
  `Functor.toBoundedBelowRightDerivedZero`,
  `isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits`;
- best owner abstraction: the source-facing owner is
  `IsBoundedBelowRightAcyclicForAdditiveFunctor F A`; the injective-resolution API
  `IsRightAcyclicForAdditiveFunctor`, `Functor.toRightDerivedZero`, and `Functor.rightDerived`
  is only a stronger companion bridge;
- primitive data: the chosen bounded-below right derived functor `RF` together with its
  derivation witness `α`;
- derived API: the positive-degree vanishing predicate for `A ↦ H^i(RF(A[0]))`, the main
  acyclicity characterization, and the left exact corollary.

Source/core/bridge triage:
- `source-facing`: the bounded-below statements in the `BoundedBelow` section;
- `core/canonical`: `Functor.IsRightDerivedFunctor`, `Functor.toBoundedBelowRightDerivedZero`,
  and the bounded-below acyclicity owner from `Definition 13.15.3`;
- `bridge/view`: the later unbounded injective-resolution companions in the `Unbounded` section.
-/

section BoundedBelow

variable [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization QisPlus]

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α QisPlus]

namespace Functor

/-- The proposition that all positive right derived functors determined by the bounded-below
realization `RF` vanish on `A`. -/
abbrev boundedBelowHigherRightDerivedVanishes (RF : D⁺(𝒜) ⥤ D⁺(ℬ)) (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((RF.boundedBelowRightDerived (n + 1)).obj A)

end Functor

-- Proof sketch: by Lemma `13.15.2`, the degree-zero bounded-below complex `A[0]` computes the
-- bounded-below right derived functor exactly when it computes the unbounded one. Unwinding the
-- pointwise computation in `D⁺(ℬ)`, the unit map is the comparison `F(A) ⟶ H⁰(RF(A[0]))`, while
-- the higher cohomology objects are the positive right derived functors `RⁱF(A)`.
/-- Lemma 13.16.4: an object `A` is right acyclic for the bounded-below right derived functor of
`F` if and only if the canonical comparison morphism
`F(A) ⟶ H^0(RF(A[0]))`, formalized as `(F.toBoundedBelowRightDerivedZero RF α).app A`, is an
isomorphism and all positive right derived functors determined by `RF` vanish on `A`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_isIso_toBoundedBelowRightDerivedZero_app_and_boundedBelowHigherRightDerivedVanishes
    (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      IsIso ((F.toBoundedBelowRightDerivedZero RF α).app A) ∧
        RF.boundedBelowHigherRightDerivedVanishes A := sorry

-- Proof sketch: for a left exact additive functor, Lemma `13.16.3` identifies `F` with the
-- degree-zero branch `A ↦ H⁰(RF(A[0]))` without adding extra exactness hypotheses on the chosen
-- bounded-below right derived functor `RF`. The previous theorem then reduces right acyclicity to
-- the vanishing of the positive right derived functors.
/-- For a left exact additive functor, bounded-below right acyclicity is equivalent to the
vanishing of all positive right derived functors determined by `RF`. -/
theorem isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
    [PreservesFiniteLimits F] (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A ↔
      RF.boundedBelowHigherRightDerivedVanishes A := sorry

end BoundedBelow

section Unbounded

variable [HasDerivedCategory.{w} ℬ] [HasInjectiveResolutions 𝒜]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

namespace Functor

/-- Stronger-assumption companion: all positive unbounded right derived functors of `F` vanish on
`A`. -/
abbrev higherRightDerivedVanishes (F : 𝒜 ⥤ ℬ) [F.Additive] (A : 𝒜) : Prop :=
  ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj A)

end Functor

-- Proof sketch: under injective resolutions, the bounded-below and unbounded right derived
-- functors agree on the degree-zero complex `A[0]`, so the source-facing bounded-below statement
-- above specializes to the usual comparison `F(A) ⟶ R⁰F(A)` and the vanishing of
-- `RⁱF(A)` for `i > 0`.
/-- Stronger-assumption companion to Lemma 13.16.4: under injective resolutions and the unbounded
right derived functor, an object `A` is right acyclic for `F` if and only if the comparison
`F(A) ⟶ R⁰F(A)` is an isomorphism and the higher right derived functors vanish on `A`. -/
theorem isRightAcyclicForAdditiveFunctor_iff_isIso_toRightDerivedZero_app_and_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      IsIso (F.toRightDerivedZero.app A) ∧
        F.higherRightDerivedVanishes A := sorry

-- Proof sketch: for a left exact additive functor, `F.toRightDerivedZero : F ⟶ R⁰F` is an
-- isomorphism, so the previous companion reduces right acyclicity to the vanishing of the
-- positive right derived functors.
/-- Stronger-assumption companion: for a left exact additive functor, unbounded right acyclicity
is equivalent to the vanishing of all higher right derived functors. -/
theorem isRightAcyclicForAdditiveFunctor_iff_higherRightDerivedVanishes
    [Functor.HasRightDerivedFunctor KtoD Qis] [PreservesFiniteLimits F] (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A ↔
      F.higherRightDerivedVanishes A := sorry

end Unbounded

end

end CategoryTheory

import Mathlib
import stacks_project.Chap13.Definition_13_16_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]

local notation "Qplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)

/-
Domain-style sampling:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, together with the degree-zero branch `A ↦ H⁰(RF(A[0]))`;
- sampled owner declarations:
  `Functor.IsRightDerivedFunctor`,
  `Functor.totalRightDerivedUnit`,
  `single0Plus`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the source-facing bounded-below owner is a chosen
  `RF : D⁺(𝒜) ⥤ D⁺(𝒝)` equipped with a derivation witness
  `α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
    mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF`;
- primitive data: the chosen bounded-below right derived functor `RF` and its derivation witness
  `α`;
- derived API: the vanishing of `H^i(RF(A[0]))` for `i < 0`, the left exactness of
  `A ↦ H⁰(RF(A[0]))`, and the canonical comparison
  `F ⟶ (A ↦ H⁰(RF(A[0])))`;
- source/core/bridge triage:
  `source-facing`: the three bounded-below statements below;
  `core/canonical`: `Functor.IsRightDerivedFunctor`, `Functor.totalRightDerivedUnit`, and the
    bounded-below localization owners from Situation `13.15.1`;
  `bridge/view`: the bounded-below degree-zero comparison
    `Functor.toBoundedBelowRightDerivedZero`, and the later injective-resolution owners
    `Functor.rightDerived` and `Functor.toRightDerivedZero`, which are kept only as
    stronger-assumption companions.
--/

section BoundedBelow

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]

variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶ Qplus ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

-- Proof sketch: the degree-zero object `A[0]` in `D⁺(𝒜)` is concentrated in degrees `≥ 0`, so
-- any bounded-below right derived functor `RF` has no cohomology in negative degrees on `RF(A[0])`.
/-- Lemma 13.16.3 (1): for a bounded-below right derived functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the functor
`A ↦ H^i(RF(A[0]))` vanishes for every `i < 0`. -/
theorem boundedBelowRightDerived_isZero_of_neg
    (i : ℤ) (hi : i < 0) :
    IsZero (RF.boundedBelowRightDerived i) := by
  sorry

-- Proof sketch: the exactness package needed to build the long exact cohomology sequence for the
-- bounded-below derived functor `RF` is part of the proof route, not of the source-facing
-- statement. Using that exactness internally and then part `(1)` to remove the negative term
-- leaves left exactness in degree `0`.
/-- Lemma 13.16.3 (2): the degree-zero branch of a bounded-below right derived functor,
formalized as `A ↦ H^0(RF(A[0]))`, is left exact. -/
theorem boundedBelowRightDerivedZero_preservesFiniteLimits
    : PreservesFiniteLimits (RF.boundedBelowRightDerived 0) := by
  sorry

-- Proof sketch: if `F` is identified with `A ↦ H^0(RF(A[0]))`, transport left exactness along
-- that identification using part `(2)`. Conversely, when `F` is left exact, the canonical
-- degree-zero comparison attached to the bounded-below right derived functor is an isomorphism.
-- Any exactness structures on `RF` used in the proof are internal consequences of the chosen
-- right-derived-functor setup and do not belong in the public API of this source-facing lemma.
/-- Lemma 13.16.3 (3): the canonical comparison
`F ⟶ (A ↦ H^0(RF(A[0])))`, formalized as `F.toBoundedBelowRightDerivedZero RF α`, is an
isomorphism exactly when `F` is left exact. -/
theorem isIso_toBoundedBelowRightDerivedZero_iff_preservesFiniteLimits
    : IsIso (F.toBoundedBelowRightDerivedZero RF α) ↔ PreservesFiniteLimits F := by
  sorry

end BoundedBelow

end

section RightDerived

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  (F : 𝒜 ⥤ 𝒝) [F.Additive]

variable [HasInjectiveResolutions 𝒜]

-- Proof sketch: this is the injective-resolution specialization of the bounded-below degree-zero
-- statement above, expressed in mathlib's canonical owner `Functor.rightDerived 0`.
/-- Stronger-assumption companion to Lemma 13.16.3 (2): under injective resolutions, the degree-zero
right derived functor `R^0F`, formalized as `F.rightDerived 0`, is left exact. -/
theorem rightDerivedZero_preservesFiniteLimits :
    PreservesFiniteLimits (F.rightDerived 0) := sorry

-- Proof sketch: if `F ⟶ R^0F` is an isomorphism, transport left exactness from `R^0F` using the
-- previous companion. Conversely, if `F` is left exact, mathlib's canonical comparison
-- `F.toRightDerivedZero : F ⟶ F.rightDerived 0` is an isomorphism.
/-- Stronger-assumption companion to Lemma 13.16.3 (3): under injective resolutions, the canonical
comparison map `F ⟶ R^0F`, formalized as `F.toRightDerivedZero`, is an isomorphism exactly when
`F` is left exact. -/
theorem isIso_toRightDerivedZero_iff_preservesFiniteLimits :
    IsIso F.toRightDerivedZero ↔ PreservesFiniteLimits F := by
  constructor
  · intro h
    letI := h
    letI := rightDerivedZero_preservesFiniteLimits F
    exact preservesFiniteLimits_of_natIso (asIso F.toRightDerivedZero).symm
  · intro h
    letI := h
    infer_instance

end RightDerived

end CategoryTheory

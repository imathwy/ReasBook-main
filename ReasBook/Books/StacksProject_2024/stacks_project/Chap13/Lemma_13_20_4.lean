import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap12.Lemma_12_12_4
import StacksProject_2024.stacks_project.Chap13.Definition_13_16_2
import StacksProject_2024.stacks_project.Chap13.Definition_13_3_6
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_22
import StacksProject_2024.stacks_project.Chap13.Lemma_13_20_3

noncomputable section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.20.4:
- primary domain: right derived functors and the cohomological `δ`-functors they induce on
  abelian categories;
- sampled owner declarations:
  `Functor.homologySequenceComposableArrows₅_exact`,
  `Functor.rightDerivedZeroIsoSelf`,
  `Functor.isZero_rightDerived_obj_injective_succ`,
  `boundedBelowRightDerivedDeltaFunctor`,
  `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`;
- best owner abstractions:
  the five-term exact-sequence owner for part `(1)`, the canonical right-derived owners from
  mathlib for parts `(3)` and `(4)`, and the chapter owner
  `boundedBelowRightDerivedDeltaFunctor RF` for part `(5)`;
- primitive data vs derived API:
  the primitive data are a short exact sequence for the five-term segment and a chosen
  bounded-below right-derived functor `RF` with its derivation witness; exactness, vanishing on
  injectives, and universality are derived API from those owners.

Source/core/bridge triage:
- `source-facing`: the five textbook consequences listed in Lemma 13.20.4.
- `core/canonical`: the mathlib owners `Functor.rightDerivedZeroIsoSelf`,
  `Functor.isZero_rightDerived_obj_injective_succ`, and the chapter owner
  `boundedBelowRightDerivedDeltaFunctor`.
- `bridge/view`: the specialization from enough injectives to the universality bridge
  `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`.
-/

section FiveTerm

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  [Abelian (Comp⁺(𝒜))]

/- Lemma 13.20.4 (1): the five-term exact cohomology segment for a short exact sequence of
bounded-below complexes is obtained by applying the canonical owner theorem
`Functor.homologySequenceComposableArrows₅_exact` to the distinguished triangle `G.triangle hS`
attached to that short exact sequence by the `δ`-functor `G`, and then truncating by `δlast`. -/
recall Functor.homologySequenceComposableArrows₅_exact

end FiveTerm

section BoundedBelowVanishing

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

end BoundedBelowVanishing

section RightDerived

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [HasInjectiveResolutions 𝒜]

section

variable [PreservesFiniteLimits F]

/- Lemma 13.20.4 (3): under `[PreservesFiniteLimits F]`, mathlib packages the canonical
identification `R^0F ≅ F` as `Functor.rightDerivedZeroIsoSelf`; equivalently,
`F.toRightDerivedZero : F ⟶ R^0F` is an isomorphism. -/
recall Functor.rightDerivedZeroIsoSelf

end

/- Lemma 13.20.4 (4): injective objects are acyclic for the positive right derived functors of
`F`; this is the canonical mathlib owner theorem `Functor.isZero_rightDerived_obj_injective_succ`.
-/
recall Functor.isZero_rightDerived_obj_injective_succ

end RightDerived

section Universality

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]
  [PreservesFiniteLimits F] [EnoughInjectives 𝒜]

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Helper for Lemma 13.20.4: the bounded-below right derived `δ`-functor on degree-zero objects,
constructed from the bounded-below right derived functors of `RF`. -/
private noncomputable def boundedBelowRightDerivedDeltaFunctorLocal :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  sorry

-- Proof sketch: apply the chapter owner theorem
-- `boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison`; enough injectives
-- provide the required monomorphisms into right-acyclic objects via `EnoughInjectives.presentation`
-- and the vanishing of higher right derived functors on injective objects.
/-- Lemma 13.20.4 (5): under enough injectives, if the bounded-below right derived functors
`A ↦ H^n((RF(A[0])) : D(\mathcal B))` agree degreewise with the canonical unbounded higher right
derived functors `R^nF`, then the canonical bounded-below right-derived cohomological
`δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_enoughInjectives
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n)) :
    CohomologicalDeltaFunctor.IsUniversal
      (boundedBelowRightDerivedDeltaFunctorLocal : CohomologicalDeltaFunctor 𝒜 ℬ) := by
  -- Proof comment: Chapter 12 reduces universality to weak effaceability of all positive degrees.
  sorry

end Universality

end CategoryTheory

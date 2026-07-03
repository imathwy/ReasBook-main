import Mathlib
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Functor
open ComplexShape
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Lemma 13.15.2:
- primary domain: comparison of pointwise derived-functor computation between the unbounded
  homotopy localization `K(\mathcal A) ⟶ D(\mathcal B)` and its bounded-below / bounded-above
  full-subcategory views;
- sampled owner declarations:
  `LocalizerMorphism.ofEq`,
  `LocalizerMorphism.hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure`,
  `LocalizerMorphism.isIso_iff_of_isRightDerivabilityStructure`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction: the bounded inclusions are not second derived-functor owners; they are
  bridge/view localizer morphisms from `Qis⁺(𝒜)` and `Qis⁻(𝒜)` to the ambient quasi-isomorphism
  class `HomotopyCategory.quasiIso 𝒜 (up ℤ)`, and the six statements below are their
  source-facing consequences for pointwise derived functors;
- primitive data: the canonical functors from `Situation_13_15_1`, together with the bounded
  quasi-isomorphism owners `Qis⁺(𝒜)` and `Qis⁻(𝒜)` from `Lemma_13_11_6`;
- derived API: the equivalence of pointwise derived-definedness, the comparison of pointwise
  derived values, and the corresponding `ComputesRightDerivedAt` / `ComputesLeftDerivedAt`
  equivalences.

Source/core/bridge triage:
- `source-facing`: the six bounded-vs-unbounded comparison statements of Lemma `13.15.2`;
- `core/canonical`: the mathlib `LocalizerMorphism` derivability-structure comparison API and the
  Chapter `13` owners `Functor.ComputesRightDerivedAt` / `Functor.ComputesLeftDerivedAt`;
- `bridge/view`: the bounded inclusions `K⁺(𝒜) ⥤ K(\mathcal A)` and `K⁻(𝒜) ⥤ K(\mathcal A)`,
  which induce the comparison between the bounded and unbounded derived setups.
-/

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "KminusToDminus" => mapBoundedAboveHomotopyCategoryToDerivedAbove F

-- Proof sketch: by Lemma 13.11.5, every quasi-isomorphism out of the bounded-below object `X`
-- can be refined to one whose target is still bounded below. This is exactly the
-- `LocalizerMorphism.ofEq rfl` bridge from `Qis⁺(𝒜)` to `Qis`, together with the canonical
-- right-derivability-structure comparison API, so the pointwise right-derived existence condition
-- is unchanged.
/-- Lemma 13.15.2 (1): for a bounded-below object `X` of `K^+(\mathcal A)`, the right derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the right derived functor of `K^+(\mathcal A) ⥤ D^+(\mathcal B)` is defined at `X`. -/
theorem right_derived_defined_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X := sorry

-- Proof sketch: once both pointwise right-derived values exist, the localizer-morphism bridge
-- `LocalizerMorphism.ofEq rfl` for `Qis⁺(𝒜) ⟶ Qis` and the canonical derivability-structure
-- comparison supply the comparison morphism; its invertibility is exactly the pointwise
-- comparison encoded by `LocalizerMorphism.rightDerivedFunctorComparison`. The bounded-below
-- value is viewed in `D(\mathcal B)` through the canonical full-subcategory inclusion
-- `D^+(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (2): when the right-derived values at a bounded-below object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^+(\mathcal B)`. -/
noncomputable def right_derived_value_comparison_iso_bounded_below
    (X : K⁺(𝒜))
    [HasPointwiseRightDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseRightDerivedFunctorAt KplusToDplus (Qis⁺(𝒜)) X] :
    rightDerivedValue Qis KtoD X.obj ≅
      (rightDerivedValue (Qis⁺(𝒜)) KplusToDplus X).obj := sorry

-- Proof sketch: combine the equivalence of pointwise right-derived existence with the canonical
-- `isIso_iff_of_isRightDerivabilityStructure` comparison for the identity legs.
/-- Lemma 13.15.2 (3): a bounded-below object `X` computes the right derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`. -/
theorem computes_right_derived_functor_at_iff_bounded_below
    (X : K⁺(𝒜)) :
    ComputesRightDerivedAt KtoD Qis X.obj ↔
      ComputesRightDerivedAt KplusToDplus (Qis⁺(𝒜)) X := sorry

-- Proof sketch: this is the dual argument to part (1). Lemma 13.11.5 furnishes bounded-above
-- refinements of quasi-isomorphisms into `X`; equivalently, `LocalizerMorphism.ofEq rfl` from
-- `Qis⁻(𝒜)` to `Qis` is the left-derivability-structure bridge, so pointwise left-derived
-- existence is unchanged.
/-- Lemma 13.15.2 (4): for a bounded-above object `X` of `K^-(\mathcal A)`, the left derived
functor of `K(\mathcal A) ⥤ D(\mathcal B)` is defined at the underlying object of `X` if and only
if the left derived functor of `K^-(\mathcal A) ⥤ D^-(\mathcal B)` is defined at `X`. -/
theorem left_derived_defined_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj ↔
      HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X := sorry

-- Proof sketch: after both pointwise left-derived values are defined, the localizer-morphism
-- bridge `LocalizerMorphism.ofEq rfl` for `Qis⁻(𝒜) ⟶ Qis` identifies the bounded-above and
-- unbounded structured-arrow diagrams, and the resulting canonical comparison morphism is the one
-- whose invertibility is tracked by the left-derived derivability-structure API. The
-- bounded-above value is viewed in `D(\mathcal B)` through the canonical full-subcategory
-- inclusion `D^-(\mathcal B) ↪ D(\mathcal B)`.
/-- Lemma 13.15.2 (5): when the left-derived values at a bounded-above object `X` are defined in
both settings, there is a canonical comparison isomorphism from the value computed in
`D(\mathcal B)` to the underlying object of the value computed in `D^-(\mathcal B)`. -/
noncomputable def left_derived_value_comparison_iso_bounded_above
    (X : K⁻(𝒜))
    [HasPointwiseLeftDerivedFunctorAt KtoD Qis X.obj]
    [HasPointwiseLeftDerivedFunctorAt KminusToDminus (Qis⁻(𝒜)) X] :
    leftDerivedValue Qis KtoD X.obj ≅
      (leftDerivedValue (Qis⁻(𝒜)) KminusToDminus X).obj := sorry

-- Proof sketch: combine the equivalence of pointwise left-derived existence with the comparison
-- of the canonical pointwise counit morphisms under the derived-structure bridge.
/-- Lemma 13.15.2 (6): a bounded-above object `X` computes the left derived functor of
`K(\mathcal A) ⥤ D(\mathcal B)` if and only if it computes the left derived functor of
`K^-(\mathcal A) ⥤ D^-(\mathcal B)`. -/
theorem computes_left_derived_functor_at_iff_bounded_above
    (X : K⁻(𝒜)) :
    ComputesLeftDerivedAt KtoD Qis X.obj ↔
      ComputesLeftDerivedAt KminusToDminus (Qis⁻(𝒜)) X := sorry

end

end CategoryTheory

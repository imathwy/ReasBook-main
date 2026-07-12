import Mathlib
import StacksProject_2024.Chap13.Lemma_13_10_6
import StacksProject_2024.Chap13.Lemma_13_20_3
import StacksProject_2024.Chap13.Proposition_13_23_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/-
Domain-style sampling:
- primary domain: bounded-below right derived functors computed via injective complexes and a lift
  of the homotopy resolution functor;
- sampled owner declarations:
  `HomotopyResolutionFunctor`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.IsRightDerivedFunctor`;
- best owner abstraction: the canonical localization owner is
  `mapBoundedBelowHomotopyToDerivedBelow`, and the injective-complex inclusion is owned by
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`; the localization lift itself is
  owned canonically by `Localization.Lifting`, and the passage through `K^+(\mathcal I)` is a
  bridge/view built from those owners rather than a separate root functor declaration;
- primitive data: the additive functor `F`, the homotopy resolution functor `j`, the lifted
  functor `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)`, and the explicit lift datum
  `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`;
- existence data such as `[EnoughInjectives 𝒜]` belongs upstream, where one proves that
  a `HomotopyResolutionFunctor 𝒜` exists, not in this bridge lemma about a fixed choice;
- derived API: the comparison 2-cell and the induced `IsRightDerivedFunctor` structure on the
  composite through bounded-below injectives.

Source/core/bridge triage:
- `source-facing`: Lemma 13.25.1 itself;
- `core/canonical`: `mapBoundedBelowHomotopyToDerivedBelow`,
  `Localization.Lifting`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`, and
  `Functor.IsRightDerivedFunctor`;
- `bridge/view`: the composite `j' ⋙
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyCategoryToDerivedBelow F`.
-/
local notation "DplusA" => boundedBelowDerivedCategory 𝒜
local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ DplusA)
local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
local notation "KinjToDplusB" =>
  KinjIncl ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F
local notation "WInj" => (Qis⁺(𝒜)).inverseImage KinjIncl

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- Helper for Lemma 13.25.1: the injective inclusion as a localizer morphism from the pulled-back
bounded-below quasi-isomorphisms to the ambient bounded-below quasi-isomorphisms. -/
local abbrev ΦInj : LocalizerMorphism WInj (Qis⁺(𝒜)) :=
  LocalizerMorphism.ofEq rfl

/-- The comparison 2-cell from the cochain-level functor `K^+(\mathcal A) ⥤ D^+(\mathcal B)` to
the composite through a lifted injective-resolution functor `j'`, packaged by the canonical
localization-lift datum `hj'`. -/
noncomputable def resolutionLiftComparison
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
      Q ⋙ (j' ⋙ KinjToDplusB) :=
  Functor.whiskerRight j.ι (mapBoundedBelowHomotopyCategoryToDerivedBelow F) ≫
    (Functor.associator j.toFunctor KinjIncl
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).hom ≫
    (Functor.isoWhiskerRight hj'.iso.symm KinjToDplusB).hom ≫
    (Functor.associator Q j' KinjToDplusB).hom

/-- Helper for Lemma 13.25.1: a pulled-back bounded-below quasi-isomorphism between injective
complexes is already an isomorphism. -/
theorem injective_quasi_iso_is_iso
    (j : HomotopyResolutionFunctor 𝒜)
    {X Y : K⁺ᵢ(𝒜)} (f : X ⟶ Y) (hf : WInj f) :
    IsIso f := by
  let F' : K⁺ᵢ(𝒜) ⥤ DplusA := KinjIncl ⋙ Q
  letI : Functor.IsEquivalence F' := by
    simpa [F'] using j.toDerived_isEquivalence
  letI : F'.Full := (Functor.asEquivalence F').fullyFaithfulFunctor.full
  letI : F'.Faithful := (Functor.asEquivalence F').fullyFaithfulFunctor.faithful
  have hmap : IsIso (F'.map f) := by
    -- The bounded-below localization inverts the pulled-back quasi-isomorphism `hf`.
    change IsIso (Q.map (KinjIncl.map f))
    exact Localization.inverts Q (Qis⁺(𝒜)) _ hf
  exact isIso_of_fully_faithful F' f

/-- Helper for Lemma 13.25.1: the injective inclusion induces an equivalence on the localized
bounded-below homotopy category. -/
theorem injective_localizer_isLocalizedEquivalence
    (j : HomotopyResolutionFunctor 𝒜) :
    (ΦInj (𝒜 := 𝒜)).IsLocalizedEquivalence := by
  let F' : K⁺ᵢ(𝒜) ⥤ DplusA := KinjIncl ⋙ Q
  letI : Functor.IsEquivalence F' := by
    simpa [F'] using j.toDerived_isEquivalence
  have hWInj :
      WInj ≤ MorphismProperty.isomorphisms (K⁺ᵢ(𝒜)) := by
    intro X Y f hf
    -- On the injective source, pulled-back quasi-isomorphisms are actual isomorphisms.
    exact injective_quasi_iso_is_iso (j := j) f hf
  letI : Functor.IsLocalization F' WInj :=
    Functor.IsLocalization.of_isEquivalence F' WInj hWInj
  -- Both localizations are represented by the same equivalence into `D^+(\mathcal A)`.
  simpa [F', ΦInj, KinjIncl] using
    (LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization
      (Φ := ΦInj (𝒜 := 𝒜))
      (L₂ := Q))

/-- Helper for Lemma 13.25.1: the injective localizer bridge carries the right-derivability
structure needed to test right-derived comparisons on injective models. -/
theorem injective_localizer_right_derivability
    (j : HomotopyResolutionFunctor 𝒜) :
    (ΦInj (𝒜 := 𝒜)).IsRightDerivabilityStructure := by
  letI : (ΦInj (𝒜 := 𝒜)).IsLocalizedEquivalence :=
    injective_localizer_isLocalizedEquivalence (𝒜 := 𝒜) j
  -- A localized equivalence already provides the required right-derivability structure.
  simpa using (LocalizerMorphism.IsRightDerivabilityStructure.mk' (ΦInj (𝒜 := 𝒜)))

/-- Helper for Lemma 13.25.1: the cochain-level source functor already inverts the pulled-back
quasi-isomorphisms on injective models. -/
theorem injective_localizer_derives_source
    (j : HomotopyResolutionFunctor 𝒜) :
    (ΦInj (𝒜 := 𝒜)).Derives (mapBoundedBelowHomotopyCategoryToDerivedBelow F) := by
  intro X Y f hf
  -- Once `f` is an isomorphism inside `K^+(\mathcal I)`, every functor sends it to an
  -- isomorphism, in particular the bounded-below derived source functor.
  letI : IsIso f := injective_quasi_iso_is_iso (𝒜 := 𝒜) (j := j) f hf
  change IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map (KinjIncl.map f))
  infer_instance

/-- Helper for Lemma 13.25.1: on an injective model, the comparison map
`resolutionLiftComparison` is an isomorphism. -/
theorem resolutionLiftComparison_app_isIso_on_injective
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j')
    (X : K⁺ᵢ(𝒜)) :
    IsIso (((resolutionLiftComparison F j j' hj').app (KinjIncl.obj X))) := by
  let g : X ⟶ j.toFunctor.obj (KinjIncl.obj X) :=
    ObjectProperty.homMk (j.ι.app (KinjIncl.obj X))
  have hg : WInj g := by
    -- The resolution morphism is a quasi-isomorphism, and both source and target are injective.
    simpa [WInj, g, KinjIncl] using j.quasiIso_app (KinjIncl.obj X)
  have hgIso : IsIso g := injective_quasi_iso_is_iso (𝒜 := 𝒜) (j := j) g hg
  have hfirst :
      IsIso
        (((Functor.whiskerRight j.ι
            (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).app (KinjIncl.obj X))) := by
    -- The first leg is the image of the injective quasi-isomorphism `g` under the source functor.
    change IsIso ((mapBoundedBelowHomotopyCategoryToDerivedBelow F).map (KinjIncl.map g))
    letI : IsIso g := hgIso
    infer_instance
  -- The remaining factors are the associators and the localization-lift isomorphism.
  simpa [resolutionLiftComparison, Category.assoc] using
    (show IsIso
      ((((Functor.whiskerRight j.ι
            (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).app (KinjIncl.obj X)) ≫
          (Functor.associator j.toFunctor KinjIncl
            (mapBoundedBelowHomotopyCategoryToDerivedBelow F)).hom.app (KinjIncl.obj X) ≫
          (Functor.isoWhiskerRight hj'.iso.symm KinjToDplusB).hom.app (KinjIncl.obj X) ≫
          (Functor.associator Q j' KinjToDplusB).hom.app (KinjIncl.obj X)) from
      infer_instance)

-- Proof sketch: by Lemma 13.20.1, every bounded-below complex of injective objects computes the
-- right derived functor of `K^+(\mathcal A) ⟶ D^+(\mathcal B)`. The functor `j'` sends a derived
-- object to such an injective representative, and the comparison 2-cell is induced from the
-- resolution quasi-isomorphism `ι`; hence the composite through `K^+(\mathcal I)` is itself a
-- right derived functor, and therefore is naturally isomorphic to `RF` by uniqueness.
/-- Lemma 13.25.1: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is the lift of a homotopy
resolution functor `j` through the localization functor `K^+(\mathcal A) ⥤ D^+(\mathcal A)`,
encoded by `hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j'`, then the composite
`j' ⋙ F` with the induced functor
`F : K^+(\mathcal I) ⥤ D^+(\mathcal B)` is a right derived functor of
`K^+(\mathcal A) ⥤ D^+(\mathcal B)`; equivalently, it is naturally isomorphic to the bounded-
below right derived functor `RF`. -/
@[stacks 05TN]
theorem resolution_lift_comp_isRightDerivedFunctor
    (j : HomotopyResolutionFunctor 𝒜) (j' : DplusA ⥤ K⁺ᵢ(𝒜))
    (hj' : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j') :
    (j' ⋙ KinjToDplusB).IsRightDerivedFunctor
      (resolutionLiftComparison F j j' hj')
      (Qis⁺(𝒜)) := by
  letI : (ΦInj (𝒜 := 𝒜)).IsRightDerivabilityStructure :=
    injective_localizer_right_derivability (𝒜 := 𝒜) j
  let hΦ := injective_localizer_derives_source (𝒜 := 𝒜) (ℬ := ℬ) (F := F) j
  -- Route correction: the source proof computes the right derived functor on injective
  -- representatives, so the chapter-localizer criterion reduces the proof to injective models.
  exact hΦ.isRightDerivedFunctor_of_isIso (resolutionLiftComparison F j j' hj')
    (fun X ↦ resolutionLiftComparison_app_isIso_on_injective
      (𝒜 := 𝒜) (ℬ := ℬ) (F := F) j j' hj' X)

end

end CategoryTheory

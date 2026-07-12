import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap13.Lemma_13_14_16
import StacksProject_2024.Chap13.Lemma_13_20_2
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Sections_on_open

open CategoryTheory
open CategoryTheory.Functor
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped CategoryTheory RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (V : Opens Y.carrier)

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "ΓModV" => ModuleCat (sectionsRingOnOpen Y V)
local notation "QX" => boundedBelowHomotopyQuasiIso ModX
local notation "QY" => boundedBelowHomotopyQuasiIso ModY
local notation "pushforwardPlus" =>
  (mapBoundedBelowHomotopyCategory (f _*) : K⁺(ModX) ⥤ K⁺(ModY))
local notation "sectionsAtOpen" =>
  (SheafOfModules.evaluation Y.ringCatSheaf (op V) : ModY ⥤ ΓModV)
local notation "sectionsAtOpenPlus" =>
  mapBoundedBelowHomotopyCategoryToDerivedBelow sectionsAtOpen

/- Domain-style sampling for Lemma 20.13.1:
- primary domain: bounded-below Grothendieck comparison morphisms for module pushforward followed
  by sections on an open subset of a ringed space;
- sampled owner declarations:
  `preimageOpen`,
  `sectionsRingOnOpen`,
  `moduleSectionsRestrictionFunctor`,
  `Functor.rightDerivedCompComparison`;
- best owner abstraction:
  `source-facing`: the comparison between `restriction ∘ Γ(f ⁻¹ᵁ V, -)` and `Γ(V, -) ∘ f_*`;
  `core/canonical`: `Functor.rightDerivedCompComparison` applied to the canonical pushforward and
    open-sections owners;
  `bridge/view`: restriction of scalars along the induced map on section rings.
- primitive data: a morphism `f : X ⟶ Y` and an open subset `V ⊆ Y`;
- derived API: the bounded-below comparison isomorphism for `Γ(V, -) ∘ f_*`.
-/

-- Both underived composites evaluate an `𝒪_X`-module on `f ⁻¹ᵁ V` and then view the resulting
-- section module as a `Γ(V, 𝒪_Y)`-module by restriction of scalars along `f♯(V)`.
/-- The underived identity `restriction ∘ Γ(f ⁻¹ᵁ V, -) = Γ(V, -) ∘ f_*`. -/
theorem moduleSectionsEvaluation_atPreimage_comp_restriction_eq_pushforward_comp_sections :
    SheafOfModules.evaluation X.ringCatSheaf (op (preimageOpen f V)) ⋙
        moduleSectionsRestrictionFunctor f V =
      (f _*) ⋙ sectionsAtOpen := rfl

/-- The bounded-below right derived functor of sections on `V` exists. -/
local instance moduleSectionsAtOpen_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor sectionsAtOpenPlus QY := by
  let _ : Functor.HasPointwiseRightDerivedFunctor sectionsAtOpenPlus QY :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      sectionsAtOpenPlus
  infer_instance

/-- The bounded-below right derived functor of `f_*` followed by localization on `D⁺(Y)` exists.
-/
local instance modulePushforward_then_localization_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (pushforwardPlus ⋙ MorphismProperty.Q QY)
      QX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (pushforwardPlus ⋙ MorphismProperty.Q QY)
        QX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (pushforwardPlus ⋙ MorphismProperty.Q QY)
  infer_instance

/-- The bounded-below right derived functor of `Γ(V, -) ∘ f_*` exists. -/
local instance modulePushforward_then_sectionsAtOpen_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor
      (pushforwardPlus ⋙ sectionsAtOpenPlus)
      QX := by
  let _ :
      Functor.HasPointwiseRightDerivedFunctor
        (pushforwardPlus ⋙ sectionsAtOpenPlus)
        QX :=
    CategoryTheory.boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (pushforwardPlus ⋙ sectionsAtOpenPlus)
  infer_instance

private theorem modulePushforward_isBoundedBelowRightAcyclic_for_sectionsAtOpen_of_injective
    (I : ModX) [Injective I] :
    IsBoundedBelowRightAcyclicForAdditiveFunctor
      sectionsAtOpen
      ((f _*).obj I) := by
  -- Lemma `20.11.10` gives the vanishing of the positive cohomology groups
  -- `H^p(V, f_* I)`, and the Chapter `13` acyclicity criterion translates that vanishing into the
  -- bounded-below right-acyclicity required by `rightDerivedCompComparison_isIso_iff`.
  sorry

-- Use the underived identity above to identify the source composite with
-- `restriction ∘ Γ(f ⁻¹ᵁ V, -)`. Since restriction of scalars is exact, Lemma `20.11.10`
-- supplies the right-acyclicity of pushforwards of injective `𝒪_X`-modules for `Γ(V, -)`.
/-- Lemma 20.13.1: for an open subset `V ⊆ Y`, the canonical bounded-below Grothendieck
comparison morphism for `Γ(V, -) ∘ f_*`, equivalently for
`restriction ∘ Γ(f ⁻¹ᵁ V, -)`, is an isomorphism. -/
@[stacks 01EZ]
instance modulePushforward_sectionsAtOpen_boundedBelowRightDerivedCompComparison_isIso :
    IsIso
      (rightDerivedCompComparison
        QX
        QY
        pushforwardPlus
        sectionsAtOpenPlus) := by
  sorry

end AlgebraicGeometry.RingedSpace

import Mathlib
import StacksProject_2024.stacks_project.Chap14.Definition_14_26_6
import StacksProject_2024.stacks_project.Chap14.Lemma_14_33_4
import StacksProject_2024.stacks_project.Chap14.Lemma_14_34_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped IteratedEndofunctor
open scoped Simplicial

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable {U : 𝒮 ⥤ 𝒜} {V : 𝒜 ⥤ 𝒮}

/- Domain-style sampling for Lemma 14.34.3:
- primary domain: simplicial resolutions attached to an adjunction via its induced comonad, and
  simplicial homotopy equivalences of the resulting augmentations;
- sampled owner declarations:
  `IteratedEndofunctorRealization`,
  `iteratedEndofunctorAugmentation`,
  `prePostcomposeAugmented`,
  `CategoryTheory.SimplicialObject.HomotopyEquiv`;
- best owner abstraction: the source-facing augmentations in Lemma 14.34.3 already live on the
  canonical owners `prePostcomposeAugmented ... (iteratedEndofunctorAugmentation ...)`; the only
  additional primitive data needed for the explicit inverse is the degree-`0` section induced by
  the adjunction unit;
- primitive data vs. derived API:
  primitive data are `adj`, the realization witness `hX`, and the degree-`0` sections below;
  the simplicial inverses obtained from `SimplicialObject.fromZero` and the homotopy-equivalence
  statements are derived API;
- source/core/bridge triage:
  - `source-facing`: the two augmentation morphisms in the statement of Lemma 14.34.3;
  - `core/canonical`: `IteratedEndofunctorRealization`, `iteratedEndofunctorAugmentation`,
    `prePostcomposeAugmented`, and `SimplicialObject.IsHomotopyEquivalence`;
  - `bridge/view`: the explicit degree-`0` sections and their induced `fromZero` simplicial maps.
-/

section

variable (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
variable (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X)

local notation "aug" =>
  iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX

local notation "postAug" =>
  prePostcomposeAugmented (𝟭 𝒜) V aug

local notation "preAug" =>
  prePostcomposeAugmented U (𝟭 𝒜) aug

/-- The degree-`0` section of the postcomposed adjunction-resolution augmentation induced by the
unit of `adj`. -/
def postcompose_adjunctionResolutionAugmentation_zeroSection :
    V ⟶ (postAug).left _⦋0⦌ :=
  V.rightUnitor.inv ≫ V.whiskerLeft adj.unit ≫ (V.associator U V).inv ≫
    eqToHom (congrArg (fun Z : 𝒜 ⥤ 𝒜 ↦ Z ⋙ V) (hX.obj_eq 0).symm)

-- Proof sketch: unfold the degree-`0` augmentation component, which is the counit
-- `adj.toComonad.ε = adj.counit`, and compute the composite with the unit-induced section above.
-- After evaluating at an object `A : 𝒜`, this is exactly the right triangle identity for `adj`.
/-- The unit-induced degree-`0` map is a section of the degree-`0` augmentation component after
postcomposition by `V`. -/
theorem postcompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero :
    postcompose_adjunctionResolutionAugmentation_zeroSection adj hX ≫
        (postAug).hom.app (op ⦋0⦌) =
      𝟙 V := sorry

/-- The degree-`0` section of the precomposed adjunction-resolution augmentation induced by the
unit of `adj`. -/
def precompose_adjunctionResolutionAugmentation_zeroSection :
    U ⟶ (preAug).left _⦋0⦌ :=
  U.leftUnitor.inv ≫ whiskerRight adj.unit U ≫ (U.associator V U).hom ≫
    eqToHom (congrArg (fun Z : 𝒜 ⥤ 𝒜 ↦ U ⋙ Z) (hX.obj_eq 0).symm)

-- Proof sketch: unfold the degree-`0` augmentation component and evaluate at an object
-- `S : 𝒮`; the resulting composite is the left triangle identity for `adj`.
/-- The unit-induced degree-`0` map is a section of the degree-`0` augmentation component after
precomposition by `U`. -/
theorem precompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero :
    precompose_adjunctionResolutionAugmentation_zeroSection adj hX ≫
        (preAug).hom.app (op ⦋0⦌) =
      𝟙 U := sorry

-- Proof sketch: apply Lemma 14.33.4 to the canonical augmentation
-- after postcomposition by `V`, using the unit of the adjunction to construct a section of
-- the degree-`0` component. Then apply Lemma 14.33.5 to show the two composites are simplicially
-- homotopic to the relevant identities, with the triangle identity providing the degree-`0`
-- equality.
/-- Lemma 14.34.3 (1): after postcomposing the standard simplicial resolution attached to an
adjunction `U ⊣ V` with `V`, the induced augmentation to the constant simplicial object on `V` is a
simplicial homotopy equivalence. -/
theorem postcompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
    (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X) :
    IsHomotopyEquivalence
      (prePostcomposeAugmented (𝟭 𝒜) V
        (iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX)).hom := by
  let εX := iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX
  have hsection :
      (prePostcomposeAugmented (𝟭 𝒜) V εX).left.fromZero
          (postcompose_adjunctionResolutionAugmentation_zeroSection adj hX) ≫
        (prePostcomposeAugmented (𝟭 𝒜) V εX).hom =
      𝟙 _ := by
    simpa using
      prePostcomposeAugmentation_fromZero_comp_eq_id
        (𝟭 𝒜)
        V
        εX
        (postcompose_adjunctionResolutionAugmentation_zeroSection adj hX)
        (postcompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero adj hX)
  sorry

-- Proof sketch: apply Lemma 14.33.4 to the canonical augmentation
-- after precomposition by `U`, using the unit of the adjunction to construct a section of
-- the degree-`0` component. Then apply Lemma 14.33.5 to show the two composites are simplicially
-- homotopic to the relevant identities, with the other triangle identity providing the degree-`0`
-- equality.
/-- Lemma 14.34.3 (2): after precomposing the standard simplicial resolution attached to an
adjunction `U ⊣ V` with `U`, the induced augmentation to the constant simplicial object on `U` is a
simplicial homotopy equivalence. -/
theorem precompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
    (adj : U ⊣ V) {X : SimplicialObject (𝒜 ⥤ 𝒜)}
    (hX : IteratedEndofunctorRealization adj.toComonad.ε adj.toComonad.δ X) :
    IsHomotopyEquivalence
      (prePostcomposeAugmented U (𝟭 𝒜)
        (iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX)).hom := by
  let εX := iteratedEndofunctorAugmentation adj.toComonad.ε adj.toComonad.δ hX
  have hsection :
      (prePostcomposeAugmented U (𝟭 𝒜) εX).left.fromZero
          (precompose_adjunctionResolutionAugmentation_zeroSection adj hX) ≫
        (prePostcomposeAugmented U (𝟭 𝒜) εX).hom =
      𝟙 _ := by
    simpa using
      prePostcomposeAugmentation_fromZero_comp_eq_id
        U
        (𝟭 𝒜)
        εX
        (precompose_adjunctionResolutionAugmentation_zeroSection adj hX)
        (precompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero adj hX)
  sorry

end

end CategoryTheory

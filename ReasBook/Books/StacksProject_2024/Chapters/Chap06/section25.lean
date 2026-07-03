import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_25_1 (from Chap06) -/
universe u

open CategoryTheory

namespace AlgebraicGeometry

/- Domain-style sampling for Definition 6.25.1:
- primary domain: ringed spaces and morphisms of ringed spaces;
- sampled owner declarations:
  `RingedSpace`,
  `SheafedSpace`,
  `SheafedSpace.sheaf`,
  `TopCat.Sheaf.pushforward`;
- owner abstraction: the source-facing owner is `RingedSpace`; the underlying
  `SheafedSpace CommRingCat` infrastructure is core/canonical support and should not replace the
  ringed-space surface;
- primitive data: a ringed space `X` and a morphism `f : X ⟶ Y`;
- derived API: the underlying continuous map `f.hom.base` and the structure-sheaf morphism
  `⟨f.hom.c⟩ : 𝒪_Y ⟶ f_* 𝒪_X`.

Source/core/bridge triage:
- `source-facing`: ringed spaces and morphisms of ringed spaces;
- `core/canonical`: `SheafedSpace CommRingCat`;
- `bridge/view`: the component maps `f.hom.base` and `⟨f.hom.c⟩`.
-/

variable {X Y : RingedSpace.{u}}

/- Definition 6.25.1, owner recall: a ringed space is the canonical mathlib owner
`AlgebraicGeometry.RingedSpace`. -/
recall RingedSpace

/- A morphism of ringed spaces is an arrow in the category `AlgebraicGeometry.RingedSpace`. -/
#check (X ⟶ Y)

/- The first component of a morphism of ringed spaces is the underlying continuous map. -/
#check fun (f : X ⟶ Y) ↦ f.hom.base

/- The second component is the structure-sheaf morphism
`f^\sharp : \mathcal{O}_Y ⟶ f_* \mathcal{O}_X`. -/
#check fun (f : X ⟶ Y) ↦
  (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf from
    ⟨f.hom.c⟩)

end AlgebraicGeometry

/-! ### Example_6_25_2 (from Chap06) -/
open CategoryTheory Opposite TopologicalSpace
open TopCat.Sheaf

noncomputable section

/- Domain-style sampling for Example 6.25.2:
- primary domain: morphisms of sheaves of continuous real-valued functions along a continuous map;
- sampled owner declarations:
  `continuousRealFunctionsSheaf`,
  `TopCat.Sheaf.pushforward`,
  `ContinuousMap.compRightAlgHom`,
  `ObjectProperty.homMk`;
- best owner abstraction: the canonical `f`-map is a morphism in the sheaf category
  `continuousRealFunctionsSheaf Y ⟶
    (pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)`;
- primitive data: for each open `V ⊆ Y`, the pullback algebra homomorphism
  `C⁰(V, ℝ) → C⁰(f ⁻¹' V, ℝ)` induced by `ContinuousMap.compRightAlgHom`;
- derived API: the naturality of these sectionwise maps and the resulting packaged sheaf morphism.

Source/core/bridge triage:
- `source-facing`: the induced `f^\sharp` on the sheaf of continuous real-valued functions;
- `core/canonical`: a presheaf morphism into the canonical sheaf pushforward owner;
- `bridge/view`: `ObjectProperty.homMk`, packaging the underlying presheaf morphism as a morphism
  of sheaves. -/

/-- The sectionwise pullback homomorphism on continuous real-valued functions over an open subset
of the target. -/
private def continuousRealFunctionsSheafPullbackApp {X Y : TopCat} (f : X ⟶ Y)
    (V : (Opens Y)ᵒᵖ) :
    (continuousRealFunctionsSheaf Y).presheaf.obj V ⟶
      ((pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)).presheaf.obj V :=
  CommAlgCat.ofHom <|
    ContinuousMap.compRightAlgHom ℝ ℝ (f.hom.restrictPreimage (V.unop : Set Y))

private def continuousRealFunctionsPresheafFMap {X Y : TopCat} (f : X ⟶ Y) :
    (continuousRealFunctionsSheaf Y).presheaf ⟶
      ((pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X)).presheaf where
  app := continuousRealFunctionsSheafPullbackApp f
  naturality := fun {_ _} i ↦ by
    ext h
    rfl

/-- Example 6.25.2: a continuous map `f : X → Y` induces the canonical `f`-map
`f^\sharp : \mathcal{C}^0_Y → \mathcal{C}^0_X` of sheaves of `ℝ`-algebras, whose component on an
open `V ⊆ Y` sends a continuous function `h : V → ℝ` to the pullback `h ∘ f|_{f^{-1}(V)}`. -/
def continuous_real_functions_sheaf_f_map {X Y : TopCat} (f : X ⟶ Y) :
    continuousRealFunctionsSheaf Y ⟶
      (pushforward (CommAlgCat ℝ) f).obj (continuousRealFunctionsSheaf X) :=
  ObjectProperty.homMk (continuousRealFunctionsPresheafFMap f)

/-- The component of `continuous_real_functions_sheaf_f_map` over an open subset `V ⊆ Y` is the
sectionwise pullback homomorphism `h ↦ h ∘ f|_{f^{-1}(V)}`. -/
theorem continuous_real_functions_sheaf_f_map_app {X Y : TopCat} (f : X ⟶ Y)
    (V : (Opens Y)ᵒᵖ) :
    (continuous_real_functions_sheaf_f_map f).1.app V =
      CommAlgCat.ofHom
        (ContinuousMap.compRightAlgHom ℝ ℝ (f.hom.restrictPreimage (V.unop : Set Y))) :=
  rfl

/-! ### Definition_6_25_3 (from Chap06) -/
universe u v

open CategoryTheory
open Opposite TopologicalSpace

namespace AlgebraicGeometry

variable {X Y Z : RingedSpace.{u, v}} (f : X ⟶ Y) (g : Y ⟶ Z)

/- Domain-style sampling for Definition 6.25.3:
- primary domain: categorical composition of morphisms in `RingedSpace` and the resulting formulas
  on the underlying `SheafedSpace` and topological-space components;
- sampled owner declarations:
  `CategoryStruct.comp`,
  `InducedCategory.comp_hom`,
  `SheafedSpace.comp_hom_base`,
  `SheafedSpace.comp_hom_c_app'`;
- owner abstraction: categorical composition in `RingedSpace`;
- primitive data: composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`;
- derived API: the formulas for the underlying `SheafedSpace` morphism, the underlying continuous
  map, and the sectionwise structure-sheaf map of `f ≫ g`.

Source/core/bridge triage:
- `source-facing`: the Stacks formula
  `(g, g^\sharp) \circ (f, f^\sharp) = (g \circ f, f^\sharp \circ g^\sharp)`;
- `core/canonical`: categorical composition in `RingedSpace`;
- `bridge/view`: the induced component formulas
  `InducedCategory.comp_hom`, `SheafedSpace.comp_hom_base`, and
  `SheafedSpace.comp_hom_c_app'`.

This item only recalls canonical owner data already present upstream, so the refined file should
stay recall-shaped and avoid any parallel local wrapper for composition. -/

/- Definition 6.25.3: the composition of morphisms of ringed spaces is the canonical categorical
composition `f ≫ g : X ⟶ Z`. This matches the Stacks Project formula
`(g, g^\sharp) ∘ (f, f^\sharp) = (g ∘ f, f^\sharp ∘ g^\sharp)`. -/
#check (f ≫ g : X ⟶ Z)

/- Companion recall: on the underlying `SheafedSpace`, composition is exactly the canonical
induced-category composition theorem. -/
recall InducedCategory.comp_hom

#check (InducedCategory.comp_hom f g : (f ≫ g).hom = f.hom ≫ g.hom)

/- Companion recall: on underlying continuous maps, the same formula is the standard
`SheafedSpace` component lemma. -/
recall SheafedSpace.comp_hom_base

#check (SheafedSpace.comp_hom_base f g :
  (f ≫ g).hom.base = f.hom.base ≫ g.hom.base)

/- Companion recall: on sections over an open `U ⊆ Z`, the structure-sheaf component of the
composite is the composite `g^\sharp(U) ≫ f^\sharp(g^{-1}U)`. -/
recall SheafedSpace.comp_hom_c_app'

variable (U : Opens Z)

#check (SheafedSpace.comp_hom_c_app' f g U)

end AlgebraicGeometry

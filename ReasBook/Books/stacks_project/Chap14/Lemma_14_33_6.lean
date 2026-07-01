import Mathlib
import stacks_project.Chap14.Lemma_14_33_2
import stacks_project.Chap14.Lemma_14_33_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject.Augmented
open scoped IteratedEndofunctor

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace IteratedEndofunctorResolutionWhiskerNotation

/- Source-facing notation for the two standard horizontal whiskerings of an endomorphism
`f : 𝟭 C ⟶ 𝟭 C` with a simplicial endofunctor object `X`. These are the simplicial maps whose
degreewise components are `f ⋆ 1_X` and `1_X ⋆ f`. -/
set_option quotPrecheck false in
scoped notation:81 f:81 " ⋆ₗ " X:82 =>
  Functor.whiskerLeft X ((whiskeringLeft C C C).map f)

set_option quotPrecheck false in
scoped notation:81 X:82 " ⋆ᵣ " f:81 =>
  Functor.whiskerLeft X ((whiskeringRight C C C).map f)

end IteratedEndofunctorResolutionWhiskerNotation

open scoped IteratedEndofunctorResolutionWhiskerNotation

/- Domain-style sampling for Lemma 14.33.6:
- primary domain: simplicial objects of endofunctors, augmented simplicial objects, whiskering of
  natural transformations by endofunctors, and the zigzag homotopy relation on simplicial maps;
- sampled same-kind declarations:
  `Functor.whiskeringLeft`,
  `Functor.whiskeringRight`,
  `Functor.id_hcomp`,
  `Functor.hcomp_id`,
  `prePostcomposeAugmented`,
  `SimplicialObject.Augmented.whiskeringObj`,
  `prePostcomposeAugmentedMap_homotopic`,
  `SimplicialObject.Augmented`;
- best owner abstraction: the primitive owner is the canonical whiskering action of the functors
  `whiskeringLeft C C C` and `whiskeringRight C C C` on the endofunorphism `f : 𝟭 C ⟶ 𝟭 C`; the
  source-facing simplicial maps are obtained by whiskering a simplicial object `X` by those owner
  maps, and for Lemma 14.33.6 the relevant `X` is the canonical iterated endofunctor resolution
  from `Lemma_14_33_2`, while the final homotopy statement is a specialization of the chapter-level
  theorem `prePostcomposeAugmentedMap_homotopic`;
- primitive data: the simplicial identities `hσδ₀`, `hσδ₁`, `hσσ` defining the canonical
  resolution, together with a natural endomorphism `f : 𝟭 C ⟶ 𝟭 C`;
- derived API: the source-facing simplicial endomorphisms
  `f ⋆ₗ X` and `X ⋆ᵣ f`, corresponding degreewise to `f ⋆ 1_X` and `1_X ⋆ f`, the canonical
  augmentation-compatibility squares for the iterated resolution, and the resulting homotopy
  statement.

Source/core/bridge triage:
- `source-facing`: the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` of the canonical simplicial
  endofunctor resolution arising from the iterated endofunctor construction;
- `core/canonical`: the functorial owner maps `(whiskeringLeft C C C).map f`,
  `(whiskeringRight C C C).map f`, whiskering by `X`, and the augmented pre/postcomposition owner
  API from `Lemma_14_33_5`;
- `bridge/view`: the notation-level source-facing whiskered maps `f ⋆ₗ X` and `X ⋆ᵣ f`, together
  with their augmentation-compatibility squares, which supply the augmented morphisms whose
  induced simplicial maps are obtained directly by `whiskeringObj.map ... |>.left`.
-/

private theorem prePostcomposeAugmented_id_id_hom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    :
    (prePostcomposeAugmented (𝟭 C) (𝟭 C) ε).hom = ε := by
  ext n
  simp [prePostcomposeAugmented]

private def leftStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringLeft C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem leftStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).left = f ⋆ₗ X := by
  simp [leftStarAugmentedHom]

@[simp] private theorem leftStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (leftStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [leftStarAugmentedHom]

private def rightStarAugmentedHom
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    prePostcomposeAugmented (𝟭 C) (𝟭 C) ε ⟶
      prePostcomposeAugmented (𝟭 C) (𝟭 C) ε :=
  ((SimplicialObject.Augmented.whiskering (C ⥤ C) (C ⥤ C)).map
    ((whiskeringRight C C C).map f)).app
      { left := X, right := 𝟭 C, hom := ε }

@[simp] private theorem rightStarAugmentedHom_left
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).left = X ⋆ᵣ f := by
  simp [rightStarAugmentedHom]

@[simp] private theorem rightStarAugmentedHom_right
    (X : SimplicialObject (C ⥤ C))
    (ε : X ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
    (f : 𝟭 C ⟶ 𝟭 C) :
    (rightStarAugmentedHom X ε f).right = f := by
  ext Z
  simp [rightStarAugmentedHom]

section IteratedResolution

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
local notation "X⦅" n:max "⦆" => Y⦅n⦆
local notation "d^⦅" n ", " j "⦆" => d[Y, d]⦅n, j⦆
local notation "s^⦅" n ", " j "⦆" => s[Y, s]⦅n, j⦆

-- Proof sketch: specialize the generic left-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `f ⋆ 1_X`): the left-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
theorem iterated_endofunctor_left_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (leftStarAugmentedHom X ε f).w

-- Proof sketch: specialize the generic right-whiskering compatibility square to the canonical
-- iterated endofunctor resolution and its canonical augmentation.
/-- Lemma 14.33.6 (compatibility for `1_X ⋆ f`): the right-whiskered endomorphism of the canonical
iterated endofunctor resolution is compatible with the augmentation via `f`. -/
theorem iterated_endofunctor_right_star_augmentation_compatible
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    CommSq
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f)
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      (iteratedEndofunctorAugmentation d s
        (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ))
      ((SimplicialObject.const (C ⥤ C)).map f) := by
  let X := iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ
  let ε := iteratedEndofunctorAugmentation d s
    (iteratedEndofunctorResolution_realization d s hσδ₀ hσδ₁ hσσ)
  simpa [X, ε, prePostcomposeAugmented_id_id_hom] using
    CommSq.mk (rightStarAugmentedHom X ε f).w

-- Proof sketch: specialize `prePostcomposeAugmentedMap_homotopy` to the augmented simplicial
-- object coming from the canonical iterated endofunctor resolution, taking both source and
-- target functors to be `𝟭 C`. The two required augmented morphisms are the ones determined by
-- the public compatibility theorems above; after identifying the whiskering owners at `𝟭 C` with the
-- original simplicial endofunctor object, the two resulting simplicial maps are
-- `f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ` and
-- `iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f`.
/-- Lemma 14.33.6: for the simplicial endofunctor object arising from `Example 14.33.1` and
`Lemma 14.33.2`, the endomorphisms `f ⋆ 1_X` and `1_X ⋆ f` are homotopic in the zigzag sense. -/
theorem iterated_endofunctor_left_star_right_star_homotopic
    (hσδ₀ : s^⦅0, 0⦆ ≫ d^⦅0, 0⦆ = 𝟙 X⦅0⦆)
    (hσδ₁ : s^⦅0, 0⦆ ≫ d^⦅0, 1⦆ = 𝟙 X⦅0⦆)
    (hσσ : s^⦅0, 0⦆ ≫ s^⦅1, 0⦆ = s^⦅0, 0⦆ ≫ s^⦅1, 1⦆)
    (f : 𝟭 C ⟶ 𝟭 C) :
    SimplicialObject.Homotopic
      (f ⋆ₗ iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ)
      (iteratedEndofunctorResolution d s hσδ₀ hσδ₁ hσσ ⋆ᵣ f) :=
  sorry

end IteratedResolution

end CategoryTheory

import Mathlib
import stacks_project.Chap04.«4_34_2_3»
import stacks_project.Chap08.Lemma_8_7_1
import stacks_project.Chap08.Lemma_8_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 8.8.5:
- primary domain: absolute inertia of fibred categories over a site and stackification morphisms.
- inspected owner-level declarations:
  `FibredCategoryOver.absoluteInertiaOver`,
  `CategoryOver.absoluteInertiaOverMap`,
  `absoluteInertiaStack`,
  `FibredCategoryMor.IsStackification`.
- best owner abstraction: the Chapter 4 fibred-category owner
  `FibredCategoryOver.absoluteInertiaOver`; the Chapter 4 based-category map
  `CategoryOver.absoluteInertiaOverMap` is only bridge/view data, and the Chapter 8 bundled stack
  target is `absoluteInertiaStack X'`.
- primitive data: a morphism `F : X ⟶ Y` of fibred categories and the canonical absolute inertia
  owner map induced by its underlying based functor over `C`.
- derived API: the strongly-cartesian preservation theorem below, the rebundled owner morphism
  `absoluteInertiaMap`, and the source-facing stackification theorem.

Source/core/bridge triage:
- `source-facing`: `absoluteInertia_of_stackification_isStackification`.
- `core/canonical`: `FibredCategoryOver.absoluteInertiaOver`, `absoluteInertiaStack`, and
  `FibredCategoryMor.IsStackification`.
- `bridge/view`: the Chapter 4 based-category map `CategoryOver.absoluteInertiaOverMap`, the
  preservation theorem below, and the rebundled induced morphism `absoluteInertiaMap`. -/

-- Proof sketch: view the absolute inertia as the relative inertia of the structure functor and
-- transport the preservation of strongly cartesian arrows along the explicit iterated `2`-fibre
-- product model of Lemma `4.34.1`.
/-- The canonical map on absolute inertia induced by a morphism of fibred categories preserves
strongly cartesian morphisms. -/
theorem absoluteInertiaOverMap_preservesStronglyCartesian
    {X Y : FibredCategoryOver C} (F : X ⟶ Y) :
    BasedFunctor.PreservesStronglyCartesian
      (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F)) := sorry

/-- The absolute inertia of a bundled stack, viewed again as a bundled stack over `(C, J)`. -/
abbrev absoluteInertiaOfStack
    (Y : StackOver J) :
    StackOver J :=
  ⟨FibredCategoryOver.absoluteInertiaOver Y.toFibredCategoryOver, inferInstance⟩

/-- The canonical morphism on absolute inertia induced by a morphism from a fibred category to a
stack over `(C, J)`. -/
noncomputable abbrev absoluteInertiaMap
    {X : FibredCategoryOver C} {Y : StackOver J} (F : X ⟶ Y) :
    FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver :=
  show FibredCategoryMor
      (FibredCategoryOver.absoluteInertiaOver X)
      (absoluteInertiaOfStack Y).toFibredCategoryOver
    from
      FibredCategoryMor.ofBasedFunctor
        (absoluteInertiaOverMap (FibredCategoryMor.toBasedFunctor F))
        (absoluteInertiaOverMap_preservesStronglyCartesian F)

-- Proof sketch: use Lemma `4.34.1` to identify absolute inertia with a `2`-fibre-product
-- construction, then apply Lemma `8.8.4` to the stackification morphism `i : X ⟶ X'`. Lemma
-- `8.7.1` supplies the canonical stack structure on the absolute inertia of the stack `X'`,
-- yielding the desired stackification statement for the induced inertia morphism.
/-- Lemma 8.8.5: if `i : X ⟶ X'` exhibits the stack `X'` as a stackification of the fibred
category `X` over the site `(C, J)`, then the induced morphism on absolute inertia exhibits the
absolute inertia of `X'` as a stackification of the absolute inertia of `X`. -/
theorem absoluteInertia_of_stackification_isStackification
    {X : FibredCategoryOver C} {X' : StackOver J}
    (i : X ⟶ X')
    (hi : FibredCategoryMor.IsStackification i) :
    FibredCategoryMor.IsStackification (absoluteInertiaMap i) := sorry

end CategoryTheory

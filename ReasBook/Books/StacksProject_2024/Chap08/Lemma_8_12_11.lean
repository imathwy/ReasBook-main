import Mathlib
import StacksProject_2024.Chap04.Lemma_4_18_3
import StacksProject_2024.Chap08.Lemma_8_8_1
import StacksProject_2024.Chap08.Lemma_8_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits
open scoped CategoryTheory.FibredCategoryOver
universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [HasFiniteNonemptyLimits C]

/-
Domain-style sampling for Lemma 8.12.11:
- primary domain: stackifications of fibred categories and their functoriality under the
  localized pushforward construction along `u : C ⥤ D`.
- inspected owner-level declarations:
  `FibredCategoryMor.IsStackification`,
  `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`,
  `stackification_precompose_functor`,
  `Functor.IsEquivalence`.
- best owner abstraction: the public statement should stay on the owner predicate
  `FibredCategoryMor.IsStackification` for the canonical composite
  `pushforwardFibredCategoryMap u G ≫ iYinv`, rather than introducing a local comparison wrapper.
- primitive data: a stackification `G : X ⟶ Y`, a chosen inverse-image stackification
  `iYinv : u ₚ Y ⟶ Yinv`, and the induced canonical pushforward morphism
  `pushforwardFibredCategoryMap u G : u ₚ X ⟶ u ₚ Y`.
- derived API: the composed stackification statement below and, when needed downstream, the
  canonical equivalence object `(stackification_precompose_functor _ iYinv).asEquivalence`.

Source/core/bridge triage:
- `source-facing`: the theorem `inverseImageStackAlong_isStackification_of_stackification`.
- `core/canonical`: `FibredCategoryMor.IsStackification`, `FibredCategoryOver.pushforward`,
  `pushforwardFibredCategoryMap`.
- `bridge/view`: the canonical owner statement
  `Functor.IsEquivalence (stackification_precompose_functor _ iYinv)`, whose `.asEquivalence`
  supplies the universal-property perspective on these stackification morphisms. -/

-- Proof sketch: apply the localized pushforward construction to the stackification morphism
-- `G : X ⟶ Y`, obtaining the canonical morphism `uₚ X ⟶ uₚ Y`. Composing with the chosen
-- stackification morphism `i : uₚ Y ⟶ Yinv` gives the desired canonical
-- comparison map. The stackification properties are checked on morphism presheaves and local
-- essential surjectivity exactly as in the Stacks Project argument.
/-- Lemma 8.12.11: if `G : X ⟶ Y` exhibits the stack `Y` as a stackification of the fibred
category `X` over `(C, J)`, then for any stackification `i : uₚ Y ⟶ Yinv` representing an
inverse-image stack of `Y` along `u`, the canonical comparison morphism `uₚ X ⟶ Yinv` is a
stackification of `uₚ X`. -/
theorem inverseImageStackAlong_isStackification_of_stackification
    (u : C ⥤ D) [PreservesFiniteNonemptyLimits u]
    {X : FibredCategoryOver C} {Y : StackOver J}
    (G : X ⟶ Y)
    (hG : FibredCategoryMor.IsStackification G)
    {Yinv : StackOver K}
    (iYinv : u ₚ Y ⟶ Yinv)
    (hiYinv : FibredCategoryMor.IsStackification iYinv) :
    FibredCategoryMor.IsStackification (pushforwardFibredCategoryMap u G ≫ iYinv) := sorry

end

end CategoryTheory

import Mathlib
import StacksProject_2024.Chap04.Definition_4_35_1
import StacksProject_2024.Chap08.Definition_8_12_4
import StacksProject_2024.Chap08.Lemma_8_12_5
import StacksProject_2024.Chap08.Lemma_8_12_6
import StacksProject_2024.Chap08.Lemma_8_12_8.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/- Domain-style sampling for Lemma 8.12.8:
- primary domain: the pushforward/pullback comparison for morphisms of fibred categories, built
  from the localized pushforward construction and the canonical pullback fibred category.
- inspected owner-level declarations:
  `FibredCategoryOver.pushforward`,
  `FibredCategoryOver.pullback`,
  `Functor.pushforwardProjection`,
  `FibredCategoryMor.objectProperty`,
  `SubTwoCategory.Hom.toHom`,
  `FibredCategoryMor.ofBasedFunctor`,
  `FibredCategoryMor.ofObjectProperty`.
- best owner abstraction: the public bridge should live on `FibredCategoryMor` between the
  canonical bundled objects `FibredCategoryOver.pushforward u X` and `u ᵖ Y`, with the strongly-cartesian condition expressed
  through the owner property `FibredCategoryMor.objectProperty` and the underlying based-functor
  comparison derived from the existing owner APIs.
- primitive data: the localized pushforward projection `u.pushforwardProjection X.p`, the unit
  `X.S ⥤ (FibredCategoryOver.pushforward u X).S`, and the canonical pullback owner `u ᵖ Y`.
- derived API: `FibredCategoryOver.pushforward`, `pushforwardFibredCategoryMap`,
  `pushforwardFibredCategoryUnit`, and the comparison functor
  `pushforwardPullbackFibredMorphismFunctor`.

Source/core/bridge triage:
- `source-facing`: the equivalence
  `pushforwardPullbackFibredMorphismFunctor_isEquivalence`.
- `core/canonical`: `FibredCategoryOver.pullback`, `Functor.pushforwardProjection`,
  `FibredCategoryMor`.
- `bridge/view`: `FibredCategoryOver.pushforward`, `pushforwardFibredCategoryUnit`, and
  `pushforwardPullbackFibredMorphismFunctor`. -/
/-- The canonical functor
`Mor_{Fib/D}(uₚ X, Y) ⥤ Mor_{Fib/C}(X, uᵖ Y)`. -/
noncomputable abbrev pushforwardPullbackFibredMorphismFunctor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    ((FibredCategoryOver.pushforward u X) ⟶ Y) ⥤
      (X ⟶ (u ᵖ Y)) :=
  pushforwardPullbackFibredMorphismLift u X Y ⋙
    FibredCategoryMor.ofObjectProperty X (u ᵖ Y)

/-- Helper for Chap08 Lemma 8 12 8: the lift stage of the pushforward-pullback comparison
is an equivalence. -/
lemma pushforwardPullbackFibredMorphismLift_isEquivalence
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    Functor.IsEquivalence (pushforwardPullbackFibredMorphismLift u X Y) := by
  -- The theorem-local helper split has already proved the three fields of a functor
  -- equivalence, so this proof only packages those fields for reuse.
  refine ⟨?_, ?_, ?_⟩
  · exact pushforwardPullbackFibredMorphismLift_faithful u X Y
  · exact pushforwardPullbackFibredMorphismLift_full u X Y
  · exact pushforwardPullbackFibredMorphismLift_essSurj u X Y

-- Proof sketch: the forward functor is the explicit construction `G ↦ H` from the text, obtained
-- by restricting `G : uₚ X ⟶ Y` along the canonical unit `X ⟶ uₚ X` and packaging the result as a
-- functor `X ⟶ uᵖ Y`. The inverse sends `H : X ⟶ uᵖ Y` to the functor `uₚ X ⟶ Y` induced from
-- the localization universal property of Lemma `4.27.16`, exactly as in the proof of the Stacks
-- Project lemma. The two constructions are mutually quasi-inverse on morphism categories.
/-- Chap08 Lemma 8 12 8: if `C` has pullbacks and equalizers and `u : C ⥤ D` preserves them, then the
canonical functor from morphisms of fibred categories `uₚ X ⟶ Y` over `D` to morphisms of
fibred categories `X ⟶ uᵖ Y` over `C` is an equivalence of categories. -/
@[stacks 04WI]
theorem pushforwardPullbackFibredMorphismFunctor_isEquivalence
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    Functor.IsEquivalence (pushforwardPullbackFibredMorphismFunctor u X Y) := by
  -- The comparison functor is the composite of the lift equivalence and the object-property
  -- comparison equivalence, so typeclass inference can assemble the final equivalence.
  letI : Functor.IsEquivalence (pushforwardPullbackFibredMorphismLift u X Y) :=
    pushforwardPullbackFibredMorphismLift_isEquivalence u X Y
  letI : Functor.IsEquivalence (FibredCategoryMor.ofObjectProperty X (u ᵖ Y)) :=
    fibredCategoryMorOfObjectProperty_isEquivalence X (u ᵖ Y)
  infer_instance

end Pushforward

end

end CategoryTheory

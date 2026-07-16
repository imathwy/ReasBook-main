import Mathlib
import StacksProject_2024.stacks_project.Chap08.Definition_8_12_9
import StacksProject_2024.stacks_project.Chap08.Lemma_8_8_3
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_2
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open InducedCategory.Hom
open scoped FibredCategoryOver
open scoped Bicategory

universe u v

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable [HasFiniteNonemptyLimits C]
variable (u : C ⥤ D) [Functor.IsContinuous u J K] [PreservesFiniteNonemptyLimits u]

attribute [local instance] pushforwardPullbackFibredMorphismFunctor_isEquivalence

/- Domain-style sampling for Lemma 8.12.10:
- primary domain: the inverse-image/direct-image adjunction for stacks, expressed through the
  universal property of stackification and the canonical pushforward/pullback comparison for
  fibred-category morphisms.
- inspected owner-level declarations:
  `StackOver.pullback`,
  `stackification_precompose_functor`,
  `stackification_precompose_functor_isEquivalence`,
  `pushforwardPullbackFibredMorphismFunctor`,
  `pushforwardPullbackFibredMorphismFunctor_isEquivalence`,
  `InducedCategory.Hom.ofFibredCategoryMor`.
- best owner abstraction: the main source-facing construction is the composite of those two owner
  equivalences, with the target direct-image stack expressed by the existing bridge
  `T.pullback u`; the remaining stack-morphism/fibred-morphism comparison is the hom inclusion of
  the full sub-`2`-category of stacks.
- primitive data: a chosen stackification `iSinv : u ₚ S.toFibredCategoryOver ⟶ Sinv` and a
  target stack `T`.
- derived API: the canonical equivalence objects produced by
  `stackification_precompose_functor`, `pushforwardPullbackFibredMorphismFunctor`, and
  the explicit stack-hom/ambient-hom equivalence constructed below.

Source/core/bridge triage:
- `source-facing`: the adjunction-style equivalence on stack morphism categories in Lemma 8.12.10.
- `core/canonical`: `stackification_precompose_functor`,
  `pushforwardPullbackFibredMorphismFunctor`, `StackOver.pullback`, and
  the `Functor.IsEquivalence` owners on the stackification and pushforward/pullback comparison
  functors.
- `bridge/view`: the explicit equivalence between stack morphisms and ambient fibred-category
  morphisms built from `InducedCategory.Hom.ambientEquivalence`. -/

/-- The ambient equivalence identifying morphisms from `S` to the pullback stack `T.pullback u`
with ambient morphisms into the underlying pullback fibred category. -/
private noncomputable abbrev stackMor_pullback_ambientEquivalence
    (S : StackOver J) (T : StackOver K) :
    ((S : FibredCategoryOver C) ⟶ u ᵖ (T : FibredCategoryOver D)) ≌
      (S ⟶ T.pullback u) :=
  ((ambientEquivalence :
      (S ⟶ T.pullback u) ≌
        (S.toFibredCategoryOver ⟶ (T.pullback u).toFibredCategoryOver)).symm)

/-- Lemma 8.12.10: for a chosen inverse-image stack `f^{-1} S` represented by a stackification
`uₚ S ⟶ f^{-1} S`, morphisms of stacks `f^{-1} S ⟶ T` are canonically equivalent to morphisms
`S ⟶ f_* T`, modeled here by morphisms of stacks `S ⟶ T.pullback u`. -/
noncomputable def inverseImage_stackMor_to_directImage_stackMor_equivalence
    (S : StackOver J) (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T : StackOver K) :
    (Sinv ⟶ T) ≌ (S ⟶ T.pullback u) :=
  let _ : HasPullbacks C := inferInstance
  let _ : HasEqualizers C := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan u := inferInstance
  let _ : PreservesLimitsOfShape WalkingParallelPair u := inferInstance
  let G := stackification_precompose_functor T iSinv
  let _ : Functor.IsEquivalence G :=
    stackification_precompose_functor_isEquivalence T iSinv hiSinv
  let H :
      ((u ₚ (S : FibredCategoryOver C)) ⟶ (T : FibredCategoryOver D)) ⥤
        ((S : FibredCategoryOver C) ⟶ u ᵖ (T : FibredCategoryOver D)) :=
    pushforwardPullbackFibredMorphismFunctor
      u (S : FibredCategoryOver C) (T : FibredCategoryOver D)
  let eI := stackMor_pullback_ambientEquivalence u S T
  G.asEquivalence.trans (H.asEquivalence.trans eI)

-- Proof sketch: this is the tautological identity satisfied by the canonical equivalence object
-- constructed above; later proof stages can replace it with more explicit objectwise formulas.
/-- The canonical equivalence constructor of Lemma `8.12.10` is stable as the chosen public owner
for the stack-morphism equivalence. -/
theorem inverseImage_stackMor_to_directImage_stackMor_equivalence_exists
    (S : StackOver J) (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (T : StackOver K) :
    let _e := inverseImage_stackMor_to_directImage_stackMor_equivalence u S Sinv iSinv hiSinv T
    True := sorry

end

end CategoryTheory

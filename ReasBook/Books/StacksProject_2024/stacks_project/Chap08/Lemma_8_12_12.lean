import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_1
import StacksProject_2024.stacks_project.Chap04.Definition_4_33_9
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_11
import StacksProject_2024.stacks_project.Chap08.Definition_8_12_9
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_10
import StacksProject_2024.stacks_project.Chap08.Lemma_8_8_3
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_2
import StacksProject_2024.stacks_project.Chap08.Lemma_8_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Bicategory
open FibredCategoryOver
open InducedCategory.Hom
open scoped FibredCategoryOver
open scoped Bicategory

universe u v u1 u2

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{max u v} C] [Category.{max u v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

variable [HasFiniteNonemptyLimits C] [PreservesFiniteNonemptyLimits u]

/- Domain-style sampling for Lemma 8.12.12:
- primary domain: inverse-image stacks along a morphism of sites and the induced comparison with
  the direct-image model on stacks.
- inspected owner-level declarations:
  `StackOver.pullback`,
  `inverseImage_stackMor_to_directImage_stackMor_equivalence`,
  `stackification_unique_up_to_unique_twoIso`,
  `InducedCategory.Hom.IsEquivalenceOverBase`.
- best owner abstraction: the direct-image side should use the canonical Chapter 8 bridge
  `Sinv.pullback u`, while equivalence of stacks should be recorded by the stack-morphism owner
  predicate `IsEquivalenceOverBase`; the morphism-category comparison in part `(2)` is then a
  source-facing bridge built from the owner equivalence of Lemma `8.12.10`, not a second owner.
- primitive data: a stack `S`, a chosen inverse-image stackification `iSinv : u ₚ S ⟶ Sinv`,
  and similarly for `S'`.
- derived API: the canonical comparison `S ⟶ Sinv.pullback u`, the owner equivalence predicate on
  that comparison, and the induced equivalence between the two stack-morphism categories.

Source/core/bridge triage:
- `source-facing`: the comparison of `S` with `f_* f⁻¹ S` and the induced equivalence on
  stack-morphism categories.
- `core/canonical`: `StackOver.pullback`,
  `inverseImage_stackMor_to_directImage_stackMor_equivalence`,
  `stackification_unique_up_to_unique_twoIso`,
  `InducedCategory.Hom.IsEquivalenceOverBase`.
- `bridge/view`: the chosen stackification morphisms `iSinv`, `iSinv'`. -/

/-- The canonical comparison morphism `S ⟶ Sinv.pullback u` associated to the chosen
inverse-image stackification `iSinv : u ₚ S ⟶ Sinv`. -/
noncomputable def pushforwardInverseImageComparison
    [Functor.IsContinuous u J K]
    (S : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv) :
    S ⟶ Sinv.pullback u :=
  let SinvPull : StackOver J := Sinv.pullback u
  let _ : HasPullbacks C := inferInstance
  let _ : HasEqualizers C := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan u := inferInstance
  let _ : PreservesLimitsOfShape WalkingParallelPair u := inferInstance
  let F :=
    pushforwardPullbackFibredMorphismFunctor
      u (S : FibredCategoryOver C) (Sinv : FibredCategoryOver D)
  show S ⟶ SinvPull from
    ofFibredCategoryMor (F.obj iSinv)

/-- Lemma 8.12.12 (1): if `Sinv` is a chosen inverse-image stack representing `f^{-1} S`, then
the canonical comparison from `S` to the Chapter 8 direct-image model `Sinv.pullback u` of
`f_* f^{-1} S` is an equivalence of stacks over `(C, J)`. -/
theorem stack_equivalent_to_pushforward_inverseImage
    [Functor.IsContinuous u J K] [u.Full] [u.Faithful]
    (S : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv) :
    IsEquivalenceOverBase (pushforwardInverseImageComparison u S Sinv iSinv) :=
  sorry

-- Proof sketch: Lemma `8.12.10` identifies morphisms out of a chosen inverse-image stack with
-- morphisms into the canonical direct-image model `Sinv'.pullback u`. Apply part `(1)` to compare
-- `S'` with `Sinv'.pullback u`, then transport morphisms across that equivalence to obtain the
-- source-facing equivalence between morphisms `S ⟶ S'` and morphisms `Sinv ⟶ Sinv'`.
/-- Lemma 8.12.12 (2): the canonical composite from postcomposition with the comparison
`S' ⟶ Sinv'.pullback u` and the inverse of the Lemma `8.12.10` equivalence is an equivalence on
stack-morphism categories. -/
theorem inverseImage_induces_equivalence_on_stackMorphismCategories
    [Functor.IsContinuous u J K] [u.Full] [u.Faithful]
    (S S' : StackOver J)
    (Sinv : StackOver K)
    (iSinv : u ₚ S ⟶ Sinv)
    (hiSinv : FibredCategoryMor.IsStackification iSinv)
    (Sinv' : StackOver K)
    (iSinv' : u ₚ S' ⟶ Sinv')
    (hiSinv' : FibredCategoryMor.IsStackification iSinv') :
    Functor.IsEquivalence
      (postcomp S (pushforwardInverseImageComparison.{u, v, u1, u2} u S' Sinv' iSinv') ⋙
        (inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
          u S Sinv iSinv hiSinv Sinv').inverse) := by
  let F := postcomp S (pushforwardInverseImageComparison.{u, v, u1, u2} u S' Sinv' iSinv')
  have hF : Functor.IsEquivalence F := by
    sorry
  let eInv := inverseImage_stackMor_to_directImage_stackMor_equivalence.{u, v, u1, u2}
    u S Sinv iSinv hiSinv Sinv'
  let _ : Functor.IsEquivalence F := hF
  let _ : Functor.IsEquivalence eInv.inverse := by infer_instance
  change Functor.IsEquivalence (F ⋙ eInv.inverse)
  infer_instance

end

end CategoryTheory

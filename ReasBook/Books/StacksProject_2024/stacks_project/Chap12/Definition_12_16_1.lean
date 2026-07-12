import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Preadditive.Transfer
import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

scoped notation "Gr(" 𝒜 ")" => GradedObject ℤ 𝒜

namespace GradedObject

section Eval

variable {β : Type*} {C : Type u} [Category.{v} C]

noncomputable instance [Preadditive C] : Preadditive (GradedObject β C) := by
  let E := piEquivalenceFunctorDiscrete β C
  exact Preadditive.ofFullyFaithful E.fullyFaithfulFunctor

private noncomputable def evalIsoEvaluation (p : β) :
    (eval p : GradedObject β C ⥤ C) ≅
      (piEquivalenceFunctorDiscrete β C).functor ⋙
        (evaluation (Discrete β) C).obj (Discrete.mk p) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simp)

instance [Preadditive C] (p : β) : (eval p : GradedObject β C ⥤ C).Additive := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.Additive := E.fullyFaithfulFunctor.additive_ofFullyFaithful
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : H.Additive := inferInstance
  exact Functor.additive_of_iso (evalIsoEvaluation p).symm

noncomputable instance [HasFiniteLimits C] (p : β) :
    PreservesFiniteLimits (eval p : GradedObject β C ⥤ C) := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : PreservesFiniteLimits E.functor := PreservesLimits.preservesFiniteLimits E.functor
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : PreservesFiniteLimits H := inferInstance
  letI : PreservesFiniteLimits (E.functor ⋙ H) := comp_preservesFiniteLimits E.functor H
  exact preservesFiniteLimits_of_natIso (evalIsoEvaluation p).symm

noncomputable instance [HasFiniteColimits C] (p : β) :
    PreservesFiniteColimits (eval p : GradedObject β C ⥤ C) := by
  let E : GradedObject β C ≌ Discrete β ⥤ C := piEquivalenceFunctorDiscrete β C
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : PreservesFiniteColimits E.functor := PreservesColimits.preservesFiniteColimits E.functor
  let H : (Discrete β ⥤ C) ⥤ C := (evaluation (Discrete β) C).obj (Discrete.mk p)
  letI : PreservesFiniteColimits H := inferInstance
  letI : PreservesFiniteColimits (E.functor ⋙ H) := comp_preservesFiniteColimits E.functor H
  exact preservesFiniteColimits_of_natIso (evalIsoEvaluation p).symm

end Eval

end GradedObject

end CategoryTheory

section

variable (𝒜 : Type u) [Category.{v} 𝒜]

/- Domain-style sampling for Definition 12.16.1:
- primary domain: category-theoretic graded objects and their pointwise category structure;
- sampled owner API:
  `CategoryTheory.GradedObject`,
  `GradedObject.categoryOfGradedObjects`,
  `GradedObject.eval`,
  `piEquivalenceFunctorDiscrete`;
- source/core/bridge triage:
  `source-facing`: the textbook category `Gr(𝒜)` of `ℤ`-graded objects;
  `core/canonical`: the owner type `GradedObject ℤ 𝒜`;
  `bridge/view`: the equivalence `piEquivalenceFunctorDiscrete`, used downstream in
  [Lemma_12_16_2](/volume/math/AI4M/users/zcwang/stacks_project/stacks_project/Items/Chap12/Lemma_12_16_2.lean)
  to transfer abelianity from the functor category.

Primitive data are only the ambient category `𝒜` and the grading set `ℤ`. The pointwise category
structure and evaluation functors are derived owner API from mathlib, so there is no room here for
a second local wrapper for `Gr(𝒜)`.
-/

/- Source-facing notation: the Stacks Project writes the category of graded objects in `𝒜` as
`Gr(𝒜)`. This is notation for the canonical owner `GradedObject ℤ 𝒜`. -/
#check Gr(𝒜)

/-- The canonical category `Gr(𝒜)` of graded objects inherits the standard shift functor. -/
instance instHasShiftGradedObject : HasShift (Gr(𝒜)) ℤ := by
  show HasShift (GradedObjectWithShift (1 : ℤ) 𝒜) ℤ
  infer_instance

/-- The standard shift functor on `Gr(𝒜)` is additive. -/
instance instShiftFunctorAdditive [Preadditive 𝒜] (n : ℤ) :
    (shiftFunctor (Gr(𝒜)) n).Additive where
  map_add := by
    intro A B f g
    ext i
    rfl

/-- The standard shift functor on `Gr(𝒜)` is `ℤ`-linear. -/
instance instShiftFunctorLinear [Preadditive 𝒜] (n : ℤ) :
    Functor.Linear ℤ (shiftFunctor (Gr(𝒜)) n) where
  map_smul := by
    intro A B r f
    ext i
    simp

variable (A B : Gr(𝒜))

/- Definition 12.16.1: the category `Gr(𝒜)` of graded objects is the canonical mathlib owner
type `GradedObject ℤ 𝒜`. Its objects are families `A : ℤ → 𝒜`, and its morphisms are families
`f : ∀ i : ℤ, A i ⟶ B i` with the pointwise category structure. Although the source states this
for an additive category, the owner construction itself only needs `[Category 𝒜]`. -/
#check (A ⟶ B)

/- Companion recalls: the category structure on `Gr(𝒜)` is the canonical pointwise owner
instance on `GradedObject ℤ 𝒜`, and the standard projections to degree `i` are the evaluation
functors `GradedObject.eval i : Gr(𝒜) ⥤ 𝒜`. -/
recall GradedObject.categoryOfGradedObjects
recall GradedObject.eval

end

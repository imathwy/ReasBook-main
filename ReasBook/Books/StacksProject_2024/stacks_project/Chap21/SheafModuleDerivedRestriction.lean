import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Over

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- The category `ModuleCat Λ` is preadditive. -/
instance moduleCatPreadditive :
    Preadditive (ModuleCat.{w} Λ) :=
  (inferInstance : Abelian (ModuleCat.{w} Λ)).toPreadditive

/-- Sheaves of `Λ`-modules on `(C, J)` form a preadditive category. -/
instance sheafModulePreadditive :
    Preadditive (Sheaf J (ModuleCat.{w} Λ)) :=
  (inferInstance : Abelian (Sheaf J (ModuleCat.{w} Λ))).toPreadditive

/-- Sheaves of `Λ`-modules on slice sites form preadditive categories. -/
instance sheafModuleOverPreadditive (U : C) :
    Preadditive (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  (inferInstance : Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))).toPreadditive

/-- Sheaves of `Λ`-modules on `(C, J)` have zero morphisms. -/
instance sheafModuleHasZeroMorphisms :
    HasZeroMorphisms (Sheaf J (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- Sheaves of `Λ`-modules on slice sites have zero morphisms. -/
instance sheafModuleOverHasZeroMorphisms (U : C) :
    HasZeroMorphisms (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  Preadditive.preadditiveHasZeroMorphisms

/-- The constant sheaf functor on `Λ`-modules preserves zero morphisms. -/
instance constantSheafPreservesZeroMorphisms :
    (constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms := by
  dsimp [constantSheaf]
  infer_instance

/-- The constant sheaf functor on slice sites preserves zero morphisms. -/
instance constantSheafOverPreservesZeroMorphisms (U : C) :
    (constantSheaf (J.over U) (ModuleCat.{w} Λ)).PreservesZeroMorphisms := by
  dsimp [constantSheaf]
  infer_instance

/-- Restriction to the slice site preserves zero morphisms. -/
instance overPullbackPreservesZeroMorphisms (U : C)
    [(J.overPullback (ModuleCat.{w} Λ) U).Additive] :
    (J.overPullback (ModuleCat.{w} Λ) U).PreservesZeroMorphisms := by
  let _ : HasZeroMorphisms (Sheaf J (ModuleCat.{w} Λ)) :=
    Preadditive.preadditiveHasZeroMorphisms
  let _ : HasZeroMorphisms (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
    Preadditive.preadditiveHasZeroMorphisms
  exact Functor.preservesZeroMorphisms_of_additive (J.overPullback (ModuleCat.{w} Λ) U)

/-- A family of additive slice restriction functors yields the pointwise additive instance. -/
instance overPullbackAdditiveOfFamily
    [h : ∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive] (U : C) :
    (J.overPullback (ModuleCat.{w} Λ) U).Additive :=
  h U

/-- A family of exact slice restriction functors yields the pointwise finite-limit instance. -/
instance overPullbackPreservesFiniteLimitsOfFamily
    [h : ∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)] (U : C) :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U) :=
  h U

/-- A family of exact slice restriction functors yields the pointwise finite-colimit instance. -/
instance overPullbackPreservesFiniteColimitsOfFamily
    [h : ∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)] (U : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U) :=
  h U

end

end CategoryTheory.Sheaf

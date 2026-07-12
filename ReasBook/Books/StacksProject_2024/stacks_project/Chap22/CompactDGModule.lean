import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import StacksProject_2024.Chap22.ModuleCatHasDerivedCategory

open CategoryTheory CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

/-- Compactness of an object of `D(A, d)`, expressed as preservation of coproducts by the
represented additive Hom functor in the derived category. -/
def derivedCompactObject (E : DerivedCategory (ModuleCat.{u, u} A)) : Prop :=
  ∀ I : Type (u + 1),
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op E))

/-- The defining criterion for compactness in the derived category. -/
theorem derivedCompactObject_iff (E : DerivedCategory (ModuleCat.{u, u} A)) :
    derivedCompactObject E ↔
      ∀ I : Type (u + 1),
        PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op E)) :=
  Iff.rfl

end

end CochainComplex

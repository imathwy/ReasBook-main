import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap10.Lemma_10_76_1
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "QisMinus" => boundedAboveHomotopyQuasiIso (ModuleCat R)
local notation "KminusToDminus" =>
  mapBoundedAboveHomotopyCategoryToDerivedAbove
    (ModuleCat.extendScalars (algebraMap R A))

attribute [local instance] mapBoundedAboveHomotopyToDerivedAbove_isLocalization

-- Proof sketch: resolve bounded-above complexes of `R`-modules by bounded-above complexes of
-- projective modules. Using the Chapter 10 additive instance for `ModuleCat.extendScalars`,
-- projective modules are left acyclic for scalar extension to `A`, so the Chapter 13 bounded-
-- above existence criterion yields the bounded-above left derived functor.
/-- Scalar extension `- ⊗_R A` admits the bounded-above left derived functor
`K^-(R) ⟶ D^-(A)`. -/
local instance extendScalars_boundedAbove_hasLeftDerivedFunctor :
    Functor.HasLeftDerivedFunctor KminusToDminus QisMinus := sorry

/- 15.57.0.2: for an `R`-algebra `A`, the bounded-above derived tensor functor
`- \otimes_R^{\mathbf L} A : D^-(R) ⟶ D^-(A)` is the canonical total left derived functor of
bounded-above scalar extension along `R → A`. -/
#check
  (Functor.totalLeftDerived KminusToDminus mapBoundedAboveHomotopyToDerivedAbove QisMinus :
    boundedAboveDerivedCategory (ModuleCat R) ⥤ boundedAboveDerivedCategory (ModuleCat A))

end

end CategoryTheory

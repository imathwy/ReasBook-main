import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Triangulated.Functor

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe uR uDA uDB vDA vDB

namespace CategoryTheory

section

variable (R : Type uR) [CommRing R]
variable (DA : Type uDA) (DB : Type uDB)
variable [Category.{vDA} DA] [Category.{vDB} DB]
variable [HasZeroObject DA] [HasZeroObject DB]
variable [Preadditive DA] [Preadditive DB]
variable [Linear R DA] [Linear R DB]
variable [HasShift DA ℤ] [HasShift DB ℤ]
variable [∀ n : ℤ, (shiftFunctor DA n).Additive]
variable [∀ n : ℤ, (shiftFunctor DB n).Additive]
variable [Pretriangulated DA] [Pretriangulated DB]

/-- The reusable Chapter 22 owner for an `R`-linear equivalence of pretriangulated categories,
packaging the equivalence together with the shift, triangulated, and linear structures on both
quasi-inverse functors. -/
structure RLinearTriangulatedEquivalence where
  toEquivalence : DA ≌ DB
  functor_commShift : toEquivalence.functor.CommShift ℤ
  inverse_commShift : toEquivalence.inverse.CommShift ℤ
  functor_isTriangulated : toEquivalence.functor.IsTriangulated
  inverse_isTriangulated : toEquivalence.inverse.IsTriangulated
  functor_linear : toEquivalence.functor.Linear R
  inverse_linear : toEquivalence.inverse.Linear R

namespace RLinearTriangulatedEquivalence

/-- The forward functor underlying an `RLinearTriangulatedEquivalence`. -/
abbrev functor (e : RLinearTriangulatedEquivalence R DA DB) : DA ⥤ DB :=
  e.toEquivalence.functor

/-- The inverse functor underlying an `RLinearTriangulatedEquivalence`. -/
abbrev inverse (e : RLinearTriangulatedEquivalence R DA DB) : DB ⥤ DA :=
  e.toEquivalence.inverse

instance instFunctorCommShift (e : RLinearTriangulatedEquivalence R DA DB) :
    e.functor.CommShift ℤ :=
  e.functor_commShift

instance instInverseCommShift (e : RLinearTriangulatedEquivalence R DA DB) :
    e.inverse.CommShift ℤ :=
  e.inverse_commShift

instance instFunctorIsTriangulated (e : RLinearTriangulatedEquivalence R DA DB) :
    e.functor.IsTriangulated :=
  e.functor_isTriangulated

instance instInverseIsTriangulated (e : RLinearTriangulatedEquivalence R DA DB) :
    e.inverse.IsTriangulated :=
  e.inverse_isTriangulated

instance instFunctorLinear (e : RLinearTriangulatedEquivalence R DA DB) :
    e.functor.Linear R :=
  e.functor_linear

instance instInverseLinear (e : RLinearTriangulatedEquivalence R DA DB) :
    e.inverse.Linear R :=
  e.inverse_linear

end RLinearTriangulatedEquivalence

end

end CategoryTheory

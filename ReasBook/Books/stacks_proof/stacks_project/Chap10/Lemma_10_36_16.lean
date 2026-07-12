import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w x y

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {B' : Type w} [CommRing B'] [Algebra A B'] [Algebra B' B] [IsScalarTower A B' B]
variable {C : Type x} [CommRing C] [Algebra B' C]
variable {C' : Type y} [CommRing C'] [Algebra B' C'] [Algebra C' C] [IsScalarTower B' C' C]
variable [Algebra A C'] [IsScalarTower A B' C'] [Algebra A C] [IsScalarTower A C' C]

namespace IsIntegralClosure

/-- Lemma 10.36.16: if `B'` is the integral closure of `A` in `B` and `C'` is the integral
closure of `B'` in `C`, then `C'` is the integral closure of `A` in `C`. This is the
source-faithful closure-of-closure transitivity statement, proved by combining the canonical owner
API for integral closures with transitivity of integral algebras. -/
@[stacks 0308]
theorem trans [IsIntegralClosure B' A B] [IsIntegralClosure C' B' C] :
    IsIntegralClosure C' A C := by
  letI : IsIntegrallyClosedIn C' C := IsIntegrallyClosedIn.of_isIntegralClosure B'
  letI : Algebra.IsIntegral A B' := IsIntegralClosure.isIntegral_algebra A B
  letI : Algebra.IsIntegral B' C' := IsIntegralClosure.isIntegral_algebra B' C
  letI : Algebra.IsIntegral A C' := Algebra.IsIntegral.trans B'
  exact IsIntegralClosure.of_isIntegrallyClosedIn

end IsIntegralClosure

end

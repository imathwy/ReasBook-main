import Mathlib
import stacks_project.Chap19.Lemma_19_13_6

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

/- Fixed-base bridge extracted from Lemma 15.88.1: direct downstream module files should reuse
the canonical owner `additiveFunctorTotalRightDerived (lim : SeqMod ⥤ ModuleCat A)` and the
textbook `R lim(_)` notation, rather than restating the raw derived-functor term locally. -/

instance :
    (lim : SeqMod ⥤ ModuleCat A).Additive := by
  sorry

instance :
    IsGrothendieckAbelian SeqMod := by
  sorry

namespace CategoryTheory

/-- The fixed-base derived inverse-limit functor on sequential inverse systems of `A`-modules
commutes with the triangulated shift. -/
noncomputable instance derivedInverseLimitFunctor_commShift :
    (additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
      (lim : SeqMod ⥤ ModuleCat A) : DSeq ⥤ DMod).CommShift ℤ := by
  sorry

/- Textbook notation for the fixed-base derived inverse-limit object `R lim(K)` in `D(A)`. -/
scoped notation:max "R" " lim(" K ")" =>
  Functor.obj
    (CategoryTheory.additiveFunctorTotalRightDerived
      (CategoryTheory.Limits.lim :
        SequentialInverseSystem (ModuleCat _) ⥤ ModuleCat _))
    K

/- Textbook notation for the cohomology object `R^p lim(K) = H^p(R lim(K))` in `Mod_A`. -/
scoped notation:max "R^" p:max " lim(" K ")" =>
  Functor.obj
    (DerivedCategory.homologyFunctor (ModuleCat _) p)
    (Functor.obj
      (CategoryTheory.additiveFunctorTotalRightDerived
        (CategoryTheory.Limits.lim :
          SequentialInverseSystem (ModuleCat _) ⥤ ModuleCat _))
      K)

end CategoryTheory

end

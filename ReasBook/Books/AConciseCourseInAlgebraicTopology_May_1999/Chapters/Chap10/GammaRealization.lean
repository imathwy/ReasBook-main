import Mathlib.AlgebraicTopology.SingularSet

open CategoryTheory

universe u

noncomputable section

/-!
This support module is the single owner of the geometric realization of the total singular
complex. Both Theorem 10.5.1 and Construction 16.2.1 use this same construction.
-/

/-- The endofunctor `X ↦ Γ X` obtained by realizing the singular simplicial set of a space. -/
abbrev gammaRealizationFunctor : TopCat.{u} ⥤ TopCat.{u} :=
  TopCat.toSSet ⋙ SSet.toTop

/-- The geometric realization `Γ X` of the total singular complex of `X`. -/
abbrev gammaRealization (X : TopCat.{u}) : TopCat.{u} :=
  gammaRealizationFunctor.obj X

/-- The map `Γ f` induced by a continuous map `f`. -/
abbrev gammaRealizationMap {X Y : TopCat.{u}} (f : X ⟶ Y) :
    gammaRealization X ⟶ gammaRealization Y :=
  gammaRealizationFunctor.map f

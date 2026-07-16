import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Stable Chapter 20 owner path for open-subspace module constructions.

This file keeps the owner theorem
`moduleRestrictionToOpen_isKInjective` on the historical module path used by earlier Chapter 20
files, while reusing the canonical open-subspace restriction functor from
`Open_subspace_module_core`.
-/

/-- Restriction of a K-injective complex of `\mathcal O_X`-modules to an open subspace remains
K-injective. -/
theorem moduleRestrictionToOpen_isKInjective
    {X : RingedSpace.{u}} (U : Opens X.carrier)
    (I : CochainComplex (Modules X) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((moduleRestrictionToOpen X U).mapHomologicalComplex (up ℤ)).obj I) := by
  sorry

end AlgebraicGeometry.RingedSpace

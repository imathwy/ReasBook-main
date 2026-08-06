import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Problem_13_6_1

open AlgebraicTopology

noncomputable section

/-- The `i`th Betti number of `M` with coefficients in the field `K`. -/
abbrev manifoldBettiNumber (K : Type) [Field K] (i : ℕ) (M : Type) [TopologicalSpace M] : ℕ :=
  Module.finrank K (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
    (TopCat.of M))

/-- The Euler characteristic of `M`, viewed through the Chapter 13 singular-homology owner
`fieldTopologicalSingularHomologyEulerChar K (TopCat.of M)`. -/
abbrev manifoldEulerCharacteristic (K : Type) [Field K] (M : Type) [TopologicalSpace M] : ℤ :=
  fieldTopologicalSingularHomologyEulerChar K (TopCat.of M)

/-- Unfolding `manifoldEulerCharacteristic` recovers the Chapter 13 owner
`fieldTopologicalSingularHomologyEulerChar`. -/
@[simp] theorem manifoldEulerCharacteristic_eq_fieldTopologicalSingularHomologyEulerChar
    (K : Type) [Field K] (M : Type) [TopologicalSpace M] :
    manifoldEulerCharacteristic K M =
      fieldTopologicalSingularHomologyEulerChar K (TopCat.of M) :=
  rfl

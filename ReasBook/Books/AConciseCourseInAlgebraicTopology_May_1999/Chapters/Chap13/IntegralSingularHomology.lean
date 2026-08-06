import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.AlgebraicTopology.SingularHomology.Basic

open AlgebraicTopology

noncomputable section

/-- Ordinary singular homology with integer coefficients. -/
abbrev integralSingularHomology (q : ℕ) (X : TopCat) : ModuleCat ℤ :=
  ((singularHomologyFunctor (ModuleCat ℤ) q).obj (ModuleCat.of ℤ ℤ)).obj X

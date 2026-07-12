import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/- Semantic recall: Chapter 30 uses the standard `Proj` presentation of `\mathbf P^n_R` together
with additive sheaf cohomology `CategoryTheory.Sheaf.H'`. This file owns the shared setup API for
that model so later source-facing cohomology statements can reuse one canonical owner instead of
restating the same `Proj`/ringed-space/sheaf definitions. -/

/-- The standard grading on `R[T_0, \ldots, T_n]` used for the `Proj` model of
`\mathbf P^n_R`. -/
abbrev projectiveSpaceCohomologyGrading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard `Proj` model of projective `n`-space over `R`. -/
abbrev projectiveSpaceCohomologyScheme (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (projectiveSpaceCohomologyGrading R n)

/-- The ringed space underlying the standard `Proj` model of `\mathbf P^n_R`. -/
abbrev projectiveSpaceCohomologyRingedSpace (R : Type u) [CommRing R] (n : ℕ) :
    RingedSpace :=
  (projectiveSpaceCohomologyScheme R n).toRingedSpace

/-- The forgetful functor from modules on the standard `Proj` model of `\mathbf P^n_R` to
additive sheaves. -/
abbrev projectiveSpaceCohomologyUnderlyingSheaf (R : Type u) [CommRing R] (n : ℕ) :
    RingedSpace.Modules (projectiveSpaceCohomologyRingedSpace R n) ⥤
      (projectiveSpaceCohomologyRingedSpace R n).carrier.Sheaf AddCommGrpCat :=
  SheafOfModules.toSheaf (RingedSpace.ringCatSheaf (projectiveSpaceCohomologyRingedSpace R n))

/-- The graded polynomial piece `(R[T_0, \ldots, T_n])_m`. -/
abbrev projectiveSpaceCohomologyPolynomialPiece (R : Type u) [CommRing R] (n m : ℕ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  projectiveSpaceCohomologyGrading R n m

end AlgebraicGeometry

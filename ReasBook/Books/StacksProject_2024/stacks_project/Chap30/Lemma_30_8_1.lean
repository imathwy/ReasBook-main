import StacksProject_2024.stacks_project.Chap30.ProjectiveSpaceCohomology

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/- Semantic recall:
`lean_leansearch` surfaced the absolute `AlgebraicGeometry.Proj` /
`ProjectiveSpectrum.Proj.structureSheaf` API and the sheaf-cohomology owner
`CategoryTheory.Sheaf.H'`. The shared `Proj`/graded-piece setup now lives in
`ProjectiveSpaceCohomology`; the current file adds the 30.8.1 source-facing negative-degree model
and the three cohomology clauses for a chosen owner of `\mathcal O_{\mathbf P^n_R}(d)`. -/

/-- The concrete inverse-variable model for
`(1/(T_0\cdots T_n) R[1/T_0,\ldots,1/T_n])_d`: it is the ordinary homogeneous piece of degree
`-n - 1 - d` in variables representing `T_i^{-1}`, and is zero when that degree is negative. -/
def projectiveSpaceCohomologyNegativeLaurentPiece
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  if 0 ≤ -((n : ℤ) + 1) - d then
    projectiveSpaceCohomologyPolynomialPiece R n (-((n : ℤ) + 1) - d).toNat
  else
    ⊥

/-- If the inverse-variable degree is nonnegative, the negative Laurent piece is the corresponding
homogeneous polynomial piece. -/
theorem projectiveSpaceCohomologyNegativeLaurentPiece_of_nonneg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (h : 0 ≤ -((n : ℤ) + 1) - d) :
    projectiveSpaceCohomologyNegativeLaurentPiece R n d =
      projectiveSpaceCohomologyPolynomialPiece R n (-((n : ℤ) + 1) - d).toNat := sorry

/-- If the inverse-variable degree is negative, the negative Laurent piece is zero. -/
theorem projectiveSpaceCohomologyNegativeLaurentPiece_of_neg
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (h : ¬ 0 ≤ -((n : ℤ) + 1) - d) :
    projectiveSpaceCohomologyNegativeLaurentPiece R n d = ⊥ := sorry

section

variable (R : Type u) [CommRing R] (n : ℕ)
variable (Od : RingedSpace.Modules (projectiveSpaceCohomologyRingedSpace R n))

/-- Lemma 30.8.1 (1): for a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_R}(d)`, if `d ≥ 0`, then degree-`0` cohomology is the degree-`d`
piece `(R[T_0,\ldots,T_n])_d`, as an underlying additive group of the intended `R`-module
identification. -/
@[stacks 01XT]
theorem projectiveSpaceTwistCohomology_zero_of_nonneg
    (d : ℤ) (hd : 0 ≤ d) :
    IsIsomorphic
      (((projectiveSpaceCohomologyUnderlyingSheaf R n).obj Od).H' 0
        (⊤ : Opens (projectiveSpaceCohomologyRingedSpace R n).carrier))
      (AddCommGrpCat.of
        (projectiveSpaceCohomologyPolynomialPiece R n d.toNat)) := sorry

/-- Lemma 30.8.1 (2): for a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_R}(d)`, if `d < 0`, then degree-`n` cohomology is the degree-`d`
piece of `1/(T_0\cdots T_n) R[1/T_0,\ldots,1/T_n]`, modeled by inverse-variable exponents,
as an underlying additive group of the intended `R`-module identification. -/
@[stacks 01XT]
theorem projectiveSpaceTwistCohomology_top_of_neg
    (d : ℤ) (hd : d < 0) :
    IsIsomorphic
      (((projectiveSpaceCohomologyUnderlyingSheaf R n).obj Od).H' n
        (⊤ : Opens (projectiveSpaceCohomologyRingedSpace R n).carrier))
      (AddCommGrpCat.of
        (projectiveSpaceCohomologyNegativeLaurentPiece R n d)) := sorry

/-- Lemma 30.8.1 (3): for a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_R}(d)`, all cohomology groups outside the two preceding cases vanish. -/
@[stacks 01XT]
theorem projectiveSpaceTwistCohomology_isZero_of_not_cases
    (q : ℕ) (d : ℤ)
    (h_zero : q = 0 → ¬ 0 ≤ d)
    (h_top : q = n → ¬ d < 0) :
    IsZero
      (((projectiveSpaceCohomologyUnderlyingSheaf R n).obj Od).H' q
        (⊤ : Opens (projectiveSpaceCohomologyRingedSpace R n).carrier)) := sorry

end

end AlgebraicGeometry

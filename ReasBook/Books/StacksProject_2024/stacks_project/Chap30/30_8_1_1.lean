import StacksProject_2024.Chap30.ProjectiveSpaceTwistCompatibility

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-
Semantic recall / source-core-bridge check:
- source-facing mathematics: Equation (30.8.1.1) describes the cohomology of
  `\mathcal O_{\mathbf P^n_R}(d)`;
- core/canonical owner in the current repository: the standard `Proj` model
  `projectiveSpaceTwistCompatibilityScheme R n` together with
  `projectiveSpaceTwistCompatibilityCohomologyGroup`,
  `projectiveSpaceTwistCompatibilityDegreePiece`, and
  `projectiveSpaceTwistCompatibilityTopDual`;
- bridge layer used here: a chosen module-sheaf owner `Od` of the twist on that standard model.

The previous `RelativeProjPresentation` quantification overclaimed the statement for arbitrary
twist families. This file therefore records Equation (30.8.1.1) only on the Chapter 30 standard
projective-space model, with the identification of `Od` as the actual twist supplied externally by
the surrounding compatibility data.
-/

section ProjectiveSpaceTwistCohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-- 30.8.1.1 (1): on the standard `Proj` model of `\mathbf P^n_R`, once `Od` is chosen as the
module-sheaf owner of `\mathcal O_{\mathbf P^n_R}(d)`, the degree-`0` cohomology group is
identified with the degree-`d` graded piece of `R[T_0, \ldots, T_n]`, with negative degrees
interpreted as zero. -/
theorem projectiveSpaceTwistZeroCohomology
    (d : ℤ) (Od : (projectiveSpaceTwistCompatibilityScheme R n).Modules) :
    IsIsomorphic
      (projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0)
      (AddCommGrpCat.of (projectiveSpaceTwistCompatibilityDegreePiece R n d)) := sorry

/-- 30.8.1.1 (2): on the standard `Proj` model of `\mathbf P^n_R`, once `Od` is chosen as the
module-sheaf owner of `\mathcal O_{\mathbf P^n_R}(d)`, the intermediate cohomology groups vanish
in every degree `q ≠ 0, n`. -/
theorem projectiveSpaceTwistMiddleCohomologyVanishes
    (Od : (projectiveSpaceTwistCompatibilityScheme R n).Modules)
    (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (projectiveSpaceTwistCompatibilityCohomologyGroup R n Od q) := sorry

/-- 30.8.1.1 (3): on the standard `Proj` model of `\mathbf P^n_R`, once `Od` is chosen as the
module-sheaf owner of `\mathcal O_{\mathbf P^n_R}(d)`, the degree-`n` cohomology group is
identified with the `R`-linear dual of the graded piece in degree `-n - 1 - d`. -/
theorem projectiveSpaceTwistTopCohomology
    (d : ℤ) (Od : (projectiveSpaceTwistCompatibilityScheme R n).Modules) :
    IsIsomorphic
      (projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n)
      (AddCommGrpCat.of (projectiveSpaceTwistCompatibilityTopDual R n d)) := sorry

end ProjectiveSpaceTwistCohomology

end AlgebraicGeometry

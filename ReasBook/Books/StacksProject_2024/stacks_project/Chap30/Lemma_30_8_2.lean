import StacksProject_2024.stacks_project.Chap30.ProjectiveSpaceTwistCompatibility

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open Opposite
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
variable (n : ℕ) (d : ℤ)
variable (Od : (projectiveSpaceTwistCompatibilityScheme R n).Modules)
variable (Od' : (projectiveSpaceTwistCompatibilityScheme R' n).Modules)

/-- Lemma 30.8.2 (1): the degree-`0` identification in Equation (30.8.1.1) is compatible with
base change along a ring map `R -> R'`; under the chosen identifications, the induced cohomology
map is the coefficientwise polynomial base-change map. -/
@[stacks 01XV]
theorem projectiveSpaceTwistZeroCohomology_baseChange
    (zeroIdent :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0 ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityDegreePiece R n d))
    (zeroIdent' :
      projectiveSpaceTwistCompatibilityCohomologyGroup R' n Od' 0 ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityDegreePiece R' n d))
    (zeroBaseChange :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0 ⟶
        projectiveSpaceTwistCompatibilityCohomologyGroup R' n Od' 0) :
    ∀ x : projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0,
      ((zeroIdent'.hom (zeroBaseChange x) :
          projectiveSpaceTwistCompatibilityDegreePiece R' n d) :
            MvPolynomial (Fin (n + 1)) R') =
        MvPolynomial.map (algebraMap R R')
          ((zeroIdent.hom x : projectiveSpaceTwistCompatibilityDegreePiece R n d) :
            MvPolynomial (Fin (n + 1)) R) := sorry

/-- Lemma 30.8.2 (2): the top-cohomology identification in Equation (30.8.1.1) is compatible with
base change along a ring map `R -> R'`; under the chosen identifications, the induced cohomology
map is the base-change map on the corresponding dual graded pieces. -/
@[stacks 01XV]
theorem projectiveSpaceTwistTopCohomology_baseChange
    (topIdent :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityTopDual R n d))
    (topIdent' :
      projectiveSpaceTwistCompatibilityCohomologyGroup R' n Od' n ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityTopDual R' n d))
    (topBaseChange :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n ⟶
        projectiveSpaceTwistCompatibilityCohomologyGroup R' n Od' n)
    (topDualBaseChange :
      projectiveSpaceTwistCompatibilityTopDual R n d →+
        projectiveSpaceTwistCompatibilityTopDual R' n d) :
    ∀ x : projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n,
      (topIdent'.hom (topBaseChange x) :
          projectiveSpaceTwistCompatibilityTopDual R' n d) =
        topDualBaseChange
          (topIdent.hom x : projectiveSpaceTwistCompatibilityTopDual R n d) := sorry

end

section

variable {R : Type u} [CommRing R]
variable (n : ℕ) (d : ℤ) (m : ℕ)
variable (f : MvPolynomial (Fin (n + 1)) R)
variable (Od Odm : (projectiveSpaceTwistCompatibilityScheme R n).Modules)
variable (mulSheaf : Od ⟶ Odm)

/-- Lemma 30.8.2 (3): for a homogeneous polynomial `f` of degree `m`, multiplication by `f` on
`\mathcal O_{\mathbf P^n_R}(d)` induces, on `H^0` and under the identifications of
Equation (30.8.1.1), ordinary multiplication by `f` on homogeneous polynomial pieces. -/
@[stacks 01XV]
theorem projectiveSpaceTwistZeroCohomology_mul_homogeneous
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R m)
    (zeroIdent :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0 ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityDegreePiece R n d))
    (zeroIdentShift :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Odm 0 ≅
        AddCommGrpCat.of
          (projectiveSpaceTwistCompatibilityDegreePiece R n (d + (m : ℤ)))) :
    ∀ x : projectiveSpaceTwistCompatibilityCohomologyGroup R n Od 0,
      ((zeroIdentShift.hom
          ((projectiveSpaceTwistCompatibilityCohomologyMap R n mulSheaf 0) x) :
            projectiveSpaceTwistCompatibilityDegreePiece R n (d + (m : ℤ))) :
              MvPolynomial (Fin (n + 1)) R) =
        f *
          ((zeroIdent.hom x : projectiveSpaceTwistCompatibilityDegreePiece R n d) :
            MvPolynomial (Fin (n + 1)) R) := sorry

/-- Lemma 30.8.2 (4): for a homogeneous polynomial `f` of degree `m`, multiplication by `f` on
`\mathcal O_{\mathbf P^n_R}(d)` induces, on `H^n` and under the identifications of
Equation (30.8.1.1), the contragredient of multiplication by `f` from degree
`-n - 1 - (d + m)` to degree `-n - 1 - d`. -/
@[stacks 01XV]
theorem projectiveSpaceTwistTopCohomology_mul_homogeneous
    (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R m)
    (topIdent :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n ≅
        AddCommGrpCat.of (projectiveSpaceTwistCompatibilityTopDual R n d))
    (topIdentShift :
      projectiveSpaceTwistCompatibilityCohomologyGroup R n Odm n ≅
        AddCommGrpCat.of
          (projectiveSpaceTwistCompatibilityTopDual R n (d + (m : ℤ)))) :
    ∀ (x : projectiveSpaceTwistCompatibilityCohomologyGroup R n Od n)
      (y : MvPolynomial (Fin (n + 1)) R)
      (hy :
        y ∈ projectiveSpaceTwistCompatibilityDegreePiece R n
          (-((n : ℤ) + 1) - (d + (m : ℤ))))
      (hy_mul :
        f * y ∈ projectiveSpaceTwistCompatibilityDegreePiece R n
          (-((n : ℤ) + 1) - d)),
      ((topIdentShift.hom
          ((projectiveSpaceTwistCompatibilityCohomologyMap R n mulSheaf n) x) :
            projectiveSpaceTwistCompatibilityTopDual R n (d + (m : ℤ)))
          ⟨y, hy⟩) =
        ((topIdent.hom x : projectiveSpaceTwistCompatibilityTopDual R n d)
          ⟨f * y, hy_mul⟩) := sorry

end

end AlgebraicGeometry

import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped BigOperators
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical `Proj` and sheaf-of-modules
pushforward APIs but no global owner for the relative twisting sheaf
`\mathcal O_{\mathbf P^n_S}(d)`. Local Chapter 29 represents `\mathbf P^n_S` by
`ProjectiveSpaceOver S n`, and local Chapter 30 states higher direct images on
`((Scheme.Modules.pushforward f).rightDerived q).obj ℱ`. The target sheaves below are concrete
finite-free models for the graded pieces of `\mathcal O_S[T_0,\ldots,T_n]`. -/

/-- The monomial exponent vectors of total degree `d` in `n + 1` variables, empty when `d < 0`.
The `ULift` places the index in the same universe as the scheme so that `SheafOfModules.free`
produces an object of `S.Modules`. -/
abbrev projectiveSpaceRelativeDegreeIndex (n : ℕ) (d : ℤ) : Type u :=
  ULift.{u, 0} { e : Fin (n + 1) → ℕ // 0 ≤ d ∧ ∑ i, e i = d.toNat }

/-- The defining normal form for the monomial exponent index. -/
theorem projectiveSpaceRelativeDegreeIndex_def (n : ℕ) (d : ℤ) :
    projectiveSpaceRelativeDegreeIndex.{u} n d =
      ULift.{u, 0} { e : Fin (n + 1) → ℕ // 0 ≤ d ∧ ∑ i, e i = d.toNat } := sorry

/-- The finite-free `\mathcal O_S`-module sheaf modeling the degree-`d` piece
`(\mathcal O_S[T_0,\ldots,T_n])_d`. -/
abbrev projectiveSpaceRelativeDegreePieceSheaf
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) : S.Modules :=
  @SheafOfModules.free.{u, u, u} _ _ _ S.ringCatSheaf _ _ _
    (projectiveSpaceRelativeDegreeIndex.{u} n d)

/-- The defining normal form for the relative degree-piece sheaf. -/
theorem projectiveSpaceRelativeDegreePieceSheaf_def
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) :
    projectiveSpaceRelativeDegreePieceSheaf S n d =
      @SheafOfModules.free.{u, u, u} _ _ _ S.ringCatSheaf _ _ _
        (projectiveSpaceRelativeDegreeIndex.{u} n d) := sorry

/-- The finite-free model for
`\mathcal Hom_{\mathcal O_S}((\mathcal O_S[T_0,\ldots,T_n])_{-n-1-d}, \mathcal O_S)`.
Since each graded piece is finite free on the monomial basis, its dual is modeled by the free
sheaf on the same exponent index. -/
abbrev projectiveSpaceRelativeTopDualSheaf
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) : S.Modules :=
  projectiveSpaceRelativeDegreePieceSheaf S n (-((n : ℤ) + 1) - d)

/-- The defining normal form for the finite-free top dual sheaf. -/
theorem projectiveSpaceRelativeTopDualSheaf_def
    (S : Scheme.{u}) (n : ℕ) (d : ℤ) :
    projectiveSpaceRelativeTopDualSheaf S n d =
      projectiveSpaceRelativeDegreePieceSheaf S n (-((n : ℤ) + 1) - d) := sorry

section

variable (S : Scheme.{u}) (n : ℕ) (d : ℤ)
variable (P : ProjectiveSpaceOver S n)
variable [HasInjectiveResolutions P.scheme.Modules]
variable (Od : P.scheme.Modules)

/-- Lemma 30.8.3 (1): for the structure morphism
`f : \mathbf P^n_S \to S` and a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_S}(d)`, the degree-`0` higher direct image is the degree-`d` graded
piece of `\mathcal O_S[T_0,\ldots,T_n]`. -/
@[stacks 01XW]
theorem projectiveSpaceTwistHigherDirectImage_zero :
    IsIsomorphic
      (((Scheme.Modules.pushforward P.hom).rightDerived 0).obj Od)
      (projectiveSpaceRelativeDegreePieceSheaf S n d) := sorry

/-- Lemma 30.8.3 (2): for the structure morphism
`f : \mathbf P^n_S \to S` and a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_S}(d)`, the higher direct image vanishes in every degree
`q` with `q \ne 0` and `q \ne n`. -/
@[stacks 01XW]
theorem projectiveSpaceTwistHigherDirectImage_isZero_of_ne_zero_ne_top
    (q : ℕ) (hq0 : q ≠ 0) (hqn : q ≠ n) :
    IsZero (((Scheme.Modules.pushforward P.hom).rightDerived q).obj Od) := sorry

/-- Lemma 30.8.3 (3): for the structure morphism
`f : \mathbf P^n_S \to S` and a chosen owner `Od` of
`\mathcal O_{\mathbf P^n_S}(d)`, the degree-`n` higher direct image is the finite-free dual of
the graded piece in degree `-n - 1 - d`. -/
@[stacks 01XW]
theorem projectiveSpaceTwistHigherDirectImage_top :
    IsIsomorphic
      (((Scheme.Modules.pushforward P.hom).rightDerived n).obj Od)
      (projectiveSpaceRelativeTopDualSheaf S n d) := sorry

end

end AlgebraicGeometry

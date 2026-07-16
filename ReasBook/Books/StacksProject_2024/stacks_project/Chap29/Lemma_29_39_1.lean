import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_38_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall / owner check:
-- `Definition_29_38_1.lean` fixes the source-facing owner for relative very ampleness as
-- `RelativelyVeryAmple`, and `Definition_29_43_1.lean` fixes the Chapter 29 owner for
-- `\mathbf P^n_S` as `ProjectiveSpaceOver S n` together with the standard free-module
-- projective-bundle presentation. The source statement is therefore recorded directly against the
-- projective-space owner rather than an arbitrary scheme equipped with a separate bundle witness,
-- with the bundled `RelativelyVeryAmplePresentation` form retained only as a bridge companion.

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- The tautological quotient sheaf `\mathcal O_{\mathbf P^n_S}(1)` on a relative projective
space. -/
abbrev ProjectiveSpaceOver.tautologicalSheaf {n : ℕ} (P : ProjectiveSpaceOver S n) :
    P.scheme.Modules :=
  projectiveBundleTautologicalSheaf P.hom P.isProjectiveBundle

/-- Lemma 29.39.1: let `f : X ⟶ S` be a finite-type morphism of schemes, let `\mathcal L` be an
invertible `\mathcal O_X`-module, and assume `\mathcal L` is relatively very ample on `X/S` and
`S` is affine. Then there exist `n ≥ 0` and an immersion `i : X ⟶ \mathbf P^n_S` over `S`
together with an isomorphism from `\mathcal L` to the pullback of the tautological quotient sheaf
`\mathcal O_{\mathbf P^n_S}(1)`. This is the source-facing affine-base projective-space
presentation. -/
@[stacks 02NP]
theorem RelativelyVeryAmple.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase
    [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      ∃ e : (L ≅ (Scheme.Modules.pullback i).obj P.tautologicalSheaf),
        IsImmersion i ∧ (i ≫ (P.hom) = f) := sorry

/-- Lemma 29.39.1: let `f : X ⟶ S` be a finite-type morphism of schemes, let `\mathcal L` be an
invertible `\mathcal O_X`-module, and assume `\mathcal L` is relatively very ample on `X/S` and
`S` is affine. Then there exist `n ≥ 0` and an immersion `i : X ⟶ \mathbf P^n_S` over `S` such
that `\mathcal L` is the pullback of the tautological quotient sheaf
`\mathcal O_{\mathbf P^n_S}(1)`. This bundled `RelativelyVeryAmplePresentation` form is the
canonical bridge to the Chapter 29 projective-bundle API. -/
@[stacks 02NP]
theorem RelativelyVeryAmple.exists_projectiveSpacePresentation_of_finiteType_affineBase
    [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      RelativelyVeryAmplePresentation f L P.hom (standardProjectiveBundleModule S n)
        P.isProjectiveBundle i := by
  rcases hL.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase with
    ⟨n, P, i, e, hi, hcomp⟩
  exact ⟨n, P, i, ⟨hi, hcomp, ⟨e⟩⟩⟩

/-- Lemma 29.39.1: under the same hypotheses, the relatively very ample invertible sheaf yields
an immersion of `X` over `S` into some projective space `\mathbf P^n_S`. This is the source-level
geometric consequence of the stronger presentation theorem above, separated from the tautological
sheaf identification for downstream reuse. -/
theorem RelativelyVeryAmple.exists_projectiveSpaceImmersion_of_finiteType_affineBase
    [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f] [IsAffine S]
    (hL : RelativelyVeryAmple f L) :
    ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
      IsImmersion i ∧ (i ≫ (P.hom) = f) := by
  rcases hL.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase with
    ⟨n, P, i, _, hi, hcomp⟩
  exact ⟨n, P, i, hi, hcomp⟩

end

end AlgebraicGeometry

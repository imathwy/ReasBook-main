import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced affine-open and quasi-compact cover API, but no
-- ready-made finite-cover cohomology bound. Local Chapter 30 precedent states vanishing as
-- `IsZero` of the global sheaf-cohomology object of the underlying sheaf.

/-- A finite affine open cover of an open subscheme, used to state a chosen value of `t(U)`. -/
structure FiniteAffineOpenCoverOfOpen (U : X.Opens) (t : ℕ) where
  /-- The finite family of affine open subsets of the open subscheme. -/
  opens : Fin t → (U : Scheme.{u}).Opens
  /-- The family covers the open subscheme. -/
  isOpenCover : IsOpenCover opens
  /-- Every member of the family is affine. -/
  isAffineOpen : ∀ i, IsAffineOpen (opens i)

/-- The intersection of a finite subfamily of a finite open cover. -/
abbrev finiteOpenCoverIntersection {n : ℕ} (U : Fin n → X.Opens)
    (I : Finset (Fin n)) : X.Opens :=
  I.inf U

/-- The Stacks bound `max_I (|I| + t(⋂ i ∈ I, U_i) - 1)` for a finite open cover. -/
abbrev finiteOpenCoverCohomologyBound {n : ℕ} (U : Fin n → X.Opens)
    (t : X.Opens → ℕ) : ℕ :=
  Finset.univ.sup (fun I : Finset (Fin n) ↦
    I.card + t (finiteOpenCoverIntersection U I) - 1)

/-- Lemma 30.4.4: let `X` be a quasi-compact quasi-separated scheme, and let
`X = U_1 ∪ ... ∪ U_n` be an open covering with each `U_i` quasi-compact and separated. If
`t(U)` is the minimal number of affine opens needed to cover each finite intersection appearing in
this cover and `d = max_I (|I| + t(⋂ i ∈ I, U_i) - 1)`, then `H^p(X, \mathcal F) = 0` for all
`p ≥ d` and all quasi-coherent sheaves `\mathcal F`. -/
@[stacks 071L]
theorem globalCohomology_isZero_of_finite_qcqs_openCover
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    {n : ℕ} (U : Fin n → X.Opens) (hcover : IsOpenCover U)
    (hUcompact : ∀ i, CompactSpace ((U i : Scheme.{u}).carrier))
    (hUseparated : ∀ i, (U i : Scheme.{u}).IsSeparated)
    (t : X.Opens → ℕ)
    (hfinite : ∀ I : Finset (Fin n),
      FiniteAffineOpenCoverOfOpen (finiteOpenCoverIntersection U I)
        (t (finiteOpenCoverIntersection U I)))
    (hminimal : ∀ I : Finset (Fin n), ∀ m : ℕ,
      m < t (finiteOpenCoverIntersection U I) →
        IsEmpty (FiniteAffineOpenCoverOfOpen (finiteOpenCoverIntersection U I) m))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ)
    (hp : finiteOpenCoverCohomologyBound U t ≤ p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : Opens X)) := sorry

end AlgebraicGeometry.Scheme

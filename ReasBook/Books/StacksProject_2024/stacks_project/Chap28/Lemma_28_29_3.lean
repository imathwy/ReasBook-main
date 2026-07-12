import Mathlib.AlgebraicGeometry.Morphisms.Separated

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

/- Semantic recall: the scheme-side owners are `IsAffineOpen` and `Scheme.IsSeparated`, while
nearby Chapter 28 precedent `Lemma_28_29_1` already packages the reusable affine-open owner for
opens containing the generic points of finitely many irreducible components. The source-facing
statement therefore stays as an existence theorem for a dense separated open subscheme of `X`,
with a stronger affine-open companion for downstream reuse. -/

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- A quasi-compact scheme admits a dense affine open subscheme. This is the canonical bridge
underlying Lemma 28.29.3: an affine open containing the generic points of all irreducible
components is dense, and its induced scheme is separated. -/
theorem exists_dense_isAffineOpen :
    ∃ U : X.Opens, IsAffineOpen U ∧ Dense (U : Set X) := sorry

/-- Companion packaging of `exists_dense_isAffineOpen` through the affine-open subtype. -/
theorem exists_dense_affineOpen :
    ∃ U : X.affineOpens, Dense ((U : X.Opens) : Set X) := by
  rcases exists_dense_isAffineOpen with ⟨U, hU, h_dense⟩
  refine ⟨⟨U, hU⟩, ?_⟩
  simpa using h_dense

/-- Lemma 28.29.3: a quasi-compact scheme admits a dense open subscheme that is separated. -/
theorem exists_dense_open_isSeparated :
    ∃ U : X.Opens, U.toScheme.IsSeparated ∧ Dense (U : Set X) := by
  rcases exists_dense_isAffineOpen with ⟨U, hU, h_dense⟩
  haveI : IsAffine U.toScheme := hU
  exact ⟨U, Scheme.isSeparated_of_isAffine U.toScheme, h_dense⟩

end

end AlgebraicGeometry.Scheme

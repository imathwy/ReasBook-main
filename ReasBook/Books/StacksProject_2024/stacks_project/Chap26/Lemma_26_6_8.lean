import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` surfaced `LocallyRingedSpace.IsOpenImmersion.scheme`
-- and affine-open owners; the source conclusion is kept as the stronger affine-spectrum
-- identification with `Spec Γ(X)`, matching the proof via global sections.

/-- Lemma 26.6.8: if a locally ringed space is the disjoint union of two open subspaces and both
open subspaces are affine schemes, then the locally ringed space is the affine scheme
`Spec Γ(X, \mathcal O_X)`. -/
@[stacks 01I5]
theorem affineScheme_of_disjoint_open_union_two_affine
    {X : LocallyRingedSpace.{u}} {U V : Opens X}
    (hcover : (U : Set X) ∪ (V : Set X) = Set.univ)
    (hdisjoint : Disjoint (U : Set X) (V : Set X))
    (hU : ∃ R : CommRingCat.{u},
      Nonempty (X.restrict U.isOpenEmbedding ≅ (Spec R).toLocallyRingedSpace))
    (hV : ∃ R : CommRingCat.{u},
      Nonempty (X.restrict V.isOpenEmbedding ≅ (Spec R).toLocallyRingedSpace)) :
    Nonempty (X ≅ (Spec (Γ.obj (op X))).toLocallyRingedSpace) := sorry

end AlgebraicGeometry.LocallyRingedSpace

import Mathlib.AlgebraicGeometry.Pullbacks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/- Semantic note: `pullback.isIso_diagonal_iff` is the canonical categorical owner, and its
specialization to schemes is exactly the Stacks diagonal criterion for monomorphisms. This file
keeps the tagged source-facing scheme statement as a thin bridge. -/


variable {X Y : Scheme.{u}} (j : X ⟶ Y)

/- Lemma 26.23.2: for a morphism of schemes `j : X ⟶ Y`, `j` is a monomorphism if and only if the
diagonal morphism `Δ_{X/Y} : X ⟶ X ×[Y] X` is an isomorphism. This is the canonical theorem
`pullback.isIso_diagonal_iff`, written in the source-facing order. -/
@[stacks 01L5]
theorem mono_iff_isIso_diagonal :
    Mono j ↔ IsIso (pullback.diagonal j) :=
  (pullback.isIso_diagonal_iff j).symm

end AlgebraicGeometry

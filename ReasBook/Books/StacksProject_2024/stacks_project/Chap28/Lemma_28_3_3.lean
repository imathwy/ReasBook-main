import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

-- Source-facing/main item: Lemma 28.3.3 records irreducibility through affine-open neighborhoods.
-- Canonical companion surface: Chapter 28 states affine-local criteria with the bundled owners
-- `X.affineOpens` and `X.AffineOpenCover`, so this file keeps the source's cover and pointwise
-- affine-open formulations directly on those owners instead of introducing a separate cover class.

/-- Lemma 28.3.3 (1): a scheme `X` is irreducible iff it admits a nonempty affine open cover by
pairwise-intersecting irreducible affine opens. -/
theorem irreducibleSpace_iff_exists_affineOpenCover
    :
    IrreducibleSpace X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        (∀ i : 𝒰.I₀, IsIrreducible ((𝒰.f i).opensRange : Set X)) ∧
          ∀ i j : 𝒰.I₀,
            (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.Opens) : Set X).Nonempty := sorry

/-- Lemma 28.3.3 (2): a scheme `X` is irreducible iff it is nonempty and every nonempty affine
open subset of `X` is irreducible. -/
theorem irreducibleSpace_iff_nonempty_and_forall_nonempty_affineOpen
    :
    IrreducibleSpace X ↔
      Nonempty X ∧
        ∀ U : X.affineOpens,
          ((U : Set X).Nonempty → IsIrreducible (U : Set X)) := sorry

end AlgebraicGeometry.Scheme

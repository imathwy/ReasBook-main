import Mathlib
import StacksProject_2024.Chap28.Definition_28_9_1
import StacksProject_2024.Chap29.Definition_29_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` confirmed the existing affine-diagonal owner
-- `IsAffineHom (prod.lift (𝟙 X) (𝟙 X))`; local Chapter 29 precedent provides
-- `AlgebraicGeometry.AmpleFamily` for families of invertible modules, and Chapter 28 provides
-- `Regular` for regular schemes.

/-- Lemma 31.16.8: let `X` be a quasi-compact, regular scheme with affine diagonal. Then `X` has
an ample family of invertible modules in the sense of Morphisms, Definition 29.12.1. -/
@[stacks 0GML]
theorem exists_ampleFamily_of_compact_regular_affineDiagonal
    (X : Scheme.{u}) [CompactSpace X] [Regular X]
    [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    ∃ (ι : Type u) (L : ι → X.Modules)
      (hL : ∀ i : ι, Scheme.Modules.Invertible (L i)),
        AlgebraicGeometry.AmpleFamily L := sorry

end AlgebraicGeometry.Scheme

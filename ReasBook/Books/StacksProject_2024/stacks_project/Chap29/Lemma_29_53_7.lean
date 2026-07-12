import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled the canonical relative-normalization owner
-- `Scheme.Hom.normalization` and its universal-property API via
-- `Scheme.Hom.normalizationDesc`. This item is the transport-stable idempotence statement on the
-- canonical comparison morphism `(f.toNormalization).fromNormalization`.

/-- Lemma 29.53.7: let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of schemes, and
let `X'` be the normalization of `X` in `Y`. Then the normalization of `X'` in `Y` is `X'`;
equivalently, the canonical morphism from the normalization of `f.toNormalization` to
`f.normalization` is an isomorphism. -/
@[stacks 0BXA]
theorem Scheme.Hom.isIso_fromNormalization_toNormalization
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] :
    IsIso ((f.toNormalization).fromNormalization) := sorry

end AlgebraicGeometry

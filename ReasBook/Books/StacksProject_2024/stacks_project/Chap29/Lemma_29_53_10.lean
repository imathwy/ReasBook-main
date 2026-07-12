import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic owner check:
-- `lean_leansearch` identified `Scheme.Hom.normalizationCoprodIso` as the canonical
-- relative-normalization owner for a binary coproduct decomposition of the source.
-- This numbered lemma is therefore a direct owner check of existing mathlib API rather than a
-- wrapper declaration.

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 29.53.10: if `f : Y ⟶ X` is quasi-compact and quasi-separated and `Y` is the binary
coproduct of `Y₁` and `Y₂`, then the coproduct of the normalizations of `X` in `Y₁` and `Y₂`
is the normalization of `X` in `Y`. This is exactly the canonical isomorphism
`Scheme.Hom.normalizationCoprodIso`. -/
recall normalizationCoprodIso

end AlgebraicGeometry.Scheme.Hom

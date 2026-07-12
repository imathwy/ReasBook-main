import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.Scheme.Hom

-- Semantic recall: local Chapter 29 already uses mathlib's relative-normalization owner
-- `Scheme.Hom.normalization` together with its canonical factorization maps
-- `Scheme.Hom.toNormalization` and `Scheme.Hom.fromNormalization`. Definition 29.53.3 is therefore
-- a source-facing recall of that owner and its affine-open section formula, not a new bundled
-- package.

/- Definition 29.53.3: for a quasi-compact and quasi-separated morphism `f : Y ⟶ X`, the
normalization of `X` in `Y` is the canonical relative normalization `f.normalization`, with
factorization `Y ⟶ f.normalization ⟶ X` given by `f.toNormalization` and
`f.fromNormalization`. -/
recall normalization
recall toNormalization
recall fromNormalization

/- The canonical factorization through the relative normalization is exactly the source-facing
factorization of Definition 29.53.3. -/
recall toNormalization_fromNormalization

/- On every affine open `U ⊆ X`, the sections of the relative normalization over `ν ⁻¹ᵁ U`
identify with the integral closure of `Γ(X, U)` in `Γ(Y, f ⁻¹ᵁ U)`. -/
recall normalizationObjIso

end AlgebraicGeometry.Scheme.Hom

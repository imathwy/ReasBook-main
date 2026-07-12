import Mathlib

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recalled `Scheme.Hom.normalization`,
-- `Scheme.Hom.toNormalization`, `Scheme.Hom.fromNormalization`, and
-- `Scheme.Hom.normalizationDesc` as the canonical relative-normalization API. This item is stated
-- as the unique comparison morphism induced by a commutative square of qcqs morphisms.

/-- Lemma 29.53.5: for a commutative square of quasi-compact and quasi-separated morphisms of
schemes, there exists a unique morphism between the corresponding relative normalizations making
the induced square of canonical factorizations commute. -/
@[stacks 035J]
theorem Scheme.Hom.existsUnique_map_between_normalizations
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (f₁ : Y₁ ⟶ X₁) [QuasiCompact f₁] [QuasiSeparated f₁]
    (f₂ : Y₂ ⟶ X₂) [QuasiCompact f₂] [QuasiSeparated f₂]
    (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁)
    (comm : gY ≫ f₁ = f₂ ≫ gX) :
    ∃! h : f₂.normalization ⟶ f₁.normalization,
      f₂.toNormalization ≫ h = gY ≫ f₁.toNormalization ∧
        h ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX := sorry

end AlgebraicGeometry

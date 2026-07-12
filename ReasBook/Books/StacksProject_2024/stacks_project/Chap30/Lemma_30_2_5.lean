import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-property diagonal machinery
-- (`HasAffineProperty.diagonal_of_openCover_diagonal`), the affine-open cover owners
-- (`Scheme.affineOpenCover`, `Scheme.affineOpens`), and the absolute separated owner
-- (`Scheme.isSeparated_iff_isClosedImmersion_prod_lift`). The source-facing statements therefore
-- use the absolute diagonal `X ⟶ X ⨯ X`, affine-open intersections inside `X`, and an indexed
-- affine-intersection cover criterion expressed by iterated infima of opens.

/-- Lemma 30.2.5 (1): a scheme `X` has affine diagonal `Δ : X ⟶ X × X` if and only if for any
affine opens `U, V ⊆ X`, their intersection `U ∩ V` is an affine open of `X`. -/
theorem affineDiagonal_iff_affineOpenIntersections
    (X : Scheme.{u}) :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) ↔
      ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1) := sorry

/-- Lemma 30.2.5 (2): if intersections of affine opens in `X` are affine, then `X` admits an
open covering `X = ⋃ᵢ Uᵢ` such that every finite intersection `U_{i₀ … iₚ}` is affine open. -/
theorem exists_affineIntersectionOpenCover_of_affineOpenIntersections
    (X : Scheme.{u})
    (hX : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1)) :
    ∃ (I : Type v) (U : I → X.Opens), iSup U = ⊤ ∧
      ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a)) := sorry

/-- Lemma 30.2.5 (3): if `X` has an open covering whose every finite intersection is affine open,
then the diagonal morphism `Δ : X ⟶ X × X` is affine. -/
theorem affineDiagonal_of_exists_affineIntersectionOpenCover
    (X : Scheme.{u})
    (hX :
      ∃ (I : Type v) (U : I → X.Opens), iSup U = ⊤ ∧
        ∀ p : ℕ, ∀ σ : Fin (p + 1) → I, IsAffineOpen (⨅ a, U (σ a))) :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) := sorry

/-- Lemma 30.2.5 (4): in particular, a separated scheme has affine diagonal. -/
theorem affineDiagonal_of_isSeparated
    (X : Scheme.{u}) [X.IsSeparated] :
    IsAffineHom (prod.lift (𝟙 X) (𝟙 X)) := sorry

end AlgebraicGeometry.Scheme

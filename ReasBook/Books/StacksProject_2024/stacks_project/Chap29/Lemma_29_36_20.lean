import StacksProject_2024.Chap29.Lemma_29_34_11

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical smooth owner `Scheme.Hom.smoothLocus`;
- mathlib's affine-space file provides the relative affine space `AffineSpace (Fin d) V.toScheme`;
- the ring-level bridge `RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
  matches the textbook passage from a standard smooth affine chart to an étale map into relative
  affine space, and `Scheme.Hom.resLE` packages the corresponding restricted scheme morphism;
- local Chapter 29 already exposes the source-facing bridge `Scheme.Hom.smoothAt_iff_mem_smoothLocus`,
  so the `SmoothAt` statement is the main source-facing owner here and the smooth-locus version is
  its canonical mathlib-flavored companion.
-/

/-- Lemma 29.36.20: if `f : X ⟶ Y` is smooth at `x` and `V` is an affine open neighborhood of
`f x`, then there exists an affine open neighborhood `U` of `x` inside `f ⁻¹ᵁ V`, a relative
dimension `d`, and an étale morphism from `U.toScheme` to the relative affine space over
`V.toScheme` whose structure map is the restriction of `f`. -/
@[stacks 054L]
theorem exists_affineOpen_etale_to_affineSpace_of_smoothAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (V : Y.affineOpens) (hxV : f x ∈ (V : Y.Opens)) (hx : f.SmoothAt x) :
    ∃ d : ℕ, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
        ∃ π : ((U : X.Opens).toScheme) ⟶ AffineSpace (Fin d) ((V : Y.Opens).toScheme),
          Etale π ∧
            π ≫ (AffineSpace (Fin d) ((V : Y.Opens).toScheme) ↘ ((V : Y.Opens).toScheme)) =
              f.resLE (V : Y.Opens) (U : X.Opens) e := sorry

/-- Lemma 29.36.20, restated using the smooth locus owner from mathlib. -/
@[stacks 054L]
theorem exists_affineOpen_etale_to_affineSpace_of_mem_smoothLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (V : Y.affineOpens) (hxV : f x ∈ (V : Y.Opens)) (hx : x ∈ f.smoothLocus) :
    ∃ d : ℕ, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens),
        ∃ π : ((U : X.Opens).toScheme) ⟶ AffineSpace (Fin d) ((V : Y.Opens).toScheme),
          Etale π ∧
            π ≫ (AffineSpace (Fin d) ((V : Y.Opens).toScheme) ↘ ((V : Y.Opens).toScheme)) =
              f.resLE (V : Y.Opens) (U : X.Opens) e := by
  rw [← f.smoothAt_iff_mem_smoothLocus x] at hx
  exact exists_affineOpen_etale_to_affineSpace_of_smoothAt f x V hxV hx

end AlgebraicGeometry

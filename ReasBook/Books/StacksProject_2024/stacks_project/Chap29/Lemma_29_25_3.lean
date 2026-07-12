import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v w

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

-- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.flat_iff`,
-- `AlgebraicGeometry.Scheme.Hom.flat_appLE`, and `AlgebraicGeometry.Flat.instResLE`; local
-- precedent in `Chap29/Lemma_29_25_2.lean` packages the same criteria for relative module
-- flatness, and this file records the scheme-morphism specialization.

/-- Data of an open cover criterion for the flatness of a morphism of schemes. -/
structure FlatOpenCover
    (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  flat_resLE : ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j, Flat (f.resLE (V j) (U j i) e)

/-- Data of an affine-open cover criterion for the flatness of a morphism of schemes. -/
structure FlatAffineOpenCover
    (f : X ⟶ S) where
  J : Type v
  V : J → S.Opens
  iSup_eq_top : (⨆ j, V j) = ⊤
  affine_V : ∀ j, IsAffineOpen (V j)
  I : J → Type w
  U : ∀ j, I j → X.Opens
  iSup_eq_preimage : ∀ j, (⨆ i, U j i) = f ⁻¹ᵁ V j
  affine_U : ∀ j i, IsAffineOpen (U j i)
  appLE_flat :
    ∀ j i, ∃ e : U j i ≤ f ⁻¹ᵁ V j,
      (CommRingCat.Hom.hom (f.appLE (V j) (U j i) e)).Flat

/-- Lemma 29.25.3 (1): a morphism of schemes is flat if and only if for every affine open
`U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced ring map
`\Gamma(V, \mathcal O_S) → \Gamma(U, \mathcal O_X)` is flat. -/
@[stacks 01U5]
theorem flat_iff_affineOpen_appLE_flat
    (f : X ⟶ S) :
    Flat f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).Flat := sorry

/-- Lemma 29.25.3 (2): a morphism of schemes is flat if and only if there is an open cover of
the base and open covers of the corresponding preimages such that each restricted morphism is
flat. -/
@[stacks 01U5]
theorem flat_iff_hasFlatOpenCover
    (f : X ⟶ S) :
    Flat f ↔ Nonempty (FlatOpenCover f) := sorry

/-- Lemma 29.25.3 (3): a morphism of schemes is flat if and only if there are affine open covers
`V_j` of `S` and `U_i` of each `f^{-1}(V_j)` such that the induced ring maps on sections are
flat. -/
@[stacks 01U5]
theorem flat_iff_hasFlatAffineOpenCover
    (f : X ⟶ S) :
    Flat f ↔ Nonempty (FlatAffineOpenCover f) := sorry

/-- Lemma 29.25.3 (4): if `f : X ⟶ S` is flat, then for any open subschemes `U ⊆ X` and
`V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is flat. -/
@[stacks 01U5]
theorem flat_resLE_of_flat
    {f : X ⟶ S} (hflat : Flat f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    Flat (f.resLE V U e) := sorry

end Scheme.Hom

end

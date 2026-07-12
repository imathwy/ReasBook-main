import StacksProject_2024.Chap10.Definition_10_151_1
import StacksProject_2024.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall / source-core-bridge check:
- the source-facing owners here remain the chapter-local `Unramified` and `GUnramified`;
- the canonical ring-level ingredients are `Algebra.Unramified` and `Algebra.GUnramified`;
- the source-facing statements below therefore keep the specialized scheme-level owners while
  exposing the canonical ring-level predicates on affine restrictions.
-/

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.35.3 (1): a morphism of schemes is unramified if and only if for every affine open
`U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced ring map on sections
`\Gamma(S, V) → \Gamma(X, U)` is unramified. -/
@[stacks 02G6]
theorem unramified_iff_affineOpen_appLE_unramified :
    Unramified f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
          Algebra.Unramified Γ(S, V) Γ(X, U) := sorry

/-- Lemma 29.35.3 (2): a morphism of schemes is unramified if and only if there exists an open
cover of the target and open covers of the corresponding preimages such that each restricted
morphism is unramified. -/
@[stacks 02G6]
theorem unramified_iff_exists_openCover_preimageOpenCover :
    Unramified f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Unramified ((𝒰.f i) ≫ (𝒱.pullbackHom f j)) := sorry

/-- Lemma 29.35.3 (3): a morphism of schemes is unramified if and only if there exists an affine
open covering of the target and affine open coverings of the corresponding preimages such that the
induced ring maps on sections are unramified. -/
@[stacks 02G6]
theorem unramified_iff_exists_affineOpenCover_preimageAffineOpenCover :
    Unramified f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            let _ : Algebra Γ(S, 𝒱.obj j) Γ(X, 𝒰.obj i) :=
              (((𝒰.f i) ≫ (𝒱.openCover.pullbackHom f j)).appTop).hom.toAlgebra
            Algebra.Unramified Γ(S, 𝒱.obj j) Γ(X, 𝒰.obj i) := sorry

/-- Lemma 29.35.3 (4): if `f : X ⟶ S` is unramified, then for any open subschemes `U ⊆ X` and
`V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is unramified. -/
@[stacks 02G6]
theorem unramified_resLE_of_unramified
    {f : X ⟶ S} (hunram : Unramified f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    Unramified (f.resLE V U e) := sorry

/-- Lemma 29.35.3 (5): a morphism of schemes is G-unramified if and only if for every affine open
`U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced ring map on sections
`\Gamma(S, V) → \Gamma(X, U)` is G-unramified. -/
@[stacks 02G6]
theorem gUnramified_iff_affineOpen_appLE_gUnramified :
    GUnramified f ↔
      ∀ ⦃V : S.Opens⦄, IsAffineOpen V →
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
          Algebra.GUnramified Γ(S, V) Γ(X, U) := sorry

/-- Lemma 29.35.3 (6): a morphism of schemes is G-unramified if and only if there exists an open
cover of the target and open covers of the corresponding preimages such that each restricted
morphism is G-unramified. -/
@[stacks 02G6]
theorem gUnramified_iff_exists_openCover_preimageOpenCover :
    GUnramified f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, GUnramified ((𝒰.f i) ≫ (𝒱.pullbackHom f j)) := sorry

/-- Lemma 29.35.3 (7): a morphism of schemes is G-unramified if and only if there exists an
affine open covering of the target and affine open coverings of the corresponding preimages such
that the induced ring maps on sections are G-unramified. -/
@[stacks 02G6]
theorem gUnramified_iff_exists_affineOpenCover_preimageAffineOpenCover :
    GUnramified f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            let _ : Algebra Γ(S, 𝒱.obj j) Γ(X, 𝒰.obj i) :=
              (((𝒰.f i) ≫ (𝒱.openCover.pullbackHom f j)).appTop).hom.toAlgebra
            Algebra.GUnramified Γ(S, 𝒱.obj j) Γ(X, 𝒰.obj i) := sorry

/-- Lemma 29.35.3 (8): if `f : X ⟶ S` is G-unramified, then for any open subschemes `U ⊆ X` and
`V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is G-unramified. -/
@[stacks 02G6]
theorem gUnramified_resLE_of_gUnramified
    {f : X ⟶ S} (hgUnram : GUnramified f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    GUnramified (f.resLE V U e) := sorry

end

end Scheme.Hom

end AlgebraicGeometry

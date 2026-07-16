import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_3
import StacksProject_2024.stacks_project.Chap29.Lemma_29_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

section

namespace AlgebraicGeometry

namespace Scheme.Hom

-- Semantic recall / analogue check:
-- `Definition_29_30_1.lean` fixes the source-facing owner as
-- `Syntomic f := LocallyOfType RingHom.Syntomic f`;
-- `Lemma_29_14_3.lean` and `Lemma_29_14_4.lean` already provide the canonical affine-open,
-- open-cover, affine-open-cover, and restriction API for `LocallyOfType`. This file records the
-- corresponding syntomic specialization directly on those canonical open-cover owners, following
-- the same public surface used later in Chapter 29 for étale morphisms.

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 29.30.2 (1): a morphism of schemes is syntomic if and only if for every affine open
`U ⊆ X` and affine open `V ⊆ S` with `f(U) ⊆ V`, the induced ring map
`\Gamma(V, \mathcal O_S) → \Gamma(U, \mathcal O_X)` is syntomic. -/
@[stacks 01UD]
theorem syntomic_iff_affineOpen_appLE_syntomic
    :
    Syntomic f ↔
      ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Syntomic ((f.appLE V U e).hom) := sorry

/-- Lemma 29.30.2 (2): a morphism of schemes is syntomic if and only if there is an open cover of
the target such that each pullback piece over a member of that cover admits an open cover by
schemes syntomic over that member. -/
@[stacks 01UD]
theorem syntomic_iff_exists_openCover_preimageOpenCover :
    Syntomic f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, Syntomic ((𝒰.f i) ≫ (𝒱.pullbackHom f j)) := sorry

/-- Lemma 29.30.2 (3): a morphism of schemes is syntomic if and only if there are affine open
covers of the target such that each pullback piece over a member of that cover admits an affine
open cover on which the induced map on global sections is syntomic. -/
@[stacks 01UD]
theorem syntomic_iff_exists_affineOpenCover_preimageAffineOpenCover :
    Syntomic f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            RingHom.Syntomic ((((𝒰.f i) ≫ (𝒱.openCover.pullbackHom f j)).appTop).hom) := sorry

/-- Lemma 29.30.2 (4): if `f : X ⟶ S` is syntomic, then for any open subschemes `U ⊆ X` and
`V ⊆ S` with `f(U) ⊆ V`, the restricted morphism `U ⟶ V` is syntomic. -/
@[stacks 01UD]
theorem syntomic_resLE_of_syntomic
    (hsyntomic : Syntomic f) {U : X.Opens} {V : S.Opens}
    (e : U ≤ f ⁻¹ᵁ V) :
    Syntomic (f.resLE V U e) := sorry

end Scheme.Hom

end AlgebraicGeometry

end

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

section

variable {X S : Scheme.{u}}

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `locallyOfFiniteType_iff` is already the canonical affine-open characterization of
  `LocallyOfFiniteType`;
- the restriction stability of `LocallyOfFiniteType` along `f.resLE V U e` is already the
  canonical mathlib instance route;
- `Chap29/Definition_29_15_1.lean` records the source-style bridge
  `locallyOfFiniteType_iff_locallyOfType`;
- `Chap29/Lemma_29_14_4.lean` already gives the general source-facing open-cover and affine-open-
  cover formulations for `LocallyOfType`, so this file keeps only the Chapter 29 specializations
  of those cover statements to `RingHom.FiniteType` as local theorems.
-/

/- Lemma 29.15.2 (1): this affine-open characterization is exactly the canonical owner theorem
`AlgebraicGeometry.locallyOfFiniteType_iff`. -/
recall AlgebraicGeometry.locallyOfFiniteType_iff
    {X S : Scheme.{u}} (f : X ⟶ S) :
    LocallyOfFiniteType f ↔
      ∀ ⦃U : S.Opens⦄, IsAffineOpen U →
        ∀ ⦃V : X.Opens⦄, IsAffineOpen V → ∀ e : V ≤ f ⁻¹ᵁ U,
          (CommRingCat.Hom.hom (f.appLE U V e)).FiniteType

/-- Lemma 29.15.2 (2): a morphism of schemes is locally of finite type if and only if there is an
open cover of the base and open covers of the corresponding preimages such that each restricted
morphism is locally of finite type. -/
@[stacks 01T2]
theorem locallyOfFiniteType_iff_exists_openCover
    (f : X ⟶ S) :
    LocallyOfFiniteType f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, LocallyOfFiniteType (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- Lemma 29.15.2 (3): a morphism of schemes is locally of finite type if and only if there are
affine open covers `V_j` of `S` and `U_i` of each `f^{-1}(V_j)` such that the induced ring maps
on sections are of finite type. -/
@[stacks 01T2]
theorem locallyOfFiniteType_iff_exists_affineOpenCover
    (f : X ⟶ S) :
    LocallyOfFiniteType f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j))).FiniteType := sorry

/- Lemma 29.15.2 (4): restriction to open subschemes is already the canonical instance on
`f.resLE V U e`. -/
recall AlgebraicGeometry.instLocallyOfFiniteTypeResLE
    {f : X ⟶ S} {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (f.resLE V U e)

end Scheme.Hom

end

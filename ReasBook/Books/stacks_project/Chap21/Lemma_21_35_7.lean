import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of modules on the given ringed site. -/
abbrev RingedSiteModules (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

/-- The unbounded derived category `D(\mathcal O)` of sheaves of `\mathcal O`-modules on the
given ringed site. -/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v})
    [Abelian (RingedSiteModules J 𝒪)] :=
  DerivedCategory (RingedSiteModules J 𝒪)

variable [Abelian (RingedSiteModules J 𝒪)]
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]

/-- Lemma 21.35.7: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical morphism
`K \otimes_\mathcal O^{\mathbf L} R\mathcal H\!\mathit{om}(M, L) \to
R\mathcal H\!\mathit{om}(M, K \otimes_\mathcal O^{\mathbf L} L)`.
In the closed monoidal formalization of `D(\mathcal O)`, `R\mathcal H\!\mathit{om}(A, B)` is
`(ihom A).obj B`, and this morphism is the adjoint transpose of the map obtained by braiding `M`
past `K` and then evaluating `R\mathcal H\!\mathit{om}(M, L)`. -/
noncomputable def ringedSiteDerivedTensorInternalHomComparison
    (K L M : RingedSiteDerived J 𝒪) :
    (K ⊗ (ihom M).obj L) ⟶ (ihom M).obj (K ⊗ L) :=
  MonoidalClosed.curry
    ((α_ M K ((ihom M).obj L)).inv ≫
      ((β_ M K).hom ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
      (α_ K M ((ihom M).obj L)).hom ≫
      (𝟙 K ⊗ₘ (ihom.ev M).app L))

-- Proof sketch: this is immediate from the definition and the `curry`/`uncurry` adjunction in
-- the closed monoidal category `D(\mathcal O)`.
/-- Uncurrying the tensor-internal-Hom comparison recovers the braiding-evaluation composite used
to define it. -/
theorem ringedSiteDerivedTensorInternalHomComparison_uncurry
    (K L M : RingedSiteDerived J 𝒪) :
    MonoidalClosed.uncurry (ringedSiteDerivedTensorInternalHomComparison K L M) =
      (α_ M K ((ihom M).obj L)).inv ≫
        ((β_ M K).hom ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
        (α_ K M ((ihom M).obj L)).hom ≫
        (𝟙 K ⊗ₘ (ihom.ev M).app L) := sorry

-- Proof sketch: apply naturality of the braiding, associator, `MonoidalClosed.pre`, and
-- `ihom.map` to the defining uncurried composite, then use the injectivity of `curry`.
/-- The tensor-internal-Hom comparison is functorial in `K` and `L`, and contravariantly
functorial in `M`. -/
theorem ringedSiteDerivedTensorInternalHomComparison_natural
    {K₁ K₂ L₁ L₂ M₁ M₂ : RingedSiteDerived J 𝒪}
    (fK : K₁ ⟶ K₂) (fL : L₁ ⟶ L₂) (fM : M₁ ⟶ M₂) :
    (fK ⊗ₘ ((MonoidalClosed.pre fM).app L₁ ≫ (ihom M₁).map fL)) ≫
        ringedSiteDerivedTensorInternalHomComparison K₂ L₂ M₁ =
      ringedSiteDerivedTensorInternalHomComparison K₁ L₁ M₂ ≫
        (MonoidalClosed.pre fM).app (K₁ ⊗ L₁) ≫
        (ihom M₁).map (fK ⊗ₘ fL) := sorry

end

end SheafOfModules.RingedSite

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

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
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

/-- Lemma 21.35.8: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L` of
`D(\mathcal O)`, the canonical coevaluation morphism
`K \to R\mathcal H\!\mathit{om}(L, K \otimes_\mathcal O^{\mathbf L} L)`. In the closed monoidal
formalization of `D(\mathcal O)`, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the
canonical morphism is the adjoint transpose of the braiding
`L \otimes K \to K \otimes L`. -/
noncomputable def ringedSiteDerivedTensorInternalHomUnit
    (K L : RingedSiteDerived J 𝒪) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  MonoidalClosed.curry ((β_ L K).hom)

-- Proof sketch: uncurry both sides. Naturality in `K` reduces to naturality of the braiding in
-- the second variable, followed by the naturality of `curry` with respect to postcomposition on
-- the target of `R\mathcal H\!\mathit{om}(L, -)`.
/-- The canonical derived tensor-Hom unit is functorial in the left variable `K`. -/
theorem ringedSiteDerivedTensorInternalHomUnit_naturalLeft
    {K₁ K₂ L : RingedSiteDerived J 𝒪} (α : K₁ ⟶ K₂) :
    α ≫ ringedSiteDerivedTensorInternalHomUnit K₂ L =
      ringedSiteDerivedTensorInternalHomUnit K₁ L ≫
        (ihom L).map (α ⊗ₘ 𝟙 L) := sorry

-- Proof sketch: uncurry both sides. Naturality in `L` is the compatibility of the braiding with
-- a morphism `β : L₁ ⟶ L₂`, rewritten through the contravariant action `MonoidalClosed.pre β`
-- on the first internal-Hom argument and the induced map on the tensor target.
/-- The canonical derived tensor-Hom unit is functorial in the right variable `L`. -/
theorem ringedSiteDerivedTensorInternalHomUnit_naturalRight
    (K : RingedSiteDerived J 𝒪) {L₁ L₂ : RingedSiteDerived J 𝒪} (β : L₁ ⟶ L₂) :
    ringedSiteDerivedTensorInternalHomUnit K L₂ ≫
        (MonoidalClosed.pre β).app (K ⊗ L₂) =
      ringedSiteDerivedTensorInternalHomUnit K L₁ ≫
        (ihom L₁).map (𝟙 K ⊗ₘ β) := sorry

end

end SheafOfModules.RingedSite

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

/-- Lemma 21.35.5: for a ringed site `(\mathcal C, \mathcal O)` and objects `K`, `L`, `M` of
`D(\mathcal O)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_\mathcal O^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)`. In the monoidal closed derived
category formalization used here, `R\mathcal H\!\mathit{om}(A, B)` is `(ihom A).obj B`, and the
canonical morphism is the currying of the composite obtained by first evaluating
`R\mathcal H\!\mathit{om}(K, L)` on `K` and then evaluating `R\mathcal H\!\mathit{om}(L, M)` on
the resulting object `L`. -/
noncomputable def ringedSiteDerivedTensorInternalHomToIteratedInternalHom
    (K L M : RingedSiteDerived J 𝒪) :
    ((ihom L).obj M ⊗ K) ⟶
      (ihom ((ihom K).obj L)).obj M :=
  let A := (ihom L).obj M
  let B := (ihom K).obj L
  MonoidalClosed.curry
    ((α_ B A K).inv ≫
      ((β_ B A).hom ⊗ₘ 𝟙 K) ≫
      (α_ A B K).hom ≫
      (𝟙 A ⊗ₘ (β_ B K).hom) ≫
      (𝟙 A ⊗ₘ (ihom.ev K).app L) ≫
      (β_ A L).hom ≫
      (ihom.ev L).app M)

-- Proof sketch: this is the defining `curry`/`uncurry` adjunction in the closed monoidal
-- category `D(\mathcal O)`. Uncurrying the displayed morphism returns the composite of the
-- braiding and the two evaluation maps that was curried in the definition.
/-- Uncurrying the canonical derived tensor-to-iterated-internal-Hom morphism recovers the
evaluation composite used to define it. -/
theorem ringedSiteDerivedTensorInternalHomToIteratedInternalHom_uncurry
    (K L M : RingedSiteDerived J 𝒪) :
    MonoidalClosed.uncurry
      (ringedSiteDerivedTensorInternalHomToIteratedInternalHom K L M) =
      (α_ ((ihom K).obj L) ((ihom L).obj M) K).inv ≫
        ((β_ ((ihom K).obj L) ((ihom L).obj M)).hom ⊗ₘ 𝟙 K) ≫
        (α_ ((ihom L).obj M) ((ihom K).obj L) K).hom ≫
        (𝟙 ((ihom L).obj M) ⊗ₘ (β_ ((ihom K).obj L) K).hom) ≫
        (𝟙 ((ihom L).obj M) ⊗ₘ (ihom.ev K).app L) ≫
        (β_ ((ihom L).obj M) L).hom ≫
        (ihom.ev L).app M := sorry

end

end SheafOfModules.RingedSite
